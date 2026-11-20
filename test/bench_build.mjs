/**
 * Fast, low-noise build-time regression detector for QED.
 *
 * Combines two layers:
 *   1. Zero-jitter structural guardrails (~15ms, 0% noise):
 *      - Pure non-meta modules must never transitively import `Lean`
 *      - Critical-path / proof-module import separation rules
 *      - Rust `Cargo.lock` crate count budget
 *      - Per-target `.olean` byte totals
 *   2. Selective `lean --profile` + end-to-end CLI timings vs. a saved baseline:
 *      - Default (fast mode, ~5–8s): profiles git-changed `.lean` files + 4 high-signal
 *        canaries (`Render`, `ValidLemmas`, `CloudBooks`, `SyntaxChecks`) + `./scripts/qed check`.
 *      - `--all`: profiles all library/proof/example/test modules, computes exact
 *        time-weighted critical paths (`Qed`, `QedServer`, `QedProofs`, `JsProofs`,
 *        `Tests.SyntaxChecks`), plus `qed check` and `qed build` (Counter & CloudBooks).
 *      - Dual regression gate (+threshold% AND +min-delta-ms) with automatic min-of-2
 *        re-verification on any suspect module to eliminate wall-clock jitter, plus
 *        phase-level `lean --profile` root-cause deltas.
 *
 * Usage:
 *   node test/bench_build.mjs --all --save-baseline   # save full baseline (122 modules)
 *   node test/bench_build.mjs                         # fast check (changed files + canaries)
 *   node test/bench_build.mjs --fail-on-regression    # fail CI / pre-push on regressions
 *   node test/bench_build.mjs --since origin/main     # check all files changed since ref
 *   node test/bench_build.mjs Qed/Render.lean         # check specific file(s)
 */
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import zlib from 'node:zlib';
import { ROOT, withElanPath } from './harness.mjs';

const BENCH_DIR = path.join(ROOT, '.qed', 'bench');
mkdirSync(BENCH_DIR, { recursive: true });

// ---- CLI args ----
const args = process.argv.slice(2);
const hasFlag = (f) => args.includes(f);
const flagVal = (f) => {
  const i = args.indexOf(f);
  return i >= 0 && args[i + 1] && !args[i + 1].startsWith('--') ? args[i + 1] : null;
};
const positional = [];
for (let i = 0; i < args.length; i++) {
  if (args[i].startsWith('--')) {
    if (['--baseline', '--save-baseline', '--since', '--threshold', '--min-delta-ms', '--jobs'].includes(args[i]) &&
        args[i + 1] && !args[i + 1].startsWith('--')) i++;
  } else {
    positional.push(args[i]);
  }
}

const ALL_MODE = hasFlag('--all');
const SAVE_BASELINE = hasFlag('--save-baseline') || process.env.SAVE_BASELINE === '1';
const FAIL_ON_REGRESSION = hasFlag('--fail-on-regression');
const SINCE_REF = flagVal('--since');
const THRESHOLD_PCT = Number(flagVal('--threshold') || process.env.BUILD_THRESHOLD_PCT || 20);
const MIN_DELTA_MS = Number(flagVal('--min-delta-ms') || process.env.BUILD_MIN_DELTA_MS || 150);
const OLEAN_PCT = 15;
const OLEAN_MIN_BYTES = 512 * 1024;
const JOBS = Math.max(1, Number(flagVal('--jobs') || (ALL_MODE ? Math.min(4, Math.max(1, Math.floor(os.cpus().length / 4))) : 1)));
const BASELINE_PATH = flagVal('--baseline') || flagVal('--save-baseline') || path.join(BENCH_DIR, 'build_baseline.json');
const baseline = existsSync(BASELINE_PATH) ? JSON.parse(readFileSync(BASELINE_PATH, 'utf8')) : null;

const ENV = withElanPath();
const QED_BIN = existsSync(path.join(ROOT, '.lake', 'build', 'bin', 'qed'))
  ? path.join(ROOT, '.lake', 'build', 'bin', 'qed')
  : path.join(ROOT, 'scripts', 'qed');

const CANARY_FILES = [
  'Qed/Render.lean',
  'Qed/Runtime/ValidLemmas.lean',
  'Examples/CloudBooks.lean',
  'Tests/SyntaxChecks.lean',
];

const TARGET_ROOTS = {
  Qed: ['Qed'],
  QedServer: ['Qed.Server.Native'],
  QedProofs: ['Qed.Proofs.DomArena', 'Qed.Proofs.KeyedReconcile', 'Qed.Proofs.ViewPatch', 'Qed.Proofs.Hydration'],
  JsProofs: ['Js.Proofs'],
  'Tests.SyntaxChecks': ['Tests.SyntaxChecks'],
};

const PURE_EXACT = new Set([
  'Qed.Html', 'Qed.Render', 'Qed.View.Core', 'Qed.Ssr', 'Qed.Resource',
  'Qed.Socket', 'Qed.Driver', 'Qed.Speculative',
  'Qed.Runtime.AppCore', 'Qed.Runtime.LocalCore', 'Qed.Runtime.Cmd',
  'Qed.Server.Core', 'Qed.Server.Http', 'Qed.Server.Net', 'Qed.Server.Prim',
  'Qed.Server.Native', 'Qed.Server.Ensured',
]);
const PURE_PREFIXES = ['Qed.Driver.', 'Qed.Socket.', 'Qed.Speculative.', 'Qed.Proofs.'];

const FORBIDDEN_EDGES = [
  ['Qed.Style.Syntax',          'Qed.Style.Proofs'],
  ['Qed.Component.Speculative', 'Qed.Speculative.Proofs'],
  ['Qed.Server.Core',           'Qed.Json.Proofs'],
  ['Qed.Socket.Basic',          'Qed.Json.Proofs'],
  ['Qed.Server.Syntax',         'Qed.Server.Core'],
  ['Qed.Server.FnElab',         'Qed.Server.Invariant'],
  ['Qed.Server.FnElab',         'Qed.Server.External'],
  ['Qed.Invariant.State',       'Qed.Runtime.App'],
  ['Qed.Invariant.View',        'Qed.Runtime.App'],
  ['Qed.Invariant.ForEach',     'Qed.Runtime.App'],
  ['Qed.Invariant.View',        'Qed.Invariant.State'],
  ['Qed.Schema',                'Qed.Runtime.Verify'],
  ['Qed.Component.Rewrite',     'Qed.Runtime.Verify'],
];
const MAX_RUST_CRATES = 30;

// ---- Helpers ----
function collectLeanFiles(dir, out = []) {
  const full = path.join(ROOT, dir);
  if (!existsSync(full)) return out;
  for (const ent of readdirSync(full, { withFileTypes: true })) {
    const rel = path.join(dir, ent.name);
    if (ent.isDirectory()) collectLeanFiles(rel, out);
    else if (ent.name.endsWith('.lean')) out.push(rel.replace(/\\/g, '/'));
  }
  return out;
}

const fileToMod = (rel) => rel.replace(/\.lean$/, '').replace(/\//g, '.');
const modToOlean = (mod) => path.join(ROOT, '.lake', 'build', 'lib', 'lean', ...mod.split('.')) + '.olean';

function parseImports(rel) {
  const src = readFileSync(path.join(ROOT, rel), 'utf8');
  const imps = [];
  for (const raw of src.split('\n')) {
    const line = raw.trim();
    if (line.startsWith('import ')) {
      const m = line.slice(7).trim().split(/\s|--/)[0];
      if (m) imps.push(m);
    }
  }
  return imps;
}

function buildImportGraph() {
  const files = [
    ...(existsSync(path.join(ROOT, 'Qed.lean')) ? ['Qed.lean'] : []),
    ...collectLeanFiles('Qed'),
    ...collectLeanFiles('Js'),
    ...collectLeanFiles('Examples'),
    ...collectLeanFiles('Tests'),
  ].sort();
  const adj = new Map();
  const modFile = new Map();
  for (const f of files) {
    const m = fileToMod(f);
    modFile.set(m, f);
    adj.set(m, parseImports(f));
  }
  return { files, adj, modFile };
}

function transitiveClosure(adj, roots) {
  const seen = new Set();
  const stack = [...roots];
  while (stack.length) {
    const cur = stack.pop();
    if (seen.has(cur) || !adj.has(cur)) continue;
    seen.add(cur);
    for (const dep of adj.get(cur)) {
      if (adj.has(dep) && !seen.has(dep)) stack.push(dep);
    }
  }
  return seen;
}

function reaches(adj, start, target) {
  const seen = new Set();
  const stack = [start];
  while (stack.length) {
    const cur = stack.pop();
    if (seen.has(cur)) continue;
    seen.add(cur);
    for (const dep of adj.get(cur) || []) {
      if (dep === target || (target === 'Lean' && dep.startsWith('Lean.'))) return true;
      if (adj.has(dep) && !seen.has(dep)) stack.push(dep);
    }
  }
  return false;
}

function checkStructure(adj) {
  const errors = [];
  let pureCount = 0;
  for (const mod of adj.keys()) {
    const isPure = PURE_EXACT.has(mod) || PURE_PREFIXES.some((p) => mod.startsWith(p));
    if (isPure) {
      if (reaches(adj, mod, 'Lean')) {
        errors.push(`pure module \`${mod}\` transitively imports \`Lean\``);
      } else {
        pureCount++;
      }
    }
  }
  for (const [src, dst] of FORBIDDEN_EDGES) {
    if (adj.has(src) && reaches(adj, src, dst)) {
      errors.push(`\`${src}\` reaches forbidden dependency \`${dst}\``);
    }
  }
  const lockPath = path.join(ROOT, 'rust', 'qed_server', 'Cargo.lock');
  let rustCrates = 0;
  if (existsSync(lockPath)) {
    const src = readFileSync(lockPath, 'utf8');
    rustCrates = (src.match(/^\[\[package\]\]$/gm) || []).length;
    if (rustCrates > MAX_RUST_CRATES) {
      errors.push(`rust/qed_server/Cargo.lock has ${rustCrates} crates (budget ≤ ${MAX_RUST_CRATES})`);
    }
  }
  const oleanBytes = {};
  for (const [name, roots] of Object.entries(TARGET_ROOTS)) {
    let total = 0;
    for (const m of transitiveClosure(adj, roots)) {
      const p = modToOlean(m);
      if (existsSync(p)) total += statSync(p).size;
    }
    oleanBytes[name] = total;
  }
  return { errors, pureCount, rustCrates, oleanBytes };
}

function resolveLeanPath() {
  const leanLib = path.join(ROOT, '.lake', 'build', 'lib', 'lean');
  if (existsSync(leanLib) && !existsSync(path.join(ROOT, '.lake', 'packages'))) {
    const sysroot = execFileSync('lean', ['--print-libdir'], { env: ENV, encoding: 'utf8' }).trim();
    return `${leanLib}:${sysroot}`;
  }
  return execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: ROOT, env: ENV, encoding: 'utf8' }).trim();
}

function parseProfileMs(stderr) {
  const phases = {};
  for (const line of stderr.split('\n')) {
    const m = line.match(/^\t(.+?)\s+([0-9.]+)(ms|s)\s*$/);
    if (m) {
      const ms = m[3] === 's' ? Number(m[2]) * 1000 : Number(m[2]);
      phases[m[1]] = Math.round(ms * 10) / 10;
    }
  }
  return phases;
}

function profileModuleAsync(rel, leanPath) {
  return new Promise((resolve, reject) => {
    const t0 = process.hrtime.bigint();
    const child = spawn('lean', ['--root=.', '--profile', rel], {
      cwd: ROOT,
      env: { ...ENV, LEAN_PATH: leanPath },
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let out = '', err = '';
    child.stdout.on('data', (d) => { out += d; });
    child.stderr.on('data', (d) => { err += d; });
    child.on('error', reject);
    child.on('close', (code) => {
      const wallMs = Math.round(Number(process.hrtime.bigint() - t0) / 1e6);
      if (code !== 0) {
        reject(new Error(`lean --profile ${rel} failed (exit ${code}):\n${out}${err}`));
        return;
      }
      const phases = parseProfileMs(out + '\n' + err);
      const oleanPath = modToOlean(fileToMod(rel));
      const oleanBytes = existsSync(oleanPath) ? statSync(oleanPath).size : 0;
      resolve({ wall_ms: wallMs, olean_bytes: oleanBytes, phases });
    });
  });
}

async function profileBatch(files, leanPath, jobs) {
  const out = {};
  let idx = 0;
  const workers = Array.from({ length: Math.min(jobs, files.length) }, async () => {
    while (idx < files.length) {
      const rel = files[idx++];
      out[rel] = await profileModuleAsync(rel, leanPath);
    }
  });
  await Promise.all(workers);
  return out;
}

function computeCriticalPath(adj, roots, modTimesMs) {
  const nodes = transitiveClosure(adj, roots);
  const memo = new Map();
  const visit = (m) => {
    if (memo.has(m)) return memo.get(m);
    const self = modTimesMs.get(m) || 0;
    let best = 0;
    for (const d of adj.get(m) || []) {
      if (nodes.has(d)) best = Math.max(best, visit(d));
    }
    const total = self + best;
    memo.set(m, total);
    return total;
  };
  let seqSum = 0;
  let crit = 0;
  for (const m of nodes) {
    seqSum += modTimesMs.get(m) || 0;
    crit = Math.max(crit, visit(m));
  }
  return { mods: nodes.size, seq_ms: Math.round(seqSum), crit_ms: Math.round(crit) };
}

function timeCommand(cmd, cmdArgs, extraEnv = {}) {
  const t0 = process.hrtime.bigint();
  const r = spawnSync(cmd, cmdArgs, {
    cwd: ROOT,
    env: { ...ENV, QED_HOME: ROOT, ...extraEnv },
    encoding: 'utf8',
  });
  const wallMs = Math.round(Number(process.hrtime.bigint() - t0) / 1e6);
  if (r.status !== 0) {
    throw new Error(`${cmd} ${cmdArgs.join(' ')} failed:\n${r.stdout || ''}${r.stderr || ''}`);
  }
  return wallMs;
}

function measureProdBuild(webRoot) {
  const distDir = path.join(ROOT, 'dist');
  rmSync(distDir, { recursive: true, force: true });
  try {
    const wallMs = timeCommand(QED_BIN, ['build'], { QED_WEB_ROOT: webRoot });
    let gzBytes = 0;
    if (existsSync(distDir)) {
      for (const f of readdirSync(distDir)) {
        if (f.endsWith('.mjs') && !f.startsWith('ssr')) {
          gzBytes += zlib.gzipSync(readFileSync(path.join(distDir, f))).length;
        }
      }
    }
    return { wall_ms: wallMs, gz_bytes: gzBytes };
  } finally {
    rmSync(distDir, { recursive: true, force: true });
  }
}

function gitChangedLeanFiles(sinceRef) {
  const changed = new Set();
  const runGit = (gitArgs) => {
    const r = spawnSync('git', gitArgs, { cwd: ROOT, encoding: 'utf8' });
    if (r.status !== 0) return;
    for (const line of r.stdout.split('\n')) {
      const f = line.trim().replace(/\\/g, '/');
      if (f.endsWith('.lean') && existsSync(path.join(ROOT, f))) changed.add(f);
    }
  };
  if (sinceRef) {
    runGit(['diff', '--name-only', `${sinceRef}...HEAD`]);
  }
  runGit(['diff', '--name-only', 'HEAD']);
  runGit(['ls-files', '--others', '--exclude-standard', '*.lean']);
  return [...changed].filter((f) => !f.startsWith('Cli/') && f !== 'Cli.lean' && !f.startsWith('scripts/') && !f.startsWith('Bench/') && f !== 'lakefile.lean');
}

const fmtMs = (ms) => (ms >= 1000 ? `${(ms / 1000).toFixed(2)}s` : `${Math.round(ms)}ms`);
const fmtMb = (b) => `${(b / (1024 * 1024)).toFixed(2)} MB`;
const fmtDelta = (curr, prev) => {
  if (prev == null || prev <= 0) return '';
  const pct = ((curr - prev) / prev) * 100;
  return ` (${pct >= 0 ? '+' : ''}${pct.toFixed(1)}%)`;
};

function topPhaseDeltas(currPhases, prevPhases) {
  if (!prevPhases) return '';
  const keys = new Set([...Object.keys(currPhases || {}), ...Object.keys(prevPhases || {})]);
  const diffs = [];
  for (const k of keys) {
    const d = (currPhases?.[k] || 0) - (prevPhases?.[k] || 0);
    if (Math.abs(d) >= 30) diffs.push([k, d]);
  }
  diffs.sort((a, b) => Math.abs(b[1]) - Math.abs(a[1]));
  return diffs.slice(0, 3).map(([k, d]) => `${k} ${d >= 0 ? '+' : ''}${Math.round(d)}ms`).join(', ');
}

// ---- Main ----
const { files: allFiles, adj } = buildImportGraph();
const struct = checkStructure(adj);

// Warm check / ensure .olean files are up to date before profiling
const qedCheckMs = timeCommand(QED_BIN, ['check']);
const leanPath = resolveLeanPath();

let targetFiles;
let modeLabel;
if (ALL_MODE) {
  targetFiles = allFiles;
  modeLabel = `all ${allFiles.length} modules (jobs=${JOBS})`;
} else if (positional.length > 0) {
  targetFiles = positional.map((f) => f.replace(/\\/g, '/'));
  modeLabel = `${targetFiles.length} specified file(s)`;
} else {
  const changed = gitChangedLeanFiles(SINCE_REF);
  const set = new Set([...changed, ...CANARY_FILES.filter((f) => existsSync(path.join(ROOT, f)))]);
  targetFiles = [...set].sort();
  modeLabel = `fast (${changed.length} changed + ${CANARY_FILES.length} canaries)`;
}

const modules = await profileBatch(targetFiles, leanPath, JOBS);

// Anti-jitter re-verify (min-of-2) for any suspect timing regression
const regressions = [];
for (const err of struct.errors) regressions.push(`structure: ${err}`);

for (const rel of targetFiles) {
  const prev = baseline?.modules?.[rel];
  if (!prev) continue;
  let curr = modules[rel];
  const pct = prev.wall_ms > 0 ? ((curr.wall_ms - prev.wall_ms) / prev.wall_ms) * 100 : 0;
  if (pct > THRESHOLD_PCT && (curr.wall_ms - prev.wall_ms) > MIN_DELTA_MS) {
    // Re-measure single-threaded to rule out transient OS/CPU jitter
    const retry = await profileModuleAsync(rel, leanPath);
    if (retry.wall_ms < curr.wall_ms) {
      modules[rel] = retry;
      curr = retry;
    }
    const pct2 = prev.wall_ms > 0 ? ((curr.wall_ms - prev.wall_ms) / prev.wall_ms) * 100 : 0;
    if (pct2 > THRESHOLD_PCT && (curr.wall_ms - prev.wall_ms) > MIN_DELTA_MS) {
      const cause = topPhaseDeltas(curr.phases, prev.phases);
      regressions.push(
        `module ${rel}: ${fmtMs(prev.wall_ms)} → ${fmtMs(curr.wall_ms)} (+${pct2.toFixed(1)}%)` +
        (cause ? ` [${cause}]` : '')
      );
    }
  }
  if (prev.olean_bytes > 0 && curr.olean_bytes > 0) {
    const oPct = ((curr.olean_bytes - prev.olean_bytes) / prev.olean_bytes) * 100;
    if (oPct > OLEAN_PCT && (curr.olean_bytes - prev.olean_bytes) > OLEAN_MIN_BYTES) {
      regressions.push(
        `.olean ${rel}: ${fmtMb(prev.olean_bytes)} → ${fmtMb(curr.olean_bytes)} (+${oPct.toFixed(1)}%)`
      );
    }
  }
}

// Re-verify qed check if regressed
let finalQedCheckMs = qedCheckMs;
if (baseline?.commands?.qed_check_ms) {
  const prev = baseline.commands.qed_check_ms;
  const pct = ((finalQedCheckMs - prev) / prev) * 100;
  if (pct > THRESHOLD_PCT && (finalQedCheckMs - prev) > MIN_DELTA_MS) {
    finalQedCheckMs = Math.min(finalQedCheckMs, timeCommand(QED_BIN, ['check']));
    const pct2 = ((finalQedCheckMs - prev) / prev) * 100;
    if (pct2 > THRESHOLD_PCT && (finalQedCheckMs - prev) > MIN_DELTA_MS) {
      regressions.push(`qed check: ${fmtMs(prev)} → ${fmtMs(finalQedCheckMs)} (+${pct2.toFixed(1)}%)`);
    }
  }
}

// Optional end-to-end prod builds & critical path in --all mode
const commands = { qed_check_ms: finalQedCheckMs };
let criticalPaths = null;
if (ALL_MODE) {
  const modTimesMs = new Map();
  for (const [rel, data] of Object.entries(modules)) modTimesMs.set(fileToMod(rel), data.wall_ms);
  criticalPaths = {};
  for (const [name, roots] of Object.entries(TARGET_ROOTS)) {
    criticalPaths[name] = computeCriticalPath(adj, roots, modTimesMs);
  }
  criticalPaths.All = computeCriticalPath(adj, [...adj.keys()], modTimesMs);

  commands.counter_prod = measureProdBuild('Examples.Counter');
  commands.cloudbooks_prod = measureProdBuild('Examples.CloudBooks');
  for (const [k, label] of [['counter_prod', 'Counter prod'], ['cloudbooks_prod', 'CloudBooks prod']]) {
    const prev = baseline?.commands?.[k];
    const curr = commands[k];
    if (prev?.gz_bytes > 0) {
      const gzPct = ((curr.gz_bytes - prev.gz_bytes) / prev.gz_bytes) * 100;
      if (gzPct > 10) {
        regressions.push(`${label} gzipped bundle: ${prev.gz_bytes} B → ${curr.gz_bytes} B (+${gzPct.toFixed(1)}%)`);
      }
    }
  }
}

// ---- Report ----
console.log(`\n  Build-Time Regression Check — ${modeLabel}${baseline ? ` [vs ${path.relative(ROOT, BASELINE_PATH)}]` : ''}\n`);
console.log(`  Structural guardrails: ${struct.errors.length === 0 ? 'PASS' : `FAIL (${struct.errors.length})`}  ·  guarded pure modules: ${struct.pureCount}  ·  Rust Cargo.lock crates: ${struct.rustCrates}/${MAX_RUST_CRATES}`);
const oleanLine = Object.entries(struct.oleanBytes)
  .filter(([k]) => k !== 'Tests.SyntaxChecks')
  .map(([k, b]) => `${k} ${fmtMb(b)}${fmtDelta(b, baseline?.structure?.oleanBytes?.[k])}`)
  .join('  ·  ');
console.log(`  .olean footprints    : ${oleanLine}`);
console.log(`  ./scripts/qed check  : ${fmtMs(finalQedCheckMs)}${fmtDelta(finalQedCheckMs, baseline?.commands?.qed_check_ms)}`);

if (criticalPaths) {
  console.log('\n  Target                 Mods         Seq Sum              Critical Path');
  console.log('  ' + '-'.repeat(72));
  for (const [name, cp] of Object.entries(criticalPaths)) {
    const p = baseline?.criticalPaths?.[name];
    const seqStr = `${fmtMs(cp.seq_ms)}${fmtDelta(cp.seq_ms, p?.seq_ms)}`.padStart(20);
    const critStr = `${fmtMs(cp.crit_ms)}${fmtDelta(cp.crit_ms, p?.crit_ms)}`.padStart(24);
    console.log(`  ${name.padEnd(22)} ${String(cp.mods).padStart(4)} ${seqStr} ${critStr}`);
  }
  console.log(`\n  Prod builds          : Counter ${fmtMs(commands.counter_prod.wall_ms)}${fmtDelta(commands.counter_prod.wall_ms, baseline?.commands?.counter_prod?.wall_ms)} (${(commands.counter_prod.gz_bytes / 1024).toFixed(1)} KB gz)  ·  CloudBooks ${fmtMs(commands.cloudbooks_prod.wall_ms)}${fmtDelta(commands.cloudbooks_prod.wall_ms, baseline?.commands?.cloudbooks_prod?.wall_ms)} (${(commands.cloudbooks_prod.gz_bytes / 1024).toFixed(1)} KB gz)`);
}

const rows = targetFiles
  .map((rel) => [rel, modules[rel], baseline?.modules?.[rel]])
  .sort((a, b) => b[1].wall_ms - a[1].wall_ms);
const shown = ALL_MODE ? rows.slice(0, 15) : rows;
console.log(`\n  ${ALL_MODE ? 'Top 15 slowest modules' : 'Profiled modules'}:`);
for (const [rel, curr, prev] of shown) {
  const cause = prev ? topPhaseDeltas(curr.phases, prev.phases) : '';
  console.log(
    `    ${rel.padEnd(36)} ${fmtMs(curr.wall_ms).padStart(7)}${fmtDelta(curr.wall_ms, prev?.wall_ms).padEnd(11)}` +
    (cause ? `  [${cause}]` : '')
  );
}

if (regressions.length > 0) {
  console.log(`\n  REGRESSIONS (${regressions.length}):`);
  for (const r of regressions) console.log(`    ✗ ${r}`);
} else {
  console.log('\n  ✓ No build-time regressions detected.');
}

if (SAVE_BASELINE) {
  const merged = {
    saved_at: new Date().toISOString(),
    structure: { pureCount: struct.pureCount, rustCrates: struct.rustCrates, oleanBytes: struct.oleanBytes },
    commands: { ...(baseline?.commands || {}), ...commands },
    criticalPaths: criticalPaths || baseline?.criticalPaths || null,
    modules: { ...(baseline?.modules || {}), ...modules },
  };
  writeFileSync(BASELINE_PATH, JSON.stringify(merged, null, 2) + '\n');
  console.log(`  Saved baseline (${Object.keys(merged.modules).length} modules) to ${path.relative(ROOT, BASELINE_PATH)}`);
} else if (!baseline) {
  console.log('  Tip: run `node test/bench_build.mjs --all --save-baseline` to save a full baseline.');
}
console.log('');

if (FAIL_ON_REGRESSION && regressions.length > 0) process.exit(1);
if (struct.errors.length > 0) process.exit(1);
