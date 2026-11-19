import { execFile, execFileSync, spawn, spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import { existsSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import puppeteer from 'puppeteer';

export { setTimeout as sleep } from 'node:timers/promises';

const execFileAsync = promisify(execFile);
export const ROOT = path.resolve(fileURLToPath(new URL('..', import.meta.url)));
export const SERVE = path.join(ROOT, '.qed', 'dev');
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.json': 'application/json', '.css': 'text/css' };
const LAUNCH_OPTS = { headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] };
const qedBin = () => existsSync(path.join(ROOT, '.lake', 'build', 'bin', 'qed')) ? path.join(ROOT, '.lake', 'build', 'bin', 'qed') : './scripts/qed';

export function withElanPath(env = process.env) {
  const elanBin = path.join(env.HOME || '', '.elan', 'bin');
  const PATH = elanBin && !(env.PATH || '').split(':').includes(elanBin) ? `${elanBin}:${env.PATH || ''}` : (env.PATH || '');
  return { ...env, PATH };
}

let cachedLeanPath = null;
export function leanEnv() {
  const env = withElanPath();
  if (!cachedLeanPath) {
    cachedLeanPath = env.LEAN_PATH || execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: ROOT, env, encoding: 'utf8' }).trim();
  }
  return { ...env, LEAN_PATH: cachedLeanPath };
}

function buildEnv(webRoot, outDir) {
  return { ...withElanPath(), QED_HOME: ROOT, QED_WEB_ROOT: webRoot, ...(outDir !== SERVE ? { QED_OUT_DIR: outDir } : {}) };
}

export function buildDev(webRoot = 'Examples.Counter', outDir = SERVE) {
  const r = spawnSync(qedBin(), ['build', '--dev'], { cwd: ROOT, env: buildEnv(webRoot, outDir), encoding: 'utf8' });
  if (r.status !== 0) { process.stderr.write((r.stdout || '') + (r.stderr || '')); process.exit(1); }
}

const buildCache = new Map();
export function buildDevAsync(webRoot = 'Examples.Counter', outDir = path.join(ROOT, '.qed', 'test', webRoot)) {
  if (!buildCache.has(outDir)) {
    buildCache.set(outDir, execFileAsync(qedBin(), ['build', '--dev'], { cwd: ROOT, env: buildEnv(webRoot, outDir), maxBuffer: 16 << 20 }).then(() => outDir));
  }
  return buildCache.get(outDir);
}

// ---- Shared Networking, Process, Auth & Protobuf Helpers ----

export const getFreePort = () => new Promise((resolve, reject) => {
  const s = net.createServer();
  s.once('error', reject);
  s.listen(0, '127.0.0.1', () => { const { port } = s.address(); s.close(() => resolve(port)); });
});

export const rawHttpReq = (port, rawReq) => new Promise((resolve, reject) => {
  const sock = net.connect(port, '127.0.0.1', () => sock.write(rawReq));
  const chunks = [];
  sock.on('data', (c) => chunks.push(c));
  sock.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
  sock.on('error', reject);
});

export const signSessionToken = (secret, userId) =>
  `${userId}.${crypto.createHmac('sha256', secret).update(userId).digest('hex')}`;

export async function stopProc(proc, timeoutMs = 1500) {
  if (!proc || proc.exitCode !== null) return;
  proc.kill('SIGTERM');
  await new Promise((resolve) => {
    const t = setTimeout(() => { try { proc.kill('SIGKILL'); } catch {} resolve(); }, timeoutMs);
    proc.once('exit', () => { clearTimeout(t); resolve(); });
  });
}

export async function waitHealth(baseUrl, timeoutMs = 4000) {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    try { if ((await fetch(`${baseUrl}/_qed/health`)).status === 200) return true; } catch {}
    await new Promise((r) => setTimeout(r, 40));
  }
  return false;
}

export async function startNativeServer(dir, extraEnv = {}, { dev = true, port = null } = {}) {
  const srvPort = port ?? await getFreePort();
  const baseUrl = `http://127.0.0.1:${srvPort}`;
  const args = [dir, String(srvPort), ...(dev ? ['--dev'] : [])];
  const env = { ...process.env, ...extraEnv };
  const spawnOne = () => spawn(path.join(dir, 'server'), args, { cwd: ROOT, env, stdio: ['ignore', 'pipe', 'pipe'] });
  let proc = spawnOne();
  const healthy = await waitHealth(baseUrl);
  return {
    port: srvPort,
    baseUrl,
    healthy,
    stop: () => stopProc(proc),
    restart: async () => {
      await stopProc(proc);
      proc = spawnOne();
      return waitHealth(baseUrl);
    },
  };
}

export function checkLeakGate(check, modName, decls) {
  const qedjsBin = path.join(ROOT, '.lake/build/bin/qedjs');
  const rtPath = path.join(ROOT, 'runtime/qed_rt.mjs');
  const env = leanEnv();
  for (const decl of decls) {
    const r = spawnSync(qedjsBin, ['--check-externs', rtPath, modName, '--', decl], { cwd: ROOT, env, encoding: 'utf8' });
    check(`leak gate blocks ${decl}`, r.status !== 0 && /client bundle leak gate/.test(r.stdout + r.stderr), true);
  }
}

export function encodeVarint(n) {
  let v = BigInt(n), out = [];
  while (v >= 128n) { out.push(Number((v & 0x7fn) | 0x80n)); v >>= 7n; }
  out.push(Number(v));
  return Buffer.from(out);
}
export const tagBytes = (fieldNum, wireType) => encodeVarint((fieldNum << 3) | wireType);
export const lenField = (fieldNum, buf) => { const b = Buffer.isBuffer(buf) ? buf : Buffer.from(buf); return Buffer.concat([tagBytes(fieldNum, 2), encodeVarint(b.length), b]); };
export const varintField = (fieldNum, n) => Buffer.concat([tagBytes(fieldNum, 0), encodeVarint(n)]);
export function decodeVarintAt(buf, pos) {
  let val = 0n, shift = 0n, p = pos;
  while (p < buf.length) {
    const b = BigInt(buf[p++]);
    val |= (b & 0x7fn) << shift;
    if ((b & 0x80n) === 0n) return { val: Number(val), pos: p };
    shift += 7n;
  }
  throw new Error('truncated varint');
}
export function decodeFields(buf) {
  const fields = [];
  let p = 0;
  while (p < buf.length) {
    const t = decodeVarintAt(buf, p); p = t.pos;
    const fn = t.val >> 3, wt = t.val & 7;
    if (wt === 0) { const v = decodeVarintAt(buf, p); p = v.pos; fields.push([fn, v.val]); }
    else if (wt === 2) { const l = decodeVarintAt(buf, p); p = l.pos; fields.push([fn, Buffer.from(buf.subarray(p, p + l.val))]); p += l.val; }
    else throw new Error(`unsupported wire type ${wt}`);
  }
  return fields;
}

// ---- HTTP Static Harness & Browser Runner ----

export function send(res, code, type, body) {
  res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store' });
  res.end(body);
}

export async function serve({ dir = SERVE, spa = true, routes } = {}) {
  const server = createServer(async (req, res) => {
    const url = new URL(req.url, `http://${req.headers.host || '127.0.0.1'}`);
    if (routes && (await routes(req, res, url))) return;
    if (url.pathname === '/__build_id') return send(res, 200, 'text/plain', 'test');
    const rel = (url.pathname === '/' || (spa && !url.pathname.includes('.'))) ? '/index.html' : url.pathname;
    const fp = path.resolve(dir, '.' + rel);
    if (!fp.startsWith(dir + path.sep) && fp !== dir) return send(res, 404, 'text/plain', 'not found');
    try { send(res, 200, MIME[path.extname(fp)] || 'application/octet-stream', await readFile(fp)); }
    catch { send(res, 404, 'text/plain', 'not found'); }
  });
  await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve); });
  const { port } = server.address();
  return { server, port, baseUrl: `http://127.0.0.1:${port}`, close: () => { server.closeAllConnections?.(); return new Promise((r) => server.close(r)); } };
}

export function checker(name) {
  let passed = 0, failures = 0;
  const check = (label, got, want) => {
    const ok = got === want ||
      (got != null && want != null && typeof got !== 'object' && typeof want !== 'object' && String(got) === String(want)) ||
      (typeof got === 'object' && typeof want === 'object' && JSON.stringify(got) === JSON.stringify(want));
    if (ok) passed++;
    else { console.error(`  FAIL  ${label}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`); failures++; }
  };
  const fail = (msg) => { console.error(`  FAIL  ${msg}`); failures++; };
  const finish = () => {
    if (failures === 0) console.log(`  ✓ ${name.toLowerCase()} (${passed})`);
    else console.error(`  ✗ ${name.toLowerCase()}: ${failures} failed (${passed} passed)`);
    if (globalThis.__QED_SHARED_BROWSER) {
      if (failures > 0) { const err = new Error(`${name.toLowerCase()}: ${failures} failed`); err.__qedReported = true; throw err; }
    }
    else if (failures > 0) process.exitCode = 1;
  };
  return { check, fail, finish };
}

export async function withPage(fn) {
  const shared = await globalThis.__QED_SHARED_BROWSER;
  const target = shared ? await shared.createBrowserContext() : await puppeteer.launch(LAUNCH_OPTS);
  try { return await fn(await target.newPage()); }
  finally { await target.close(); }
}

export async function withBrowser(name, opts, fn) {
  if (typeof opts === 'function') { fn = opts; opts = {}; }
  const { check, fail, finish } = checker(name);
  const srv = await serve(opts);
  try {
    await withPage(async (page) => {
      page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));
      await fn({ page, check, fail, baseUrl: srv.baseUrl, port: srv.port, dir: opts.dir });
    });
  } finally { await srv.close(); }
  finish();
}

const SUBPROCESS_SUITES = ['cli_scaffold_test.mjs', 'js_gate_test.mjs'];
const BROWSER_SUITES = [
  'fullstack_rpc_test.mjs',
  'speculative_test.mjs',
  'websocket_test.mjs',
  'dom_equivalence_test.mjs',
];

const runSubprocess = (file) => new Promise((resolve) => {
  const child = spawn(process.execPath, [path.join(ROOT, 'test', file)], { cwd: ROOT, env: process.env, stdio: ['ignore', 'pipe', 'pipe'] });
  let out = '', err = '';
  child.stdout.on('data', (c) => { out += c; });
  child.stderr.on('data', (c) => { err += c; });
  child.on('close', (code) => {
    if (out) process.stdout.write(out);
    if (err) process.stderr.write(err);
    resolve(code === 0 ? 0 : 1);
  });
});

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  (async () => {
    const total = SUBPROCESS_SUITES.length + BROWSER_SUITES.length;
    const subPromise = Promise.all(SUBPROCESS_SUITES.map(runSubprocess));
    const browserPromise = puppeteer.launch(LAUNCH_OPTS);
    globalThis.__QED_SHARED_BROWSER = browserPromise;

    let failed = 0, nextIdx = 0;
    async function worker() {
      while (nextIdx < BROWSER_SUITES.length) {
        const file = BROWSER_SUITES[nextIdx++];
        try { await import(pathToFileURL(path.join(ROOT, 'test', file)).href); }
        catch (err) {
          failed++;
          if (!err?.__qedReported) console.error(`  ✗ ${file}: ${err?.stack || err}`);
        }
      }
    }

    try { await Promise.all(Array.from({ length: Math.min(4, BROWSER_SUITES.length) }, worker)); }
    finally { const b = await browserPromise.catch(() => null); if (b) await b.close(); }
    failed += (await subPromise).reduce((a, b) => a + b, 0);
    console[failed ? 'error' : 'log'](failed === 0 ? `\x1b[32m✓ ${total}/${total} test suites passed\x1b[0m` : `\x1b[31m✗ ${failed}/${total} test suite(s) failed\x1b[0m`);
    process.exit(failed === 0 ? 0 : 1);
  })();
}
