// Differential gate: run every probe (Examples/JsGate.lean) natively in Lean and
// transpiled under node; assert identical output. Flushes out emitter/extern bugs.
import { execFileSync } from 'node:child_process';
import { writeFileSync, copyFileSync, readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = fileURLToPath(new URL('..', import.meta.url));
const gate = path.join(root, 'test', '.gate');
const run = (cmd, args) => execFileSync(cmd, args, { cwd: root, encoding: 'utf8', maxBuffer: 64 << 20 });

// 1. Native oracle.
const oraclePath = path.join(gate, 'oracle.lean');
writeFileSync(oraclePath, 'import Examples.JsGate\ndef main : IO Unit := JsGate.emitOracle\n');
console.log('▸ generating native oracle…');
const oracleText = run('lake', ['env', 'lean', '--run', oraclePath]);
const want = new Map();
for (const line of oracleText.split('\n')) { const t = line.split('\t'); if (t.length === 3) want.set(`${t[0]}|${t[1]}`, JSON.parse(t[2])); }

// 2. Transpile the probes.
console.log('▸ transpiling probes…');
const appPath = path.join(gate, 'app.mjs');
run('lake', ['env', path.join(root, '.lake/build/bin/qedjs'), appPath, 'Examples.JsGate', '--',
  'JsGate.run:run', 'JsGate.counts:counts', 'JsGate.probeCount:probeCount', 'JsGate.names:names']);
copyFileSync(path.join(root, 'runtime/qed_rt.mjs'), path.join(gate, 'qed_rt.mjs'));

// 3. Compare.
const P = await import(path.join(gate, 'app.mjs'));
const $ = await import(path.join(gate, 'qed_rt.mjs'));
$.assertExterns(P.__externs, $);
const names = P.names();  // Lean Array → JS array
let total = 0, fail = 0; const byProbe = {};
const nprobes = Number(P.probeCount());
for (let p = 0; p < nprobes; p++) {
  const n = Number(P.counts(BigInt(p))); byProbe[names[p]] = [0, 0];
  for (let i = 0; i < n; i++) {
    const got = P.run(BigInt(p), BigInt(i)); const exp = want.get(`${p}|${i}`); total++; byProbe[names[p]][0]++;
    if (got !== exp) { fail++; byProbe[names[p]][1]++; if (fail <= 12) console.log(`  MISMATCH ${names[p]}#${i}\n    got:  ${JSON.stringify(got)}\n    want: ${JSON.stringify(exp)}`); }
  }
}
for (const [name, [n, f]] of Object.entries(byProbe)) console.log(`  ${f ? 'FAIL' : 'ok  '} ${name}: ${n - f}/${n}`);
console.log(`\ndifferential gate: ${total - fail}/${total} cases identical to native Lean`);
process.exit(fail ? 1 : 0);
