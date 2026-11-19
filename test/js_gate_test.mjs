import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, writeFileSync, copyFileSync } from 'node:fs';
import path from 'node:path';
import { ROOT, leanEnv, withElanPath } from './harness.mjs';

const gate = path.join(ROOT, 'test', '.gate');
mkdirSync(gate, { recursive: true });
const run = (cmd, args, env = withElanPath()) =>
  execFileSync(cmd, args, { cwd: ROOT, env, encoding: 'utf8', maxBuffer: 64 << 20 });

const qedjsBin = path.join(ROOT, '.lake/build/bin/qedjs');
if (process.env.QED_PREBUILT !== '1' || !existsSync(qedjsBin)) {
  run('lake', ['build', 'Tests.JsGate', 'qedjs']);
}
const gateEnv = leanEnv();

const oraclePath = path.join(gate, 'oracle.lean');
writeFileSync(oraclePath, 'import Tests.JsGate\ndef main : IO Unit := JsGate.emitOracle\n');
const oracleText = run('lean', ['--run', oraclePath], gateEnv);
const want = new Map();
for (const line of oracleText.split('\n')) {
  const t = line.split('\t');
  if (t.length === 3) want.set(`${t[0]}|${t[1]}`, JSON.parse(t[2]));
}

const appPath = path.join(gate, 'app.mjs');
run(qedjsBin, [appPath, 'Tests.JsGate', '--',
  'JsGate.run:run', 'JsGate.counts:counts', 'JsGate.probeCount:probeCount', 'JsGate.names:names'], gateEnv);
copyFileSync(path.join(ROOT, 'runtime/qed_rt.mjs'), path.join(gate, 'qed_rt.mjs'));

const P = await import(path.join(gate, 'app.mjs'));
const $ = await import(path.join(gate, 'qed_rt.mjs'));
$.assertExterns(P.__externs, $);
for (const [label, bytes, expected] of [
  ['valid ASCII', new TextEncoder().encode('hello'), 1],
  ['valid UTF-8 CJK+emoji', new TextEncoder().encode('日本語😀'), 1],
  ['invalid 0xFF 0xFE', new Uint8Array([0xff, 0xfe]), 0],
  ['overlong 0xC0 0xAF', new Uint8Array([0xc0, 0xaf]), 0],
  ['lone surrogate 0xED 0xA0 0x80', new Uint8Array([0xed, 0xa0, 0x80]), 0],
  ['truncated 0xE2 0x82', new Uint8Array([0xe2, 0x82]), 0],
]) {
  if ($.String_validateUTF8(bytes) !== expected || $.ByteArray_validateUTF8(bytes) !== expected) {
    console.error(`  FAIL String_validateUTF8 (${label}): got ${$.String_validateUTF8(bytes)}, want ${expected}`);
    process.exit(1);
  }
}
const names = P.names();
let total = 0, fail = 0;
const byProbe = {};
const nprobes = Number(P.probeCount());
for (let p = 0; p < nprobes; p++) {
  const n = Number(P.counts(BigInt(p)));
  byProbe[names[p]] = [0, 0];
  for (let i = 0; i < n; i++) {
    const got = P.run(BigInt(p), BigInt(i));
    const exp = want.get(`${p}|${i}`);
    total++;
    byProbe[names[p]][0]++;
    if (got !== exp) {
      fail++;
      byProbe[names[p]][1]++;
      if (fail <= 12) console.log(`  MISMATCH ${names[p]}#${i}\n    got:  ${JSON.stringify(got)}\n    want: ${JSON.stringify(exp)}`);
    }
  }
}
if (fail) {
  for (const [name, [n, f]] of Object.entries(byProbe)) if (f) console.error(`  FAIL ${name}: ${n - f}/${n}`);
  console.error(`  ✗ js-gate: ${fail}/${total} failed`);
  process.exit(1);
}
console.log(`  ✓ js-gate (${total})`);
