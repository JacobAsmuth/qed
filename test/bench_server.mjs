/**
 * Standardized HTTP, JSON, RPC, Fortunes SSR, Static Asset, and WebSocket
 * Pub/Sub Fanout throughput harness for Qed's native Rust/Lean server
 * (single-worker & multi-worker).
 *
 * Uses a zero-dependency compiled Rust HTTP/1.1 keep-alive load generator
 * (`test/loadgen.rs`) so the client never becomes the bottleneck.
 *
 * Usage:
 *   node test/bench_server.mjs
 *   node test/bench_server.mjs --save-baseline
 *   DURATION_MS=3000 CONNS=64 node test/bench_server.mjs
 */
import { execFileSync, spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import net from 'node:net';
import os from 'node:os';
import path from 'node:path';
import { lenField, ROOT, startNativeServer, withElanPath } from './harness.mjs';

// ---- Minimal RFC 6455 WebSocket helpers ----
function encodeWsFrame(opcode, payload, masked) {
  const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
  const len = data.length;
  const hdrLen = 2 + (len >= 65536 ? 8 : len >= 126 ? 2 : 0) + (masked ? 4 : 0);
  const out = Buffer.allocUnsafe(hdrLen + len);
  out[0] = 0x80 | (opcode & 0x0f);
  let p = 2;
  if (len < 126) { out[1] = (masked ? 0x80 : 0) | len; }
  else if (len < 65536) { out[1] = (masked ? 0x80 : 0) | 126; out.writeUInt16BE(len, 2); p = 4; }
  else { out[1] = (masked ? 0x80 : 0) | 127; out.writeBigUInt64BE(BigInt(len), 2); p = 10; }
  if (masked) {
    const mask = crypto.randomBytes(4);
    mask.copy(out, p); p += 4;
    for (let i = 0; i < len; i++) out[p + i] = data[i] ^ mask[i & 3];
  } else {
    data.copy(out, p);
  }
  return out;
}

function makeWsFrameParser(onFrame) {
  let buf = Buffer.alloc(0);
  return (chunk) => {
    buf = buf.length ? Buffer.concat([buf, chunk]) : chunk;
    while (buf.length >= 2) {
      const opcode = buf[0] & 0x0f, masked = (buf[1] & 0x80) !== 0;
      let len = buf[1] & 0x7f, p = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); p = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); p = 10; }
      const maskOff = p;
      if (masked) p += 4;
      if (buf.length < p + len) return;
      const payload = Buffer.allocUnsafe(len);
      if (masked) { for (let i = 0; i < len; i++) payload[i] = buf[p + i] ^ buf[maskOff + (i & 3)]; }
      else { buf.copy(payload, 0, p, p + len); }
      buf = buf.subarray(p + len);
      onFrame(opcode, payload);
    }
  };
}

// ---- Orchestrator ----
const CONNS = Math.max(4, Number(process.env.CONNS || 64));
const DURATION_MS = Math.max(500, Number(process.env.DURATION_MS || 2500));
const WARMUP_MS = Math.max(200, Number(process.env.WARMUP_MS || 500));
const MULTI_WORKERS = Math.max(2, Math.min(8, Math.floor(os.cpus().length / 2)));
const WS_SUBS = Number(process.env.WS_SUBS || 100);
const WS_MSGS = Number(process.env.WS_MSGS || 200);
const DIST = path.join(ROOT, 'dist');
const BENCH_DIR = path.join(ROOT, '.qed', 'bench');
mkdirSync(BENCH_DIR, { recursive: true });

const argVal = (flag) => {
  const i = process.argv.indexOf(flag);
  return i >= 0 && process.argv[i + 1] && !process.argv[i + 1].startsWith('--') ? process.argv[i + 1] : null;
};
const SAVE_BASELINE = process.argv.includes('--save-baseline') || process.env.SAVE_BASELINE === '1';
const BASELINE_PATH = argVal('--baseline') || argVal('--save-baseline') || path.join(BENCH_DIR, 'server_baseline.json');
const baseline = existsSync(BASELINE_PATH) ? JSON.parse(readFileSync(BASELINE_PATH, 'utf8')) : null;

// 1. Compile zero-dep Rust loadgen (cached by mtime)
const loadgenSrc = path.join(ROOT, 'test', 'loadgen.rs');
const loadgenBin = path.join(BENCH_DIR, 'loadgen');
if (!existsSync(loadgenBin) || statSync(loadgenSrc).mtimeMs > statSync(loadgenBin).mtimeMs) {
  execFileSync('rustc', ['-O', loadgenSrc, '-o', loadgenBin], { stdio: 'inherit' });
}

// 2. Production build of Bench.Server (`-O3 -DNDEBUG` native binary + hashed prod static assets)
{
  const qedBin = existsSync(path.join(ROOT, '.lake', 'build', 'bin', 'qed'))
    ? path.join(ROOT, '.lake', 'build', 'bin', 'qed')
    : './scripts/qed';
  const r = spawnSync(qedBin, ['build'], {
    cwd: ROOT,
    env: { ...withElanPath(), QED_HOME: ROOT, QED_WEB_ROOT: 'Bench.Server' },
    encoding: 'utf8',
  });
  if (r.status !== 0) {
    process.stderr.write((r.stdout || '') + (r.stderr || ''));
    process.exit(1);
  }
}

const hashedAppFile = readdirSync(DIST).find((f) => /^app\.[0-9a-f]+\.mjs$/.test(f));
if (!hashedAppFile) throw new Error('expected hashed app.<hash>.mjs in dist/');
const staticUrl = `/${hashedAppFile}`;
const staticFile = path.join(DIST, hashedAppFile);
const staticSizeKb = (statSync(staticFile).size / 1024).toFixed(1);

// Protobuf body for BenchSrv.ping("hello-world-benchmark-payload")
const pingProtoHex = lenField(1, Buffer.from('hello-world-benchmark-payload', 'utf8')).toString('hex');

function runLoadgen(port, method, urlPath, ctype = '', bodyHex = '') {
  const args = [`127.0.0.1:${port}`, String(CONNS), String(DURATION_MS), String(WARMUP_MS), method, urlPath];
  if (ctype) args.push(ctype, bodyHex);
  const out = execFileSync(loadgenBin, args, { encoding: 'utf8' });
  const res = JSON.parse(out.trim());
  if (res.errors > 0 || res.reqs === 0) {
    throw new Error(`loadgen errors on ${method} ${urlPath}: ${out.trim()}`);
  }
  return res;
}

async function verifyEndpoints(baseUrl, label) {
  const h = await fetch(`${baseUrl}/_qed/health`);
  if (h.status !== 200 || (await h.text()) !== '{"ok":true}') throw new Error(`[${label}] /_qed/health failed`);

  const ssr = await fetch(`${baseUrl}/`);
  const html = await ssr.text();
  const tbody = html.slice(html.indexOf('<tbody>'), html.indexOf('</tbody>'));
  if (ssr.status !== 200 ||
      !tbody.includes('&lt;script&gt;alert(') ||
      tbody.includes('<script>alert(') ||
      !tbody.includes('フレームワークのベンチマーク') ||
      !tbody.includes('Additional fortune added at request time.')) {
    throw new Error(`[${label}] Fortunes SSR verification failed (status=${ssr.status}): ${tbody.slice(0, 600)}`);
  }

  const rpc = await fetch(`${baseUrl}/_qed/rpc/BenchSrv/ping`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-protobuf', Origin: baseUrl, 'Sec-Fetch-Site': 'same-origin' },
    body: Buffer.from(pingProtoHex, 'hex'),
  });
  if (rpc.status !== 200) throw new Error(`[${label}] RPC ping status ${rpc.status}`);

  const st = await fetch(`${baseUrl}${staticUrl}`);
  if (st.status !== 200) throw new Error(`[${label}] static ${staticUrl} status ${st.status}`);
}

// Qed mux frame builders
function encodeMuxSub(subId, channel) {
  const chB = Buffer.from(channel, 'utf8');
  const out = Buffer.allocUnsafe(7 + chB.length);
  out[0] = 0x01; out.writeUInt32BE(subId, 1); out.writeUInt16BE(chB.length, 5);
  chB.copy(out, 7);
  return out;
}
function encodeMuxSend(subId, payloadBuf) {
  const out = Buffer.allocUnsafe(5 + payloadBuf.length);
  out[0] = 0x03; out.writeUInt32BE(subId, 1);
  payloadBuf.copy(out, 5);
  return out;
}

function connectWsSubscriber(port, wsPath, onEvent) {
  return new Promise((resolve, reject) => {
    const key = crypto.randomBytes(16).toString('base64');
    const sock = net.connect(port, '127.0.0.1', () => {
      sock.setNoDelay(true);
      sock.write(
        `GET ${wsPath} HTTP/1.1\r\nHost: 127.0.0.1:${port}\r\n` +
        'Upgrade: websocket\r\nConnection: Upgrade\r\n' +
        `Sec-WebSocket-Key: ${key}\r\nSec-WebSocket-Version: 13\r\n` +
        `Origin: http://127.0.0.1:${port}\r\n\r\n`
      );
    });
    let upgraded = false, joined = false, hdr = Buffer.alloc(0);
    const timer = setTimeout(() => { sock.destroy(); reject(new Error('WS join timeout')); }, 5000);
    const parse = makeWsFrameParser((opcode, payload) => {
      if (opcode !== 0x02 || payload.length < 5) return;
      const op = payload[0];
      if (!joined && op === 0x11) { clearTimeout(timer); joined = true; resolve(sock); }
      else if (!joined && op === 0x13) { clearTimeout(timer); sock.destroy(); reject(new Error('WS SUB rejected')); }
      else if (op === 0x12) onEvent();
    });
    sock.on('data', (chunk) => {
      if (!upgraded) {
        hdr = Buffer.concat([hdr, chunk]);
        const idx = hdr.indexOf('\r\n\r\n');
        if (idx < 0) return;
        if (!hdr.subarray(0, idx).toString('latin1').includes('101')) {
          reject(new Error('WS upgrade rejected')); return;
        }
        upgraded = true;
        sock.write(encodeWsFrame(0x02, encodeMuxSub(1, 'feed'), true));
        const rest = hdr.subarray(idx + 4);
        if (rest.length) parse(rest);
      } else {
        parse(chunk);
      }
    });
    sock.on('error', reject);
  });
}

async function benchWsFanout(port, wsPath) {
  let received = 0;
  let waitResolve = null;
  let target = 0;
  const onEvent = () => {
    received++;
    if (waitResolve && received >= target) {
      const r = waitResolve; waitResolve = null; r();
    }
  };
  const sockets = [];
  try {
    for (let i = 0; i < WS_SUBS; i++) {
      sockets.push(await connectWsSubscriber(port, wsPath, onEvent));
    }
    const payload = encodeMuxSend(1, lenField(1, Buffer.from('tick:42:broadcast-fanout-bench', 'utf8')));
    const sendOne = () => new Promise((resolve, reject) => {
      const t = setTimeout(() => reject(new Error(`WS fanout timeout (got ${received}/${target})`)), 5000);
      target = received + WS_SUBS;
      waitResolve = () => { clearTimeout(t); resolve(); };
      sockets[0].write(encodeWsFrame(0x02, payload, true));
    });
    // Warmup
    for (let w = 0; w < 10; w++) await sendOne();
    const latsUs = [];
    const tStart = process.hrtime.bigint();
    for (let i = 0; i < WS_MSGS; i++) {
      const t0 = process.hrtime.bigint();
      await sendOne();
      latsUs.push(Number(process.hrtime.bigint() - t0) / 1000);
    }
    const totalMs = Number(process.hrtime.bigint() - tStart) / 1e6;
    latsUs.sort((a, b) => a - b);
    const pct = (p) => Math.round(latsUs[Math.round((latsUs.length - 1) * p)]);
    return {
      broadcasts_per_sec: (WS_MSGS / (totalMs / 1000)),
      deliveries_per_sec: ((WS_MSGS * WS_SUBS) / (totalMs / 1000)),
      p50_us: pct(0.50),
      p99_us: pct(0.99),
    };
  } finally {
    for (const s of sockets) s.destroy();
  }
}

const TARGETS = [
  { key: 'qed-1w', label: 'Qed (1w)',               start: () => startNativeServer(DIST, { QED_WORKERS: '1' }, { dev: false }), ws: true },
  { key: 'qed-mw', label: `Qed (${MULTI_WORKERS}w)`, start: () => startNativeServer(DIST, { QED_WORKERS: String(MULTI_WORKERS) }, { dev: false }), ws: true },
];

const SCENARIOS = [
  { key: 'health',   label: 'GET /_qed/health (JSON)',      method: 'GET',  path: '/_qed/health' },
  { key: 'rpc',      label: 'POST /_qed/rpc/ping (proto)',  method: 'POST', path: '/_qed/rpc/BenchSrv/ping', ctype: 'application/x-protobuf', bodyHex: pingProtoHex },
  { key: 'fortunes', label: 'GET / (Fortunes SSR HTML)',    method: 'GET',  path: '/' },
  { key: 'static',   label: `GET static (${staticSizeKb} KB asset)`, method: 'GET', path: staticUrl },
];

const results = {};
try {
  for (const t of TARGETS) {
    const srv = await t.start();
    try {
      await verifyEndpoints(srv.baseUrl, t.label);
      const entry = {};
      for (const sc of SCENARIOS) {
        entry[sc.key] = runLoadgen(srv.port, sc.method, sc.path, sc.ctype || '', sc.bodyHex || '');
      }
      if (t.ws) {
        entry.ws_fanout = await benchWsFanout(srv.port, '/_qed/ws/BenchSrv');
      }
      results[t.key] = entry;
    } finally {
      await srv.stop();
    }
  }
} finally {
  rmSync(DIST, { recursive: true, force: true });
}

const fmtRps = (n) => Math.round(n).toLocaleString('en-US');
const fmtUs = (u) => (u >= 1000 ? `${(u / 1000).toFixed(2)}ms` : `${u}us`);
const fmtDelta = (curr, prev) => {
  if (!prev || prev <= 0) return '';
  const pct = ((curr - prev) / prev) * 100;
  return ` (${pct >= 0 ? '+' : ''}${pct.toFixed(1)}%)`;
};

const COL = baseline ? 28 : 22;
console.log(`\n  Server Throughput Benchmark — ${CONNS} keep-alive conns, ${DURATION_MS}ms/test (${os.cpus().length} CPU cores)${baseline ? ` [vs ${path.relative(ROOT, BASELINE_PATH)}]` : ''}\n`);
console.log('  endpoint'.padEnd(36) + TARGETS.map((t) => t.label.padStart(COL)).join(''));
console.log('  ' + '-'.repeat(34 + TARGETS.length * COL));
for (const sc of SCENARIOS) {
  const row = TARGETS.map((t) => {
    const r = results[t.key][sc.key];
    const d = fmtDelta(r.rps, baseline?.[t.key]?.[sc.key]?.rps);
    return `${fmtRps(r.rps)} r/s${d}`.padStart(COL);
  }).join('');
  const lats = TARGETS.map((t) => {
    const r = results[t.key][sc.key];
    return `p50 ${fmtUs(r.p50_us)} p99 ${fmtUs(r.p99_us)}`.padStart(COL);
  }).join('');
  console.log('  ' + sc.label.padEnd(34) + row);
  console.log('  ' + ''.padEnd(34) + lats);
}

console.log(`\n  WebSocket Pub/Sub Fanout — ${WS_SUBS} subscribers × ${WS_MSGS} broadcasts (${(WS_SUBS * WS_MSGS).toLocaleString()} delivered frames)\n`);
for (const t of TARGETS.filter((x) => x.ws)) {
  const w = results[t.key].ws_fanout;
  const d = fmtDelta(w.deliveries_per_sec, baseline?.[t.key]?.ws_fanout?.deliveries_per_sec);
  console.log(
    `  ${t.label.padEnd(14)} ${fmtRps(w.deliveries_per_sec).padStart(10)} msgs/s${d.padEnd(baseline ? 10 : 0)}  ` +
    `(${fmtRps(w.broadcasts_per_sec).padStart(6)} bcast/s)  p50 ${fmtUs(w.p50_us).padStart(7)}  p99 ${fmtUs(w.p99_us).padStart(7)}`
  );
}

if (SAVE_BASELINE) {
  writeFileSync(BASELINE_PATH, JSON.stringify(results, null, 2) + '\n');
  console.log(`\n  Saved baseline to ${path.relative(ROOT, BASELINE_PATH)}`);
} else if (!baseline) {
  console.log('\n  Tip: run with --save-baseline to save a baseline for relative diffs.');
}
console.log('\n' + JSON.stringify(results));
