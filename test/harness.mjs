import { execFile, spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { createServer } from 'node:http';
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

function buildEnv(webRoot, outDir) {
  const elanBin = path.join(process.env.HOME || '', '.elan', 'bin');
  const PATH = elanBin && !(process.env.PATH || '').split(':').includes(elanBin) ? `${elanBin}:${process.env.PATH || ''}` : (process.env.PATH || '');
  return { ...process.env, PATH, QED_HOME: ROOT, QED_WEB_ROOT: webRoot, ...(outDir !== SERVE ? { QED_OUT_DIR: outDir } : {}) };
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

export function send(res, code, type, body) {
  res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store' });
  res.end(body);
}

export async function serve({ dir = SERVE, spa = true, routes, upgrade } = {}) {
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
  if (upgrade) server.on('upgrade', upgrade);
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
  const dir = opts.webRoot ? await buildDevAsync(opts.webRoot, opts.dir) : opts.dir;
  const { check, fail, finish } = checker(name);
  const srv = await serve({ ...opts, dir });
  try {
    await withPage(async (page) => {
      page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));
      if (opts.onConsole) page.on('console', (m) => opts.onConsole(m, fail));
      await fn({ page, check, fail, baseUrl: srv.baseUrl, port: srv.port, dir });
    });
  } finally { await srv.close(); }
  finish();
}

const SUBPROCESS_SUITES = ['cli_scaffold_test.mjs', 'js_gate_test.mjs'];
const BROWSER_SUITES = [
  'fullstack_rpc_test.mjs',
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
