import { spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import puppeteer from 'puppeteer';

export { setTimeout as sleep } from 'node:timers/promises';

export const ROOT = path.resolve(fileURLToPath(new URL('..', import.meta.url)));
export const SERVE = path.join(ROOT, '.qed', 'dev');

const MIME = {
  '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript',
  '.json': 'application/json', '.css': 'text/css',
};

function runQuiet(cmd, args, env = process.env) {
  const r = spawnSync(cmd, args, { cwd: ROOT, env, encoding: 'utf8' });
  if (r.status !== 0) {
    process.stderr.write((r.stdout || '') + (r.stderr || ''));
    process.exit(1);
  }
  return r.stdout;
}

export function buildDev(webRoot = 'Examples.Web') {
  runQuiet('./scripts/qed', ['build', '--dev'], { ...process.env, QED_WEB_ROOT: webRoot });
}

export function buildExe(exe) {
  runQuiet('lake', ['build', exe]);
  return path.join(ROOT, '.lake', 'build', 'bin', exe);
}

export function runExe(exe, args = []) {
  return runQuiet(buildExe(exe), args);
}

export async function ssrShell(webRoot, exe) {
  buildDev(webRoot);
  const serverApp = runExe(exe).trim().replace('class="count"', 'class="count" data-server="1"');
  if (!serverApp.includes('data-server')) { console.error('could not mark server node'); process.exit(1); }
  return (await readFile(path.join(SERVE, 'index.html'), 'utf8')).replace('loading…', serverApp);
}

export function send(res, code, type, body) {
  res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store' });
  res.end(body);
}

export async function serve({ dir = SERVE, spa = true, routes, upgrade } = {}) {
  const server = createServer(async (req, res) => {
    const url = new URL(req.url, `http://${req.headers.host || '127.0.0.1'}`);
    if (routes && (await routes(req, res, url))) return;
    if (url.pathname === '/__build_id') return send(res, 200, 'text/plain', 'test'), undefined;
    const rel = (url.pathname === '/' || (spa && !url.pathname.includes('.'))) ? '/index.html' : url.pathname;
    const fp = path.resolve(dir, '.' + rel);
    if (!fp.startsWith(dir + path.sep) && fp !== dir) return send(res, 404, 'text/plain', 'not found');
    try {
      send(res, 200, MIME[path.extname(fp)] || 'application/octet-stream', await readFile(fp));
    } catch {
      send(res, 404, 'text/plain', 'not found');
    }
  });
  if (upgrade) server.on('upgrade', upgrade);
  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, '127.0.0.1', resolve);
  });
  const port = server.address().port;
  return {
    server,
    port,
    baseUrl: `http://127.0.0.1:${port}`,
    close: () => {
      server.closeAllConnections?.();
      return new Promise((r) => server.close(() => r()));
    },
  };
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
    process.exit(failures === 0 ? 0 : 1);
  };
  return { check, fail, finish };
}

export async function withBrowser(name, opts, fn) {
  if (typeof opts === 'function') { fn = opts; opts = {}; }
  if (opts.webRoot) buildDev(opts.webRoot);
  const { check, fail, finish } = checker(name);
  const srv = await serve(opts);
  const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
  try {
    const page = await browser.newPage();
    page.on('pageerror', (e) => fail(`[pageerror] ${e.message}`));
    if (opts.onConsole) page.on('console', (m) => opts.onConsole(m, fail));
    await fn({ page, check, fail, baseUrl: srv.baseUrl, port: srv.port });
  } finally {
    await browser.close();
    await srv.close();
  }
  finish();
}
