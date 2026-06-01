// ssr_test.mjs — server-side render + hydration.
//
// Renders the counter's initial #app HTML *natively* (`lake exe counter`, the same verified
// view/render the browser uses), serves it pre-filled into #app, and checks that the client
// HYDRATES it: adopts the existing DOM in place (a server-only `data-server` attribute
// survives — proving the node was not rebuilt) and wires events onto it (clicking works).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8155;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building counter (Examples.Web → .qed/dev)…');
let build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.Web ./qed build --dev`], { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

// Server-side render: the #app content from the native build of the SAME app.
console.log('▸ rendering #app natively (lake exe counter)…');
const ssr = spawnSync('bash', ['-lc', `cd '${ROOT}' && lake exe counter 2>/dev/null`], { encoding: 'utf8' });
if (ssr.status !== 0) { console.error('native render failed'); process.exit(1); }
// mark a server node so we can tell adoption (it survives) from a rebuild (it vanishes)
const serverApp = ssr.stdout.trim().replace('class="count"', 'class="count" data-server="1"');
if (!serverApp.includes('data-server')) { console.error('could not mark server node'); process.exit(1); }

const shell = (await readFile(`${SERVE}/index.html`, 'utf8')).replace('loading…', serverApp);

const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.wasm': 'application/wasm', '.json': 'application/json', '.css': 'text/css' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const head = (type) => ({ 'Content-Type': type, 'Cross-Origin-Opener-Policy': 'same-origin', 'Cross-Origin-Embedder-Policy': 'require-corp', 'Cache-Control': 'no-store' });
  if (pathname === '/' || pathname === '/index.html') { res.writeHead(200, head('text/html')); return res.end(shell); }
  try {
    const buf = await readFile(SERVE + pathname);
    res.writeHead(200, head(MIME[pathname.slice(pathname.lastIndexOf('.'))] || 'application/octet-stream'));
    res.end(buf);
  } catch { res.writeHead(404, head('text/plain')); res.end('not found'); }
});
server.listen(PORT);
await sleep(300);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'] });
try {
  const page = await browser.newPage();
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .count', { timeout: 15000 });

  const count = () => page.$eval('#app .count', (e) => e.textContent.trim());
  const adopted = () => page.$eval('#app .count', (e) => e.getAttribute('data-server') === '1');

  check('server-rendered count is shown', await count(), '0');
  // give the wasm a beat to instantiate and hydrate
  await sleep(800);
  check('hydration ADOPTED the server node (data-server survived)', await adopted(), true);

  // events were wired onto the adopted DOM
  await page.click('[data-qed-click="0"]'); await sleep(60);  // − (guarded at 0 → stays 0)
  const incBtn = await page.evaluate(() => {
    const b = [...document.querySelectorAll('#app button')].find((b) => b.textContent === '+');
    b.click(); return true;
  });
  await sleep(60);
  check('clicking + after hydration increments', await count(), '1');
  check('the adopted node is still the same after an update', await adopted(), true);
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL SSR CHECKS PASSED ✅' : `\n${failures} SSR CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
