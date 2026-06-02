// ssr_template_test.mjs — hydration of a `view%` fine-grained template app.
//
// SSRs the template demo's initial #app natively, serves it pre-filled, and checks the client
// HYDRATES it: adopts the server DOM in place (a server-only attr survives → not rebuilt),
// re-inserts the invisible placeholders the server omits (hidden showIf), wires events
// (clicking + drives the bound count), and rebinds signals (toggling a row flips its class).
import { spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8188;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building template demo (Examples.TemplateWeb → .qed/dev)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.TemplateWeb ./qed build --dev`], { stdio: 'inherit' }).status !== 0) {
  console.error('build failed'); process.exit(1);
}
console.log('▸ rendering #app natively (lake exe template_ssr)…');
const ssr = spawnSync('bash', ['-lc', `cd '${ROOT}' && lake exe template_ssr 2>/dev/null`], { encoding: 'utf8' });
if (ssr.status !== 0) { console.error('native render failed'); process.exit(1); }
const serverApp = ssr.stdout.trim().replace('class="count"', 'class="count" data-server="1"');
if (!serverApp.includes('data-server')) { console.error('could not mark server node'); process.exit(1); }
const shell = (await readFile(`${SERVE}/index.html`, 'utf8')).replace('loading…', serverApp);

const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.wasm': 'application/wasm', '.json': 'application/json', '.css': 'text/css' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const head = (t) => ({ 'Content-Type': t, 'Cross-Origin-Opener-Policy': 'same-origin', 'Cross-Origin-Embedder-Policy': 'require-corp', 'Cache-Control': 'no-store' });
  if (pathname === '/' || pathname === '/index.html') { res.writeHead(200, head('text/html')); return res.end(shell); }
  try {
    const buf = await readFile(SERVE + pathname);
    res.writeHead(200, head(MIME[pathname.slice(pathname.lastIndexOf('.'))] || 'application/octet-stream'));
    res.end(buf);
  } catch { res.writeHead(404, head('text/plain')); res.end('nf'); }
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
  await sleep(900); // let the wasm instantiate + hydrate

  const count = () => page.$eval('#app .count', (e) => e.textContent.trim());
  const adopted = () => page.$eval('#app .count', (e) => e.getAttribute('data-server') === '1');
  const rowDone = (i) => page.$eval(`.demo ul.todos li:nth-child(${i + 1})`, (e) => e.className === 'done');

  check('template SSR shows count 0', await count(), '0');
  check('hydration ADOPTED the count node (data-server survived)', await adopted(), true);
  check('row 0 (done) hydrated with its class', await rowDone(0), true);

  // a bound scalar: clicking + drives the count via the hydrated dyn
  await page.evaluate(() => [...document.querySelectorAll('#app button')].find((b) => b.textContent === '+').click());
  await sleep(80);
  check('clicking + after hydration increments the count', await count(), '1');
  check('count node is still the adopted one', await adopted(), true);

  // a rebound signal: toggling row 1 flips its class (the row click + class signal were hydrated)
  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  await sleep(80);
  check('toggling a row flips its class (signal rehydrated)', await rowDone(1), true);
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL TEMPLATE-HYDRATION CHECKS PASSED ✅' : `\n${failures} TEMPLATE-HYDRATION CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
