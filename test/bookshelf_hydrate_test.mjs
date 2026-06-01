// bookshelf_hydrate_test.mjs — the dehydrated-SSR cache: the client starts from the server's
// model instead of refetching.
//
// The server returns the per-route SSR page (which now embeds the model in #qed-state) and the
// WASM bundle, but serves NO /api endpoint and counts any /api hit. So if the client adopts the
// dehydrated state, the catalog renders with zero API calls; if it ignored the state and
// refetched, /api/books would 404 and the list would error. We assert the former.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8143;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building client (Examples.BookshelfWeb) + SSR renderer…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev`], { stdio: 'inherit' }).status !== 0)
  { console.error('client build failed'); process.exit(1); }
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && lake build bookshelf_ssr`], { stdio: 'inherit' }).status !== 0)
  { console.error('ssr build failed'); process.exit(1); }

const ssr = (path) => spawnSync('bash', ['-lc', `cd '${ROOT}' && lake exe bookshelf_ssr '${path}' 2>/dev/null`], { encoding: 'utf8' }).stdout;

let apiHits = 0;
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.wasm': 'application/wasm', '.css': 'text/css', '.json': 'application/json' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const head = (code, type) => res.writeHead(code, {
    'Content-Type': type, 'Cross-Origin-Opener-Policy': 'same-origin',
    'Cross-Origin-Embedder-Policy': 'require-corp', 'Cache-Control': 'no-store',
  });
  if (pathname.startsWith('/api/')) { apiHits++; head(404, 'application/json'); res.end('{}'); return; }
  if (pathname.includes('.')) {  // an asset (qed.js, qed.wasm, …) → serve from the dev build
    try { const buf = await readFile(SERVE + pathname); head(200, MIME[pathname.slice(pathname.lastIndexOf('.'))] || 'application/octet-stream'); res.end(buf); }
    catch { head(404, 'text/plain'); res.end('not found'); }
    return;
  }
  head(200, 'text/html'); res.end(ssr(pathname));   // a route → the SSR page (carries #qed-state)
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

  // sanity: the SSR page embeds the dehydrated state
  check('SSR page carries the dehydrated state', ssr('/').includes('id="qed-state"'), true);

  await page.goto(`http://localhost:${PORT}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .catalog', { timeout: 20000 });
  await sleep(150);  // give a (hypothetical) refetch time to fire

  const text = await page.$eval('#app .catalog', (e) => e.textContent);
  check('catalog rendered the books (from dehydrated state)', text.includes('Dune') && text.includes('Neuromancer'), true);
  check('no "Loading…" — the data was already present', text.includes('Loading'), false);
  check('the client did NOT refetch the catalog (zero /api hits)', apiHits, 0);

  // and the booted app is interactive: a link click routes (and only THEN may it fetch)
  await page.click('#app nav a');
  await sleep(50);
  check('app is live after hydration (nav present)', await page.$('#app nav') !== null, true);
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL HYDRATE CHECKS PASSED ✅' : `\n${failures} HYDRATE CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
