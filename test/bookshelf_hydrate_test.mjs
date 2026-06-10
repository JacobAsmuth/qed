// bookshelf_hydrate_test.mjs: the dehydrated-SSR cache: the client starts from the
// server's model instead of refetching.
//
// Pages come from the generated request handler (ssr.mjs) with its data source injected
// directly, so the server makes NO HTTP calls of its own; the server's /api endpoint just
// counts hits and 404s. So if the client adopts the dehydrated state, the catalog renders
// with zero /api hits; if it ignored the state and refetched, /api/books would 404 and
// the list would error. We assert the former.
import { spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const SERVE = path.join(ROOT, '.qed', 'dev');
const PORT = 8143;

console.log('▸ building (QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev`], { stdio: 'inherit' }).status !== 0)
  { console.error('build failed'); process.exit(1); }

const books = [
  { id: 'dune',        title: 'Dune',        author: 'Frank Herbert',  year: 1965, genre: 'fiction', inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer', author: 'William Gibson', year: 1984, genre: 'fiction', inPrint: true },
];
const ssrMod = await import(pathToFileURL(path.join(SERVE, 'ssr.mjs')).href);
const handler = ssrMod.makeHandler(ssrMod.mod, {
  title: 'Bookshelf', script: '/qed_host.mjs',
  fetch: async (u) => new URL(u).pathname === '/api/books'
    ? new Response(JSON.stringify(books), { status: 200 })
    : new Response('{}', { status: 404 }),
});
const ssr = async (p) => await (await handler(new Request(`http://localhost:${PORT}${p}`))).text();

let apiHits = 0;
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css', '.json': 'application/json' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const head = (code, type) => res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store' });
  if (pathname.startsWith('/api/')) { apiHits++; head(404, 'application/json'); res.end('{}'); return; }
  if (pathname.includes('.')) {  // an asset (app.mjs, qed_host.mjs, …) → the dev build
    try { const buf = await readFile(SERVE + pathname); head(200, MIME[pathname.slice(pathname.lastIndexOf('.'))] || 'application/octet-stream'); res.end(buf); }
    catch { head(404, 'text/plain'); res.end('not found'); }
    return;
  }
  head(200, 'text/html'); res.end(await ssr(pathname));   // a route → the SSR page (carries #qed-state)
});
server.listen(PORT);
await sleep(300);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
try {
  const page = await browser.newPage();
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  // sanity: the SSR page embeds the dehydrated state
  check('SSR page carries the dehydrated state', (await ssr('/')).includes('id="qed-state"'), true);

  await page.goto(`http://localhost:${PORT}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .catalog', { timeout: 20000 });
  await sleep(150);  // give a (hypothetical) refetch time to fire

  const text = await page.$eval('#app .catalog', (e) => e.textContent);
  check('catalog rendered the books (from dehydrated state)', text.includes('Dune') && text.includes('Neuromancer'), true);
  check('no "Loading…", the data was already present', text.includes('Loading'), false);
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
