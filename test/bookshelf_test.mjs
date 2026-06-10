// bookshelf_test.mjs: end-to-end test for the full-stack demo: routing + Resource
// (a fetched list AND a fetched record) + a validated form that POSTs and routes to
// its result + scoped styles, all in one app.
//
// Builds Examples.BookshelfWeb to .qed/dev and serves it from a node server that also
// implements the API (GET /api/books, GET /api/books/<id>, POST /api/books) and
// SPA-falls-back to index.html for routes (so deep links work). Then it drives the
// real app in headless Chromium:
//   • a deep link fetches + decodes one book (HTTP + Qed.Json + router),
//   • the catalog fetches + lists the collection,
//   • link clicks navigate without a reload,
//   • the add form gates submit on validity, POSTs a new book, and routes to it,
//   • the new book is then served by the API (the POST persisted),
//   • a scoped style is applied.
import { spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8144;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building bookshelf (Examples.BookshelfWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

// In-memory catalog (the same seed the SSR tests use).
const books = [
  { id: 'dune',        title: 'Dune',                author: 'Frank Herbert',      year: 1965, genre: 'fiction',    inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer',         author: 'William Gibson',     year: 1984, genre: 'fiction',    inPrint: true },
  { id: 'geb',         title: 'Gödel, Escher, Bach', author: 'Douglas Hofstadter', year: 1979, genre: 'nonfiction', inPrint: false },
];
const slug = (t) => t.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');

const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript',
               '.json': 'application/json', '.css': 'text/css' };
const server = createServer(async (req, res) => {
  const { pathname } = new URL(req.url, 'http://x');
  const send = (code, type, body) => {
    res.writeHead(code, {
      'Content-Type': type,
      'Cache-Control': 'no-store',
    });
    res.end(body);
  };
  // --- API ---
  if (pathname === '/api/books' && req.method === 'POST') {
    let raw = '';
    for await (const chunk of req) raw += chunk;
    const b = JSON.parse(raw);
    const created = { ...b, id: slug(b.title) };
    books.push(created);
    return send(200, 'application/json', JSON.stringify(created));
  }
  if (pathname === '/api/books') {
    return send(200, 'application/json', JSON.stringify(books));
  }
  if (pathname.startsWith('/api/books/')) {
    const id = decodeURIComponent(pathname.slice('/api/books/'.length));
    const b = books.find((x) => x.id === id);
    return b ? send(200, 'application/json', JSON.stringify(b))
             : send(404, 'application/json', JSON.stringify({ error: 'no such book' }));
  }
  // extensionless paths are routes → serve the SPA shell; asset paths serve the file
  const fp = (pathname === '/' || !pathname.includes('.')) ? `${SERVE}/index.html` : SERVE + pathname;
  try {
    const buf = await readFile(fp);
    send(200, MIME[fp.slice(fp.lastIndexOf('.'))] || 'application/octet-stream', buf);
  } catch { send(404, 'text/plain', 'not found'); }
});
server.listen(PORT);
await sleep(300);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox'],
});

try {
  const page = await browser.newPage();
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  const text = (sel) => page.$eval(sel, (e) => e.textContent.trim());
  const path = () => page.evaluate(() => location.pathname);
  const count = (sel) => page.$$eval(sel, (els) => els.length);

  // --- deep link: route parsed from the URL, then one book fetched + decoded ---
  await page.goto(`http://localhost:${PORT}/books/dune`, { waitUntil: 'load' });
  await page.waitForSelector('#app .book h1', { timeout: 20000 });
  check('deep link fetched + decoded the book', await text('#app .book h1'), 'Dune');
  check('the detail shows the decoded author/year',
    (await text('#app .author')).includes('Frank Herbert') && (await text('#app .author')).includes('1965'), true);
  await page.evaluate(() => { window.__noReload = true; });

  // --- a scoped style is applied (the hashed shell class set the page width) ---
  check('scoped style applied (max-width: 40rem)',
    await page.$eval('#app .app', (e) => getComputedStyle(e).maxWidth), '640px');

  // --- Catalog link routes home (no reload) and the list is fetched ---
  await page.click('#app nav a:nth-child(1)');
  await page.waitForSelector('#app ul.books', { timeout: 5000 });
  check('Catalog fetched + listed the collection', await count('#app ul.books > li'), 3);
  check('navigation did not reload the page', await page.evaluate(() => window.__noReload === true), true);

  // --- clicking a book link routes to its detail ---
  await page.click('#app ul.books > li:nth-child(2) .book-link');
  await page.waitForSelector('#app .book h1', { timeout: 5000 });
  check('book link routed to the detail', await path(), '/books/neuromancer');
  check('and shows that book', await text('#app .book h1'), 'Neuromancer');

  // --- the add form: gated until valid, then POSTs and routes to the new book ---
  await page.click('#app nav a:nth-child(2)');               // "Add a book"
  await page.waitForSelector('#app .qed-form', { timeout: 5000 });
  check('add page is the form', await path(), '/new');

  const SUBMIT = '#app .qed-form button';
  check('submit disabled when empty', await page.$eval(SUBMIT, (b) => b.hasAttribute('disabled')), true);

  await page.type('#app .qed-form > label:nth-child(1) input', 'The Hobbit');     // title
  await page.type('#app .qed-form > label:nth-child(2) input', 'J.R.R. Tolkien'); // author
  await page.type('#app input[type="number"]', '1937');                           // year
  await page.select('#app select', 'fiction');                                    // genre
  await page.click('#app input[type="checkbox"]');                                // inPrint = true
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'),
    { timeout: 4000 }, SUBMIT);
  check('submit enabled once every field validates', await page.$eval(SUBMIT, (b) => b.hasAttribute('disabled')), false);

  await page.click(SUBMIT);
  await page.waitForSelector('#app .book h1', { timeout: 6000 });
  check('POST created the book and routed to it', await path(), '/books/the-hobbit');
  check('the new book detail shows the entered title', await text('#app .book h1'), 'The Hobbit');
  check('the checkbox value round-tripped (In print)', await text('#app .in-print'), 'In print');

  // --- the POST persisted: the catalog now lists four ---
  await page.click('#app nav a:nth-child(1)');
  await page.waitForFunction(() => document.querySelectorAll('#app ul.books > li').length === 4,
    { timeout: 5000 });
  check('the created book persisted into the catalog', await count('#app ul.books > li'), 4);

  // --- a missing book surfaces the failed state ---
  await page.click('#app nav a:nth-child(1)');               // ensure we're home, current is set
  await page.goto(`http://localhost:${PORT}/books/nope`, { waitUntil: 'load' });
  await page.waitForSelector('#app .error', { timeout: 6000 });
  check('a missing book renders the error state', (await text('#app .error')).includes('Error'), true);
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL BOOKSHELF CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
