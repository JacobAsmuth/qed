import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { buildDevAsync, send, withBrowser } from './harness.mjs';

const dir = await buildDevAsync('Examples.BookshelfWeb');
const ssrMod = await import(pathToFileURL(path.join(dir, 'ssr.mjs')).href);

const books = [
  { id: 'dune',        title: 'Dune',                author: 'Frank Herbert',      year: 1965, genre: 'fiction',    inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer',         author: 'William Gibson',     year: 1984, genre: 'fiction',    inPrint: true },
  { id: 'geb',         title: 'Gödel, Escher, Bach', author: 'Douglas Hofstadter', year: 1979, genre: 'nonfiction', inPrint: false },
];
const slug = (t) => t.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');
const api = (pathname) => {
  if (pathname === '/api/books') return JSON.stringify(books);
  if (pathname.startsWith('/api/books/')) {
    const b = books.find((x) => x.id === decodeURIComponent(pathname.slice('/api/books/'.length)));
    return b ? JSON.stringify(b) : null;
  }
  return null;
};

let clientApiHits = 0;

await withBrowser('BOOKSHELF', {
  dir,
  spa: false,
  routes: async (req, res, url) => {
    if (url.pathname === '/api/books' && req.method === 'POST') {
      let raw = '';
      for await (const chunk of req) raw += chunk;
      const parsed = JSON.parse(raw);
      const created = { ...parsed, id: slug(parsed.title) };
      books.push(created);
      send(res, 200, 'application/json', JSON.stringify(created));
      return true;
    }
    if (url.pathname.startsWith('/api/')) {
      if (!req.headers['x-qed-ssr']) clientApiHits++;
      const body = api(url.pathname);
      send(res, body !== null ? 200 : 404, 'application/json', body ?? JSON.stringify({ error: 'no such book' }));
      return true;
    }
    if (!url.pathname.includes('.')) {
      const r = await ssrMod.default(new Request(url));
      res.writeHead(r.status, Object.fromEntries(r.headers.entries()));
      res.end(await r.text());
      return true;
    }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  const text = (sel) => page.$eval(sel, (e) => e.textContent.trim());
  const pathOf = () => page.evaluate(() => location.pathname);
  const count = (sel) => page.$$eval(sel, (els) => els.length);

  const [home, dune, geb, add] = await Promise.all(
    ['/', '/books/dune', '/books/geb', '/new'].map((p) => fetch(`${baseUrl}${p}`).then((r) => r.text())),
  );
  check('SSR catalog lists every book and embeds state',
    home.includes('class="books"') && home.includes('>Dune<') && home.includes('>Neuromancer<') &&
    home.includes('Gödel, Escher, Bach') && home.includes('id="qed-state"'), true);
  check('SSR detail renders book fields',
    dune.includes('Frank Herbert') && dune.includes('1965') && dune.includes('In print'), true);
  check('SSR renders out-of-print branch', geb.includes('Out of print'), true);
  check('SSR /new renders form',
    add.includes('class="qed-form"') && add.includes('type="checkbox"') && add.includes('<select'), true);

  clientApiHits = 0;
  await page.goto(`${baseUrl}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .catalog ul.books', { timeout: 20000 });
  const catText = await text('#app .catalog');
  check('hydrated catalog shows books from #qed-state', catText.includes('Dune') && catText.includes('Neuromancer'), true);
  check('no Loading state on SSR hydration', catText.includes('Loading'), false);
  check('zero /api refetch on initial SSR hydration', clientApiHits, 0);
  await page.evaluate(() => { window.__noReload = true; });

  await page.click('#app ul.books > li:nth-child(2) .book-link');
  await page.waitForSelector('#app .book h1', { timeout: 5000 });
  check('book link routed to detail without reload',
    [await pathOf(), await text('#app .book h1'), await page.evaluate(() => window.__noReload === true)],
    ['/books/neuromancer', 'Neuromancer', true]);
  check('scoped style applied (max-width: 40rem)',
    await page.$eval('#app .app', (e) => getComputedStyle(e).maxWidth), '640px');

  await page.click('#app nav a:nth-child(2)');
  await page.waitForSelector('#app .qed-form', { timeout: 5000 });
  const SUBMIT = '#app .qed-form button';
  check('submit disabled when empty', await page.$eval(SUBMIT, (b) => b.hasAttribute('disabled')), true);

  await page.type('#app .qed-form > label:nth-child(1) input', 'The Hobbit');
  await page.type('#app .qed-form > label:nth-child(2) input', 'J.R.R. Tolkien');
  await page.type('#app input[type="number"]', '1937');
  await page.select('#app select', 'fiction');
  await page.click('#app input[type="checkbox"]');
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'), { timeout: 4000 }, SUBMIT);
  check('submit enabled once every field validates', await page.$eval(SUBMIT, (b) => b.hasAttribute('disabled')), false);

  await page.click(SUBMIT);
  await page.waitForSelector('#app .book h1', { timeout: 6000 });
  check('POST created book and routed to detail', await pathOf(), '/books/the-hobbit');
  check('created book detail and checkbox round-tripped',
    [await text('#app .book h1'), await text('#app .in-print')], ['The Hobbit', 'In print']);

  await page.click('#app nav a:nth-child(1)');
  await page.waitForFunction(() => document.querySelectorAll('#app ul.books > li').length === 4, { timeout: 5000 });
  check('created book persisted into catalog', await count('#app ul.books > li'), 4);

  await page.goto(`${baseUrl}/books/nope`, { waitUntil: 'load' });
  await page.waitForSelector('#app .error', { timeout: 6000 });
  check('missing book renders error state', (await text('#app .error')).includes('Error'), true);
});
