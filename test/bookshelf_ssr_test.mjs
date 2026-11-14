import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { SERVE, buildDev, serve, send, withBrowser, sleep } from './harness.mjs';

buildDev('Examples.BookshelfWeb');

const books = [
  { id: 'dune',        title: 'Dune',                author: 'Frank Herbert',      year: 1965, genre: 'fiction',    inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer',         author: 'William Gibson',     year: 1984, genre: 'fiction',    inPrint: true },
  { id: 'geb',         title: 'Gödel, Escher, Bach', author: 'Douglas Hofstadter', year: 1979, genre: 'nonfiction', inPrint: false },
];
const api = (pathname) => {
  if (pathname === '/api/books') return JSON.stringify(books);
  if (pathname.startsWith('/api/books/')) {
    const b = books.find((x) => x.id === decodeURIComponent(pathname.slice('/api/books/'.length)));
    return b ? JSON.stringify(b) : null;
  }
  return null;
};

const ssrMod = await import(pathToFileURL(path.join(SERVE, 'ssr.mjs')).href);
const handler = ssrMod.makeHandler(ssrMod.mod, {
  title: 'Bookshelf', script: '/qed_host.mjs',
  fetch: async (u) => {
    const body = api(new URL(u).pathname);
    return body !== null ? new Response(body, { status: 200 }) : new Response('{}', { status: 404 });
  },
});
const render = async (p, origin = 'http://127.0.0.1') =>
  await (await handler(new Request(`${origin}${p}`))).text();

let apiHits = 0;

await withBrowser('BOOKSHELF-SSR', {
  spa: false,
  routes: async (req, res, url) => {
    if (url.pathname.startsWith('/api/')) {
      apiHits++;
      send(res, 404, 'application/json', '{}');
      return true;
    }
    if (!url.pathname.includes('.')) {
      send(res, 200, 'text/html', await render(url.pathname, url.origin));
      return true;
    }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  const home = await render('/');
  const dune = await render('/books/dune');
  const geb  = await render('/books/geb');
  const add  = await render('/new');

  check('catalog lists every book server-side',
    home.includes('class="books"') && home.includes('>Dune<') && home.includes('>Neuromancer<') && home.includes('Gödel, Escher, Bach'), true);
  check("a detail page carries that book's fields",
    dune.includes('Frank Herbert') && dune.includes('1965') && dune.includes('In print'), true);
  check('out-of-print is rendered from the data', geb.includes('Out of print'), true);
  check('the add page is the form', add.includes('class="qed-form"') && add.includes('type="checkbox"') && add.includes('<select'), true);
  check('rendering is dynamic (pages differ by route)', home !== dune && dune !== geb && geb !== add, true);
  check('each page is a full document that loads the app', dune.includes('id="app"') && dune.includes('<script'), true);
  check('the page embeds the dehydrated state', home.includes('id="qed-state"'), true);

  const apiSrv = await serve({
    routes: async (req, res, url) => {
      const body = api(url.pathname);
      if (body !== null) { send(res, 200, 'application/json', body); return true; }
      const r = await ssrMod.default(new Request(url));
      res.writeHead(r.status, Object.fromEntries(r.headers.entries()));
      res.end(await r.text());
      return true;
    },
  });
  try {
    const viaServer = await (await fetch(`${apiSrv.baseUrl}/books/neuromancer`)).text();
    check('served end-to-end (same-origin API, default fetch)', viaServer.includes('William Gibson'), true);
  } finally {
    await apiSrv.close();
  }

  await page.goto(`${baseUrl}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .catalog', { timeout: 20000 });
  await sleep(150);

  const text = await page.$eval('#app .catalog', (e) => e.textContent);
  check('catalog rendered the books (from dehydrated state)', text.includes('Dune') && text.includes('Neuromancer'), true);
  check('no "Loading…", the data was already present', text.includes('Loading'), false);
  check('the client did NOT refetch the catalog (zero /api hits)', apiHits, 0);

  await page.click('#app nav a');
  await sleep(50);
  check('app is live after hydration (nav present)', (await page.$('#app nav')) !== null, true);
});
