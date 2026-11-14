import { withBrowser, send } from './harness.mjs';

const books = [
  { id: 'dune',        title: 'Dune',                author: 'Frank Herbert',      year: 1965, genre: 'fiction',    inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer',         author: 'William Gibson',     year: 1984, genre: 'fiction',    inPrint: true },
  { id: 'geb',         title: 'Gödel, Escher, Bach', author: 'Douglas Hofstadter', year: 1979, genre: 'nonfiction', inPrint: false },
];
const slug = (t) => t.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');

await withBrowser('BOOKSHELF', {
  webRoot: 'Examples.BookshelfWeb',
  routes: async (req, res, url) => {
    if (url.pathname === '/api/books' && req.method === 'POST') {
      let raw = '';
      for await (const chunk of req) raw += chunk;
      const b = JSON.parse(raw);
      const created = { ...b, id: slug(b.title) };
      books.push(created);
      send(res, 200, 'application/json', JSON.stringify(created));
      return true;
    }
    if (url.pathname === '/api/books') {
      send(res, 200, 'application/json', JSON.stringify(books));
      return true;
    }
    if (url.pathname.startsWith('/api/books/')) {
      const id = decodeURIComponent(url.pathname.slice('/api/books/'.length));
      const b = books.find((x) => x.id === id);
      if (b) send(res, 200, 'application/json', JSON.stringify(b));
      else send(res, 404, 'application/json', JSON.stringify({ error: 'no such book' }));
      return true;
    }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  const text = (sel) => page.$eval(sel, (e) => e.textContent.trim());
  const path = () => page.evaluate(() => location.pathname);
  const count = (sel) => page.$$eval(sel, (els) => els.length);

  await page.goto(`${baseUrl}/books/dune`, { waitUntil: 'load' });
  await page.waitForSelector('#app .book h1', { timeout: 20000 });
  check('deep link fetched + decoded the book', await text('#app .book h1'), 'Dune');
  check('the detail shows the decoded author/year',
    (await text('#app .author')).includes('Frank Herbert') && (await text('#app .author')).includes('1965'), true);
  await page.evaluate(() => { window.__noReload = true; });

  check('scoped style applied (max-width: 40rem)',
    await page.$eval('#app .app', (e) => getComputedStyle(e).maxWidth), '640px');

  await page.click('#app nav a:nth-child(1)');
  await page.waitForSelector('#app ul.books', { timeout: 5000 });
  check('Catalog fetched + listed the collection', await count('#app ul.books > li'), 3);
  check('navigation did not reload the page', await page.evaluate(() => window.__noReload === true), true);

  await page.click('#app ul.books > li:nth-child(2) .book-link');
  await page.waitForSelector('#app .book h1', { timeout: 5000 });
  check('book link routed to the detail', await path(), '/books/neuromancer');
  check('and shows that book', await text('#app .book h1'), 'Neuromancer');

  await page.click('#app nav a:nth-child(2)');
  await page.waitForSelector('#app .qed-form', { timeout: 5000 });
  check('add page is the form', await path(), '/new');

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
  check('POST created the book and routed to it', await path(), '/books/the-hobbit');
  check('the new book detail shows the entered title', await text('#app .book h1'), 'The Hobbit');
  check('the checkbox value round-tripped (In print)', await text('#app .in-print'), 'In print');

  await page.click('#app nav a:nth-child(1)');
  await page.waitForFunction(() => document.querySelectorAll('#app ul.books > li').length === 4, { timeout: 5000 });
  check('the created book persisted into the catalog', await count('#app ul.books > li'), 4);

  await page.goto(`${baseUrl}/books/nope`, { waitUntil: 'load' });
  await page.waitForSelector('#app .error', { timeout: 6000 });
  check('a missing book renders the error state', (await text('#app .error')).includes('Error'), true);
});
