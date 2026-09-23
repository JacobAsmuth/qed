// Local demo API + generated SSR handler. Books live in memory until restart.
// From the repo root:
//   QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev
//   node Examples/bookshelf-server.mjs
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';

const build = new URL('../.qed/dev/', import.meta.url);
const port = Number(process.env.PORT ?? 8000);
const books = [
  { id: 'dune', title: 'Dune', author: 'Frank Herbert', year: 1965, genre: 'fiction', inPrint: true },
  { id: 'neuromancer', title: 'Neuromancer', author: 'William Gibson', year: 1984, genre: 'fiction', inPrint: true },
  { id: 'geb', title: 'Gödel, Escher, Bach', author: 'Douglas Hofstadter', year: 1979, genre: 'nonfiction', inPrint: false },
];
let nextId = 1;

// Both the SSR renderer and browser use the same mock data source.
function api(pathname, method = 'GET', body = '') {
  if (pathname === '/api/books' && method === 'POST') {
    let value;
    try { value = JSON.parse(body); }
    catch { return Response.json({ error: 'Invalid JSON' }, { status: 400 }); }
    if (!value || typeof value !== 'object' || Array.isArray(value)) {
      return Response.json({ error: 'Expected a book object' }, { status: 400 });
    }
    const created = { ...value, id: `book-${nextId++}` };
    books.push(created);
    return Response.json(created, { status: 201 });
  }
  if (method !== 'GET') return Response.json({ error: 'Method not allowed' }, { status: 405 });
  if (pathname === '/api/books') return Response.json(books);
  if (pathname.startsWith('/api/books/')) {
    const book = books.find((b) => b.id === decodeURIComponent(pathname.slice('/api/books/'.length)));
    if (book) return Response.json(book);
  }
  return Response.json({ error: 'Book not found' }, { status: 404 });
}

const { makeHandler, mod } = await import(new URL('ssr.mjs', build));
const render = makeHandler(mod, {
  title: 'Bookshelf',
  script: '/qed_host.mjs',
  fetch: async (url, options) => api(new URL(url).pathname, options?.method, options?.body),
});
const clientFiles = new Set(['app.mjs', 'qed_rt.mjs', 'qed_dom.mjs', 'qed_host.mjs']);

createServer(async (req, res) => {
  try {
    const url = new URL(req.url, `http://localhost:${port}`);
    let response;
    if (url.pathname.startsWith('/api/')) {
      let body = '';
      for await (const chunk of req) {
        body += chunk;
        if (body.length > 64 * 1024) {
          res.writeHead(413).end('Demo request too large');
          return;
        }
      }
      response = api(url.pathname, req.method, body);
    } else if (req.method !== 'GET') {
      response = new Response('Method not allowed', { status: 405 });
    } else if (clientFiles.has(url.pathname.slice(1))) {
      response = new Response(await readFile(new URL(url.pathname.slice(1), build)), {
        headers: { 'content-type': 'text/javascript' },
      });
    } else if (url.pathname === '/favicon.ico') {
      response = new Response(null, { status: 204 });
    } else {
      response = await render(new Request(url));
    }
    res.writeHead(response.status, {
      ...Object.fromEntries(response.headers),
      'cache-control': 'no-store',
    });
    res.end(Buffer.from(await response.arrayBuffer()));
  } catch (error) {
    console.error(error);
    res.writeHead(500, { 'content-type': 'text/plain' }).end('Bookshelf demo request failed');
  }
}).listen(port, '127.0.0.1', () => {
  console.log(`Bookshelf: http://localhost:${port} (SSR + in-memory demo API)`);
});
