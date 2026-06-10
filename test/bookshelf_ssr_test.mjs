// bookshelf_ssr_test.mjs: server-side rendering through the generated request handler.
//
// `qed build` emits ssr.mjs next to the client bundle: a request → HTML handler built
// from the app itself (route dispatch, the app's own `queries` run server-side, render,
// dehydrate). The app contains no SSR code. We render a few routes through the handler
// (data injected via the `fetch` option) and assert the markup is dynamic and complete,
// then serve one page through a real HTTP server with the API on the same origin, the
// default-fetch path `qed start` uses.
import { spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const ROOT = new URL('..', import.meta.url).pathname;
const SERVE = path.join(ROOT, '.qed', 'dev');
const PORT = 8188;

console.log('▸ building (QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BookshelfWeb ./qed build --dev`], { stdio: 'inherit' }).status !== 0) {
  console.error('build failed'); process.exit(1);
}

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

// A handler with the data source injected: render pages without any HTTP server at all.
const handler = ssrMod.makeHandler(ssrMod.mod, {
  title: 'Bookshelf', script: '/qed_host.mjs',
  fetch: async (u) => {
    const body = api(new URL(u).pathname);
    return body !== null ? new Response(body, { status: 200 })
                         : new Response('{}', { status: 404 });
  },
});
const render = async (p) => await (await handler(new Request(`http://localhost:${PORT}${p}`))).text();

let failures = 0;
const check = (label, got, want) => {
  const ok = got === want;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};
const has = (h, n) => h.includes(n);

const home = await render('/');
const dune = await render('/books/dune');
const geb  = await render('/books/geb');
const add  = await render('/new');

check('catalog lists every book server-side',
  has(home, 'class="books"') && has(home, '>Dune<') && has(home, '>Neuromancer<') && has(home, 'Gödel, Escher, Bach'), true);
check('a detail page carries that book\'s fields',
  has(dune, 'Frank Herbert') && has(dune, '1965') && has(dune, 'In print'), true);
check('out-of-print is rendered from the data', has(geb, 'Out of print'), true);
check('the add page is the form', has(add, 'class="qed-form"') && has(add, 'type="checkbox"') && has(add, '<select'), true);
check('rendering is dynamic (pages differ by route)', home !== dune && dune !== geb && geb !== add, true);
check('each page is a full document that loads the app', has(dune, 'id="app"') && has(dune, '<script'), true);
check('the page embeds the dehydrated state', has(home, 'id="qed-state"'), true);

// And once through a real server: same-origin /api + the default handler (real fetch).
const server = createServer(async (req, res) => {
  const u = new URL(req.url, `http://localhost:${PORT}`);
  const body = api(u.pathname);
  if (body !== null) { res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(body); return; }
  const r = await ssrMod.default(new Request(u));
  res.writeHead(r.status, Object.fromEntries(r.headers.entries()));
  res.end(await r.text());
});
server.listen(PORT);
try {
  const viaServer = await (await fetch(`http://localhost:${PORT}/books/neuromancer`)).text();
  check('served end-to-end (same-origin API, default fetch)', has(viaServer, 'William Gibson'), true);
} finally {
  server.close();
}

console.log(failures === 0 ? '\nALL BOOKSHELF-SSR CHECKS PASSED ✅' : `\n${failures} BOOKSHELF-SSR CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
