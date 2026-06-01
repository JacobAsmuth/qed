// bookshelf_ssr_test.mjs — dynamic, per-request server-side rendering of the full-stack demo.
//
// A front HTTP server calls the Lean renderer (`lake exe bookshelf_ssr <path>`) once per
// request; each renders the full page for THAT route with its data filled server-side. We
// fetch a few paths and assert the markup is rendered dynamically and correctly — the catalog
// lists every book, a detail page carries that book's fields, and the add page is the form —
// all in the initial HTML, no client fetch. (Client hydration of this fetched-per-route data
// is a separate concern: see the README note on SSR.)
import { spawnSync } from 'node:child_process';
import { createServer } from 'node:http';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8188;

console.log('▸ building the SSR renderer (lake exe bookshelf_ssr)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && lake build bookshelf_ssr`], { stdio: 'inherit' }).status !== 0) {
  console.error('build failed'); process.exit(1);
}

const render = (path) => {
  const r = spawnSync('bash', ['-lc', `cd '${ROOT}' && lake exe bookshelf_ssr '${path}' 2>/dev/null`], { encoding: 'utf8' });
  return r.stdout;
};

const server = createServer((req, res) => {
  res.writeHead(200, { 'Content-Type': 'text/html' });
  res.end(render(new URL(req.url, 'http://x').pathname));
});
server.listen(PORT);

let failures = 0;
const check = (label, got, want) => {
  const ok = got === want;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};
const has = (h, n) => h.includes(n);

try {
  const home = await (await fetch(`http://localhost:${PORT}/`)).text();
  const dune = await (await fetch(`http://localhost:${PORT}/books/dune`)).text();
  const geb  = await (await fetch(`http://localhost:${PORT}/books/geb`)).text();
  const add  = await (await fetch(`http://localhost:${PORT}/new`)).text();

  check('catalog lists every book server-side',
    has(home, 'class="books"') && has(home, '>Dune<') && has(home, '>Neuromancer<') && has(home, 'Gödel, Escher, Bach'), true);
  check('a detail page carries that book\'s fields',
    has(dune, 'Frank Herbert') && has(dune, '1965') && has(dune, 'In print'), true);
  check('out-of-print is rendered from the data', has(geb, 'Out of print'), true);
  check('the add page is the form', has(add, 'class="qed-form"') && has(add, 'type="checkbox"') && has(add, '<select'), true);
  check('rendering is dynamic (pages differ by route)', home !== dune && dune !== geb && geb !== add, true);
  check('each page is a full document that loads the app', has(dune, 'id="app"') && has(dune, '<script'), true);
} finally {
  server.close();
}

console.log(failures === 0 ? '\nALL BOOKSHELF-SSR CHECKS PASSED ✅' : `\n${failures} BOOKSHELF-SSR CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
