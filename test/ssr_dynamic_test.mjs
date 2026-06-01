// ssr_dynamic_test.mjs — dynamic, per-request server-side rendering.
//
// A front HTTP server calls the Lean renderer (`lake exe users_ssr <path>`) once per request;
// each request renders the full page for THAT route, with a user page's profile filled
// server-side. We fetch a few paths and assert the HTML is rendered dynamically and correctly
// (home → search; /users/<name> → that person's bio, in the initial HTML, no client fetch).
import { spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import puppeteer from 'puppeteer'; // (unused, but keeps the test env identical to the others)

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8177;

console.log('▸ building the SSR renderer (lake exe users_ssr)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && lake build users_ssr`], { stdio: 'inherit' }).status !== 0) {
  console.error('build failed'); process.exit(1);
}

const render = (path) => {
  const r = spawnSync('bash', ['-lc', `cd '${ROOT}' && lake exe users_ssr '${path}' 2>/dev/null`], { encoding: 'utf8' });
  return r.stdout;
};

// the "Lean-native HTTP entry": one render per request, dynamic on the path.
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
  const ada = await (await fetch(`http://localhost:${PORT}/users/ada`)).text();
  const alan = await (await fetch(`http://localhost:${PORT}/users/alan`)).text();

  check('home renders the search page', has(home, 'class="search"') && !has(home, 'class="bio"'), true);
  check('/users/ada renders Ada\'s bio server-side', has(ada, 'Wrote the first algorithm.') && has(ada, 'class="bio"'), true);
  check('/users/alan renders Alan\'s bio server-side', has(alan, 'Asked what machines can decide.'), true);
  check('rendering is dynamic (pages differ by route)', home !== ada && ada !== alan, true);
  check('each page is a full document that loads the app', has(ada, 'id="app"') && has(ada, '<script'), true);
} finally {
  server.close();
}

console.log(failures === 0 ? '\nALL DYNAMIC-SSR CHECKS PASSED ✅' : `\n${failures} DYNAMIC-SSR CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
