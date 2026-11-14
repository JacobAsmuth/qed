import { spawnSync } from 'node:child_process';
import { ROOT, buildExe, serve, send, checker } from './harness.mjs';

const bin = buildExe('users_ssr');
const render = (p) => spawnSync(bin, [p], { cwd: ROOT, encoding: 'utf8' }).stdout;
const { check, finish } = checker('DYNAMIC-SSR');
const srv = await serve({
  routes: (req, res, url) => {
    send(res, 200, 'text/html', render(url.pathname));
    return true;
  },
});

try {
  const home = await (await fetch(`${srv.baseUrl}/`)).text();
  const ada  = await (await fetch(`${srv.baseUrl}/users/ada`)).text();
  const alan = await (await fetch(`${srv.baseUrl}/users/alan`)).text();

  check('home renders the search page', home.includes('class="search"') && !home.includes('class="bio"'), true);
  check("/users/ada renders Ada's bio server-side", ada.includes('Wrote the first algorithm.') && ada.includes('class="bio"'), true);
  check("/users/alan renders Alan's bio server-side", alan.includes('Asked what machines can decide.'), true);
  check('rendering is dynamic (pages differ by route)', home !== ada && ada !== alan, true);
  check('each page is a full document that loads the app', ada.includes('id="app"') && ada.includes('<script'), true);
} finally {
  await srv.close();
}
finish();
