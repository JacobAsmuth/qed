// users_test.mjs — end-to-end test for HTTP fetch+decode, URL routing, and events.
//
// Builds the routed users demo to .qed/dev and serves it from a tiny node server
// that also answers /api/users/<name> with JSON and SPA-falls-back to index.html
// (so deep links work). Then it
// drives the real app in headless Chromium and checks:
//   • a deep link fetches + decodes a profile (HTTP + Qed.Json),
//   • link clicks / form submit navigate without a page reload (router),
//   • back/forward re-routes (popstate),
//   • focus highlights the box, Escape clears it, Enter submits (events).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8133;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building users (Examples.UsersWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.UsersWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

const profiles = {
  ada:  { name: 'Ada',  bio: 'Wrote the first algorithm.' },
  alan: { name: 'Alan', bio: 'Asked what machines can decide.' },
  slow: { name: 'Slow', bio: 'Arrived late.' },   // served with a delay, to test the stale-response race
};
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
  if (pathname.startsWith('/api/users/')) {
    const name = decodeURIComponent(pathname.slice('/api/users/'.length)).toLowerCase();
    const p = profiles[name];
    const respond = () => p ? send(200, 'application/json', JSON.stringify(p))
                            : send(404, 'application/json', JSON.stringify({ error: 'no such user' }));
    if (name === 'slow') return void setTimeout(respond, 800);   // delay so a faster nav can overtake it
    return respond();
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

  const bio = () => page.$eval('#app .profile .bio', (e) => e.textContent.trim());
  const path = () => page.evaluate(() => location.pathname);

  // --- deep link: initial route is parsed from the URL, then the profile is fetched + decoded ---
  await page.goto(`http://localhost:${PORT}/users/ada`, { waitUntil: 'load' });
  await page.waitForSelector('#app .profile .bio', { timeout: 20000 });
  check('deep link fetched + decoded the profile', await bio(), 'Wrote the first algorithm.');
  // mark the window so we can detect a full page reload (which would clear it)
  await page.evaluate(() => { window.__noReload = true; });

  // --- link click navigates home without reloading ---
  await page.click('#app .home-link');
  await page.waitForSelector('#app .search', { timeout: 5000 });
  check('Home link routed to the search page', await path(), '/');
  check('navigation did not reload the page', await page.evaluate(() => window.__noReload === true), true);

  // --- submit the search (button) → navigate to a user page → fetch + decode ---
  await page.type('#app .q', 'alan');
  await page.click('#app .go');
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('search submit navigated to the user', await path(), '/users/alan');
  check('and fetched the right profile', await bio(), 'Asked what machines can decide.');

  // --- back button re-routes (popstate) ---
  await page.goBack();
  await page.waitForSelector('#app .search', { timeout: 5000 });
  check('back button routed home', await path(), '/');

  // --- focus highlights the box; Escape clears it (onFocus/onBlur/onKeydown) ---
  await page.focus('#app .q');
  await page.waitForFunction(() => document.querySelector('#app .q')?.classList.contains('focused'),
    { timeout: 4000 });
  check('input gains a focused class on focus', true, true);
  await page.type('#app .q', 'zzz');
  await page.keyboard.press('Escape');
  await sleep(50);
  check('Escape clears the query (onKeydown)', await page.$eval('#app .q', (e) => e.value), '');
  await page.evaluate(() => document.querySelector('#app .q').blur());
  await sleep(50);
  check('input loses the focused class on blur',
    await page.$eval('#app .q', (e) => e.classList.contains('focused')), false);

  // --- Enter submits the form (onSubmit, reload suppressed) ---
  await page.focus('#app .q');
  await page.type('#app .q', 'ada');
  await page.keyboard.press('Enter');
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('Enter submitted the form and navigated', await path(), '/users/ada');
  check('and fetched the profile', await bio(), 'Wrote the first algorithm.');

  // --- stale-response race: start a SLOW fetch, then navigate to a fast one before it resolves.
  //     The slow (now-stale) response must NOT overwrite the page — Cached.put drops it by key. ---
  const search = async (name) => {            // clear the box (Escape) then submit a username
    await page.focus('#app .q'); await page.keyboard.press('Escape'); await sleep(20);
    await page.type('#app .q', name); await page.keyboard.press('Enter');
  };
  await page.click('#app .home-link'); await page.waitForSelector('#app .search', { timeout: 5000 });
  await search('slow');
  await page.waitForSelector('#app .loading', { timeout: 5000 });   // slow profile is loading…
  await page.click('#app .home-link'); await page.waitForSelector('#app .search', { timeout: 5000 });
  await search('ada');                                              // …overtake it before it resolves
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('fast navigation shows the current user', await bio(), 'Wrote the first algorithm.');
  await sleep(1000);                                                // let the slow (stale) response land
  check('stale response did NOT overwrite the page (race fixed)', await bio(), 'Wrote the first algorithm.');
} finally {
  await browser.close();
  server.close();
}

console.log(failures === 0 ? '\nALL USERS CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
