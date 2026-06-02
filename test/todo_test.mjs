// todo_test.mjs — end-to-end test for a keyed list of reusable row components.
//
// Builds the todo web entry to .qed/dev, serves it (cross-origin isolated), then
// drives the real app in headless Chromium. It checks the component half (a click
// inside a row toggles only that row) and the keyed half (removing or sorting moves
// whole rows, keeping each row's DOM node — proven by an expando that survives — and
// the focus inside a moved row, via the atomic moveBefore where supported).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8132;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building todo (Examples.TodoWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.TodoWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

const server = spawn('python3', ['-m', 'http.server', String(PORT), '--directory', SERVE], { stdio: 'inherit' });
await sleep(900);

let failures = 0;
const check = (label, got, want) => {
  const ok = JSON.stringify(got) === JSON.stringify(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'],
});

try {
  const page = await browser.newPage();
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .todo', { timeout: 20000 });

  const NEW = '#app .todo .new';
  const texts = () => page.$$eval('#app .todo .row .item', (els) => els.map((e) => e.textContent));
  const dones = () => page.$$eval('#app .todo .row .item', (els) => els.map((e) => e.classList.contains('done')));
  const markAt = (n) => page.$eval(`#app .todo .row:nth-child(${n})`, (el) => el.dataset.mark || '');
  const addItem = async (t) => { await page.type(NEW, t); await page.click('#app .addbtn'); await sleep(40); };
  // tag the row whose label === `t` with a DOM expando (survives iff the node is reused)
  const tagRow = (t, mark) => page.$$eval('#app .todo .row', (els, t, mark) => {
    const li = els.find((e) => e.querySelector('.item').textContent === t);
    if (li) li.dataset.mark = mark;
  }, t, mark);
  // dispatch the handler on a row's child (.item toggle or .rm remove) programmatically,
  // so a click can't be confused with the cause and won't steal focus
  const dispatchChild = async (t, childSel) => {
    const id = await page.$$eval('#app .todo .row', (els, t, childSel) => {
      const li = els.find((e) => e.querySelector('.item').textContent === t);
      return li ? li.querySelector(childSel).getAttribute('data-qed-on-click') : null;
    }, t, childSel);
    await page.evaluate((i) => window.qed.dispatch(Number(i)), id);
    await sleep(50);
  };
  const toggle = (t) => dispatchChild(t, '.item');
  const remove = (t) => dispatchChild(t, '.rm');

  // --- add three rows ---
  check('starts empty', await texts(), []);
  await addItem('alpha'); await addItem('beta'); await addItem('gamma');
  check('three rows added', await texts(), ['alpha', 'beta', 'gamma']);
  check('input cleared after add', await page.$eval(NEW, (el) => el.value), '');

  // --- component: a click inside a row toggles only that row ---
  await toggle('beta');
  check('toggling a row updates only that row (component, routed by key)',
    await dones(), [false, true, false]);

  // --- keyed remove from the MIDDLE: gamma's node survives and moves up ---
  await tagRow('gamma', 'gamma-node');
  await remove('beta');
  check('middle row removed', await texts(), ['alpha', 'gamma']);
  check('the row below the removed one kept its own DOM node (keyed)',
    await markAt(2), 'gamma-node');

  // --- keyed sort: a row keeps its node AND its local state across the move ---
  await addItem('delta');                 // [alpha, gamma, delta]
  await toggle('delta');                  // delta done
  await tagRow('delta', 'delta-node');
  await page.click('#app .sortbtn'); await sleep(50);   // [alpha, delta, gamma]
  check('sorted alphabetically', await texts(), ['alpha', 'delta', 'gamma']);
  check('moved row kept its DOM node across the sort', await markAt(2), 'delta-node');
  check('moved row kept its component state (still done)', (await dones())[1], true);

  // --- focus inside a row follows that row across a keyed move ---
  const hasMoveBefore = await page.evaluate(() => typeof Element.prototype.moveBefore === 'function');
  await page.evaluate(() => {
    const li = [...document.querySelectorAll('#app .todo .row')]
      .find((e) => e.querySelector('.item').textContent === 'gamma');
    li.querySelector('.rm').focus();
  });
  await remove('delta');                  // [alpha, gamma]; gamma moves up
  const focusedRow = await page.evaluate(() =>
    document.activeElement?.closest?.('.row')?.querySelector?.('.item')?.textContent);
  if (hasMoveBefore)
    check('focus follows a row across a keyed move (atomic moveBefore)', focusedRow, 'gamma');
  else
    console.log('  SKIP  focus-follows-move: browser lacks moveBefore (node identity still preserved)');

  // --- a focused, half-typed input (a sibling of the list) is untouched by reconcile ---
  await page.focus(NEW);
  await page.type(NEW, 'eggs');
  await remove('gamma');
  check('input KEEPS focus across a list change',
    await page.evaluate(() => document.activeElement?.classList.contains('new')), true);
  check('input KEEPS its half-typed draft', await page.$eval(NEW, (el) => el.value), 'eggs');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL TODO CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
