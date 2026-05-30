// todo_test.mjs — end-to-end test for keyed add / remove / reorder of list items.
//
// Builds the todo web entry to .qed/dev, serves it (cross-origin isolated), then
// drives the real app in headless Chromium. Beyond "the list matches the model",
// it asserts the things that distinguish KEYED reconciliation from positional:
//   1. removing a middle row drops that row's node and the row below keeps its own
//      DOM node (an expando set on it survives), rather than being rewritten;
//   2. a row follows its key across a Sort (its tagged node, and a focus inside it,
//      move with it instead of staying at the old position).
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

const server = spawn('python3', [`${ROOT}runtime/serve.py`, String(PORT), SERVE], { stdio: 'inherit' });
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
  const texts = () => page.$$eval('#app .todo .item .text', (els) => els.map((e) => e.textContent));
  const markAt = (n) => page.$eval(`#app .todo .item:nth-child(${n})`, (el) => el.dataset.mark || '');
  const addItem = async (t) => { await page.type(NEW, t); await page.click('#app .addbtn'); await sleep(40); };
  // tag the row whose text === `t` with a DOM expando (survives iff the node is reused)
  const tagByText = (t, mark) => page.$$eval('#app .todo .item', (els, t, mark) => {
    const li = els.find((e) => e.querySelector('.text').textContent === t);
    if (li) li.dataset.mark = mark;
  }, t, mark);
  // dispatch a row's remove (or any control's) programmatically — no click, so focus
  // isn't stolen and the removal can't be confused with a click side effect
  const dispatchOf = async (sel) => {
    const id = await page.$eval(sel, (el) => el.getAttribute('data-qed-click'));
    await page.evaluate((i) => window.qed.dispatch(Number(i)), id);
    await sleep(50);
  };
  const removeByText = async (t) => {
    const id = await page.$$eval('#app .todo .item', (els, t) => {
      const li = els.find((e) => e.querySelector('.text').textContent === t);
      return li ? li.querySelector('.rm').getAttribute('data-qed-click') : null;
    }, t);
    await page.evaluate((i) => window.qed.dispatch(Number(i)), id);
    await sleep(50);
  };

  // --- add three items ---
  check('starts empty', await texts(), []);
  await addItem('alpha'); await addItem('beta'); await addItem('gamma');
  check('three items added', await texts(), ['alpha', 'beta', 'gamma']);
  check('input cleared after add', await page.$eval(NEW, (el) => el.value), '');

  // --- keyed remove from the MIDDLE: gamma's node must survive and move up ---
  await tagByText('gamma', 'gamma-node');
  await removeByText('beta');
  check('middle row removed', await texts(), ['alpha', 'gamma']);
  check('the row BELOW the removed one kept its own DOM node (keyed, not rewritten)',
    await markAt(2), 'gamma-node');   // positional diff would have lost this expando

  // --- reorder by Sort: a tagged row follows its key to the new position ---
  await addItem('beta'); await addItem('delta');     // [alpha, gamma, beta, delta]
  await tagByText('beta', 'beta-node');
  await page.click('#app .sortbtn'); await sleep(50);
  check('sorted alphabetically', await texts(), ['alpha', 'beta', 'delta', 'gamma']);
  check('moved row kept its DOM node across the sort',
    await markAt(2), 'beta-node');     // beta moved 4th → 2nd, same node

  // --- focus inside a row follows that row across a reorder ---
  // Focus gamma's remove button, then trigger a reconcile that MOVES gamma. With
  // an atomic move (moveBefore, Chrome 133+) the focus rides along; without it a
  // relocate is a remove+insert that blurs. Node identity is preserved either way
  // (proven by the expando checks above), so we only assert the focus-follows
  // bonus where the browser supports the atomic move.
  const hasMoveBefore = await page.evaluate(() => typeof Element.prototype.moveBefore === 'function');
  await page.evaluate(() => {
    const li = [...document.querySelectorAll('#app .todo .item')]
      .find((e) => e.querySelector('.text').textContent === 'gamma');
    li.querySelector('.rm').focus();
  });
  await removeByText('delta');                       // [alpha, beta, gamma]; gamma moves up
  const focusedRow = await page.evaluate(() =>
    document.activeElement?.closest?.('.item')?.querySelector?.('.text')?.textContent);
  if (hasMoveBefore)
    check('focus follows a row across a keyed move (atomic moveBefore)', focusedRow, 'gamma');
  else
    console.log('  SKIP  focus-follows-move: browser lacks moveBefore (node identity still preserved)');

  // --- a focused, half-typed input (a sibling of the list) is untouched by reconcile ---
  await page.focus(NEW);
  await page.type(NEW, 'eggs');
  await removeByText('beta');
  check('input KEEPS focus across a list change',
    await page.evaluate(() => document.activeElement?.classList.contains('new')), true);
  check('input KEEPS its half-typed draft', await page.$eval(NEW, (el) => el.value), 'eggs');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL TODO CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
