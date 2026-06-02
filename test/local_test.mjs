// local_test.mjs — end-to-end test for keyed local-state components (`useState`).
//
// Builds the local-state web entry to .qed/dev, serves it (cross-origin isolated),
// then drives the real app in headless Chromium. It covers the whole feature:
//   • local + sibling isolation — a widget update touches only that widget.
//   • caret — typing in a local note keeps focus + value across local re-renders.
//   • bubble — a widget's Report reaches the root `update`.
//   • init-from-props — each widget's note is seeded from its row label (.localInit).
//   • nesting — a Tag inside a Widget bubbles up to the Widget (two levels deep).
//   • unmount GC — removing a row drops its (and its nested tag's) state.
//   • snapshot/restore — the whole local store round-trips through window.qed.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8134;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building local-state demo (Examples.LocalWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.LocalWeb ./qed build --dev`],
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
  await page.waitForSelector('#app .app .rows .row', { timeout: 20000 });

  const A = '#app .rows .row:nth-child(1)';
  const B = '#app .rows .row:nth-child(2)';
  const countAt   = (row) => page.$eval(`${row} .widget .count`, (e) => e.textContent);
  const noteAt    = (row) => page.$eval(`${row} .widget .note`, (e) => e.value);
  const pinnedAt  = (row) => page.$eval(`${row} .widget .pinned`, (e) => e.textContent);
  const reportTxt = () => page.$eval('#app .report', (e) => e.textContent);
  const labels    = () => page.$$eval('#app .rows .row .label', (els) => els.map((e) => e.textContent));
  const snapshot  = () => page.evaluate(() => JSON.parse(window.qed.snapshot()));
  const clickIn = async (row, sel) => {
    await page.evaluate((row, sel) => document.querySelector(`${row} ${sel}`).click(), row, sel);
    await sleep(30);
  };
  const tag    = (sel, mark) => page.$eval(sel, (el, mark) => { el.dataset.mark = mark; }, mark);
  const markOf = (sel) => page.$eval(sel, (el) => el.dataset.mark || '');

  // --- init-from-props: each widget seeded from its row (note = label) ---
  check('two rows mounted', await labels(), ['Alpha', 'Beta']);
  check('row A widget starts at 0', await countAt(A), '0');
  check('row A note seeded from its row label (init-from-props)', await noteAt(A), 'Alpha');
  check('row B note seeded from its row label', await noteAt(B), 'Beta');
  check('no reports yet', await reportTxt(), 'no reports yet');

  // --- local + sibling isolation ---
  await tag(`${A} .widget`, 'A-widget');
  await tag(`${B} .widget`, 'B-widget');
  await clickIn(A, '.inc'); await clickIn(A, '.inc'); await clickIn(A, '.inc');
  check('local increments affect only that row', await countAt(A), '3');
  check('sibling row is untouched by a local update', await countAt(B), '0');
  check("the updated row's widget node was patched in place", await markOf(`${A} .widget`), 'A-widget');
  check('a local update does not re-render siblings', await markOf(`${B} .widget`), 'B-widget');
  check('a local update does not touch the root model', await reportTxt(), 'no reports yet');

  // --- caret survival in a local input (note already holds "Alpha") ---
  await page.focus(`${A} .widget .note`);
  await page.type(`${A} .widget .note`, 'X');
  check('local note keeps its value across per-keystroke re-renders', await noteAt(A), 'AlphaX');
  check('local note keeps focus while typing',
    await page.evaluate(() => document.activeElement?.classList.contains('note')), true);
  check('typing in one note does not leak to a sibling', await noteAt(B), 'Beta');

  // --- nesting: a Tag inside the Widget bubbles up to the Widget ---
  check('row A not pinned initially', await pinnedAt(A), '');
  await clickIn(A, '.widget .pin');                       // click the nested tag's button
  check('nested Tag bubbled up to its parent Widget (pinned)', await pinnedAt(A), 'pinned');
  check('nesting is isolated to that row', await pinnedAt(B), '');

  // --- bubble a typed output up to the root ---
  await clickIn(A, '.report');
  check('a Report bubbles the count up to the root', await reportTxt(), 'last report: row 0 = 3');

  // --- local state survives a root re-render; new row seeded fresh ---
  await page.type('#app .new', 'Gamma');
  await page.click('#app .addbtn');
  await sleep(50);
  check('row added (root re-render)', await labels(), ['Alpha', 'Beta', 'Gamma']);
  check('local count survived the root re-render', await countAt(A), '3');
  check('local note survived the root re-render', await noteAt(A), 'AlphaX');
  check('pinned state survived the root re-render', await pinnedAt(A), 'pinned');
  check('the new row seeds its own note from its label', await noteAt('#app .rows .row:nth-child(3)'), 'Gamma');
  check('the new row starts at 0', await countAt('#app .rows .row:nth-child(3)'), '0');

  // --- snapshot / restore: the whole local store round-trips ---
  const snap = await snapshot();
  check('snapshot holds row 0 widget state', JSON.parse(snap['widget@0']).count, 3);
  check('snapshot holds the nested tag state', JSON.parse(snap['tag@t0']).on, true);
  await clickIn(A, '.inc'); await clickIn(A, '.inc');     // count 3 → 5
  await page.type(`${A} .widget .note`, 'ZZZ');           // note drift
  check('local state drifted before restore', await countAt(A), '5');
  await page.evaluate((s) => window.qed.restore(JSON.stringify(s)), snap);
  await sleep(40);
  check('restore brought the count back', await countAt(A), '3');
  check('restore brought the note back', await noteAt(A), 'AlphaX');

  // --- unmount GC: removing a row drops its (and its nested tag's) state ---
  check('store has row 1 widget + tag before removal',
    [snap['widget@1'] !== undefined, snap['tag@t1'] !== undefined], [true, true]);
  await page.evaluate(() => {
    const li = [...document.querySelectorAll('#app .rows .row')].find((e) => e.querySelector('.label').textContent === 'Beta');
    li.querySelector('.rm').click();
  });
  await sleep(50);
  const after = await snapshot();
  check('Beta removed', await labels(), ['Alpha', 'Gamma']);
  check('removed row widget state was GC-ed', after['widget@1'], undefined);
  check('removed row nested tag state was GC-ed', after['tag@t1'], undefined);
  check('surviving row state kept', JSON.parse(after['widget@0']).count, 3);
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL LOCAL CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
