import { withBrowser, sleep } from './harness.mjs';

await withBrowser('LOCAL', { webRoot: 'Examples.LocalWeb' }, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
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

  const stepCount = () => page.$eval('#app .solo .stepper .count', (e) => e.textContent);
  const stepSaved = () => page.$eval('#app .solo .stepper .savedv', (e) => e.textContent);
  const stepClick = async (sel) => {
    await page.evaluate((s) => document.querySelector(`#app .solo .stepper ${s}`).click(), sel);
    await sleep(30);
  };
  check('stepper starts at its declared default', await stepCount(), '0');
  await stepClick('.dec');
  check('decrement at 0 stays 0 (the clamp stepperSafe is proven on)', await stepCount(), '0');
  await stepClick('.inc'); await stepClick('.inc');
  check('two increments', await stepCount(), '2');
  await stepClick('.save');
  check('save copies count into saved (cross-field set)', await stepSaved(), '2');
  await stepClick('.inc'); await stepClick('.save');
  check('save reads the count at delivery time, not a captured one', await stepSaved(), '3');

  check('two rows mounted', await labels(), ['Alpha', 'Beta']);
  check('row A widget starts at 0', await countAt(A), '0');
  check('row A note seeded from its row label (init-from-props)', await noteAt(A), 'Alpha');
  check('row B note seeded from its row label', await noteAt(B), 'Beta');
  check('no reports yet', await reportTxt(), 'no reports yet');

  await tag(`${A} .widget`, 'A-widget');
  await tag(`${B} .widget`, 'B-widget');
  await clickIn(A, '.inc'); await clickIn(A, '.inc'); await clickIn(A, '.inc');
  check('local increments affect only that row', await countAt(A), '3');
  check('sibling row is untouched by a local update', await countAt(B), '0');
  check("the updated row's widget node was patched in place", await markOf(`${A} .widget`), 'A-widget');
  check('a local update does not re-render siblings', await markOf(`${B} .widget`), 'B-widget');
  check('a local update does not touch the root model', await reportTxt(), 'no reports yet');

  await page.focus(`${A} .widget .note`);
  await page.type(`${A} .widget .note`, 'X');
  check('local note keeps its value across per-keystroke re-renders', await noteAt(A), 'AlphaX');
  check('local note keeps focus while typing',
    await page.evaluate(() => document.activeElement?.classList.contains('note')), true);
  check('typing in one note does not leak to a sibling', await noteAt(B), 'Beta');

  check('row A not pinned initially', await pinnedAt(A), '');
  await clickIn(A, '.widget .pin');
  check('nested Tag bubbled up to its parent Widget (pinned)', await pinnedAt(A), 'pinned');
  check('nesting is isolated to that row', await pinnedAt(B), '');

  await clickIn(A, '.report');
  check('a Report bubbles the count up to the root', await reportTxt(), 'last report: row 0 = 3');

  await page.type('#app .new', 'Gamma');
  await page.click('#app .addbtn');
  await sleep(50);
  check('row added (root re-render)', await labels(), ['Alpha', 'Beta', 'Gamma']);
  check('local count survived the root re-render', await countAt(A), '3');
  check('local note survived the root re-render', await noteAt(A), 'AlphaX');
  check('pinned state survived the root re-render', await pinnedAt(A), 'pinned');
  check('the new row seeds its own note from its label', await noteAt('#app .rows .row:nth-child(3)'), 'Gamma');
  check('the new row starts at 0', await countAt('#app .rows .row:nth-child(3)'), '0');

  const snap = await snapshot();
  check('snapshot holds row 0 widget state', JSON.parse(snap['Local.Widget@0']).count, 3);
  check('snapshot holds the nested tag state', JSON.parse(snap['Local.Tag@t0']).on, true);
  await clickIn(A, '.inc'); await clickIn(A, '.inc');
  await page.type(`${A} .widget .note`, 'ZZZ');
  check('local state drifted before restore', await countAt(A), '5');
  await page.evaluate((s) => window.qed.restore(JSON.stringify(s)), snap);
  await sleep(40);
  check('restore brought the count back', await countAt(A), '3');
  check('restore brought the note back', await noteAt(A), 'AlphaX');

  check('store has row 1 widget + tag before removal',
    [snap['Local.Widget@1'] !== undefined, snap['Local.Tag@t1'] !== undefined], [true, true]);
  await page.evaluate(() => {
    const li = [...document.querySelectorAll('#app .rows .row')].find((e) => e.querySelector('.label').textContent === 'Beta');
    li.querySelector('.rm').click();
  });
  await sleep(50);
  const after = await snapshot();
  check('Beta removed', await labels(), ['Alpha', 'Gamma']);
  check('removed row widget state was GC-ed', after['Local.Widget@1'], undefined);
  check('removed row nested tag state was GC-ed', after['Local.Tag@t1'], undefined);
  check('surviving row state kept', JSON.parse(after['Local.Widget@0']).count, 3);

  await page.focus(`${A} .widget .note`);
  await page.$eval(`${A} .widget .note`, (e) => e.setSelectionRange(2, 2));
  await clickIn(A, '.rename');
  check('parent prop changes reach an extracted child view',
    await page.$eval(`${A} .live-label`, (e) => e.textContent), 'Alpha!');
  check('live props reach nested local components',
    await page.$eval(`${A} .pin`, (e) => e.title), 'Alpha!: AlphaX');
  check('changing props does not reseed local state', await noteAt(A), 'AlphaX');
  check('prop updates preserve local focus and caret',
    await page.$eval(`${A} .note`, (e) => [document.activeElement === e, e.selectionStart]), [true, 2]);
  check('props do not enter the persisted state',
    Object.hasOwn(JSON.parse((await snapshot())['Local.Widget@0']), 'label'), false);
  await clickIn(A, '.reset-note');
  check('named actions read current props', await noteAt(A), 'Alpha!');
  await page.evaluate((s) => window.qed.restore(JSON.stringify(s)), after);
  await sleep(40);
  check('restoring state keeps current props',
    await page.$eval(`${A} .live-label`, (e) => e.textContent), 'Alpha!');
  check('restoring state restores the note separately', await noteAt(A), 'AlphaX');
  check('restore refreshes props derived from parent local state',
    await page.$eval(`${A} .pin`, (e) => e.title), 'Alpha!: AlphaX');
  check('prop refresh does not duplicate local subtrees',
    await page.$$eval('#app .rows .widget', (es) => es.length), 2);
});
