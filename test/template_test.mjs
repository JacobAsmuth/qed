// template_test.mjs — end-to-end test for the fine-grained `View` template driver.
//
// Builds the template demo, serves it, drives it in headless Chromium, and checks that
// the fine-grained path (build once, patch only changed bindings) produces correct DOM:
// scalar value updates (counter, input echo), a `showIf` flip (greeting appears/hides),
// a keyed-list toggle (a row's class), and a keyed-list grow (add a row). It also checks
// node identity is preserved across an update (the counter's element is not rebuilt) and
// that a typed input keeps its caret — the point of not re-rendering the tree.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8142;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building template demo (Examples.TemplateWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.TemplateWeb ./qed build --dev`],
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
  await page.waitForSelector('#app .demo', { timeout: 20000 });

  const count   = () => page.$eval('.count', (e) => e.textContent);
  const greeting = () => page.$$eval('.demo > p.greeting', (ps) => ps.map((p) => p.textContent));
  // the native `if/else` (lifted to `ifElse`): a `.hint` paragraph at count 0, else `.live`
  const status  = () => page.$eval('.demo > p.hint, .demo > p.live',
    (p) => ({ cls: p.className, text: p.textContent }));
  const rows    = () => page.$$eval('.demo ul.todos li', (ls) => ls.map((l) => ({ text: l.textContent, done: l.className === 'done' })));
  // the structural list: each row is `<p>` when done, `<span>` when open (an ifElse inside the
  // row). The tag of row i's single child tells us which branch is live.
  const structTag = (i) => page.$eval(`.demo ul.structural li:nth-child(${i + 1}) > *`, (e) => e.tagName);
  const clickText = (t) => page.evaluate((t) => {
    const b = [...document.querySelectorAll('button')].find((b) => b.textContent === t);
    b.click();
  }, t);

  // initial render
  check('count starts 0', await count(), '0');
  check('no greeting initially', await greeting(), []);
  check('ifElse shows the hint branch at count 0', await status(), { cls: 'hint', text: 'click + to start' });
  check('two todos, first done', await rows(), [{ text: 'learn Lean', done: true }, { text: 'write a template', done: false }]);
  // scoped styling: the <style> emitted by styleSheet applies to the hashed class
  check('scoped style applied (padding from styleSheet)',
    await page.$eval('#styled-banner', (e) => getComputedStyle(e).padding), '7px');
  // a keyless `.map` still compiles + renders (it degraded to a diffed dynNode list)
  check('keyless map renders the items (total fallback)',
    await page.$$eval('.demo ul.keyless li', (ls) => ls.map((l) => l.textContent)),
    ['learn Lean', 'write a template']);
  check('structural row 0 is the done branch (<p>)', await structTag(0), 'P');
  check('structural row 1 is the open branch (<span>)', await structTag(1), 'SPAN');

  // node identity across an update: tag the count element, then bump the counter
  await page.$eval('.count', (e) => (e.dataset.tag = 'sentinel'));
  await clickText('+');
  check('count is 1 after +', await count(), '1');
  check('ifElse flipped to the live branch after +', await status(), { cls: 'live', text: 'count is 1' });
  check('count node was patched in place, not rebuilt',
    await page.$eval('.count', (e) => e.dataset.tag), 'sentinel');
  await clickText('+'); await clickText('+');
  check('count is 3', await count(), '3');
  await clickText('−');
  check('count is 2 after −', await count(), '2');
  check('updating the counter did not disturb the list', (await rows()).length, 2);

  // a controlled input + a showIf flip: typing reveals the greeting; clearing hides it
  await page.focus('input');
  await page.type('input', 'Ada', { delay: 10 });
  check('input echoes the model', await page.$eval('input', (e) => e.value), 'Ada');
  check('caret kept at end while typing', await page.$eval('input', (e) => e.selectionStart), 3);
  check('showIf revealed the greeting', await greeting(), ['Hello, Ada!']);
  // clear the field
  await page.$eval('input', (e) => { e.value = ''; });
  await page.type('input', ' ', { delay: 10 });           // fire an input event
  await page.$eval('input', (e) => { e.value = ''; e.dispatchEvent(new Event('input', { bubbles: true })); });
  await sleep(30);
  check('showIf hid the greeting when empty', await greeting(), []);

  // keyed list, value-only update: toggle a row — its `class` is a signal-attribute, so
  // the class flips fine-grained (no diff); the click handler survives the value-only update
  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  check('second row toggled to done (signal-attribute class)', (await rows())[1], { text: 'write a template', done: true });
  // the staleness fix: the SAME toggle flips the structural row's element from <span> to <p>.
  // The ifElse is baked statically in the row, so this only updates because the structural
  // fingerprint changed the row key → reconciled through the verified keyed diff.
  check('structural row 1 flipped to <p> on toggle (no staleness)', await structTag(1), 'P');
  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  check('row click still works after a value-only update', (await rows())[1], { text: 'write a template', done: false });
  check('structural row 1 flipped back to <span>', await structTag(1), 'SPAN');
  // structural update: add a row
  await clickText('add todo');
  check('row added (keyed list grew)', await rows(), [
    { text: 'learn Lean', done: true },
    { text: 'write a template', done: false },
    { text: 'item 3', done: false },
  ]);

  // inline editing: a CONTROLLED input inside a row's ifElse. The crucial property: typing
  // must NOT rebuild the row, so the input keeps focus and caret. We tag the input node and
  // verify the tag (and focus) survive several keystrokes.
  const editSel = '.demo ul.edit li:nth-child(1) input.editor';
  await page.evaluate(() => document.querySelector('.demo ul.edit li:nth-child(1) .label').click()); // startEdit
  await sleep(20);
  check('inline edit: row 0 became a controlled input', (await page.$(editSel)) !== null, true);
  await page.$eval(editSel, (e) => { e.dataset.tag = 'editsentinel'; e.focus(); e.setSelectionRange(e.value.length, e.value.length); });
  await page.type(editSel, 'ZZ', { delay: 15 });
  await sleep(20);
  check('inline edit: input node survived typing (NOT rebuilt — focus would be lost otherwise)',
    await page.$eval(editSel, (e) => e.dataset.tag), 'editsentinel');
  check('inline edit: input still has focus after typing',
    await page.evaluate(() => document.activeElement && document.activeElement.dataset.tag === 'editsentinel'), true);
  check('inline edit: controlled value reflects the typing', await page.$eval(editSel, (e) => e.value), 'learn LeanZZ');
  check('inline edit: model received the edit (other lists show new text)',
    await page.$eval('.demo ul.todos li:nth-child(1)', (e) => e.textContent), 'learn LeanZZ');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL TEMPLATE CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
