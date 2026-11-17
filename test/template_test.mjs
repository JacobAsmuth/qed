import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { buildDevAsync, send, withBrowser } from './harness.mjs';

const dir = await buildDevAsync('Examples.TemplateWeb');
const ssrMod = await import(pathToFileURL(path.join(dir, 'ssr.mjs')).href);
const shell = (await (await ssrMod.default(new Request('http://127.0.0.1/'))).text())
  .replace('class="count"', 'class="count" data-server="1"');
if (!shell.includes('data-server')) throw new Error('could not mark server node');

await withBrowser('TEMPLATE', {
  dir,
  routes: (req, res, url) => {
    if (url.pathname === '/ssr') { send(res, 200, 'text/html', shell); return true; }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .demo', { timeout: 20000 });

  const count    = () => page.$eval('.count', (e) => e.textContent);
  const greeting = () => page.$$eval('.demo > p.greeting', (ps) => ps.map((p) => p.textContent));
  const status   = () => page.$eval('.demo > p.hint, .demo > p.live', (p) => ({ cls: p.className, text: p.textContent }));
  const rows     = () => page.$$eval('.demo ul.todos li', (ls) => ls.map((l) => ({ text: l.textContent, done: l.className === 'done' })));
  const structTag = (i) => page.$eval(`.demo ul.structural li:nth-child(${i + 1}) > *`, (e) => e.tagName);
  const clickText = (t) => page.evaluate((t) => {
    [...document.querySelectorAll('button')].find((b) => b.textContent === t).click();
  }, t);

  check('count starts 0', await count(), '0');
  check('no greeting initially', await greeting(), []);
  check('ifElse shows the hint branch at count 0', await status(), { cls: 'hint', text: 'click + to start' });
  check('two todos, first done', await rows(), [{ text: 'learn Lean', done: true }, { text: 'write a template', done: false }]);
  check('scoped style applied (padding from auto-injected css)',
    await page.$eval('#styled-banner', (e) => getComputedStyle(e).padding), '7px');
  check('keyless map renders the items (total fallback)',
    await page.$$eval('.demo ul.keyless li', (ls) => ls.map((l) => l.textContent)),
    ['learn Lean', 'write a template']);
  check('structural row 0 is the done branch (<p>)', await structTag(0), 'P');
  check('structural row 1 is the open branch (<span>)', await structTag(1), 'SPAN');

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

  await page.focus('input');
  await page.type('input', 'Ada', { delay: 10 });
  check('input echoes the model', await page.$eval('input', (e) => e.value), 'Ada');
  check('caret kept at end while typing', await page.$eval('input', (e) => e.selectionStart), 3);
  check('showIf revealed the greeting', await greeting(), ['Hello, Ada!']);
  await page.$eval('input', (e) => { e.value = ''; e.dispatchEvent(new Event('input', { bubbles: true })); });
  check('showIf hid the greeting when empty', await greeting(), []);

  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  check('second row toggled to done (signal-attribute class)', (await rows())[1], { text: 'write a template', done: true });
  check('structural row 1 flipped to <p> on toggle (no staleness)', await structTag(1), 'P');
  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  check('row click still works after a value-only update', (await rows())[1], { text: 'write a template', done: false });
  check('structural row 1 flipped back to <span>', await structTag(1), 'SPAN');

  await clickText('add todo');
  check('row added (keyed list grew)', await rows(), [
    { text: 'learn Lean', done: true },
    { text: 'write a template', done: false },
    { text: 'item 3', done: false },
  ]);

  const editSel = '.demo ul.edit li:nth-child(1) input.editor';
  await page.evaluate(() => document.querySelector('.demo ul.edit li:nth-child(1) .label').click());
  await page.waitForSelector(editSel, { timeout: 4000 });
  check('inline edit: row 0 became a controlled input', (await page.$(editSel)) !== null, true);
  await page.$eval(editSel, (e) => { e.dataset.tag = 'editsentinel'; e.focus(); e.setSelectionRange(e.value.length, e.value.length); });
  await page.type(editSel, 'ZZ', { delay: 10 });
  check('inline edit: input node survived typing (NOT rebuilt)',
    await page.$eval(editSel, (e) => e.dataset.tag), 'editsentinel');
  check('inline edit: input still has focus after typing',
    await page.evaluate(() => document.activeElement?.dataset.tag === 'editsentinel'), true);
  check('inline edit: controlled value reflects the typing', await page.$eval(editSel, (e) => e.value), 'learn LeanZZ');
  check('inline edit: model received the edit (other lists show new text)',
    await page.$eval('.demo ul.todos li:nth-child(1)', (e) => e.textContent), 'learn LeanZZ');

  // SSR hydration & server node adoption
  await page.goto(`${baseUrl}/ssr`, { waitUntil: 'load' });
  await page.waitForSelector('#app .count', { timeout: 15000 });
  await page.waitForFunction(() => Boolean(window.qed), { timeout: 5000 });
  const adopted = () => page.$eval('#app .count', (e) => e.getAttribute('data-server') === '1');
  const rowDone = (i) => page.$eval(`.demo ul.todos li:nth-child(${i + 1})`, (e) => e.className === 'done');

  check('SSR count starts 0', await count(), '0');
  check('hydration adopted server node (data-server survived)', await adopted(), true);
  check('SSR row 0 (done) hydrated with its class', await rowDone(0), true);
  await clickText('+');
  check('clicking + after hydration increments', await count(), '1');
  check('adopted count node survived update', await adopted(), true);
  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  check('toggling a row after hydration flips its class', await rowDone(1), true);
});
