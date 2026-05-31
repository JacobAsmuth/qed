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
  const greeting = () => page.$$eval('.demo > p', (ps) => ps.map((p) => p.textContent));
  const rows    = () => page.$$eval('.demo ul li', (ls) => ls.map((l) => l.textContent));
  const clickText = (t) => page.evaluate((t) => {
    const b = [...document.querySelectorAll('button')].find((b) => b.textContent === t);
    b.click();
  }, t);

  // initial render
  check('count starts 0', await count(), '0');
  check('no greeting initially', await greeting(), []);
  check('two todos, first done', await rows(), ['✓ learn Lean', 'write a template']);

  // node identity across an update: tag the count element, then bump the counter
  await page.$eval('.count', (e) => (e.dataset.tag = 'sentinel'));
  await clickText('+');
  check('count is 1 after +', await count(), '1');
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

  // keyed list, value-only update: toggle a row (its text is a signal) — the row's click
  // handler must survive even though the handler tables aren't rebuilt
  await page.evaluate(() => [...document.querySelectorAll('.demo ul li')][1].click());
  check('second row toggled (signal text update)', (await rows())[1], '✓ write a template');
  await page.evaluate(() => [...document.querySelectorAll('.demo ul li')][1].click());
  check('row click still works after a value-only update', (await rows())[1], 'write a template');
  // structural update: add a row
  await clickText('add todo');
  check('row added (keyed list grew)', await rows(), ['✓ learn Lean', 'write a template', 'item 3']);
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL TEMPLATE CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
