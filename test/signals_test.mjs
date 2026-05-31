// signals_test.mjs — end-to-end test for fine-grained signals.
//
// Builds the signals web entry, serves it, and drives it in headless Chromium. It proves
// the defining property: `window.qed.setSignal(name, v)` updates only the bound element —
// no message, no `update`, no diff — so the `renders` counter never moves, and sibling
// signals are independent. The normal dispatch path still works alongside.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8138;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building signals demo (Examples.SignalsWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.SignalsWeb ./qed build --dev`],
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
  await page.waitForSelector('#app .signals', { timeout: 20000 });

  const sig = (n) => page.$eval(`[data-qed-signal="${n}"]`, (e) => e.textContent);
  const renders = () => page.$eval('#renders', (e) => e.textContent);
  const setSignal = (n, v) => page.evaluate((n, v) => window.qed.setSignal(n, v), n, v);

  check('signals start empty', [await sig('a'), await sig('b')], ['', '']);
  check('no renders yet', await renders(), '0');

  // setting a signal updates only its bound element — no message, no diff
  await setSignal('a', 'hello');
  check('setSignal updated the bound element', await sig('a'), 'hello');
  check('sibling signal untouched', await sig('b'), '');
  check('setSignal did NOT re-render the view', await renders(), '0');

  await setSignal('b', 'world');
  check('second signal updates independently', [await sig('a'), await sig('b')], ['hello', 'world']);
  check('still no re-render from signals', await renders(), '0');

  // the normal dispatch path still works alongside signals
  await page.click('#app #ping'); await sleep(30);
  check('a real message re-renders', await renders(), '1');
  check('signals survive a re-render', [await sig('a'), await sig('b')], ['hello', 'world']);

  // a signal can keep changing at any frequency, still without a re-render
  for (let i = 0; i < 5; i++) await setSignal('a', `tick ${i}`);
  check('rapid signal updates land', await sig('a'), 'tick 4');
  check('rapid signal updates never re-render', await renders(), '1');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL SIGNALS CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
