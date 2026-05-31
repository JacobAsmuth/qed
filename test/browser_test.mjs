// browser_test.mjs — drives the real DOM in headless Chromium and asserts that
// clicks flow through the Lean `update` and re-render correctly, including the
// proven invariant (decrement at 0 stays 0).
import { spawn } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const PORT = 8123;
const ROOT = new URL('..', import.meta.url).pathname;

// 1. Serve the dev build (.qed/dev) with the COOP/COEP headers the pthread build needs.
const server = spawn('python3', [`${ROOT}runtime/serve.py`, String(PORT), `${ROOT}.qed/dev`], {
  stdio: 'inherit',
});
await sleep(800);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
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

  // Wait for Lean to mount the counter.
  await page.waitForSelector('[data-qed-click]', { timeout: 15000 });

  const count = () => page.$eval('#app .count', (el) => el.textContent.trim());
  const click = async (id) => {
    await page.click(`[data-qed-click="${id}"]`);
    await sleep(50); // allow the synchronous re-render to settle
  };

  check('initial count', await count(), '0');
  await click(1); await click(1);            // increment twice
  check('after +1 +1', await count(), '2');
  await click(0);                            // decrement
  check('after -1', await count(), '1');
  await click(2);                            // reset
  check('after reset', await count(), '0');
  await click(0);                            // decrement at 0 — invariant guards it
  check('decrement at 0 stays 0 (proven invariant)', await count(), '0');

  // The payoff of the verified diff engine: an update patches only the count
  // text, so the input the user is typing in is never rebuilt — focus, cursor,
  // and value all survive. We dispatch the update *programmatically* (as a timer
  // or socket would), which is exactly the case full re-render (innerHTML)
  // destroys: it would blow away the input mid-type.
  await page.focus('#app input');
  await page.type('#app input', 'hello world');
  await page.keyboard.press('Home');         // cursor → position 0
  await page.keyboard.press('ArrowRight');   // cursor → position 1
  await page.evaluate(() => window.qed.dispatch(1)); // increment, no click
  await sleep(50);
  check('count updated under focused input', await count(), '1');
  check('input KEEPS focus after update',
        await page.evaluate(() => document.activeElement?.tagName === 'INPUT'), true);
  check('input KEEPS its typed value',
        await page.$eval('#app input', (el) => el.value), 'hello world');
  check('input KEEPS its cursor position',
        await page.$eval('#app input', (el) => el.selectionStart), 1);

  // Html.lazy: the banner's key never changes, so the diff emits a lazyReuse and the
  // driver skips it. Tag its DOM node and confirm it survives many updates untouched.
  check('lazy banner rendered', await page.$eval('#banner', (el) => el.textContent), 'built once, then memoized');
  await page.evaluate(() => { document.getElementById('banner').dataset.mark = 'memoized-node'; });
  await page.evaluate(() => window.qed.dispatch(1)); await sleep(20);   // increment
  await page.evaluate(() => window.qed.dispatch(0)); await sleep(20);   // decrement
  await page.evaluate(() => window.qed.dispatch(2)); await sleep(20);   // reset
  check('lazy subtree skipped — its DOM node survived every update',
        await page.$eval('#banner', (el) => el.dataset.mark), 'memoized-node');
  check('count still updated around the memoized subtree', await count(), '0');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL BROWSER CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
