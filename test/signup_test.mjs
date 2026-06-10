// signup_test.mjs — end-to-end test for the form across HTML input types.
//
// Builds the signup web entry to .qed/dev, serves it (static, cross-origin
// isolated), then drives the real app in headless Chromium: fill text/number/date,
// pick a <select>, toggle the checkbox. Asserts the submit gate tracks validity
// (so the `onCheck` event and the "submit ⇔ valid" guarantee work in a browser).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8126;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building signup (Examples.SignupWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.SignupWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

// mock_llm.py doubles as a static server for the build.
const server = spawn('python3', [`${ROOT}test/mock_llm.py`, String(PORT), SERVE], { stdio: 'inherit' });
await sleep(900);

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

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .qed-form', { timeout: 20000 });

  const EMAIL = '#app .qed-form > label:nth-child(1) input';
  const AGE   = '#app .qed-form > label:nth-child(2) input';
  const DATE  = '#app input[type="date"]';
  const AGREE = '#app input[type="checkbox"]';
  const PLAN  = '#app select';
  const SUBMIT = '#app .qed-form button';
  const disabled = () => page.$eval(SUBMIT, (b) => b.hasAttribute('disabled'));
  // set a value and fire the `input` event the driver listens for (for date)
  const setInput = (sel, v) => page.$eval(sel, (el, v) => {
    el.value = v; el.dispatchEvent(new Event('input', { bubbles: true }));
  }, v);

  // --- empty: submit gated off ---
  check('submit disabled when empty', await disabled(), true);

  // --- fill the text + number + date + select, but leave the box unchecked ---
  await page.type(EMAIL, 'a@b.co');     // onInput (text)
  await page.type(AGE, '30');           // onInput (number)
  await setInput(DATE, '1995-06-15');   // onInput (date → verified Qed.Date)
  await page.select(PLAN, 'pro');       // onInput (select)
  check('still disabled before checkbox', await disabled(), true);   // agree must be true

  // --- check the box: onCheck fires, draft.agree = "true", form now valid ---
  await page.click(AGREE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'),
    { timeout: 4000 }, SUBMIT);
  check('enabled after checking the box (onCheck)', await disabled(), false);

  // --- unchecking re-gates: onCheck works both directions ---
  await page.click(AGREE);
  await page.waitForFunction((s) => document.querySelector(s).hasAttribute('disabled'),
    { timeout: 4000 }, SUBMIT);
  check('disabled again after unchecking', await disabled(), true);

  // --- recheck and submit: the validated account surfaces ---
  await page.click(AGREE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'),
    { timeout: 4000 }, SUBMIT);
  await page.click(SUBMIT);
  await page.waitForSelector('#app .ok', { timeout: 4000 });
  check('submitted account shows the email',
    await page.$eval('#app .ok', (e) => e.textContent.trim()), 'Created account for a@b.co');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL SIGNUP CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
