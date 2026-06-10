// booking_test.mjs — end-to-end test for threading the current time into a form.
//
// The app reads the clock at startup (Cmd.now) and only then renders the form, so
// `.qed-form` appearing at all proves Cmd.now delivered "today". The `when` field's
// rule is "strictly after today", so a past date keeps submit disabled and a future
// date enables it — computed relative to the real clock.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8127;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building booking (Examples.BookingWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BookingWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

const server = spawn('python3', [`${ROOT}test/mock_llm.py`, String(PORT), SERVE], { stdio: 'inherit' });
await sleep(900);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

// dates relative to the real clock: June 15 of next/last year is always future/past
const year = new Date().getFullYear();
const FUTURE = `${year + 1}-06-15`;
const PAST = `${year - 1}-06-15`;

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox'],
});

try {
  const page = await browser.newPage();
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  // the form only renders once Cmd.now reports today — so this waiting *is* the check
  await page.waitForSelector('#app .qed-form', { timeout: 20000 });
  check('form rendered after Cmd.now delivered today', true, true);

  const WHO = '#app .qed-form > label:nth-child(1) input';
  const WHEN = '#app input[type="date"]';
  const SUBMIT = '#app .qed-form button';
  const disabled = () => page.$eval(SUBMIT, (b) => b.hasAttribute('disabled'));
  const setDate = (v) => page.$eval(WHEN, (el, v) => {
    el.value = v; el.dispatchEvent(new Event('input', { bubbles: true }));
  }, v);

  await page.type(WHO, 'Ada');
  await setDate(PAST);
  check('submit disabled for a past date', await disabled(), true);

  await setDate(FUTURE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'),
    { timeout: 4000 }, SUBMIT);
  check('submit enabled for a future date', await disabled(), false);

  await page.click(SUBMIT);
  await page.waitForSelector('#app .ok', { timeout: 4000 });
  check('booking confirmed', await page.$eval('#app .ok', (e) => e.textContent.trim()), 'Booked for Ada');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL BOOKING CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
