import { withBrowser } from './harness.mjs';

const year = new Date().getFullYear();
const FUTURE = `${year + 1}-06-15`;
const PAST = `${year - 1}-06-15`;

await withBrowser('BOOKING', { webRoot: 'Examples.BookingWeb' }, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .qed-form', { timeout: 20000 });
  check('form rendered after Cmd.now delivered today', true, true);

  const WHO = '#app .qed-form > label:nth-child(1) input';
  const WHEN = '#app input[type="date"]';
  const SUBMIT = '#app .qed-form button';
  const disabled = () => page.$eval(SUBMIT, (b) => b.hasAttribute('disabled'));
  const setDate = (v) => page.$eval(WHEN, (el, v) => {
    el.value = v;
    el.dispatchEvent(new Event('input', { bubbles: true }));
  }, v);

  await page.type(WHO, 'Ada');
  await setDate(PAST);
  check('submit disabled for a past date', await disabled(), true);

  await setDate(FUTURE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'), { timeout: 4000 }, SUBMIT);
  check('submit enabled for a future date', await disabled(), false);

  await page.click(SUBMIT);
  await page.waitForSelector('#app .ok', { timeout: 4000 });
  check('booking confirmed', await page.$eval('#app .ok', (e) => e.textContent.trim()), 'Booked for Ada');
});
