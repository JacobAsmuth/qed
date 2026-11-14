import { withBrowser } from './harness.mjs';

await withBrowser('SIGNUP', { webRoot: 'Examples.SignupWeb' }, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .qed-form', { timeout: 20000 });

  const EMAIL = '#app .qed-form > label:nth-child(1) input';
  const AGE   = '#app .qed-form > label:nth-child(2) input';
  const DATE  = '#app input[type="date"]';
  const AGREE = '#app input[type="checkbox"]';
  const PLAN  = '#app select';
  const SUBMIT = '#app .qed-form button';
  const disabled = () => page.$eval(SUBMIT, (b) => b.hasAttribute('disabled'));
  const setInput = (sel, v) => page.$eval(sel, (el, v) => {
    el.value = v;
    el.dispatchEvent(new Event('input', { bubbles: true }));
  }, v);

  check('submit disabled when empty', await disabled(), true);

  await page.type(EMAIL, 'a@b.co');
  await page.type(AGE, '30');
  await setInput(DATE, '1995-06-15');
  await page.select(PLAN, 'pro');
  check('still disabled before checkbox', await disabled(), true);

  await page.click(AGREE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'), { timeout: 4000 }, SUBMIT);
  check('enabled after checking the box (onCheck)', await disabled(), false);

  await page.click(AGREE);
  await page.waitForFunction((s) => document.querySelector(s).hasAttribute('disabled'), { timeout: 4000 }, SUBMIT);
  check('disabled again after unchecking', await disabled(), true);

  await page.click(AGREE);
  await page.waitForFunction((s) => !document.querySelector(s).hasAttribute('disabled'), { timeout: 4000 }, SUBMIT);
  await page.click(SUBMIT);
  await page.waitForSelector('#app .ok', { timeout: 4000 });
  check('submitted account shows the email',
    await page.$eval('#app .ok', (e) => e.textContent.trim()), 'Created account for a@b.co');
});
