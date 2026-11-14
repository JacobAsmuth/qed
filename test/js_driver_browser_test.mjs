import { withBrowser, sleep } from './harness.mjs';

await withBrowser('DRIVER', { webRoot: 'Examples.Web' }, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .count', { timeout: 15000 });
  const count = () => page.$eval('#app .count', (el) => el.textContent.trim());
  const clickBtn = (label) => page.evaluate((lab) => {
    [...document.querySelectorAll('#app button')].find((x) => x.textContent.trim() === lab).click();
  }, label);

  check('initial', await count(), '0');
  await clickBtn('+'); await clickBtn('+'); await sleep(20);
  check('after + +', await count(), '2');
  await clickBtn('−'); await sleep(20);
  check('after -', await count(), '1');
  await clickBtn('−'); await clickBtn('−'); await clickBtn('−'); await sleep(20);
  check('decrement guarded >= 0 (counterSafe)', await count(), '0');

  await page.focus('#app input'); await page.keyboard.type('hello');
  await clickBtn('+'); await sleep(20);
  check('count after + while typing', await count(), '1');
  check('input keeps value (verified diff)', await page.$eval('#app input', (e) => e.value), 'hello');
  check('input keeps focus', await page.evaluate(() => document.activeElement.tagName), 'INPUT');
  await clickBtn('reset'); await sleep(20);
  check('after reset', await count(), '0');
});
