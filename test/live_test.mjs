import { withBrowser } from './harness.mjs';

await withBrowser('LIVE', { webRoot: 'Examples.LiveWeb' }, async ({ page, check, baseUrl }) => {
  const n = () => page.$eval('#app .live .n', (e) => e.textContent.trim());

  await page.goto(`${baseUrl}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .live .n', { timeout: 20000 });
  check('starts at 0', await n(), '0');

  for (let i = 0; i < 3; i++) await page.click('#app .inc');
  check('three +1 clicks → 3', await n(), '3');

  await page.click('#app .double');
  check('double reflects the current number (fresh handler)', await n(), '6');

  await page.$eval('#app .reset', (e) => e.dispatchEvent(new MouseEvent('dblclick', { bubbles: true })));
  check('onDoubleClick (generic `on` event) fired', await n(), '0');
});
