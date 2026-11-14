import { withBrowser, ssrShell, send, sleep } from './harness.mjs';

const shell = await ssrShell('Examples.Web', 'counter');

await withBrowser('SSR', {
  spa: false,
  routes: (req, res, url) => {
    if (url.pathname === '/' || url.pathname === '/index.html') {
      send(res, 200, 'text/html', shell);
      return true;
    }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .count', { timeout: 15000 });

  const count = () => page.$eval('#app .count', (e) => e.textContent.trim());
  const adopted = () => page.$eval('#app .count', (e) => e.getAttribute('data-server') === '1');

  check('server-rendered count is shown', await count(), '0');
  await page.waitForFunction(() => document.querySelector('[data-qed-on-click]') !== null, { timeout: 5000 });
  check('hydration ADOPTED the server node (data-server survived)', await adopted(), true);

  await page.click('[data-qed-on-click="0"]'); await sleep(40);
  await page.evaluate(() => [...document.querySelectorAll('#app button')].find((b) => b.textContent === '+').click());
  await sleep(40);
  check('clicking + after hydration increments', await count(), '1');
  check('the adopted node is still the same after an update', await adopted(), true);
});
