import { withBrowser, ssrShell, send, sleep } from './harness.mjs';

const shell = await ssrShell('Examples.TemplateWeb', 'template_ssr');

await withBrowser('TEMPLATE-HYDRATION', {
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
  await page.waitForFunction(() => document.querySelector('[data-qed-on-click]') !== null, { timeout: 5000 });

  const count = () => page.$eval('#app .count', (e) => e.textContent.trim());
  const adopted = () => page.$eval('#app .count', (e) => e.getAttribute('data-server') === '1');
  const rowDone = (i) => page.$eval(`.demo ul.todos li:nth-child(${i + 1})`, (e) => e.className === 'done');

  check('template SSR shows count 0', await count(), '0');
  check('hydration ADOPTED the count node (data-server survived)', await adopted(), true);
  check('row 0 (done) hydrated with its class', await rowDone(0), true);

  await page.evaluate(() => [...document.querySelectorAll('#app button')].find((b) => b.textContent === '+').click());
  await sleep(60);
  check('clicking + after hydration increments the count', await count(), '1');
  check('count node is still the adopted one', await adopted(), true);

  await page.evaluate(() => [...document.querySelectorAll('.demo ul.todos li')][1].click());
  await sleep(60);
  check('toggling a row flips its class (signal rehydrated)', await rowDone(1), true);
});
