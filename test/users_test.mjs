import { withBrowser, send, sleep } from './harness.mjs';

const profiles = {
  ada:  { name: 'Ada',  bio: 'Wrote the first algorithm.' },
  alan: { name: 'Alan', bio: 'Asked what machines can decide.' },
  slow: { name: 'Slow', bio: 'Arrived late.' },
};

await withBrowser('USERS', {
  webRoot: 'Examples.UsersWeb',
  routes: (req, res, url) => {
    if (!url.pathname.startsWith('/api/users/')) return false;
    const name = decodeURIComponent(url.pathname.slice('/api/users/'.length)).toLowerCase();
    const p = profiles[name];
    const respond = () => p ? send(res, 200, 'application/json', JSON.stringify(p))
                            : send(res, 404, 'application/json', JSON.stringify({ error: 'no such user' }));
    if (name === 'slow') setTimeout(respond, 800);
    else respond();
    return true;
  },
}, async ({ page, check, baseUrl }) => {
  const bio = () => page.$eval('#app .profile .bio', (e) => e.textContent.trim());
  const path = () => page.evaluate(() => location.pathname);

  await page.goto(`${baseUrl}/users/ada`, { waitUntil: 'load' });
  await page.waitForSelector('#app .profile .bio', { timeout: 20000 });
  check('deep link fetched + decoded the profile', await bio(), 'Wrote the first algorithm.');
  await page.evaluate(() => { window.__noReload = true; });

  await page.click('#app .home-link');
  await page.waitForSelector('#app .search', { timeout: 5000 });
  check('Home link routed to the search page', await path(), '/');
  check('navigation did not reload the page', await page.evaluate(() => window.__noReload === true), true);

  await page.type('#app .q', 'alan');
  await page.click('#app .go');
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('search submit navigated to the user', await path(), '/users/alan');
  check('and fetched the right profile', await bio(), 'Asked what machines can decide.');

  await page.goBack();
  await page.waitForSelector('#app .search', { timeout: 5000 });
  check('back button routed home', await path(), '/');

  await page.focus('#app .q');
  await page.waitForFunction(() => document.querySelector('#app .q')?.classList.contains('focused'), { timeout: 4000 });
  check('input gains a focused class on focus', true, true);
  await page.type('#app .q', 'zzz');
  await page.keyboard.press('Escape');
  await sleep(50);
  check('Escape clears the query (onKeydown)', await page.$eval('#app .q', (e) => e.value), '');
  await page.evaluate(() => document.querySelector('#app .q').blur());
  await sleep(50);
  check('input loses the focused class on blur',
    await page.$eval('#app .q', (e) => e.classList.contains('focused')), false);

  await page.focus('#app .q');
  await page.type('#app .q', 'ada');
  await page.keyboard.press('Enter');
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('Enter submitted the form and navigated', await path(), '/users/ada');
  check('and fetched the profile', await bio(), 'Wrote the first algorithm.');

  const search = async (name) => {
    await page.focus('#app .q'); await page.keyboard.press('Escape'); await sleep(20);
    await page.type('#app .q', name); await page.keyboard.press('Enter');
  };
  await page.click('#app .home-link'); await page.waitForSelector('#app .search', { timeout: 5000 });
  await search('slow');
  await page.waitForSelector('#app .loading', { timeout: 5000 });
  await page.click('#app .home-link'); await page.waitForSelector('#app .search', { timeout: 5000 });
  await search('ada');
  await page.waitForSelector('#app .profile .bio', { timeout: 5000 });
  check('fast navigation shows the current user', await bio(), 'Wrote the first algorithm.');
  await sleep(1000);
  check('stale response did NOT overwrite the page (race fixed)', await bio(), 'Wrote the first algorithm.');
});
