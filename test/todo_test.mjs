import { withBrowser, sleep } from './harness.mjs';

await withBrowser('TODO', { webRoot: 'Examples.TodoWeb' }, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .todo', { timeout: 20000 });

  const NEW = '#app .todo .new';
  const texts = () => page.$$eval('#app .todo .row .item', (els) => els.map((e) => e.textContent));
  const dones = () => page.$$eval('#app .todo .row .item', (els) => els.map((e) => e.classList.contains('done')));
  const markAt = (n) => page.$eval(`#app .todo .row:nth-child(${n})`, (el) => el.dataset.mark || '');
  const addItem = async (t) => { await page.type(NEW, t); await page.click('#app .addbtn'); await sleep(40); };
  const tagRow = (t, mark) => page.$$eval('#app .todo .row', (els, t, mark) => {
    const li = els.find((e) => e.querySelector('.item').textContent === t);
    if (li) li.dataset.mark = mark;
  }, t, mark);
  const dispatchChild = async (t, childSel) => {
    const id = await page.$$eval('#app .todo .row', (els, t, childSel) => {
      const li = els.find((e) => e.querySelector('.item').textContent === t);
      return li ? li.querySelector(childSel).getAttribute('data-qed-on-click') : null;
    }, t, childSel);
    await page.evaluate((i) => window.qed.dispatch(Number(i)), id);
    await sleep(50);
  };
  const toggle = (t) => dispatchChild(t, '.item');
  const remove = (t) => dispatchChild(t, '.rm');

  check('starts empty', await texts(), []);
  await addItem('alpha'); await addItem('beta'); await addItem('gamma');
  check('three rows added', await texts(), ['alpha', 'beta', 'gamma']);
  check('input cleared after add', await page.$eval(NEW, (el) => el.value), '');

  await toggle('beta');
  check('toggling a row updates only that row (component, routed by key)', await dones(), [false, true, false]);

  await tagRow('gamma', 'gamma-node');
  await remove('beta');
  check('middle row removed', await texts(), ['alpha', 'gamma']);
  check('the row below the removed one kept its own DOM node (keyed)', await markAt(2), 'gamma-node');

  await addItem('delta');
  await toggle('delta');
  await tagRow('delta', 'delta-node');
  await page.click('#app .sortbtn'); await sleep(50);
  check('sorted alphabetically', await texts(), ['alpha', 'delta', 'gamma']);
  check('moved row kept its DOM node across the sort', await markAt(2), 'delta-node');
  check('moved row kept its component state (still done)', (await dones())[1], true);

  const hasMoveBefore = await page.evaluate(() => typeof Element.prototype.moveBefore === 'function');
  await page.evaluate(() => {
    const li = [...document.querySelectorAll('#app .todo .row')]
      .find((e) => e.querySelector('.item').textContent === 'gamma');
    li.querySelector('.rm').focus();
  });
  await remove('delta');
  const focusedRow = await page.evaluate(() =>
    document.activeElement?.closest?.('.row')?.querySelector?.('.item')?.textContent);
  if (hasMoveBefore)
    check('focus follows a row across a keyed move (atomic moveBefore)', focusedRow, 'gamma');

  await page.focus(NEW);
  await page.type(NEW, 'eggs');
  await remove('gamma');
  check('input KEEPS focus across a list change',
    await page.evaluate(() => document.activeElement?.classList.contains('new')), true);
  check('input KEEPS its half-typed draft', await page.$eval(NEW, (el) => el.value), 'eggs');
});
