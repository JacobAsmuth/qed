import { writeFileSync } from 'node:fs';
import { withBrowser, sleep } from './harness.mjs';

const FILE = '/tmp/qed-effects-pick.txt';
writeFileSync(FILE, 'hello-from-file');

await withBrowser('EFFECTS', {
  webRoot: 'Examples.EffectsWeb',
  onConsole: (m, fail) => {
    const t = m.text();
    if (t.includes('unknown effect') || t.includes('unknown result effect'))
      fail('host.js reported an unhandled effect kind');
  },
}, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#count', { timeout: 20000 });

  const count  = () => page.$eval('#count', (e) => e.textContent);
  const status = () => page.$eval('#status', (e) => e.textContent);
  const click  = async (sel) => { await page.click(`#app ${sel}`); await sleep(40); };

  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'load' });
  await page.waitForSelector('#count');
  check('count starts at 0 (clean storage)', await count(), '0');
  await click('.inc'); await click('.inc');
  check('count is 2 after two increments', await count(), '2');
  await page.reload({ waitUntil: 'load' });
  await page.waitForSelector('#count');
  await sleep(60);
  check('count persisted across reload (localStorage)', await count(), '2');

  await page.type('#title-input', 'Hello Qed');
  await click('.apply');
  check('Cmd.setTitle set the document title', await page.title(), 'Hello Qed');

  await click('.roll');
  const rolled = parseInt((await status()).replace('rolled: ', ''), 10);
  check('Cmd.randomInt returned a d6', rolled >= 1 && rolled <= 6, true);

  await click('.delay');
  check('status shows waiting immediately', await status(), 'waiting…');
  await sleep(400);
  check('Cmd.after fired the delayed message', await status(), 'delayed!');

  await page.evaluate(() => {
    globalThis.__qed.ports['echoOut'] = (p) => globalThis.__qed.send('echoIn', JSON.stringify(JSON.parse(p) + '-pong'));
  });
  await click('.ping');
  await sleep(40);
  check('typed port round-trip (echoOut → JS → echoIn → onPort)', await status(), 'echo: ping-pong');

  await page.click('#app .search');
  await page.type('#app .search', 'abc', { delay: 25 });
  await sleep(350);
  check('debounced search ran for the final query', await status(), 'searched: abc');
  check('afterKeyed cancelled the intermediate timers', await page.$eval('#searches', (e) => e.textContent), '1');

  await click('.save');
  check('batch updated the status', await status(), 'saved+titled');
  check('batch ran setTitle too', await page.title(), 'Saved!');

  await click('.focus');
  check('Cmd.focus focused the input', await page.evaluate(() => document.activeElement?.id), 'title-input');

  const [chooser] = await Promise.all([page.waitForFileChooser(), click('.pick')]);
  await chooser.accept([FILE]);
  await sleep(80);
  check('Cmd.pickFile read the chosen file', await status(), 'file: qed-effects-pick.txt=hello-from-file');
});
