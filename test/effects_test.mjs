import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { withBrowser } from './harness.mjs';

await withBrowser('EFFECTS', {
  webRoot: 'Examples.EffectsWeb',
  onConsole: (m, fail) => {
    const t = m.text();
    if (t.includes('unknown effect') || t.includes('unknown result effect'))
      fail('host.js reported an unhandled effect kind');
  },
}, async ({ page, check, baseUrl }) => {
  const tmpDir = mkdtempSync(path.join(tmpdir(), 'qed-fx-'));
  const file = path.join(tmpDir, 'qed-effects-pick.txt');
  writeFileSync(file, 'hello-from-file');

  try {
    await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
    await page.waitForSelector('#count', { timeout: 20000 });

    const count  = () => page.$eval('#count', (e) => e.textContent);
    const status = () => page.$eval('#status', (e) => e.textContent);

    check('count starts at 0 (clean storage)', await count(), '0');
    await page.click('#app .inc');
    await page.click('#app .inc');
    check('count is 2 after two increments', await count(), '2');
    await page.reload({ waitUntil: 'load' });
    await page.waitForFunction(() => document.querySelector('#count')?.textContent === '2', { timeout: 4000 });
    check('count persisted across reload (localStorage)', await count(), '2');

    await page.type('#title-input', 'Hello Qed');
    await page.click('#app .apply');
    check('Cmd.setTitle set the document title', await page.title(), 'Hello Qed');

    await page.click('#app .roll');
    const rolled = parseInt((await status()).replace('rolled: ', ''), 10);
    check('Cmd.randomInt returned a d6', rolled >= 1 && rolled <= 6, true);

    await page.click('#app .delay');
    check('status shows waiting immediately', await status(), 'waiting…');
    await page.waitForFunction(() => document.querySelector('#status')?.textContent === 'delayed!', { timeout: 4000 });
    check('Cmd.after fired the delayed message', await status(), 'delayed!');

    await page.evaluate(() => {
      globalThis.__qed.ports['echoOut'] = (p) => globalThis.__qed.send('echoIn', JSON.stringify(JSON.parse(p) + '-pong'));
    });
    await page.click('#app .ping');
    check('typed port round-trip (echoOut → JS → echoIn → onPort)', await status(), 'echo: ping-pong');

    await page.click('#app .search');
    await page.type('#app .search', 'abc', { delay: 15 });
    await page.waitForFunction(() => document.querySelector('#status')?.textContent === 'searched: abc', { timeout: 4000 });
    check('debounced search ran for the final query', await status(), 'searched: abc');
    check('afterKeyed cancelled the intermediate timers', await page.$eval('#searches', (e) => e.textContent), '1');

    await page.click('#app .save');
    check('batch updated the status', await status(), 'saved+titled');
    check('batch ran setTitle too', await page.title(), 'Saved!');

    await page.click('#app .focus');
    check('Cmd.focus focused the input', await page.evaluate(() => document.activeElement?.id), 'title-input');

    const [chooser] = await Promise.all([page.waitForFileChooser(), page.click('#app .pick')]);
    await chooser.accept([file]);
    await page.waitForFunction(() => document.querySelector('#status')?.textContent?.startsWith('file: '), { timeout: 4000 });
    check('Cmd.pickFile read the chosen file', await status(), 'file: qed-effects-pick.txt=hello-from-file');
  } finally {
    rmSync(tmpDir, { recursive: true, force: true });
  }
});
