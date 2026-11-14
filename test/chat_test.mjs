import { mkdirSync } from 'node:fs';
import path from 'node:path';
import { ROOT, withBrowser, sleep } from './harness.mjs';

const SHOTS = path.join(ROOT, 'test', 'screenshots');
const REPLY = 'Hello! I am a mock LLM, streaming this reply token by token.';
mkdirSync(SHOTS, { recursive: true });

await withBrowser('CHAT', {
  webRoot: 'Examples.ChatWeb',
  routes: async (req, res, url) => {
    if (req.method !== 'POST' || url.pathname.replace(/\/$/, '') !== '/v1/chat/completions') return false;
    for await (const _ of req) { /* drain */ }
    res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-store', 'Connection': 'close' });
    const emit = (obj) => res.write(`data: ${JSON.stringify(obj)}\n\n`);
    for (const tok of REPLY.match(/\S+\s*/g)) {
      emit({ choices: [{ delta: { content: tok } }] });
      await sleep(30);
    }
    emit({ choices: [{ delta: {}, finish_reason: 'stop' }] });
    res.end('data: [DONE]\n\n');
    return true;
  },
}, async ({ page, check, baseUrl }) => {
  await page.setViewport({ width: 480, height: 720, deviceScaleFactor: 2 });
  await page.goto(`${baseUrl}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .composer', { timeout: 20000 });

  const shot = (n) => page.screenshot({ path: path.join(SHOTS, `${n}.png`) });
  const msgCount = () => page.$$eval('#app .msg', (els) => els.length);
  const disabled = (sel) => page.$eval(sel, (b) => b.hasAttribute('disabled'));
  const draftVal = () => page.$eval('#app .draft', (i) => i.value);

  check('starts with no messages', await msgCount(), 0);
  check('send disabled when draft empty', await disabled('#app .send'), true);
  await shot('01-empty');

  await page.focus('#app .draft');
  await page.type('#app .draft', 'Hello there');
  check('draft captured from input', await draftVal(), 'Hello there');
  check('send enabled after typing', await disabled('#app .send'), false);
  await shot('02-typed');

  await page.click('#app .send');
  await page.waitForFunction(() => document.querySelectorAll('#app .msg').length >= 2, { timeout: 5000 });
  check('user + assistant bubbles present', await msgCount(), 2);
  check('user message text', await page.$eval('#app .msg.user', (e) => e.textContent.trim()), 'Hello there');
  check('draft cleared after send', await draftVal(), '');
  await sleep(150);
  await shot('03-streaming');

  await page.waitForFunction(
    (full) => document.querySelector('#app .msg.bot')?.textContent.trim() === full,
    { timeout: 8000 }, REPLY);
  check('assistant streamed full reply', await page.$eval('#app .msg.bot', (e) => e.textContent.trim()), REPLY);
  await shot('04-complete');

  await page.focus('#app .draft');
  await page.type('#app .draft', 'Thanks');
  await page.waitForFunction(() => !document.querySelector('#app .send').hasAttribute('disabled'), { timeout: 8000 });
  await page.click('#app .send');
  await page.waitForFunction(() => document.querySelectorAll('#app .msg').length >= 4, { timeout: 5000 });
  check('four bubbles after second turn', await msgCount(), 4);
  await page.waitForFunction(
    (full) => [...document.querySelectorAll('#app .msg.bot')].every((b) => b.textContent.trim() === full),
    { timeout: 8000 }, REPLY);
  await shot('05-second-turn');
});
