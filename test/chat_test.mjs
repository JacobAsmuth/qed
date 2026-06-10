// chat_test.mjs — end-to-end screenshot test for the streaming LLM chat.
//
// Builds the chat web entry to .qed/dev, serves it behind a mock OpenAI backend
// (test/mock_llm.py), then drives the real app in headless Chromium: type, send,
// watch the reply stream in token by token. Saves a screenshot at each stage and
// asserts the DOM, so a regression fails loudly (not just a bad picture).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { cpSync, mkdirSync } from 'node:fs';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8124;
const SERVE = `${ROOT}.qed/dev`;
const SHOTS = `${ROOT}test/screenshots`;
const REPLY = 'Hello! I am a mock LLM, streaming this reply token by token.';

// 1. Build the chat app (dev mode, fast) with the chat web entry.
console.log('▸ building chat (Examples.ChatWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.ChatWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

mkdirSync(SHOTS, { recursive: true });

// 3. Mock LLM + static server.
const server = spawn('python3', [`${ROOT}test/mock_llm.py`, String(PORT), SERVE], { stdio: 'inherit' });
await sleep(900);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox'],
});

try {
  const page = await browser.newPage();
  await page.setViewport({ width: 480, height: 720, deviceScaleFactor: 2 });
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .composer', { timeout: 20000 });

  const shot = (n) => page.screenshot({ path: `${SHOTS}/${n}.png` });
  const msgCount = () => page.$$eval('#app .msg', (els) => els.length);
  const disabled = (sel) => page.$eval(sel, (b) => b.hasAttribute('disabled'));
  const draftVal = () => page.$eval('#app .draft', (i) => i.value);

  // --- empty state ---
  check('starts with no messages', await msgCount(), 0);
  check('send disabled when draft empty', await disabled('#app .send'), true);
  await shot('01-empty');

  // --- typing captures into the model (onInput) and enables send ---
  await page.focus('#app .draft');
  await page.type('#app .draft', 'Hello there');
  check('draft captured from input', await draftVal(), 'Hello there');
  check('send enabled after typing', await disabled('#app .send'), false);
  await shot('02-typed');

  // --- send: user bubble appears, draft clears, assistant bubble starts ---
  await page.click('#app .send');
  await page.waitForFunction(() => document.querySelectorAll('#app .msg').length >= 2, { timeout: 5000 });
  check('user + assistant bubbles present', await msgCount(), 2);
  check('user message text', await page.$eval('#app .msg.user', (e) => e.textContent.trim()), 'Hello there');
  check('draft cleared after send', await draftVal(), '');
  await sleep(150); // let a few streamed tokens land
  await shot('03-streaming');

  // --- stream completes: assistant bubble holds the full reply ---
  await page.waitForFunction(
    (full) => document.querySelector('#app .msg.bot')?.textContent.trim() === full,
    { timeout: 8000 }, REPLY);
  check('assistant streamed full reply', await page.$eval('#app .msg.bot', (e) => e.textContent.trim()), REPLY);
  await shot('04-complete');

  // --- a second turn works (conversation accumulates) ---
  // Type first, then wait for Send to re-enable: the reply's last chunk arrives
  // just before `.done` flips `pending`, so we must let the stream fully settle
  // (a disabled button would swallow the click).
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
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL CHAT CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
