// effects_test.mjs — end-to-end test for the native effect set + the port escape hatch.
//
// Builds the effects web entry to .qed/dev, serves it, and drives it in headless
// Chromium. It checks: localStorage persistence across a reload, document.title, the
// `after` timer, `randomInt`, the file picker (`pickFile` via a real file chooser),
// `batch` (two effects from one message), `focus`, and a full port round-trip (an
// app-registered JS handler echoes back through `__qed.send` → `onPort`).
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { writeFileSync } from 'node:fs';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8136;
const SERVE = `${ROOT}.qed/dev`;
const FILE = '/tmp/qed-effects-pick.txt';
writeFileSync(FILE, 'hello-from-file');

console.log('▸ building effects demo (Examples.EffectsWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.EffectsWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

const server = spawn('python3', [`${ROOT}runtime/serve.py`, String(PORT), SERVE], { stdio: 'inherit' });
await sleep(900);

let failures = 0;
const check = (label, got, want) => {
  const ok = JSON.stringify(got) === JSON.stringify(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'],
});

try {
  const page = await browser.newPage();
  page.on('console', (m) => console.log('  [page]', m.text()));
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });

  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#count', { timeout: 20000 });

  const count  = () => page.$eval('#count', (e) => e.textContent);
  const status = () => page.$eval('#status', (e) => e.textContent);
  const click  = async (sel) => { await page.click(`#app ${sel}`); await sleep(40); };

  // --- localStorage: start clean, then persist across a reload ---
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'load' });
  await page.waitForSelector('#count');
  check('count starts at 0 (clean storage)', await count(), '0');
  await click('.inc'); await click('.inc');                 // each inc persists to localStorage
  check('count is 2 after two increments', await count(), '2');
  await page.reload({ waitUntil: 'load' });
  await page.waitForSelector('#count');
  await sleep(60);                                          // startup storageGet resolves
  check('count persisted across reload (localStorage)', await count(), '2');

  // --- document.title ---
  await page.type('#title-input', 'Hello Qed');
  await click('.apply');
  check('Cmd.setTitle set the document title', await page.title(), 'Hello Qed');

  // --- randomInt in [1,6] ---
  await click('.roll');
  const rolled = parseInt((await status()).replace('rolled: ', ''), 10);
  check('Cmd.randomInt returned a d6', rolled >= 1 && rolled <= 6, true);

  // --- after (timer) ---
  await click('.delay');
  check('status shows waiting immediately', await status(), 'waiting…');
  await sleep(400);
  check('Cmd.after fired the delayed message', await status(), 'delayed!');

  // --- typed ports (ports macro): app JS echoes back on the inbound channel ---
  // payloads are JSON (echoOut sends "ping"), so the handler parses + re-stringifies.
  await page.evaluate(() => {
    globalThis.__qed.ports['echoOut'] = (p) => globalThis.__qed.send('echoIn', JSON.stringify(JSON.parse(p) + '-pong'));
  });
  await click('.ping');
  await sleep(40);
  check('typed port round-trip (echoOut → JS → echoIn → onPort)', await status(), 'echo: ping-pong');

  // --- debounce via afterKeyed: type fast, only the last keystroke's timer fires ---
  await page.click('#app .search');
  await page.type('#app .search', 'abc', { delay: 25 });
  await sleep(350);                                         // > the 200ms keyed timer
  check('debounced search ran for the final query', await status(), 'searched: abc');
  check('afterKeyed cancelled the intermediate timers', await page.$eval('#searches', (e) => e.textContent), '1');

  // --- batch: one message, two effects (storageSet + setTitle) ---
  await click('.save');
  check('batch updated the status', await status(), 'saved+titled');
  check('batch ran setTitle too', await page.title(), 'Saved!');

  // --- focus by element id ---
  await click('.focus');
  check('Cmd.focus focused the input', await page.evaluate(() => document.activeElement?.id), 'title-input');

  // --- file pick via a real file chooser ---
  const [chooser] = await Promise.all([page.waitForFileChooser(), click('.pick')]);
  await chooser.accept([FILE]);
  await sleep(80);
  check('Cmd.pickFile read the chosen file', await status(), 'file: qed-effects-pick.txt=hello-from-file');
} finally {
  await browser.close();
  server.kill('SIGTERM');
}

console.log(failures === 0 ? '\nALL EFFECTS CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
