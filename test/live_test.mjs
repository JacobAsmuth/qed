// live_test.mjs — a handler message that embeds model state must stay current across updates.
//
// Builds the live-handler demo, serves it, and drives it in headless Chromium. The "double"
// and "+10" buttons carry `onClick (.setTo (m.n * 2))` / `(.setTo (m.n + 10))` — messages that
// read the model. If the driver baked the build-time value (n = 0) into the handler, "double"
// would always set 0 and "+10" always 10. We assert they reflect the *current* number.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const PORT = 8139;
const SERVE = `${ROOT}.qed/dev`;

console.log('▸ building live demo (Examples.LiveWeb → .qed/dev)…');
const build = spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.LiveWeb ./qed build --dev`],
  { stdio: 'inherit' });
if (build.status !== 0) { console.error('build failed'); process.exit(1); }

const server = spawn('python3', [`${ROOT}runtime/serve.py`, String(PORT), SERVE], { stdio: 'inherit' });
await sleep(900);

let failures = 0;
const check = (label, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${label}: got ${JSON.stringify(got)}${ok ? '' : `, want ${JSON.stringify(want)}`}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'],
});

try {
  const page = await browser.newPage();
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });
  const n = () => page.$eval('#app .live .n', (e) => e.textContent.trim());

  await page.goto(`http://localhost:${PORT}/`, { waitUntil: 'load' });
  await page.waitForSelector('#app .live .n', { timeout: 20000 });
  check('starts at 0', await n(), '0');

  for (let i = 0; i < 3; i++) await page.click('#app .inc');
  await sleep(30);
  check('three +1 clicks → 3', await n(), '3');

  // double reads the current n (3) → 6, not the baked-in 0
  await page.click('#app .double');
  await sleep(30);
  check('double reflects the current number (fresh handler)', await n(), '6');

  // +10 reads the current n (6) → 16, not 10
  await page.click('#app .plus10');
  await sleep(30);
  check('+10 reflects the current number (fresh handler)', await n(), '16');

  // double again → 32, proving the handler keeps tracking after several updates
  await page.click('#app .double');
  await sleep(30);
  check('double again tracks the latest number', await n(), '32');
} finally {
  await browser.close();
  server.kill();
}

console.log(failures === 0 ? '\nALL LIVE CHECKS PASSED ✅' : `\n${failures} CHECK(S) FAILED ❌`);
process.exit(failures === 0 ? 0 : 1);
