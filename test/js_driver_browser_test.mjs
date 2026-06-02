// The FULL driver, transpiled from Lean (no WASM): counter mounts and runs.
import { spawn } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';
const PORT = 8137;
const DIR = new URL('../dist-js', import.meta.url).pathname;
const server = spawn('python3', ['-m', 'http.server', String(PORT), '--directory', DIR], { stdio: 'ignore' });
await sleep(700);
let failures = 0;
const check = (l, got, want) => { const ok = String(got) === String(want); console.log(`${ok?'PASS':'FAIL'}  ${l}: ${JSON.stringify(got)}`); if (!ok) failures++; };
const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
try {
  const page = await browser.newPage();
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });
  page.on('console', (m) => { if (m.type() === 'error') console.log('  [page error]', m.text()); });
  await page.goto(`http://localhost:${PORT}/index.html`, { waitUntil: 'load' });
  await page.waitForSelector('#app .count', { timeout: 15000 });
  const count = () => page.$eval('#app .count', (el) => el.textContent.trim());
  const clickBtn = (label) => page.evaluate((lab) => { [...document.querySelectorAll('#app button')].find((x) => x.textContent.trim() === lab).click(); }, label);
  check('initial', await count(), '0');
  await clickBtn('+'); await clickBtn('+'); await sleep(20);
  check('after + +', await count(), '2');
  await clickBtn('−'); await sleep(20);
  check('after -', await count(), '1');
  await clickBtn('−'); await clickBtn('−'); await clickBtn('−'); await sleep(20);
  check('decrement guarded >= 0 (counterSafe)', await count(), '0');
  await page.focus('#app input'); await page.keyboard.type('hello');
  await clickBtn('+'); await sleep(20);
  check('count after + while typing', await count(), '1');
  check('input keeps value (verified diff)', await page.$eval('#app input', (e) => e.value), 'hello');
  check('input keeps focus', await page.evaluate(() => document.activeElement.tagName), 'INPUT');
  await clickBtn('reset'); await sleep(20);
  check('after reset', await count(), '0');
} finally { await browser.close(); server.kill(); }
console.log(failures ? `\n${failures} FAILURES` : '\nTranspiled DRIVER counter: ALL PASS (entire driver is transpiled Lean, no WASM)');
process.exit(failures ? 1 : 0);
