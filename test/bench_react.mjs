import { spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import path from 'node:path';
import puppeteer from 'puppeteer';
import { ROOT, buildDev, serve } from './harness.mjs';

const REPS = 15;
const median = (xs) => { xs = xs.slice().sort((a, b) => a - b); return xs[Math.floor(xs.length / 2)]; };
const fmt = (ms) => (ms < 10 ? ms.toFixed(2) : ms.toFixed(1)).padStart(7);

for (const [f, url] of [
  ['react.production.min.js', 'https://unpkg.com/react@18.3.1/umd/react.production.min.js'],
  ['react-dom.production.min.js', 'https://unpkg.com/react-dom@18.3.1/umd/react-dom.production.min.js'],
]) {
  const dest = path.join(ROOT, 'test', 'vendor', f);
  if (!existsSync(dest)) {
    spawnSync('bash', ['-lc', `mkdir -p '${path.dirname(dest)}' && curl -sSL -m 40 -o '${dest}' '${url}'`], { stdio: 'inherit' });
  }
}

buildDev('Examples.Bench.AppWeb');
const qSrv = await serve();
const rSrv = await serve({ dir: path.join(ROOT, 'test'), spa: false });
const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });

async function bench(timeFn, reps, prepFn) {
  if (prepFn) await prepFn();
  await timeFn();
  const xs = [];
  for (let k = 0; k < reps; k++) { if (prepFn) await prepFn(); xs.push(await timeFn()); }
  return median(xs);
}

const results = {};
try {
  {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log('  [qed pageerror]', e.message));
    await page.goto(`${qSrv.baseUrl}/index.html`, { waitUntil: 'load' });
    await page.waitForFunction(() => window.qed && typeof window.qed.dispatch === 'function', { timeout: 20000 });
    const t = (id) => page.evaluate((i) => { const t0 = performance.now(); window.qed.dispatch(i); return performance.now() - t0; }, id);
    results.qed = {
      create:  await bench(() => t(0), REPS, () => t(4)),
      update:  await bench(() => t(1), REPS, null),
      swap:    await bench(() => t(2), REPS, null),
      reverse: await bench(() => t(3), REPS, null),
    };
    await page.close();
  }
  for (const variant of ['plain', 'memo']) {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log(`  [react ${variant} pageerror]`, e.message));
    await page.goto(`${rSrv.baseUrl}/react_bench.html${variant === 'memo' ? '?memo' : ''}`, { waitUntil: 'load' });
    await page.waitForFunction(() => window.__bench && window.__bench.ready, { timeout: 20000 });
    const t = (op) => page.evaluate((o) => { const t0 = performance.now(); window.__bench[o](); return performance.now() - t0; }, op);
    results[`react-${variant}`] = {
      create:  await bench(() => t('create'), REPS, () => t('clear')),
      update:  await bench(() => t('update'), REPS, null),
      swap:    await bench(() => t('swap'), REPS, null),
      reverse: await bench(() => t('reverse'), REPS, null),
    };
    await page.close();
  }
} finally {
  await browser.close();
  await qSrv.close();
  await rSrv.close();
}

const ops = ['create', 'update', 'swap', 'reverse'];
const cols = [['qed', 'Qed (js)  '], ['react-plain', 'React'], ['react-memo', 'React.memo']];
console.log(`\n  10,000-row keyed list — median of ${REPS} runs, synchronous reconcile+patch (ms)\n`);
console.log('  op'.padEnd(12) + cols.map(([, h]) => h.padStart(13)).join(''));
for (const op of ops) {
  console.log('  ' + op.padEnd(10) + cols.map(([k]) => fmt(results[k][op]).padStart(13)).join(''));
}
console.log('\n' + JSON.stringify(results));
