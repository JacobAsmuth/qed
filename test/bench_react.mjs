// bench_react.mjs — a fair, in-browser head-to-head: Qed (WASM) vs React (production).
//
// Both render an identical keyed list (`ul#list > li[key] > [span,span]`, 10k rows) and
// run the identical operations. For each op we measure the SYNCHRONOUS framework cost —
// `performance.now()` around `window.qed.dispatch` (Qed runs update+diff+patch inline)
// and around `flushSync(setState)` (React commits inline) — i.e. reconcile + DOM
// mutation, excluding the browser layout/paint that follows (equal for both, since the
// resulting DOM is identical). Reports the median of N runs.
//
// Honest caveats: Qed is WebAssembly with an FFI call per DOM mutation (overhead React's
// native JS doesn't pay); React is the production build, keyed, functional components.
// The `react?memo` column is React.memo'd rows — the counterpart to Qed's `Html.lazy`.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import { existsSync } from 'node:fs';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const QPORT = 8140, RPORT = 8141;
const REPS = 15;

// ensure React is vendored (so the benchmark is reproducible offline once fetched)
for (const [f, url] of [
  ['react.production.min.js', 'https://unpkg.com/react@18.3.1/umd/react.production.min.js'],
  ['react-dom.production.min.js', 'https://unpkg.com/react-dom@18.3.1/umd/react-dom.production.min.js'],
]) {
  if (!existsSync(`${ROOT}test/vendor/${f}`)) {
    spawnSync('bash', ['-lc', `mkdir -p '${ROOT}test/vendor' && curl -sSL -m 40 -o '${ROOT}test/vendor/${f}' '${url}'`], { stdio: 'inherit' });
  }
}

console.log('▸ building Qed bench app (Examples.BenchAppWeb → .qed/dev)…');
if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=Examples.BenchAppWeb ./qed build --dev`], { stdio: 'inherit' }).status !== 0) {
  console.error('build failed'); process.exit(1);
}

const qServer = spawn('python3', ['-m', 'http.server', String(QPORT), '--directory', `${ROOT}.qed/dev`], { stdio: 'inherit' });
const rServer = spawn('python3', ['-m', 'http.server', String(RPORT), '--directory', `${ROOT}test`], { stdio: 'ignore' });
await sleep(1000);

const median = (xs) => { xs = xs.slice().sort((a, b) => a - b); return xs[Math.floor(xs.length / 2)]; };
const fmt = (ms) => (ms < 10 ? ms.toFixed(2) : ms.toFixed(1)).padStart(7);

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox', '--enable-features=SharedArrayBuffer'] });

// time `timeFn` (returns ms) `reps` times → median; `prepFn` (optional) runs untimed first
async function bench(timeFn, reps, prepFn) {
  if (prepFn) await prepFn();
  await timeFn();                          // warm
  const xs = [];
  for (let k = 0; k < reps; k++) { if (prepFn) await prepFn(); xs.push(await timeFn()); }
  return median(xs);
}

const results = {};
try {
  // ---- Qed: ops are dispatch ids (op buttons render first) ----
  {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log('  [qed pageerror]', e.message));
    await page.goto(`http://localhost:${QPORT}/index.html`, { waitUntil: 'load' });
    await page.waitForFunction(() => window.qed && typeof window.qed.dispatch === 'function', { timeout: 20000 });
    const t = (id) => page.evaluate((i) => { const t0 = performance.now(); window.qed.dispatch(i); return performance.now() - t0; }, id);
    results.qed = {
      create:  await bench(() => t(0), REPS, () => t(4)),   // clear, then time create
      update:  await bench(() => t(1), REPS, null),
      swap:    await bench(() => t(2), REPS, null),
      reverse: await bench(() => t(3), REPS, null),
    };
    // lazy rows: toggle on (id 5), re-create, then time update again
    await page.evaluate(() => window.qed.dispatch(5));
    await page.evaluate(() => window.qed.dispatch(0));
    results['qed-lazy'] = { update: await bench(() => t(1), REPS, null) };
    // signal rows: toggle on (id 6), re-create, seed signals, then time update via
    // setSignal — no message, no diff, just the bound DOM nodes.
    await page.evaluate(() => window.qed.dispatch(6));
    await page.evaluate(() => window.qed.dispatch(0));
    await page.evaluate(() => { for (let i = 1; i <= 10000; i++) window.qed.setSignal('r' + i, 'item ' + i); });
    const sigUpdate = () => page.evaluate(() => {
      window.__tick = (window.__tick || 0) + 1;
      const t0 = performance.now();
      for (let i = 1; i <= 10000; i += 10) window.qed.setSignal('r' + i, 'item ' + i + ' ' + window.__tick);
      return performance.now() - t0;
    });
    results['qed-signal'] = { update: await bench(sigUpdate, REPS, null) };
    await page.close();
  }
  // ---- React (plain, then memo) ----
  for (const variant of ['plain', 'memo']) {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log(`  [react ${variant} pageerror]`, e.message));
    await page.goto(`http://localhost:${RPORT}/react_bench.html${variant === 'memo' ? '?memo' : ''}`, { waitUntil: 'load' });
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
  qServer.kill('SIGTERM'); rServer.kill('SIGTERM');
}

const ops = ['create', 'update', 'swap', 'reverse'];
const cols = [['qed', 'Qed (wasm)'], ['react-plain', 'React'], ['react-memo', 'React.memo']];
console.log(`\n  10,000-row keyed list — median of ${REPS} runs, synchronous reconcile+patch (ms)\n`);
console.log('  op'.padEnd(12) + cols.map(([, h]) => h.padStart(13)).join(''));
for (const op of ops) {
  console.log('  ' + op.padEnd(10) + cols.map(([k]) => fmt(results[k][op]).padStart(13)).join(''));
}
console.log('  ' + 'update+lazy'.padEnd(10) + fmt(results['qed-lazy'].update).padStart(13) +
  '       (Qed lazy rows)');
console.log('  ' + 'update+sig'.padEnd(10) + fmt(results['qed-signal'].update).padStart(13) +
  '       (Qed signals — fine-grained, no diff; React.memo is ' + fmt(results['react-memo'].update).trim() + ')');
console.log('');
console.log(JSON.stringify(results));
process.exit(0);
