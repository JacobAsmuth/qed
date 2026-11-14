import puppeteer from 'puppeteer';
import { buildDev, serve } from './harness.mjs';

const REPS = 30;
const median = (xs) => { xs = xs.slice().sort((a, b) => a - b); return xs[Math.floor(xs.length / 2)]; };
const fmt = (ms) => (ms < 10 ? ms.toFixed(3) : ms.toFixed(1));

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });

async function measure(webRoot) {
  buildDev(webRoot);
  const srv = await serve();
  try {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log('  [pageerror]', e.message));
    await page.goto(`${srv.baseUrl}/index.html`, { waitUntil: 'load' });
    await page.waitForFunction(() => window.qed && typeof window.qed.dispatch === 'function', { timeout: 20000 });
    const t = () => page.evaluate(() => { const t0 = performance.now(); window.qed.dispatch(0); return performance.now() - t0; });
    await t(); await t();
    const xs = [];
    for (let k = 0; k < REPS; k++) xs.push(await t());
    await page.close();
    return median(xs);
  } finally {
    await srv.close();
  }
}

try {
  const sTempl = await measure('Examples.Bench.ScalarWeb');
  const sDiff  = await measure('Examples.Bench.ScalarDiffWeb');
  const lTempl = await measure('Examples.Bench.ListWeb');
  const lDiff  = await measure('Examples.Bench.ListDiffWeb');

  console.log(`\n  median of ${REPS} updates (ms)\n`);
  console.log('  scalar — 2000 bound values, 1 changed per update');
  console.log(`    diff path (rebuild + diff 2000 nodes) : ${fmt(sDiff)}`);
  console.log(`    View template (fine-grained)          : ${fmt(sTempl)}   (${(sDiff / sTempl).toFixed(1)}×)`);
  console.log('\n  list — 10,000 keyed rows, every 10th text changed (keys unchanged)');
  console.log(`    diff path (rebuild + diff + childAt)  : ${fmt(lDiff)}`);
  console.log(`    View template (forEach → signals)     : ${fmt(lTempl)}   (${(lDiff / lTempl).toFixed(1)}×)\n`);
} finally {
  await browser.close();
}
