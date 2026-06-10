// bench_template.mjs — fine-grained template vs the verified diff, head to head.
//
// The same app (`BenchScalar`: 2000 bound values, one changes per update) is built two
// ways — as a `View` template (fine-grained: walk the static bindings, patch the one
// changed DOM node) and through the diff path (rebuild + diff the 2000-node tree each
// update). We time `update` (median of N) in the same headless browser. Same DOM result,
// so the gap is the cost the template removes: building and diffing the tree.
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const ROOT = new URL('..', import.meta.url).pathname;
const REPS = 30;
const median = (xs) => { xs = xs.slice().sort((a, b) => a - b); return xs[Math.floor(xs.length / 2)]; };
const fmt = (ms) => (ms < 10 ? ms.toFixed(3) : ms.toFixed(1));

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });

async function measure(root, port) {
  console.log(`▸ building ${root} → .qed/dev …`);
  if (spawnSync('bash', ['-lc', `cd '${ROOT}' && QED_WEB_ROOT=${root} ./qed build --dev`], { stdio: 'inherit' }).status !== 0) {
    console.error('build failed'); process.exit(1);
  }
  const server = spawn('python3', ['-m', 'http.server', String(port), '--directory', `${ROOT}.qed/dev`], { stdio: 'ignore' });
  await sleep(900);
  try {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log('  [pageerror]', e.message));
    await page.goto(`http://localhost:${port}/index.html`, { waitUntil: 'load' });
    await page.waitForFunction(() => window.qed && typeof window.qed.dispatch === 'function', { timeout: 20000 });
    const t = () => page.evaluate(() => { const t0 = performance.now(); window.qed.dispatch(0); return performance.now() - t0; });
    await t(); await t();                              // warm
    const xs = [];
    for (let k = 0; k < REPS; k++) xs.push(await t());
    await page.close();
    return median(xs);
  } finally {
    server.kill('SIGTERM');
    await sleep(200);
  }
}

const sTempl = await measure('Examples.Bench.ScalarWeb', 8150);
const sDiff  = await measure('Examples.Bench.ScalarDiffWeb', 8151);
const lTempl = await measure('Examples.Bench.ListWeb', 8152);
const lDiff  = await measure('Examples.Bench.ListDiffWeb', 8153);
await browser.close();

console.log(`\n  median of ${REPS} updates (ms)\n`);
console.log('  scalar — 2000 bound values, 1 changed per update');
console.log(`    diff path (rebuild + diff 2000 nodes) : ${fmt(sDiff)}`);
console.log(`    View template (fine-grained)          : ${fmt(sTempl)}   (${(sDiff / sTempl).toFixed(1)}×)`);
console.log('\n  list — 10,000 keyed rows, every 10th text changed (keys unchanged)');
console.log(`    diff path (rebuild + diff + childAt)  : ${fmt(lDiff)}`);
console.log(`    View template (forEach → signals)     : ${fmt(lTempl)}   (${(lDiff / lTempl).toFixed(1)}×)\n`);
process.exit(0);
