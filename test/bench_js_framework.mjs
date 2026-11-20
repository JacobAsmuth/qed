/**
 * Faithful js-framework-benchmark (Stefan Krause) harness for Qed.
 *
 * Measures all 9 standard keyed-table operations end-to-end via Chrome DevTools
 * Trace (`EventDispatch` click → end of `Paint`), verifies DOM correctness and
 * true keyed `<tr>` node identity on swap, and reports median ms, slowdown vs.
 * VanillaJS (1.00×), geometric mean, and gzipped client bundle size.
 *
 * Usage:
 *   node test/bench_js_framework.mjs
 *   REPS=9 node test/bench_js_framework.mjs
 */
import { spawnSync } from 'node:child_process';
import { existsSync, readdirSync, readFileSync, rmSync } from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import puppeteer from 'puppeteer';
import { ROOT, serve, withElanPath } from './harness.mjs';

const REPS = Math.max(3, Number(process.env.REPS || 11));
const REPS_10K = Math.max(3, Math.min(REPS, 5));
const DIST = path.join(ROOT, 'dist');

const VENDOR = [
  ['react.production.min.js', 'https://unpkg.com/react@18.3.1/umd/react.production.min.js'],
  ['react-dom.production.min.js', 'https://unpkg.com/react-dom@18.3.1/umd/react-dom.production.min.js'],
  ['vue.global.prod.js', 'https://unpkg.com/vue@3.5.13/dist/vue.global.prod.js'],
];

for (const [f, url] of VENDOR) {
  const dest = path.join(ROOT, 'test', 'vendor', f);
  if (!existsSync(dest)) {
    const r = spawnSync('bash', ['-lc', `mkdir -p '${path.dirname(dest)}' && curl -sSL -m 40 -o '${dest}' '${url}'`], { stdio: 'inherit' });
    if (r.status !== 0) throw new Error(`failed to download ${url}`);
  }
}

// Production build of Bench.AppWeb (minified JS + hashed prod assets)
{
  const qedBin = existsSync(path.join(ROOT, '.lake', 'build', 'bin', 'qed'))
    ? path.join(ROOT, '.lake', 'build', 'bin', 'qed')
    : './scripts/qed';
  const r = spawnSync(qedBin, ['build'], {
    cwd: ROOT,
    env: { ...withElanPath(), QED_HOME: ROOT, QED_WEB_ROOT: 'Bench.AppWeb' },
    encoding: 'utf8',
  });
  if (r.status !== 0) {
    process.stderr.write((r.stdout || '') + (r.stderr || ''));
    process.exit(1);
  }
}

// Measure gzipped client bundle sizes (KB)
const gzipKb = (files) => {
  let bytes = 0;
  for (const f of files) bytes += zlib.gzipSync(readFileSync(f)).length;
  return bytes / 1024;
};
const qedClientFiles = readdirSync(DIST)
  .filter((f) => f.endsWith('.mjs') && !f.startsWith('ssr'))
  .map((f) => path.join(DIST, f));
const bundleKb = {
  vanilla: 0,
  qed: gzipKb(qedClientFiles),
  vue: gzipKb([path.join(ROOT, 'test', 'vendor', 'vue.global.prod.js')]),
  react: gzipKb([
    path.join(ROOT, 'test', 'vendor', 'react.production.min.js'),
    path.join(ROOT, 'test', 'vendor', 'react-dom.production.min.js'),
  ]),
  'react-memo': gzipKb([
    path.join(ROOT, 'test', 'vendor', 'react.production.min.js'),
    path.join(ROOT, 'test', 'vendor', 'react-dom.production.min.js'),
  ]),
};

// Lightweight Bootstrap-equivalent stylesheet matching Krause's table/button layout.
const BENCH_CSS = `
  body { margin: 0; font-family: system-ui, -apple-system, sans-serif; font-size: 14px; }
  .container { max-width: 1170px; margin: 0 auto; padding: 0 15px; }
  .jumbotron { padding: 24px 32px; margin-bottom: 20px; background: #eee; border-radius: 6px; }
  .row { display: flex; flex-wrap: wrap; }
  .col-md-6 { width: 50%; box-sizing: border-box; }
  .col-sm-6 { width: 50%; box-sizing: border-box; padding: 5px; }
  .btn { display: block; width: 100%; padding: 8px 12px; background: #337ab7; color: #fff; border: 0; border-radius: 4px; cursor: pointer; }
  table.table { width: 100%; border-collapse: collapse; }
  table.table td { padding: 8px; border-top: 1px solid #ddd; line-height: 1.4; }
  table.table-striped > tbody > tr:nth-of-type(odd) { background: #f9f9f9; }
  table.table > tbody > tr.danger > td { background: #f2dede; }
  .col-md-1 { width: 8.33%; }
  .col-md-4 { width: 33.33%; }
  .col-md-6 { width: 50%; }
  a { color: #337ab7; cursor: pointer; }
  .glyphicon-remove::before { content: "×"; }
`;

const median = (xs) => {
  const s = xs.slice().sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
};
const geomean = (xs) => Math.exp(xs.reduce((a, x) => a + Math.log(x), 0) / xs.length);

// Sum non-overlapping main-thread work intervals from click through final paint
// (matching js-framework-benchmark's CPU duration without headless 60Hz vsync idle gaps).
const WORK_EVENTS = new Set([
  'EventDispatch', 'FunctionCall', 'RunMicrotasks', 'TimerFire',
  'FireAnimationFrame', 'UpdateLayoutTree', 'Layout', 'PrePaint', 'Paint',
  'MajorGC', 'MinorGC',
]);

async function measureClick(page, selector) {
  await page.tracing.start({ categories: ['devtools.timeline'] });
  await page.click(selector);
  await page.evaluate(() => new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r))));
  const raw = await page.tracing.stop();
  const events = JSON.parse(Buffer.from(raw).toString('utf8')).traceEvents;
  const click = events.find((e) => e.name === 'EventDispatch' && e.args?.data?.type === 'click');
  if (!click) throw new Error(`no click EventDispatch in trace for ${selector}`);
  const tid = click.tid;
  let lastPaintEnd = click.ts + (click.dur || 0);
  for (const e of events) {
    if (e.tid === tid && e.ts >= click.ts && (e.name === 'Paint' || e.name === 'Layout' || e.name === 'UpdateLayoutTree')) {
      const end = e.ts + (e.dur || 0);
      if (end > lastPaintEnd) lastPaintEnd = end;
    }
  }
  const spans = [];
  for (const e of events) {
    if (e.tid !== tid || e.ph !== 'X' || !e.dur || e.ts < click.ts || e.ts > lastPaintEnd) continue;
    if (WORK_EVENTS.has(e.name)) spans.push([e.ts, Math.min(e.ts + e.dur, lastPaintEnd)]);
  }
  spans.sort((a, b) => a[0] - b[0]);
  let totalUs = 0, curS = -1, curE = -1;
  for (const [s, e] of spans) {
    if (s > curE) {
      if (curE > curS) totalUs += curE - curS;
      curS = s; curE = e;
    } else if (e > curE) {
      curE = e;
    }
  }
  if (curE > curS) totalUs += curE - curS;
  return totalUs / 1000;
}

async function clickQuiet(page, selector) {
  await page.evaluate((sel) => document.querySelector(sel).click(), selector);
  await page.evaluate(() => new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r))));
}

async function runBench(page, { setup, selector, verify, warmup = 2, reps = REPS }) {
  for (let w = 0; w < warmup; w++) {
    if (setup) await setup();
    await clickQuiet(page, selector);
  }
  const times = [];
  for (let k = 0; k < reps; k++) {
    if (setup) await setup();
    const ms = await measureClick(page, selector);
    if (k === 0 && verify) await verify();
    times.push(ms);
  }
  return median(times);
}

async function verifyKeyedSwap(page, label) {
  await clickQuiet(page, '#clear');
  await clickQuiet(page, '#run');
  await page.evaluate(() => {
    const rows = document.querySelectorAll('#tbody > tr');
    window.__tr1 = rows[1];
    window.__tr998 = rows[998];
    window.__id1 = rows[1].firstElementChild.textContent.trim();
    window.__id998 = rows[998].firstElementChild.textContent.trim();
  });
  await clickQuiet(page, '#swaprows');
  const check = await page.evaluate(() => {
    const rows = document.querySelectorAll('#tbody > tr');
    return {
      len: rows.length,
      sameNode1: rows[1] === window.__tr998,
      sameNode998: rows[998] === window.__tr1,
      textOk: rows[1].firstElementChild.textContent.trim() === window.__id998 &&
              rows[998].firstElementChild.textContent.trim() === window.__id1,
    };
  });
  if (check.len !== 1000 || !check.sameNode1 || !check.sameNode998 || !check.textOk) {
    throw new Error(`[${label}] keyed swap verification failed: ${JSON.stringify(check)}`);
  }
}

async function benchmarkFramework(browser, fwKey, url, readyFn) {
  const page = await browser.newPage();
  page.setViewport({ width: 1280, height: 900 });
  page.on('pageerror', (e) => { throw new Error(`[${fwKey} pageerror] ${e.message}`); });
  await page.goto(url, { waitUntil: 'load' });
  await page.waitForFunction(readyFn, { timeout: 20000 });
  await page.addStyleTag({ content: BENCH_CSS });

  // Verify true keyed DOM node movement before timing
  await verifyKeyedSwap(page, fwKey);

  const rowCount = () => page.evaluate(() => document.querySelectorAll('#tbody > tr').length);
  const assertEq = async (got, want, msg) => {
    if (got !== want) throw new Error(`[${fwKey}] ${msg}: got ${got}, want ${want}`);
  };

  const out = {};

  // 01_run1k: create 1,000 rows from empty
  out['01_run1k'] = await runBench(page, {
    setup: () => clickQuiet(page, '#clear'),
    selector: '#run',
    verify: async () => assertEq(await rowCount(), 1000, '01_run1k count'),
  });

  // 02_replace1k: replace all 1,000 rows with 1,000 new rows
  await clickQuiet(page, '#clear');
  await clickQuiet(page, '#run');
  let prevFirstId = await page.evaluate(() => document.querySelector('#tbody > tr > td').textContent.trim());
  out['02_replace1k'] = await runBench(page, {
    selector: '#run',
    verify: async () => {
      await assertEq(await rowCount(), 1000, '02_replace1k count');
      const nowId = await page.evaluate(() => document.querySelector('#tbody > tr > td').textContent.trim());
      if (nowId === prevFirstId) throw new Error(`[${fwKey}] 02_replace1k did not replace IDs`);
      prevFirstId = nowId;
    },
  });

  // 03_update10th1k: update every 10th row of 1,000 rows
  await clickQuiet(page, '#clear');
  await clickQuiet(page, '#run');
  out['03_update10th1k'] = await runBench(page, {
    selector: '#update',
    verify: async () => {
      const ok = await page.evaluate(() => {
        const trs = document.querySelectorAll('#tbody > tr');
        return trs[0].children[1].textContent.endsWith(' !!!') &&
               !trs[1].children[1].textContent.endsWith(' !!!') &&
               trs[10].children[1].textContent.endsWith(' !!!');
      });
      if (!ok) throw new Error(`[${fwKey}] 03_update10th1k text check failed`);
    },
  });

  // 04_select1k: select a row in 1,000 rows (always select row 5 in setup so clicking row 2 changes state)
  await clickQuiet(page, '#clear');
  await clickQuiet(page, '#run');
  out['04_select1k'] = await runBench(page, {
    setup: () => clickQuiet(page, '#tbody > tr:nth-child(5) > td:nth-child(2) > a'),
    selector: '#tbody > tr:nth-child(2) > td:nth-child(2) > a',
    verify: async () => {
      const cls = await page.evaluate(() => document.querySelector('#tbody > tr:nth-child(2)').className);
      if (!cls.includes('danger')) throw new Error(`[${fwKey}] 04_select1k missing danger class`);
    },
  });

  // 05_swap1k: swap rows 2 & 999 in 1,000 rows
  await clickQuiet(page, '#clear');
  await clickQuiet(page, '#run');
  out['05_swap1k'] = await runBench(page, {
    selector: '#swaprows',
    verify: async () => assertEq(await rowCount(), 1000, '05_swap1k count'),
  });

  // 06_remove: remove one row from 1,000 rows
  out['06_remove'] = await runBench(page, {
    setup: async () => { await clickQuiet(page, '#clear'); await clickQuiet(page, '#run'); },
    selector: '#tbody > tr:nth-child(2) > td:nth-child(3) > a',
    verify: async () => assertEq(await rowCount(), 999, '06_remove count'),
  });

  // 07_create10k: create 10,000 rows from empty
  out['07_create10k'] = await runBench(page, {
    setup: () => clickQuiet(page, '#clear'),
    selector: '#runlots',
    warmup: 1,
    reps: REPS_10K,
    verify: async () => assertEq(await rowCount(), 10000, '07_create10k count'),
  });

  // 08_append1k: append 1,000 rows onto 1,000 rows
  out['08_append1k'] = await runBench(page, {
    setup: async () => { await clickQuiet(page, '#clear'); await clickQuiet(page, '#run'); },
    selector: '#add',
    verify: async () => assertEq(await rowCount(), 2000, '08_append1k count'),
  });

  // 09_clear1k: clear 1,000 rows
  out['09_clear1k'] = await runBench(page, {
    setup: async () => { await clickQuiet(page, '#clear'); await clickQuiet(page, '#run'); },
    selector: '#clear',
    verify: async () => assertEq(await rowCount(), 0, '09_clear1k count'),
  });

  await page.close();
  return out;
}

const OPS = [
  ['01_run1k',        'create 1,000 rows'],
  ['02_replace1k',    'replace 1,000 rows'],
  ['03_update10th1k', 'partial update (10th)'],
  ['04_select1k',     'select row'],
  ['05_swap1k',       'swap rows'],
  ['06_remove',       'remove row'],
  ['07_create10k',    'create 10,000 rows'],
  ['08_append1k',     'append 1,000 rows'],
  ['09_clear1k',      'clear 1,000 rows'],
];

const FRAMEWORKS = [
  { key: 'vanilla',    label: 'VanillaJS',  url: (base) => `${base}/js_framework_bench.html?fw=vanilla`,    ready: () => window.__jsfwReady },
  { key: 'qed',        label: 'Qed',        url: (_, qBase) => `${qBase}/index.html`,                        ready: () => document.querySelector('#run') && window.qed },
  { key: 'vue',        label: 'Vue 3',      url: (base) => `${base}/js_framework_bench.html?fw=vue`,        ready: () => window.__jsfwReady },
  { key: 'react',      label: 'React 18',   url: (base) => `${base}/js_framework_bench.html?fw=react`,      ready: () => window.__jsfwReady },
  { key: 'react-memo', label: 'React.memo', url: (base) => `${base}/js_framework_bench.html?fw=react-memo`, ready: () => window.__jsfwReady },
];

const qSrv = await serve({ dir: DIST, spa: false });
const tSrv = await serve({ dir: path.join(ROOT, 'test'), spa: false });
const browser = await puppeteer.launch({
  headless: true,
  args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-frame-rate-limit', '--disable-gpu-vsync'],
});

const results = {};
try {
  for (const fw of FRAMEWORKS) {
    results[fw.key] = await benchmarkFramework(browser, fw.key, fw.url(tSrv.baseUrl, qSrv.baseUrl), fw.ready);
  }
} finally {
  await browser.close();
  await qSrv.close();
  await tSrv.close();
  rmSync(DIST, { recursive: true, force: true });
}

const fmtMs = (ms) => (ms < 10 ? ms.toFixed(2) : ms.toFixed(1));
const ratios = {};
const gmeans = {};
for (const fw of FRAMEWORKS) {
  ratios[fw.key] = {};
  for (const [op] of OPS) {
    ratios[fw.key][op] = results[fw.key][op] / results.vanilla[op];
  }
  gmeans[fw.key] = geomean(OPS.map(([op]) => ratios[fw.key][op]));
}

console.log(`\n  js-framework-benchmark (keyed) — Chrome DevTools Trace click→paint, median of ${REPS} runs (${REPS_10K} for 10k)\n`);
console.log('  operation'.padEnd(26) + FRAMEWORKS.map((f) => f.label.padStart(16)).join(''));
console.log('  ' + '-'.repeat(24 + FRAMEWORKS.length * 16));
for (const [op, desc] of OPS) {
  const cols = FRAMEWORKS.map((f) => {
    const ms = fmtMs(results[f.key][op]);
    const r = ratios[f.key][op].toFixed(2);
    return `${ms}ms (${r}x)`.padStart(16);
  }).join('');
  console.log('  ' + desc.padEnd(24) + cols);
}
console.log('  ' + '-'.repeat(24 + FRAMEWORKS.length * 16));
console.log('  ' + 'GEOMETRIC MEAN'.padEnd(24) + FRAMEWORKS.map((f) => `${gmeans[f.key].toFixed(2)}x`.padStart(16)).join(''));
console.log('  ' + 'JS bundle (gzip KB)'.padEnd(24) + FRAMEWORKS.map((f) => `${bundleKb[f.key].toFixed(1)} KB`.padStart(16)).join(''));
console.log('\n' + JSON.stringify({ results, ratios, gmeans, bundleKb }));
