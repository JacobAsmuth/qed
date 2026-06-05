// SVG namespaces — the trusted DOM boundary (runtime/qed_dom.mjs). Exercises the same calls the
// transpiled driver's `buildDom` makes: create an element in the namespace its parent established,
// then read `childNamespace` to learn the context for its children. Run in a real browser (puppeteer)
// because SVG namespace semantics are the browser's, not a mock's.
import { spawn } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import puppeteer from 'puppeteer';

const PORT = 8141;
const ROOT = new URL('..', import.meta.url).pathname;   // repo root, so /runtime/*.mjs is importable
const server = spawn('python3', ['-m', 'http.server', String(PORT), '--directory', ROOT], { stdio: 'ignore' });
await sleep(700);

let failures = 0;
const check = (l, got, want) => {
  const ok = String(got) === String(want);
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${l}: ${JSON.stringify(got)}`);
  if (!ok) failures++;
};

const browser = await puppeteer.launch({ headless: true, args: ['--no-sandbox', '--disable-setuid-sandbox'] });
try {
  const page = await browser.newPage();
  page.on('pageerror', (e) => { console.log('  [pageerror]', e.message); failures++; });
  page.on('console', (m) => { if (m.type() === 'error') console.log('  [page error]', m.text()); });
  await page.goto(`http://localhost:${PORT}/`, { waitUntil: 'load' });

  const r = await page.evaluate(async (port) => {
    const { dom } = await import(`http://localhost:${port}/runtime/qed_dom.mjs`);
    const SVG = 'http://www.w3.org/2000/svg', XHTML = 'http://www.w3.org/1999/xhtml', XLINK = 'http://www.w3.org/1999/xlink';
    const nodes = () => globalThis.__qed.nodes;
    // mirror buildDom: create `tag` in the parent context `ns`, children use childNamespace(node).
    const create  = (ns, tag) => dom.createElement(ns, tag, 0).f[0];
    const childNs = (h)       => dom.childNamespace(h, 0).f[0];
    const nsOf    = (h)       => nodes()[h].namespaceURI;
    const o = {};

    const svg = create('', 'svg');                  // <svg> from HTML context enters the SVG namespace
    o.svgNS = nsOf(svg);
    const inSvg = childNs(svg);                      // context for svg's children
    o.svgChildCtx = inSvg;
    o.circleNS = nsOf(create(inSvg, 'circle'));      // ordinary child inherits SVG
    o.feSpotLightNS = nsOf(create(inSvg, 'feSpotLight'));  // never in the old tag list — still SVG (gap #1)
    o.aNS = nsOf(create(inSvg, 'a'));                // shared HTML/SVG tag stays SVG here (gap #3)
    o.titleNS = nsOf(create(inSvg, 'title'));        //   "

    const fo = create(inSvg, 'foreignObject');       // foreignObject is itself SVG…
    o.foNS = nsOf(fo);
    const inFo = childNs(fo);                         // …but its children return to HTML
    o.foChildCtx = inFo;
    const div = nsOf(create(inFo, 'div'));
    o.divNS = div;
    o.reentrySvgNS = nsOf(create(childNs(create(inFo, 'div')), 'svg'));  // nested <svg> re-enters SVG
    o.bareDivNS = nsOf(create('', 'div'));           // no SVG ancestor → HTML

    const use = create(inSvg, 'use');                // gap #2: xlink:href must be namespaced
    dom.setAttribute(use, 'xlink:href', '#icon', 0);
    o.xlinkResolved = nodes()[use].getAttributeNS(XLINK, 'href');
    dom.removeAttribute(use, 'xlink:href', 0);
    o.xlinkRemoved = nodes()[use].getAttributeNS(XLINK, 'href');

    // rawHtml escape hatch: setInnerHtml parses a raw SVG string; inline SVG lands in SVG namespace
    const host = create('', 'div');
    dom.setInnerHtml(host, '<svg viewBox="0 0 10 10"><circle cx="5"/></svg>', 0);
    const hostEl = nodes()[host];
    o.rawChildCount = hostEl.childElementCount;
    o.rawSvgNS = hostEl.firstElementChild ? hostEl.firstElementChild.namespaceURI : 'none';
    o.rawCircleNS = hostEl.querySelector('circle') ? hostEl.querySelector('circle').namespaceURI : 'none';

    return { o, SVG, XHTML };
  }, PORT);

  const { o, SVG, XHTML } = r;
  check('root <svg> is SVG namespace', o.svgNS, SVG);
  check('svg children context is SVG', o.svgChildCtx, SVG);
  check('circle inherits SVG', o.circleNS, SVG);
  check('feSpotLight inherits SVG (no tag list)', o.feSpotLightNS, SVG);
  check('shared <a> inside svg stays SVG', o.aNS, SVG);
  check('shared <title> inside svg stays SVG', o.titleNS, SVG);
  check('foreignObject is SVG', o.foNS, SVG);
  check('foreignObject children return to HTML', o.foChildCtx, '');
  check('div under foreignObject is HTML', o.divNS, XHTML);
  check('nested <svg> in HTML subtree re-enters SVG', o.reentrySvgNS, SVG);
  check('bare div (no svg ancestor) is HTML', o.bareDivNS, XHTML);
  check('xlink:href resolved in XLink namespace', o.xlinkResolved, '#icon');
  check('xlink:href removed', o.xlinkRemoved, null);
  check('rawHtml injected the markup', o.rawChildCount, 1);
  check('rawHtml <svg> parsed in the SVG namespace', o.rawSvgNS, SVG);
  check('rawHtml <circle> parsed in the SVG namespace', o.rawCircleNS, SVG);
} finally {
  await browser.close();
  server.kill();
}

console.log(failures ? `\n${failures} FAILURES` : '\nSVG namespaces: ALL PASS (createElement + childNamespace inheritance + xlink attrs)');
process.exit(failures ? 1 : 0);
