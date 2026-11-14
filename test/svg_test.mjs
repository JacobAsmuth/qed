import { ROOT, withBrowser, send } from './harness.mjs';

await withBrowser('SVG', {
  dir: ROOT,
  spa: false,
  routes: (req, res, url) => {
    if (url.pathname === '/') { send(res, 200, 'text/html', '<!doctype html><body></body>'); return true; }
    return false;
  },
}, async ({ page, check, baseUrl }) => {
  await page.goto(`${baseUrl}/`, { waitUntil: 'load' });

  const { o, SVG, XHTML } = await page.evaluate(async (base) => {
    const { dom } = await import(`${base}/runtime/qed_dom.mjs`);
    const SVG = 'http://www.w3.org/2000/svg', XHTML = 'http://www.w3.org/1999/xhtml', XLINK = 'http://www.w3.org/1999/xlink';
    const nodes = () => globalThis.__qed.nodes;
    const create  = (ns, tag) => dom.createElement(ns, tag, 0).f[0];
    const childNs = (h)       => dom.childNamespace(h, 0).f[0];
    const nsOf    = (h)       => nodes()[h].namespaceURI;
    const o = {};

    const svg = create('', 'svg');
    o.svgNS = nsOf(svg);
    const inSvg = childNs(svg);
    o.svgChildCtx = inSvg;
    o.circleNS = nsOf(create(inSvg, 'circle'));
    o.feSpotLightNS = nsOf(create(inSvg, 'feSpotLight'));
    o.aNS = nsOf(create(inSvg, 'a'));
    o.titleNS = nsOf(create(inSvg, 'title'));

    const fo = create(inSvg, 'foreignObject');
    o.foNS = nsOf(fo);
    const inFo = childNs(fo);
    o.foChildCtx = inFo;
    o.divNS = nsOf(create(inFo, 'div'));
    o.reentrySvgNS = nsOf(create(childNs(create(inFo, 'div')), 'svg'));
    o.bareDivNS = nsOf(create('', 'div'));

    const use = create(inSvg, 'use');
    dom.setAttribute(use, 'xlink:href', '#icon', 0);
    o.xlinkResolved = nodes()[use].getAttributeNS(XLINK, 'href');
    dom.removeAttribute(use, 'xlink:href', 0);
    o.xlinkRemoved = nodes()[use].getAttributeNS(XLINK, 'href');

    const host = create('', 'div');
    dom.setInnerHtml(host, '<svg viewBox="0 0 10 10"><circle cx="5"/></svg>', 0);
    const hostEl = nodes()[host];
    o.rawChildCount = hostEl.childElementCount;
    o.rawSvgNS = hostEl.firstElementChild ? hostEl.firstElementChild.namespaceURI : 'none';
    o.rawCircleNS = hostEl.querySelector('circle') ? hostEl.querySelector('circle').namespaceURI : 'none';

    return { o, SVG, XHTML };
  }, baseUrl);

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
});
