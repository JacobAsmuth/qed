// qed_dom.mjs — the DOM externs for the transpiled driver, ported from runtime/qed_dom.c.
// Each method follows the IO protocol: it takes the world token last and returns
// EStateM.Result.ok(value, world). `Node` is a UInt32 handle into globalThis.__qed.nodes
// (index 0 = null sentinel).
import { mkOk, PUnit } from './qed_rt.mjs';

function Q() {
  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null];                    // index 0 reserved (null sentinel)
  g.sig ||= new Map();                   // signal name → { el, attr }
  g.sigVals ||= new Map();               // signal name → value
  return g;
}
const ok = (v, w) => mkOk(v, w);

// Namespaces. Elements inside an <svg> subtree must be created in the SVG namespace
// (createElementNS), and xlink:*/xml:* attributes set in their own namespace (setAttributeNS) —
// `<use xlink:href>` and friends only resolve when the attribute is namespaced.
const SVG_NS   = 'http://www.w3.org/2000/svg';
const XLINK_NS = 'http://www.w3.org/1999/xlink';
const XML_NS   = 'http://www.w3.org/XML/1998/namespace';
const attrNS = (k) => k.startsWith('xlink:') ? XLINK_NS : (k.startsWith('xml:') ? XML_NS : null);

export const dom = {
  // `ns` is the namespace the parent established for its children (see childNamespace); "" is the
  // HTML default, except a standalone `svg` tag still enters the SVG namespace.
  createElement(ns, tag, w) { const N = Q().nodes; const real = ns || (tag === 'svg' ? SVG_NS : ''); N.push(real ? document.createElementNS(real, tag) : document.createElement(tag)); return ok(N.length - 1, w); },
  // The namespace children of `node` inherit: SVG inside an <svg> subtree, HTML otherwise — and
  // back to HTML inside <foreignObject>, whose content is ordinary HTML.
  childNamespace(node, w) { const el = Q().nodes[node]; const svg = !!el && el.namespaceURI === SVG_NS && el.localName !== 'foreignObject'; return ok(svg ? SVG_NS : '', w); },
  createText(s, w)      { const N = Q().nodes; N.push(document.createTextNode(s));    return ok(N.length - 1, w); },
  createFragment(w)     { const N = Q().nodes; N.push(document.createDocumentFragment()); return ok(N.length - 1, w); },
  setAttribute(node, k, v, w) { const el = Q().nodes[node]; if (el) { const ns = attrNS(k); if (ns) { if (el.getAttributeNS(ns, k.slice(k.indexOf(':') + 1)) !== v) el.setAttributeNS(ns, k, v); } else if (el.getAttribute(k) !== v) el.setAttribute(k, v); } return ok(PUnit, w); },
  removeAttribute(node, k, w) { const el = Q().nodes[node]; if (el) { const ns = attrNS(k); if (ns) el.removeAttributeNS(ns, k.slice(k.indexOf(':') + 1)); else el.removeAttribute(k); } return ok(PUnit, w); },
  getAttribute(node, k, w)    { const el = Q().nodes[node]; const v = el ? el.getAttribute(k) : null; return ok(v == null ? '' : v, w); },
  appState(w) { const el = document.getElementById('qed-state'); return ok(el ? el.textContent : '', w); },
  clearHandlers(node, w) {
    const el = Q().nodes[node];
    if (el && el.attributes) {
      const names = [];
      for (const a of el.attributes) if (a.name.indexOf('data-qed-on') === 0) names.push(a.name);
      for (const n of names) el.removeAttribute(n);
    }
    return ok(PUnit, w);
  },
  setValue(node, v, w)  { const el = Q().nodes[node]; if (el && el.value !== v) el.value = v; return ok(PUnit, w); },
  setChecked(node, on, w) { const el = Q().nodes[node]; if (el) el.checked = !!on; return ok(PUnit, w); },
  today(w) { const d = new Date(), p = (n) => (n < 10 ? '0' : '') + n; return ok(`${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())}`, w); },
  fetchStream(url, body, cid, did, w) { Q(); if (globalThis.__qed.fetchStream) globalThis.__qed.fetchStream(url, body, cid, did); return ok(PUnit, w); },
  httpSend(method, url, body, id, w)  { Q(); if (globalThis.__qed.httpSend) globalThis.__qed.httpSend(method, url, body, id); return ok(PUnit, w); },
  currentPath(w) { return ok(location.pathname, w); },
  pushPath(p, w) { history.pushState({}, '', p); return ok(PUnit, w); },
  appendChild(parent, child, w) { const N = Q().nodes; if (N[parent] && N[child]) N[parent].appendChild(N[child]); return ok(PUnit, w); },
  setText(node, s, w) { const el = Q().nodes[node]; if (el && el.textContent !== s) el.textContent = s; return ok(PUnit, w); },
  setInnerHtml(node, html, w) { const el = Q().nodes[node]; if (el && el.innerHTML !== html) el.innerHTML = html; return ok(PUnit, w); },
  childAt(parent, index, w) { const N = Q().nodes, p = N[parent]; const c = p ? p.childNodes[index] : null; if (!c) return ok(0, w); N.push(c); return ok(N.length - 1, w); },
  childCount(parent, w) { const p = Q().nodes[parent]; return ok(p ? p.childNodes.length : 0, w); },
  appRoot(w) { const N = Q().nodes; const root = document.getElementById('app'); const c = root ? root.firstElementChild : null; if (!c) return ok(0, w); N.push(c); return ok(N.length - 1, w); },
  removeChild(parent, index, w) { const p = Q().nodes[parent]; if (p && p.childNodes[index]) p.removeChild(p.childNodes[index]); return ok(PUnit, w); },
  replaceChild(parent, index, newChild, w) { const N = Q().nodes, p = N[parent]; if (p && N[newChild] && p.childNodes[index]) p.replaceChild(N[newChild], p.childNodes[index]); return ok(PUnit, w); },
  insertBefore(parent, index, child, w) {
    const N = Q().nodes, p = N[parent], c = N[child];
    if (!p || !c) return ok(PUnit, w);
    const ref = p.childNodes[index] || null;
    if (ref === c) return ok(PUnit, w);
    if (c.parentNode === p && p.moveBefore) { try { p.moveBefore(c, ref); return ok(PUnit, w); } catch (e) {} }
    p.insertBefore(c, ref);
    return ok(PUnit, w);
  },
  mountRoot(node, w) { const root = document.getElementById('app'), el = Q().nodes[node]; if (root && el) root.replaceChildren(el); return ok(PUnit, w); },
  isConnected(node, w) { const el = Q().nodes[node]; return ok((el && el.isConnected) ? 1 : 0, w); },
  effect(kind, a, b, c, w)       { Q(); if (globalThis.__qed.effect) globalThis.__qed.effect(kind, a, b, c); return ok(PUnit, w); },
  effectResult(kind, a, b, id, w){ Q(); if (globalThis.__qed.effectResult) globalThis.__qed.effectResult(kind, a, b, id); return ok(PUnit, w); },
  portSend(name, payload, w) { Q(); const p = globalThis.__qed.ports && globalThis.__qed.ports[name]; if (p) p(payload); return ok(PUnit, w); },
  bindSignal(node, name, w) {
    const g = Q(), el = g.nodes[node]; if (!el) return ok(PUnit, w);
    // Register by name in `g.sig` (how `setSignal` finds the node on update). The
    // `data-qed-signal` attribute is an SSR-only marker (emitted by `Render`, read by no client
    // code), so the live client doesn't write it — that's one fewer DOM mutation per dynamic leaf.
    g.sig.set(name, { el, attr: null });
    const v = g.sigVals.get(name); if (v !== undefined && el.textContent !== v) el.textContent = v;
    return ok(PUnit, w);
  },
  bindSignalAttr(node, name, attr, w) {
    const g = Q(), el = g.nodes[node]; if (!el) return ok(PUnit, w);
    g.sig.set(name, { el, attr }); const v = g.sigVals.get(name);
    if (v !== undefined && el.getAttribute(attr) !== v) el.setAttribute(attr, v);
    return ok(PUnit, w);
  },
};
