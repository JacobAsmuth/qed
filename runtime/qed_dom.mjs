import { mkOk, PUnit } from './qed_rt.mjs';

function Q() {
  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null];
  g.sig ||= new Map();
  g.sigVals ||= new Map();
  return g;
}
const ok = (v, w) => mkOk(v, w);

const SVG_NS   = 'http://www.w3.org/2000/svg';
const XLINK_NS = 'http://www.w3.org/1999/xlink';
const XML_NS   = 'http://www.w3.org/XML/1998/namespace';
const attrNS = (k) => k.startsWith('xlink:') ? XLINK_NS : (k.startsWith('xml:') ? XML_NS : null);
const managedAttrs = new WeakMap();
const nodeId = (el) => {
  if (!el) return 0;
  const g = Q(), N = g.nodes, id = el.__qedId;
  if (id !== undefined && N[id] === el) return id;
  const F = (g.free ||= []);
  const slot = F.length > 0 ? F.pop() : N.length;
  N[slot] = el;
  return (el.__qedId = slot);
};
const dropNode = (el) => {
  if (!el) return;
  const g = Q(), N = g.nodes, F = (g.free ||= []), q = [el];
  while (q.length > 0) {
    const cur = q.pop(), id = cur.__qedId;
    if (id !== undefined && N[id] === cur) { N[id] = null; cur.__qedId = undefined; F.push(id); }
    if (cur.childNodes) for (let i = 0; i < cur.childNodes.length; i++) q.push(cur.childNodes[i]);
  }
};

export const dom = {
  createElement(ns, tag, w) { const real = ns || (tag === 'svg' ? SVG_NS : ''); return ok(nodeId(real ? document.createElementNS(real, tag) : document.createElement(tag)), w); },
  // Children inherit SVG namespace inside `<svg>`, except `<foreignObject>` whose content is HTML.
  childNamespace(node, w) { const el = Q().nodes[node]; const svg = !!el && el.namespaceURI === SVG_NS && el.localName !== 'foreignObject'; return ok(svg ? SVG_NS : '', w); },
  createText(s, w)      { return ok(nodeId(document.createTextNode(s)), w); },
  createFragment(w)     { return ok(nodeId(document.createDocumentFragment()), w); },
  setAttribute(node, k, v, w) { const el = Q().nodes[node]; if (el) { const ns = attrNS(k); if (ns) { if (el.getAttributeNS(ns, k.slice(k.indexOf(':') + 1)) !== v) el.setAttributeNS(ns, k, v); } else if (el.getAttribute(k) !== v) el.setAttribute(k, v); } return ok(PUnit, w); },
  removeAttribute(node, k, w) { const el = Q().nodes[node]; if (el) { const ns = attrNS(k); if (ns) el.removeAttributeNS(ns, k.slice(k.indexOf(':') + 1)); else el.removeAttribute(k); } return ok(PUnit, w); },
  retainAttributes(node, namesList, w) {
    const el = Q().nodes[node];
    if (!el?.attributes) return ok(PUnit, w);
    const previous = managedAttrs.get(el);
    if (!previous && !namesList) return ok(PUnit, w);
    const names = new Set();
    if (typeof namesList === 'string') {
      for (const n of JSON.parse(namesList)) names.add(n);
    } else {
      for (let cur = namesList; cur && cur.t === 1; cur = cur.f[1]) names.add(cur.f[0]);
    }
    // Only remove previously framework-managed attributes (preserving hydration/userland sentinels),
    // and explicitly reset `value`/`checked` DOM properties that have no backing attribute.
    if (previous) {
      if (previous.has('value') && !names.has('value')) el.value = '';
      if (previous.has('checked') && !names.has('checked')) el.checked = false;
      for (const attr of [...el.attributes]) {
        if (previous.has(attr.name) && !names.has(attr.name)) el.removeAttributeNS(attr.namespaceURI, attr.localName);
      }
    }
    if (names.size > 0) managedAttrs.set(el, names);
    else if (previous) managedAttrs.delete(el);
    return ok(PUnit, w);
  },
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
  appendChild(parent, child, w) { const N = Q().nodes, p = N[parent], c = N[child]; if (p && c) { const isFrag = c.nodeType === 11 || c.localName === '#fragment'; p.appendChild(c); if (isFrag) dropNode(c); } return ok(PUnit, w); },
  setText(node, s, w) { const el = Q().nodes[node]; if (el && el.textContent !== s) el.textContent = s; return ok(PUnit, w); },
  setInnerHtml(node, html, w) { const el = Q().nodes[node]; if (el && el.innerHTML !== html) el.innerHTML = html; return ok(PUnit, w); },
  childAt(parent, index, w) { const p = Q().nodes[parent]; return ok(nodeId(p ? p.childNodes[index] : null), w); },
  childCount(parent, w) { const p = Q().nodes[parent]; return ok(p ? p.childNodes.length : 0, w); },
  appRoot(w) { const root = document.getElementById('app'); return ok(nodeId(root ? root.firstElementChild : null), w); },
  removeChild(parent, index, w) { const p = Q().nodes[parent], old = p && p.childNodes[index]; if (old) { p.removeChild(old); dropNode(old); } return ok(PUnit, w); },
  replaceChild(parent, index, newChild, w) { const N = Q().nodes, p = N[parent], c = N[newChild], old = p && p.childNodes[index]; if (old && c) { p.replaceChild(c, old); if (old !== c) dropNode(old); } return ok(PUnit, w); },
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
