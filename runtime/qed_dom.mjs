import { mkOk, PUnit } from './qed_rt.mjs';

const ok = mkOk, okU = () => ok(PUnit);
const Q = () => { const g = (globalThis.__qed ||= {}); g.nodes ||= [null]; g.free ||= []; g.sig ||= new Map(); g.sigVals ||= new Map(); g.sigEv ||= new Map(); g.tmpls ||= [null]; return g; };
const elOf = (i) => Q().nodes[i];

const SVG_NS = 'http://www.w3.org/2000/svg', XLINK_NS = 'http://www.w3.org/1999/xlink', XML_NS = 'http://www.w3.org/XML/1998/namespace';
const attrNS = (k) => k.startsWith('xlink:') ? XLINK_NS : k.startsWith('xml:') ? XML_NS : null;
const attrLocal = (k) => k.slice(k.indexOf(':') + 1);
const setAttr = (el, k, v, ns, loc) => ns ? (el.getAttributeNS(ns, loc) !== v && el.setAttributeNS(ns, k, v)) : (el.getAttribute(k) !== v && el.setAttribute(k, v));

const managedAttrs = new WeakMap();
const allocSlot = (el, N, F) => { const slot = F.length > 0 ? F.pop() : N.length; N[slot] = el; return (el.__qedId = slot); };
const nodeId = (el) => { if (!el) return 0; const g = Q(), N = g.nodes, id = el.__qedId; return (id !== undefined && N[id] === el) ? id : allocSlot(el, N, g.free); };
const freeSlot = (cur, N, F) => { const id = cur.__qedId; if (id !== undefined && N[id] === cur) { N[id] = null; cur.__qedId = undefined; F.push(id); } };
const dropNode = (el) => {
  if (!el) return;
  const g = Q(), N = g.nodes, F = g.free;
  if (el.__qedTmpl) { freeSlot(el, N, F); el.__qedSlots = undefined; return; }
  for (const { sig, sigVals } = g, q = [el]; q.length > 0; ) {
    const cur = q.pop(), s = cur.__qedSigs; freeSlot(cur, N, F);
    if (s) { for (let i = 0; i < s.length; i++) if (sig.get(s[i])?.el === cur) { sig.delete(s[i]); sigVals.delete(s[i]); } cur.__qedSigs = undefined; }
    if (cur.childNodes) for (let i = 0; i < cur.childNodes.length; i++) q.push(cur.childNodes[i]);
  }
};

const nthChild = (el, idx) => { let c = el.firstChild; for (let i = 0; i < idx && c; i++) c = c.nextSibling; return c; };
const makeWalker = (path) => {
  const [a, b, c] = path, n = path.length;
  return n === 0 ? (r) => r : n === 1 ? (r) => nthChild(r, a) : n === 2 ? (r) => nthChild(nthChild(r, a), b)
    : n === 3 ? (r) => nthChild(nthChild(nthChild(r, a), b), c)
    : (r) => { let cur = r; for (let i = 0; i < n && cur; i++) cur = nthChild(cur, path[i]); return cur; };
};
const walkOrCreateText = (root, path) => {
  let cur = root; const n = path.length;
  for (let i = 0; i < n - 1 && cur; i++) cur = nthChild(cur, path[i]);
  if (!n || !cur) return cur;
  let t = nthChild(cur, path[n - 1]);
  return t || (cur.appendChild(t = document.createTextNode('')), t);
};

export const applySignalToEl = (el, attr, s) => {
  if (attr === 'value') { if (el.value !== s) el.value = s; }
  else if (attr === 'checked') { const on = (s !== '' && s !== 'false'); if (el.checked !== on) el.checked = on; }
  else if (attr) { if (el.getAttribute(attr) !== s) el.setAttribute(attr, s); }
  else if (el.textContent !== s) el.textContent = s;
};
const writeSlot = (t, tmpl, j, v) => {
  const k = t ? tmpl.kinds[j] : -1;
  if (k === 0) { if (t.nodeValue !== v) t.nodeValue = v; }
  else if (k === 1) { if (t.className !== v) t.className = v; }
  else if (k === 2) { if (t.value !== v) t.value = v; }
  else if (k === 3) setAttr(t, tmpl.attrNames[j], v, tmpl.attrNSs[j], tmpl.attrLocals[j]);
};
const cloneAndInitRow = (tmpl, vals) => {
  const el = tmpl.proto.cloneNode(true), { n, walkers } = tmpl, slots = new Array(n);
  for (let j = 0; j < n; j++) { const t = slots[j] = walkers[j](el), v = vals[j]; if (v !== '' && t) writeSlot(t, tmpl, j, v); }
  return (el.__qedSlots = slots, el.__qedTmpl = true, el);
};

const fwd = (k) => (...a) => { a.pop(); Q()[k]?.(...a); return okU(); };
const bindSig = (node, name, attr) => {
  const g = Q(), el = g.nodes[node];
  if (el) { g.sig.set(name, { el, attr }); (el.__qedSigs ||= []).push(name); const v = g.sigVals.get(name); if (v !== undefined) applySignalToEl(el, attr, v); }
  return okU();
};
const toNameSet = (xs) => {
  if (xs instanceof Set) return xs;
  if (typeof xs === 'string') return new Set(JSON.parse(xs));
  const s = new Set(); for (let cur = xs; cur?.t === 1; cur = cur.f[1]) s.add(cur.f[0]); return s;
};
const placeBefore = (p, c, ref) => { if (!p || !c || ref === c) return; if (c.parentNode === p && p.moveBefore) try { p.moveBefore(c, ref); return; } catch (_) {} p.insertBefore(c, ref); };

export const dom = {
  createElement(ns, tag) { const real = ns || (tag === 'svg' ? SVG_NS : ''); return ok(nodeId(real ? document.createElementNS(real, tag) : document.createElement(tag))); },
  childNamespace(node) { const el = elOf(node); return ok(el?.namespaceURI === SVG_NS && el.localName !== 'foreignObject' ? SVG_NS : ''); },
  createText(s) { return ok(nodeId(document.createTextNode(s))); }, createFragment() { return ok(nodeId(document.createDocumentFragment())); },
  setAttribute(node, k, v) { const el = elOf(node); if (el) { const ns = attrNS(k); setAttr(el, k, v, ns, ns ? attrLocal(k) : k); } return okU(); },
  removeAttribute(node, k) { const el = elOf(node); if (el) { const ns = attrNS(k); ns ? el.removeAttributeNS(ns, attrLocal(k)) : el.removeAttribute(k); } return okU(); },
  retainAttributes(node, namesList) {
    const el = elOf(node); if (!el?.attributes) return okU();
    const prevRaw = managedAttrs.get(el);
    if (!prevRaw) { if (namesList && (typeof namesList === 'string' || namesList.t === 1)) managedAttrs.set(el, namesList); return okU(); }
    const prev = toNameSet(prevRaw), names = toNameSet(namesList);
    if (prev.has('value') && !names.has('value')) el.value = '';
    if (prev.has('checked') && !names.has('checked')) el.checked = false;
    for (const a of [...el.attributes]) if (prev.has(a.name) && !names.has(a.name)) el.removeAttributeNS(a.namespaceURI, a.localName);
    names.size > 0 ? managedAttrs.set(el, names) : managedAttrs.delete(el);
    return okU();
  },
  getAttribute(node, k) { return ok(elOf(node)?.getAttribute(k) ?? ''); },
  appState() { const s = globalThis.__qedHmrState; if (typeof s === 'string') { delete globalThis.__qedHmrState; return ok(s); } return ok(document.getElementById('qed-state')?.textContent ?? ''); },
  clearHandlers(node) { const el = elOf(node); if (el?.attributes) for (const a of [...el.attributes]) if (a.name.startsWith('data-qed-on')) el.removeAttribute(a.name); return okU(); },
  setValue(node, v) { const el = elOf(node); if (el && el.value !== v) el.value = v; return okU(); }, setChecked(node, on) { const el = elOf(node); if (el) el.checked = !!on; return okU(); },
  setText(node, s) { const el = elOf(node); if (el && el.textContent !== s) el.textContent = s; return okU(); },
  today() { const d = new Date(), p = (n) => (n < 10 ? '0' : '') + n; return ok(`${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())}`); },
  currentPath() { return ok(location.pathname + location.search); }, pushPath(p) { history.pushState({}, '', p); return okU(); },
  appendChild(parent, child) { const N = Q().nodes, p = N[parent], c = N[child]; if (p && c) { const f = c.nodeType === 11 || c.localName === '#fragment'; p.appendChild(c); if (f) dropNode(c); } return okU(); },
  childAt(parent, index) { return ok(nodeId(elOf(parent)?.childNodes[index] ?? null)); }, childCount(parent) { return ok(elOf(parent)?.childNodes.length ?? 0); },
  appRoot() { return ok(nodeId(document.getElementById('app')?.firstElementChild ?? null)); }, isConnected(node) { return ok(elOf(node)?.isConnected ? 1 : 0); },
  removeChild(parent, index) { const p = elOf(parent), old = p?.childNodes[index]; if (old) { p.removeChild(old); dropNode(old); } return okU(); },
  replaceChild(parent, index, newChild) { const N = Q().nodes, p = N[parent], c = N[newChild], old = p?.childNodes[index]; if (old && c) { p.replaceChild(c, old); if (old !== c) dropNode(old); } return okU(); },
  insertBefore(parent, index, child) { const N = Q().nodes, p = N[parent]; if (p) placeBefore(p, N[child], p.childNodes[index] || null); return okU(); },
  insertBeforeRef(parent, ref, child) { const N = Q().nodes; placeBefore(N[parent], N[child], ref ? N[ref] : null); return okU(); },
  removeNode(parent, child) { const N = Q().nodes, p = N[parent], c = N[child]; if (p && c && c.parentNode === p) { p.removeChild(c); dropNode(c); } return okU(); },
  clearChildren(parent) { const p = elOf(parent); if (p) { for (let c = p.firstChild; c; c = c.nextSibling) dropNode(c); p.textContent = ''; } return okU(); },
  mountRoot(node) { const root = document.getElementById('app'), el = elOf(node); if (root && el) root.replaceChildren(el); return okU(); },
  portSend(name, payload) { Q().ports?.[name]?.(payload); return okU(); },
  bindSignal(node, name) { return bindSig(node, name, null); }, bindSignalAttr: bindSig,
  getSigSlot(name) { return ok(Q().sigEv.get(name) || 0); }, setSigSlot(name, slot) { Q().sigEv.set(name, slot); return okU(); },
  compileRowTmpl(protoNode, slotPaths, slotAttrs, evPaths, evNames) {
    const g = Q(), proto = g.nodes[protoNode]; if (!proto) return ok(0);
    dropNode(proto);
    const n = slotPaths.length, walkers = slotPaths.map(makeWalker), attrNames = slotAttrs.slice();
    const kinds = Uint8Array.from(attrNames, (a) => a === '' ? 0 : a === 'class' ? 1 : a === 'value' ? 2 : 3);
    const attrNSs = attrNames.map((a, i) => kinds[i] === 3 ? attrNS(a) : null), attrLocals = attrNames.map((a, i) => attrNSs[i] ? attrLocal(a) : a);
    const evWalkers = evPaths.map((p, i) => { const w = makeWalker(p); w(proto)?.setAttribute('data-qed-row-on-' + evNames[i], String(i)); return w; });
    return ok(g.tmpls.push({ proto, n, slotPaths, walkers, kinds, attrNames, attrNSs, attrLocals, evN: evPaths.length, evWalkers, evNames }) - 1);
  },
  mountTmplRow(tmplId, vals) { const tmpl = Q().tmpls[tmplId]; return ok(tmpl ? nodeId(cloneAndInitRow(tmpl, vals)) : 0); },
  mountTmplRows(parent, tmplId, valsPerRow) {
    const g = Q(), p = g.nodes[parent], tmpl = g.tmpls[tmplId], m = valsPerRow.length, ids = new Array(m); ids.r = 1;
    if (!p || !tmpl) { ids.fill(0); return ok(ids); }
    const N = g.nodes, F = g.free, frag = document.createDocumentFragment();
    for (let i = 0; i < m; i++) { const el = cloneAndInitRow(tmpl, valsPerRow[i]); ids[i] = allocSlot(el, N, F); frag.appendChild(el); }
    p.appendChild(frag); return ok(ids);
  },
  patchTmplRow(node, tmplId, newVals, oldVals) {
    const g = Q(), el = g.nodes[node], tmpl = g.tmpls[tmplId], slots = el?.__qedSlots;
    if (slots && tmpl) for (let j = 0; j < tmpl.n; j++) { const v = newVals[j]; if (!oldVals || oldVals[j] !== v) writeSlot(slots[j], tmpl, j, v); }
    return okU();
  },
  hydrateTmplRow(node, tmplId) {
    const g = Q(), el = g.nodes[node], tmpl = g.tmpls[tmplId]; if (!el || !tmpl) return okU();
    const slots = new Array(tmpl.n);
    for (let j = 0; j < tmpl.n; j++) slots[j] = tmpl.kinds[j] === 0 ? walkOrCreateText(el, tmpl.slotPaths[j]) : tmpl.walkers[j](el);
    for (let j = 0; j < tmpl.evN; j++) { const t = tmpl.evWalkers[j](el); if (t) { t.removeAttribute('data-qed-on-' + tmpl.evNames[j]); t.setAttribute('data-qed-row-on-' + tmpl.evNames[j], String(j)); } }
    return (el.__qedSlots = slots, el.__qedTmpl = true, okU());
  },
  wsOpen(connId, url, isBin) { Q().wsOpen?.(connId, url, !!isBin); return okU(); },
  fetchStream: fwd('fetchStream'), httpSend: fwd('httpSend'), httpSendBytes: fwd('httpSendBytes'), effect: fwd('effect'),
  effectResult: fwd('effectResult'), wsSendBytes: fwd('wsSendBytes'), wsSendText: fwd('wsSendText'), wsClose: fwd('wsClose'),
};
