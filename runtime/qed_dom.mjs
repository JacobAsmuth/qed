import { mkOk, PUnit } from './qed_rt.mjs';

function Q() {
  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null];
  g.sig ||= new Map();
  g.sigVals ||= new Map();
  g.sigEv ||= new Map();
  g.tmpls ||= [null];
  return g;
}
const ok = mkOk;

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
  const g = Q(), N = g.nodes, F = (g.free ||= []);
  if (el.__qedTmpl) {
    const id = el.__qedId;
    if (id !== undefined && N[id] === el) { N[id] = null; el.__qedId = undefined; F.push(id); }
    el.__qedSlots = undefined;
    return;
  }
  const sig = g.sig, sigVals = g.sigVals, q = [el];
  while (q.length > 0) {
    const cur = q.pop(), id = cur.__qedId;
    if (id !== undefined && N[id] === cur) { N[id] = null; cur.__qedId = undefined; F.push(id); }
    const s = cur.__qedSigs;
    if (s !== undefined) {
      for (let i = 0; i < s.length; i++) {
        const nm = s[i];
        if (sig.get(nm)?.el === cur) { sig.delete(nm); sigVals.delete(nm); }
      }
      cur.__qedSigs = undefined;
    }
    if (cur.childNodes) for (let i = 0; i < cur.childNodes.length; i++) q.push(cur.childNodes[i]);
  }
};

const nthChild = (el, idx) => {
  let c = el.firstChild;
  for (let i = 0; i < idx && c; i++) c = c.nextSibling;
  return c;
};
const makeWalker = (path) => {
  const n = path.length;
  if (n === 0) return (r) => r;
  if (n === 1) { const a = path[0]; return (r) => nthChild(r, a); }
  if (n === 2) { const a = path[0], b = path[1]; return (r) => nthChild(nthChild(r, a), b); }
  if (n === 3) { const a = path[0], b = path[1], c = path[2]; return (r) => nthChild(nthChild(nthChild(r, a), b), c); }
  return (r) => { let cur = r; for (let i = 0; i < n && cur; i++) cur = nthChild(cur, path[i]); return cur; };
};
const walkOrCreateText = (root, path) => {
  const n = path.length;
  if (n === 0) return root;
  let cur = root;
  for (let i = 0; i < n - 1 && cur; i++) cur = nthChild(cur, path[i]);
  if (!cur) return null;
  const last = path[n - 1];
  let target = nthChild(cur, last);
  if (!target) {
    target = document.createTextNode('');
    cur.appendChild(target);
  }
  return target;
};
const writeSlot = (target, kind, attrName, attrNs, attrLocal, v) => {
  if (!target) return;
  if (kind === 0) { if (target.nodeValue !== v) target.nodeValue = v; }
  else if (kind === 1) { if (target.className !== v) target.className = v; }
  else if (kind === 2) { if (target.value !== v) target.value = v; }
  else if (attrNs) { if (target.getAttributeNS(attrNs, attrLocal) !== v) target.setAttributeNS(attrNs, attrName, v); }
  else if (target.getAttribute(attrName) !== v) target.setAttribute(attrName, v);
};
const cloneAndInitRow = (tmpl, vals) => {
  const el = tmpl.proto.cloneNode(true);
  const n = tmpl.n, walkers = tmpl.walkers, kinds = tmpl.kinds;
  const attrNames = tmpl.attrNames, attrNSs = tmpl.attrNSs, attrLocals = tmpl.attrLocals;
  const slots = new Array(n);
  for (let j = 0; j < n; j++) {
    const t = walkers[j](el);
    slots[j] = t;
    const v = vals[j];
    if (v !== '' && t) {
      const k = kinds[j];
      if (k === 0) t.nodeValue = v;
      else if (k === 1) t.className = v;
      else if (k === 2) t.value = v;
      else if (attrNSs[j]) t.setAttributeNS(attrNSs[j], attrNames[j], v);
      else t.setAttribute(attrNames[j], v);
    }
  }
  el.__qedSlots = slots;
  el.__qedTmpl = true;
  return el;
};

const fwd = (k) => (...a) => { const w = a.pop(), g = Q(); if (g[k]) g[k](...a); return ok(PUnit, w); };
const bindSig = (node, name, attr, w) => {
  const g = Q(), el = g.nodes[node]; if (!el) return ok(PUnit, w);
  g.sig.set(name, { el, attr });
  if (el.__qedSigs) el.__qedSigs.push(name); else el.__qedSigs = [name];
  const v = g.sigVals.get(name);
  if (v !== undefined) {
    if (attr) { if (el.getAttribute(attr) !== v) el.setAttribute(attr, v); }
    else if (el.textContent !== v) el.textContent = v;
  }
  return ok(PUnit, w);
};

const toNameSet = (namesList) => {
  if (namesList instanceof Set) return namesList;
  const names = new Set();
  if (typeof namesList === 'string') {
    for (const n of JSON.parse(namesList)) names.add(n);
  } else {
    for (let cur = namesList; cur && cur.t === 1; cur = cur.f[1]) names.add(cur.f[0]);
  }
  return names;
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
    const prevRaw = managedAttrs.get(el);
    if (!prevRaw) {
      // Fresh element: defer Set allocation until a subsequent patch actually diffs attributes.
      if (namesList && (typeof namesList === 'string' || namesList.t === 1)) managedAttrs.set(el, namesList);
      return ok(PUnit, w);
    }
    const previous = toNameSet(prevRaw);
    const names = toNameSet(namesList);
    // Only remove previously framework-managed attributes (preserving hydration/userland sentinels),
    // and explicitly reset `value`/`checked` DOM properties that have no backing attribute.
    if (previous.has('value') && !names.has('value')) el.value = '';
    if (previous.has('checked') && !names.has('checked')) el.checked = false;
    for (const attr of [...el.attributes]) {
      if (previous.has(attr.name) && !names.has(attr.name)) el.removeAttributeNS(attr.namespaceURI, attr.localName);
    }
    if (names.size > 0) managedAttrs.set(el, names);
    else managedAttrs.delete(el);
    return ok(PUnit, w);
  },
  getAttribute(node, k, w)    { const el = Q().nodes[node]; const v = el ? el.getAttribute(k) : null; return ok(v == null ? '' : v, w); },
  appState(w) {
    if (typeof globalThis.__qedHmrState === 'string') {
      const s = globalThis.__qedHmrState;
      delete globalThis.__qedHmrState;
      return ok(s, w);
    }
    const el = document.getElementById('qed-state');
    return ok(el ? el.textContent : '', w);
  },
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
  fetchStream: fwd('fetchStream'),
  httpSend: fwd('httpSend'),
  httpSendBytes: fwd('httpSendBytes'),
  currentPath(w) { return ok(location.pathname + location.search, w); },
  pushPath(p, w) { history.pushState({}, '', p); return ok(PUnit, w); },
  appendChild(parent, child, w) { const N = Q().nodes, p = N[parent], c = N[child]; if (p && c) { const isFrag = c.nodeType === 11 || c.localName === '#fragment'; p.appendChild(c); if (isFrag) dropNode(c); } return ok(PUnit, w); },
  setText(node, s, w) { const el = Q().nodes[node]; if (el && el.textContent !== s) el.textContent = s; return ok(PUnit, w); },
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
  insertBeforeRef(parent, ref, child, w) {
    const N = Q().nodes, p = N[parent], c = N[child], r = ref ? N[ref] : null;
    if (!p || !c || r === c) return ok(PUnit, w);
    if (c.parentNode === p && p.moveBefore) { try { p.moveBefore(c, r); return ok(PUnit, w); } catch (e) {} }
    p.insertBefore(c, r);
    return ok(PUnit, w);
  },
  removeNode(parent, child, w) {
    const N = Q().nodes, p = N[parent], c = N[child];
    if (p && c && c.parentNode === p) { p.removeChild(c); dropNode(c); }
    return ok(PUnit, w);
  },
  clearChildren(parent, w) {
    const g = Q(), p = g.nodes[parent];
    if (p) {
      const N = g.nodes, F = (g.free ||= []);
      for (let c = p.firstChild; c; c = c.nextSibling) {
        if (c.__qedTmpl) {
          const id = c.__qedId;
          if (id !== undefined && N[id] === c) { N[id] = null; c.__qedId = undefined; F.push(id); }
          c.__qedSlots = undefined;
        } else {
          dropNode(c);
        }
      }
      p.textContent = '';
    }
    return ok(PUnit, w);
  },
  mountRoot(node, w) { const root = document.getElementById('app'), el = Q().nodes[node]; if (root && el) root.replaceChildren(el); return ok(PUnit, w); },
  isConnected(node, w) { const el = Q().nodes[node]; return ok((el && el.isConnected) ? 1 : 0, w); },
  effect: fwd('effect'),
  effectResult: fwd('effectResult'),
  portSend(name, payload, w) { Q(); const p = globalThis.__qed.ports && globalThis.__qed.ports[name]; if (p) p(payload); return ok(PUnit, w); },
  bindSignal(node, name, w) { return bindSig(node, name, null, w); },
  bindSignalAttr: bindSig,
  getSigSlot(name, w) { return ok(Q().sigEv.get(name) || 0, w); },
  setSigSlot(name, slot, w) { Q().sigEv.set(name, slot); return ok(PUnit, w); },
  compileRowTmpl(protoNode, slotPaths, slotAttrs, evPaths, evNames, w) {
    const g = Q(), proto = g.nodes[protoNode];
    if (!proto) return ok(0, w);
    // Detach prototype subtree from node/managedAttrs tables; cloned rows only register their root.
    dropNode(proto);
    const n = slotPaths.length;
    const walkers = new Array(n), kinds = new Uint8Array(n);
    const attrNames = new Array(n), attrNSs = new Array(n), attrLocals = new Array(n);
    for (let i = 0; i < n; i++) {
      walkers[i] = makeWalker(slotPaths[i]);
      const a = slotAttrs[i];
      attrNames[i] = a;
      if (a === '') kinds[i] = 0;
      else if (a === 'class') kinds[i] = 1;
      else if (a === 'value') kinds[i] = 2;
      else {
        kinds[i] = 3;
        const ns = attrNS(a);
        attrNSs[i] = ns;
        attrLocals[i] = ns ? a.slice(a.indexOf(':') + 1) : a;
      }
    }
    const evN = evPaths.length, evWalkers = new Array(evN);
    for (let i = 0; i < evN; i++) {
      const wk = makeWalker(evPaths[i]);
      evWalkers[i] = wk;
      const target = wk(proto);
      if (target) target.setAttribute('data-qed-row-on-' + evNames[i], String(i));
    }
    const id = g.tmpls.length;
    g.tmpls.push({ proto, n, slotPaths, walkers, kinds, attrNames, attrNSs, attrLocals, evN, evWalkers, evNames });
    return ok(id, w);
  },
  mountTmplRow(tmplId, vals, w) {
    const tmpl = Q().tmpls[tmplId];
    if (!tmpl) return ok(0, w);
    return ok(nodeId(cloneAndInitRow(tmpl, vals)), w);
  },
  mountTmplRows(parent, tmplId, valsPerRow, w) {
    const g = Q(), p = g.nodes[parent], tmpl = g.tmpls[tmplId];
    const m = valsPerRow.length, ids = new Array(m);
    ids.r = 1;
    if (!p || !tmpl) { ids.fill(0); return ok(ids, w); }
    const N = g.nodes, F = (g.free ||= []);
    const frag = document.createDocumentFragment();
    for (let i = 0; i < m; i++) {
      const el = cloneAndInitRow(tmpl, valsPerRow[i]);
      const slot = F.length > 0 ? F.pop() : N.length;
      N[slot] = el;
      el.__qedId = slot;
      ids[i] = slot;
      frag.appendChild(el);
    }
    p.appendChild(frag);
    return ok(ids, w);
  },
  patchTmplRow(node, tmplId, newVals, oldVals, w) {
    const g = Q(), el = g.nodes[node], tmpl = g.tmpls[tmplId];
    if (!el || !tmpl) return ok(PUnit, w);
    const slots = el.__qedSlots;
    if (!slots) return ok(PUnit, w);
    const n = tmpl.n, kinds = tmpl.kinds, attrNames = tmpl.attrNames, attrNSs = tmpl.attrNSs, attrLocals = tmpl.attrLocals;
    for (let j = 0; j < n; j++) {
      const v = newVals[j];
      if (oldVals && oldVals[j] === v) continue;
      writeSlot(slots[j], kinds[j], attrNames[j], attrNSs[j], attrLocals[j], v);
    }
    return ok(PUnit, w);
  },
  hydrateTmplRow(node, tmplId, w) {
    const g = Q(), el = g.nodes[node], tmpl = g.tmpls[tmplId];
    if (!el || !tmpl) return ok(PUnit, w);
    const n = tmpl.n, slots = new Array(n);
    for (let j = 0; j < n; j++) {
      slots[j] = tmpl.kinds[j] === 0 ? walkOrCreateText(el, tmpl.slotPaths[j]) : tmpl.walkers[j](el);
    }
    for (let j = 0; j < tmpl.evN; j++) {
      const target = tmpl.evWalkers[j](el);
      if (target) {
        target.removeAttribute('data-qed-on-' + tmpl.evNames[j]);
        target.setAttribute('data-qed-row-on-' + tmpl.evNames[j], String(j));
      }
    }
    el.__qedSlots = slots;
    el.__qedTmpl = true;
    return ok(PUnit, w);
  },
  wsOpen(connId, url, isBin, w) { const fn = Q().wsOpen; if (fn) fn(connId, url, !!isBin); return ok(PUnit, w); },
  wsSendBytes: fwd('wsSendBytes'),
  wsSendText: fwd('wsSendText'),
  wsClose: fwd('wsClose'),
};
