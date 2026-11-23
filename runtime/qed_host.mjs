import * as initialApp from './app.mjs';
import * as $ from './qed_rt.mjs';
import { dom, applySignalToEl } from './qed_dom.mjs';

const W = 0;
const textEnc = new TextEncoder(), textDec = new TextDecoder();
const resolveWsUrl = (u) => u.startsWith('/') ? (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + u : u;

let active = null;
let currentApp = null;
let listenersBound = false;
const attached = new Set();

const remount = (app = currentApp, stateJson, localsJson, isTimeTravel = false) => {
  if (!app) return null;
  if (active) active.teardown();
  const root = document.getElementById('app');
  if (root) root.innerHTML = '';
  document.getElementById('qed-state')?.remove();
  if (typeof stateJson === 'string' && stateJson.length > 0) globalThis.__qedHmrState = stateJson;
  const next = mountApp(app, isTimeTravel);
  if (localsJson && localsJson !== '{}') { try { next.restore(localsJson); } catch (_) {} }
  return next;
};
if (typeof window !== 'undefined') window.__qedHost = { remount, active: () => active };

function bindRootListeners() {
  if (listenersBound) return;
  listenersBound = true;
  window.addEventListener('pagehide', () => { if (active) active.teardown(); });
  window.addEventListener('popstate', () => { if (active) active.urlChanged(location.pathname + location.search); });
}

function ensureEvent(event) {
  const root = document.getElementById('app');
  if (!root || attached.has(event)) return;
  attached.add(event);
  const payloadFor = (ev, t, e) => {
    if (ev === 'keydown' || ev === 'keyup' || ev === 'keypress') return e.key;
    if (ev === 'change' && t.type === 'checkbox') return t.checked ? 'true' : 'false';
    return (t.value !== undefined && t.value !== null) ? String(t.value) : '';
  };
  root.addEventListener(event, (e) => {
    if (!active) return;
    const et = e.target; if (!et || !et.closest) return;
    if (event === 'click' && e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey) {
      const a = et.closest('a[href], [data-qed-link]');
      if (a && !a.target && !a.hasAttribute('download')) {
        const href = a.getAttribute('href') || '';
        if (a.hasAttribute('data-qed-link') || (href.startsWith('/') && !href.startsWith('//'))) {
          e.preventDefault(); history.pushState({}, '', href); active.urlChanged(href); return;
        }
      }
    }
    const nt = et.closest('[data-qed-on-' + event + ']');
    if (nt) { if (event === 'submit') e.preventDefault(); const id = parseInt(nt.getAttribute('data-qed-on-' + event), 10); if (!Number.isNaN(id)) active.fire(nt, id); }
    const rt = et.closest('[data-qed-row-on-' + event + ']');
    if (rt) {
      if (event === 'submit') e.preventDefault();
      const evIdx = rt.getAttribute('data-qed-row-on-' + event);
      const list = rt.closest('[data-qed-list]');
      if (evIdx !== null && list) {
        const listId = parseInt(list.getAttribute('data-qed-list'), 10);
        let row = rt;
        while (row && row.parentNode !== list) row = row.parentNode;
        if (row && !Number.isNaN(listId)) {
          let rowIdx = 0;
          for (let p = row.previousSibling; p; p = p.previousSibling) rowIdx++;
          active.fireStr(rt, listId, evIdx + ':' + rowIdx);
        }
      }
    }
    const vt = et.closest('[data-qed-onv-' + event + ']');
    if (vt) { const id = parseInt(vt.getAttribute('data-qed-onv-' + event), 10); if (!Number.isNaN(id)) active.fireStr(vt, id, payloadFor(event, vt, e)); }
  }, true);
}

function mountApp(app, isTimeTravel = false) {
  currentApp = app;
  $.registerDom(dom);
  $.assertExterns(app.__externs, $);
  bindRootListeners();

  let disposed = false;
  const aborts = new Map();
  const emitDev = (ev, extra) => {
    const h = typeof window !== 'undefined' && window.__qedDevHook;
    if (!h) return;
    let state = '', locals = '';
    try { state = dehydrate() || ''; } catch (_) {}
    try { locals = localSnapshot() || ''; } catch (_) {}
    h(ev, { ...extra, state, locals, ts: Date.now() });
  };
  const wrap = (fn, kind, meta) => (...a) => {
    const r = fn(...a, W);
    if (typeof window !== 'undefined' && window.__qedDevHook) emitDev('action', { kind, ...meta(...a), inFlightHttp: aborts.size });
    return r;
  };
  const init             = () => app.qed_init(W);
  const dispatch         = wrap(app.qed_dispatch, 'dispatch', (id) => ({ id }));
  const dispatchStr      = wrap(app.qed_dispatch_str, 'dispatchStr', (id, value) => ({ id, value }));
  const streamChunk      = (cid, data) => app.qed_stream_chunk(cid, data, W);
  const streamDone       = wrap(app.qed_stream_done, 'streamDone', (id) => ({ id }));
  const httpDone         = wrap(app.qed_http_done, 'http', (id, ok) => ({ id, ok: !!ok }));
  const httpBytesDone    = wrap(app.qed_http_bytes_done, 'httpBytes', (id, ok) => ({ id, ok: !!ok }));
  const urlChanged       = wrap(app.qed_url_changed, 'url', (path) => ({ path }));
  const localDispatch    = wrap(app.qed_local_dispatch, 'local', (key, id) => ({ key, id }));
  const localDispatchStr = wrap(app.qed_local_dispatch_str, 'localStr', (key, id, value) => ({ key, id, value }));
  const localSnapshot    = () => $.ioVal(app.qed_local_snapshot(W));
  const localRestore     = (s) => app.qed_local_restore(s, W);
  const dehydrate        = () => (typeof app.qed_dehydrate === 'function' ? $.ioVal(app.qed_dehydrate(W)) : '');
  const effectDone       = wrap(app.qed_effect_done, 'effect', (id) => ({ id }));
  const portRecv         = wrap(app.qed_port_recv, 'port', (name) => ({ name }));
  const wsOpen           = (cid) => app.qed_ws_open(cid, W);
  const wsBytes          = wrap(app.qed_ws_bytes, 'wsBytes', (cid) => ({ cid }));
  const wsText           = wrap(app.qed_ws_text, 'wsText', (cid) => ({ cid }));
  const wsClose          = (cid, err, nowMs) => app.qed_ws_close(cid, err, BigInt(nowMs), W);

  const g = (globalThis.__qed ||= {});
  g.nodes = [null];
  g.sig = new Map();
  g.sigVals = new Map();

  const trackAbort = (k) => { const c = new AbortController(); aborts.set(k, c); return c.signal; };
  const timers = {};
  const rawTimers = new Set();
  const wsConns = new Map();

  g.fetchStream = (url, body, cid, did) => {
    const k = 's:' + did;
    fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body, signal: trackAbort(k) }).then(async (resp) => {
      if (disposed) return;
      if (!resp.ok || !resp.body) { streamDone(did); return; }
      const reader = resp.body.getReader(), dec = new TextDecoder();
      for (;;) {
        const { done, value } = await reader.read(); if (done || disposed) break;
        const t = dec.decode(value, { stream: true }); if (t) streamChunk(cid, t);
      }
      if (!disposed) {
        const tail = dec.decode(); if (tail) streamChunk(cid, tail);
        streamDone(did);
      }
    }).catch(() => { if (!disposed) streamDone(did); }).finally(() => aborts.delete(k));
  };
  const sendHttp = (method, url, body, id, headers, read, done, errVal) => {
    const k = String(id), opts = { method, headers, signal: trackAbort(k) };
    if (method !== 'GET' && method !== 'HEAD') opts.body = body;
    fetch(url, opts).then(async (r) => { const v = await read(r); if (!disposed) done(id, r.ok ? 1 : 0, v); })
      .catch((e) => { if (!disposed) done(id, 0, errVal(e)); }).finally(() => aborts.delete(k));
  };
  g.httpSend = (m, u, b, id) => sendHttp(m, u, b, id, { 'Content-Type': 'application/json' }, (r) => r.text(), httpDone, String);
  g.httpSendBytes = (m, u, b, id) => sendHttp(m, u, b, id, { 'Content-Type': 'application/x-protobuf', 'Accept': 'application/x-protobuf' }, async (r) => new Uint8Array(await r.arrayBuffer()), httpBytesDone, (e) => textEnc.encode(String(e)));
  g.setSignal = (name, v) => {
    const s = String(v); g.sigVals.set(name, s); const b = g.sig.get(name);
    if (b && b.el && b.el.isConnected) applySignalToEl(b.el, b.attr, s);
  };
  g.effect = (kind, a, b, c) => {
    if (disposed) return;
    switch (kind) {
      case 'timer.cancel': if (timers[a]) { clearTimeout(timers[a]); delete timers[a]; } break;
      case 'http.abort': { const ac = aborts.get(a); if (ac) ac.abort(); break; }
      case 'storage.set': try { localStorage.setItem(a, b); } catch (_) {} break;
      case 'storage.remove': try { localStorage.removeItem(a); } catch (_) {} break;
      case 'storage.clear': try { localStorage.clear(); } catch (_) {} break;
      case 'history.replace': history.replaceState({}, '', a); urlChanged(a); break;
      case 'history.back': history.back(); break;
      case 'history.forward': history.forward(); break;
      case 'clipboard.write': if (navigator.clipboard) navigator.clipboard.writeText(a).catch(() => {}); break;
      case 'dom.focus': { const el = document.getElementById(a); if (el) el.focus(); break; }
      case 'dom.blur': { const el = document.getElementById(a); if (el) el.blur(); break; }
      case 'dom.select': { const el = document.getElementById(a); if (el && el.select) el.select(); break; }
      case 'dom.scrollIntoView': { const el = document.getElementById(a); if (el) el.scrollIntoView({ behavior: 'smooth' }); break; }
      case 'document.title': document.title = a; break;
      case 'signal.set': g.setSignal(a, b); break;
      case 'event.listen': ensureEvent(a); break;
      case 'file.download': { const url = URL.createObjectURL(new Blob([c], { type: b || 'text/plain' }));
        const el = document.createElement('a'); el.href = url; el.download = a; el.click();
        setTimeout(() => URL.revokeObjectURL(url), 1000); break; }
      case 'css.inject': {
        if (a && !document.querySelector('link[data-qed-styles]')) {
          let s = document.getElementById('qed-styles');
          if (!s) { s = document.createElement('style'); s.id = 'qed-styles'; document.head.appendChild(s); }
          if (s.textContent !== a) s.textContent = a;
        }
        break;
      }
      default: console.warn('qed: unknown effect', kind);
    }
  };
  const toB64 = (buf) => {
    const bytes = new Uint8Array(buf), step = 24576; let out = '';
    for (let i = 0; i < bytes.length; i += step) {
      const slice = bytes.subarray(i, Math.min(i + step, bytes.length));
      let bin = ''; for (let j = 0; j < slice.length; j++) bin += String.fromCharCode(slice[j]);
      out += btoa(bin);
    }
    return out;
  };
  const pickFile = (accept, id, maxBytes, asBytes) => {
    const input = document.createElement('input'); input.type = 'file'; if (accept) input.accept = accept;
    const reply = (v) => { if (!disposed) effectDone(id, typeof v === 'string' ? v : JSON.stringify(v)); };
    input.addEventListener('cancel', () => reply('{"error":"cancelled"}'));
    input.onchange = () => {
      const f = input.files && input.files[0]; if (!f) { reply('{"error":"cancelled"}'); return; }
      if (asBytes && maxBytes > 0 && f.size > maxBytes) { reply({ error: `file too large (${f.size} bytes; max ${maxBytes})` }); return; }
      const fail = () => reply('{"error":"read failed"}');
      const done = (v) => reply(asBytes ? { name: f.name, mime: f.type, size: f.size, base64: toB64(v) } : { name: f.name, mime: f.type, size: f.size, text: String(v) });
      if (asBytes && typeof f.arrayBuffer === 'function') f.arrayBuffer().then(done).catch(fail);
      else { const r = new FileReader(); r.onload = () => done(r.result); r.onerror = fail; asBytes ? r.readAsArrayBuffer(f) : r.readAsText(f); }
    };
    input.click();
  };
  g.effectResult = (kind, a, b, id) => {
    if (disposed) return;
    switch (kind) {
      case 'storage.get': { let v = null; try { v = localStorage.getItem(a); } catch (_) {} effectDone(id, JSON.stringify(v)); break; }
      case 'clipboard.read': (navigator.clipboard ? navigator.clipboard.readText() : Promise.resolve('')).then((t) => { if (!disposed) effectDone(id, t); }).catch(() => { if (!disposed) effectDone(id, ''); }); break;
      case 'timer.after': { const tid = setTimeout(() => { rawTimers.delete(tid); if (!disposed) effectDone(id, ''); }, parseInt(a, 10) || 0); rawTimers.add(tid); break; }
      case 'timer.afterKeyed': { if (timers[a]) clearTimeout(timers[a]); timers[a] = setTimeout(() => { delete timers[a]; if (!disposed) effectDone(id, ''); }, parseInt(b, 10) || 0); break; }
      case 'random.int': { const lo = parseInt(a, 10) || 0, hi = parseInt(b, 10) || 0; effectDone(id, String(lo + Math.floor(Math.random() * (hi - lo + 1)))); break; }
      case 'file.pick': pickFile(a, id, 0, false); break;
      case 'file.pickBytes': pickFile(a, id, parseInt(b, 10) || 0, true); break;
      default: console.warn('qed: unknown result effect', kind);
    }
  };
  g.ports ||= {};
  g.send = (name, payload) => { if (!disposed) portRecv(name, String(payload)); };

  g.wsOpen = (cid, url, isBinary) => {
    if (disposed) return;
    let ws;
    try { ws = new WebSocket(resolveWsUrl(url)); }
    catch (err) { wsClose(cid, String(err), Date.now()); return; }
    if (isBinary) ws.binaryType = 'arraybuffer';
    wsConns.set(cid, ws);
    ws.onopen = () => { if (!disposed && wsConns.get(cid) === ws) wsOpen(cid); };
    ws.onmessage = (e) => {
      if (disposed || wsConns.get(cid) !== ws) return;
      if (isBinary) {
        if (e.data instanceof ArrayBuffer) wsBytes(cid, new Uint8Array(e.data));
        else if (e.data instanceof Blob) e.data.arrayBuffer().then((ab) => { if (!disposed && wsConns.get(cid) === ws) wsBytes(cid, new Uint8Array(ab)); });
        else wsBytes(cid, textEnc.encode(String(e.data)));
      } else {
        wsText(cid, typeof e.data === 'string' ? e.data : textDec.decode(new Uint8Array(e.data)));
      }
    };
    ws.onerror = () => {};
    ws.onclose = () => {
      if (disposed || wsConns.get(cid) !== ws) return;
      wsConns.delete(cid);
      wsClose(cid, '', Date.now());
    };
  };
  const wsSend = (cid, data) => { const ws = wsConns.get(cid); if (ws && ws.readyState === 1) ws.send(data); };
  g.wsSendBytes = (cid, payload) => wsSend(cid, payload instanceof Uint8Array ? payload : new Uint8Array(0));
  g.wsSendText = (cid, text) => wsSend(cid, String(text));
  g.wsClose = (cid) => {
    const ws = wsConns.get(cid);
    if (!ws) return;
    wsConns.delete(cid);
    try { ws.close(); } catch (_) {}
  };

  const fire = (t, id) => { const lh = t.closest('[data-qed-local]'); if (lh) localDispatch(lh.getAttribute('data-qed-local'), id); else dispatch(id); };
  const fireStr = (t, id, v) => { const lh = t.closest('[data-qed-local]'); if (lh) localDispatchStr(lh.getAttribute('data-qed-local'), id, v); else dispatchStr(id, v); };
  ensureEvent('click');

  const teardown = () => {
    disposed = true;
    for (const c of aborts.values()) c.abort();
    aborts.clear();
    for (const k of Object.keys(timers)) { clearTimeout(timers[k]); delete timers[k]; }
    for (const tid of rawTimers) clearTimeout(tid);
    rawTimers.clear();
    for (const ws of wsConns.values()) { try { ws.close(); } catch (_) {} }
    wsConns.clear();
  };

  const api = { init, dispatch, dispatchStr, urlChanged, snapshot: localSnapshot, restore: localRestore, dehydrate };
  active = { ...api, fire, fireStr, teardown };
  window.qed = api;

  app.__main(W);
  init();
  emitDev('mount', { isTimeTravel });
  return active;
}

export function boot() {
  mountApp(initialApp);
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
}
