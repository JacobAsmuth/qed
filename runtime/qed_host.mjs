import * as initialApp from './app.mjs';
import * as $ from './qed_rt.mjs';
import { dom, applySignalToEl } from './qed_dom.mjs';

const W = 0, textEnc = new TextEncoder(), textDec = new TextDecoder();
const resolveWsUrl = (u) => u.startsWith('/') ? (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + u : u;
const tryRun = (fn, fb) => { try { return fn(); } catch (_) { return fb; } };
const intAttr = (el, a) => { const n = parseInt(el.getAttribute(a), 10); return Number.isNaN(n) ? null : n; };
const int0 = (s) => parseInt(s, 10) || 0;
const payloadFor = (ev, t, e) => (ev === 'keydown' || ev === 'keyup' || ev === 'keypress') ? e.key
  : (ev === 'change' && t.type === 'checkbox') ? (t.checked ? 'true' : 'false') : (t.value != null ? String(t.value) : '');

let active = null, currentApp = null, listenersBound = false;
const attached = new Set();
const remount = (app = currentApp, stateJson, localsJson, isTimeTravel = false) => {
  if (!app) return null;
  active?.teardown();
  const root = document.getElementById('app'); if (root) root.innerHTML = '';
  document.getElementById('qed-state')?.remove();
  if (typeof stateJson === 'string' && stateJson.length > 0) globalThis.__qedHmrState = stateJson;
  const next = mountApp(app, isTimeTravel);
  if (localsJson && localsJson !== '{}') tryRun(() => next.restore(localsJson));
  return next;
};
if (typeof window !== 'undefined') window.__qedHost = { remount, active: () => active };

function ensureEvent(event) {
  const root = document.getElementById('app');
  if (!root || attached.has(event)) return;
  attached.add(event);
  const onA = 'data-qed-on-' + event, rowA = 'data-qed-row-on-' + event, onvA = 'data-qed-onv-' + event;
  root.addEventListener(event, (e) => {
    const et = active && e.target;
    if (!et?.closest) return;
    if (event === 'click' && e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey) {
      const a = et.closest('a[href], [data-qed-link]'), href = a && !a.target && !a.hasAttribute('download') && !a.hasAttribute('data-qed-external') ? (a.getAttribute('href') || '') : null;
      if (href !== null && !href.startsWith('/_qed/') && (a.hasAttribute('data-qed-link') || (href.startsWith('/') && !href.startsWith('//')))) { e.preventDefault(); history.pushState({}, '', href); active.urlChanged(href); return; }
    }
    const nt = et.closest(`[${onA}]`);
    if (nt) { if (event === 'submit') e.preventDefault(); const id = intAttr(nt, onA); if (id !== null) active.fire(nt, id); }
    const rt = et.closest(`[${rowA}]`), list = rt?.closest('[data-qed-list]');
    if (rt && event === 'submit') e.preventDefault();
    if (list) {
      const evIdx = rt.getAttribute(rowA), listId = intAttr(list, 'data-qed-list');
      let row = rt, rowIdx = 0;
      while (row && row.parentNode !== list) row = row.parentNode;
      if (evIdx !== null && row && listId !== null) { for (let p = row.previousSibling; p; p = p.previousSibling) rowIdx++; active.fire(rt, listId, evIdx + ':' + rowIdx); }
    }
    const vt = et.closest(`[${onvA}]`);
    if (vt) { const id = intAttr(vt, onvA); if (id !== null) active.fire(vt, id, payloadFor(event, vt, e)); }
  }, true);
}

function mountApp(app, isTimeTravel = false) {
  currentApp = app; $.registerDom(dom); $.assertExterns(app.__externs, $);
  if (!listenersBound) {
    listenersBound = true;
    window.addEventListener('pagehide', () => active?.teardown());
    window.addEventListener('popstate', () => active?.urlChanged(location.pathname + location.search));
  }
  let disposed = false;
  const aborts = new Map(), timers = {}, rawTimers = new Set(), wsConns = new Map();
  const init = () => app.qed_init(W), localSnapshot = () => $.ioVal(app.qed_local_snapshot(W)), localRestore = (s) => app.qed_local_restore(s, W);
  const dehydrate = () => (typeof app.qed_dehydrate === 'function' ? $.ioVal(app.qed_dehydrate(W)) : '');
  const emitDev = (ev, extra) => typeof window !== 'undefined' && window.__qedDevHook?.(ev, { ...extra, state: tryRun(dehydrate, '') || '', locals: tryRun(localSnapshot, '') || '', ts: Date.now() });
  const w = (fn, kind, ...keys) => (...a) => {
    const r = app['qed_' + fn](...a, W);
    if (typeof window !== 'undefined' && window.__qedDevHook) emitDev('action', { kind, inFlightHttp: aborts.size, ...Object.fromEntries(keys.map((k, i) => [k, k === 'ok' ? !!a[i] : a[i]])) });
    return r;
  };
  const dispatch = w('dispatch', 'dispatch', 'id'), dispatchStr = w('dispatch_str', 'dispatchStr', 'id', 'value');
  const httpDone = w('http_done', 'http', 'id', 'ok'), httpBytesDone = w('http_bytes_done', 'httpBytes', 'id', 'ok');
  const urlChanged = w('url_changed', 'url', 'path'), effectDone = w('effect_done', 'effect', 'id'), streamDone = w('stream_done', 'streamDone', 'id');
  const localDispatch = w('local_dispatch', 'local', 'key', 'id'), localDispatchStr = w('local_dispatch_str', 'localStr', 'key', 'id', 'value');
  const portRecv = w('port_recv', 'port', 'name'), wsBytes = w('ws_bytes', 'wsBytes', 'cid'), wsText = w('ws_text', 'wsText', 'cid');

  const g = (globalThis.__qed ||= {});
  g.nodes = [null]; g.free = []; g.sig = new Map(); g.sigVals = new Map(); g.ports ||= {};
  const trackAbort = (k) => { const c = new AbortController(); aborts.set(k, c); return c.signal; };
  const clearKeyed = (k) => { if (timers[k]) { clearTimeout(timers[k]); delete timers[k]; } };

  g.fetchStream = (url, body, cid, did) => {
    const k = 's:' + did;
    fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body, signal: trackAbort(k) }).then(async (resp) => {
      if (disposed) return;
      if (!resp.ok || !resp.body) return streamDone(did);
      const reader = resp.body.getReader(), dec = new TextDecoder();
      for (;;) { const { done, value } = await reader.read(); if (done || disposed) break; const t = dec.decode(value, { stream: true }); if (t) app.qed_stream_chunk(cid, t, W); }
      if (!disposed) { const tail = dec.decode(); if (tail) app.qed_stream_chunk(cid, tail, W); streamDone(did); }
    }).catch(() => !disposed && streamDone(did)).finally(() => aborts.delete(k));
  };
  const sendHttp = (method, url, body, id, headers, read, done, errVal) => {
    const k = String(id), opts = { method, headers, signal: trackAbort(k), ...(method !== 'GET' && method !== 'HEAD' ? { body } : {}) };
    fetch(url, opts).then(async (r) => { const v = await read(r); if (!disposed) done(id, r.ok ? 1 : 0, v); })
      .catch((e) => !disposed && done(id, 0, errVal(e))).finally(() => aborts.delete(k));
  };
  g.httpSend = (m, u, b, id) => sendHttp(m, u, b, id, { 'Content-Type': 'application/json' }, (r) => r.text(), httpDone, String);
  g.httpSendBytes = (m, u, b, id) => sendHttp(m, u, b, id, { 'Content-Type': 'application/x-protobuf', Accept: 'application/x-protobuf' },
    async (r) => new Uint8Array(await r.arrayBuffer()), httpBytesDone, (e) => textEnc.encode(String(e)));
  g.setSignal = (name, v) => { const s = String(v), b = (g.sigVals.set(name, s), g.sig.get(name)); if (b?.el?.isConnected) applySignalToEl(b.el, b.attr, s); };

  g.effect = (kind, a, b, c) => {
    if (disposed) return;
    switch (kind) {
      case 'timer.cancel': clearKeyed(a); break;
      case 'http.abort': aborts.get(a)?.abort(); break;
      case 'storage.set': case 'storage.remove': case 'storage.clear':
        tryRun(() => kind.endsWith('t') ? localStorage.setItem(a, b) : kind.endsWith('e') ? localStorage.removeItem(a) : localStorage.clear()); break;
      case 'history.replace': history.replaceState({}, '', a); urlChanged(a); break;
      case 'location.assign': if (/^(?:https?:\/\/|mailto:|tel:|\/(?![/\\])|[#?])/.test(a)) location.assign(a); break;
      case 'history.back': case 'history.forward': history[kind.slice(8)](); break;
      case 'clipboard.write': navigator.clipboard?.writeText(a).catch(() => {}); break;
      case 'dom.focus': case 'dom.blur': case 'dom.select': document.getElementById(a)?.[kind.slice(4)]?.(); break;
      case 'dom.scrollIntoView': document.getElementById(a)?.scrollIntoView({ behavior: 'smooth' }); break;
      case 'document.title': document.title = a; break;
      case 'signal.set': g.setSignal(a, b); break;
      case 'event.listen': ensureEvent(a); break;
      case 'file.download': { const u = URL.createObjectURL(new Blob([c], { type: b || 'text/plain' })); Object.assign(document.createElement('a'), { href: u, download: a }).click(); setTimeout(() => URL.revokeObjectURL(u), 1000); break; }
      case 'css.inject': if (a && !document.querySelector('link[data-qed-styles]')) {
        const s = document.getElementById('qed-styles') || document.head.appendChild(Object.assign(document.createElement('style'), { id: 'qed-styles' })); if (s.textContent !== a) s.textContent = a; } break;
      default: console.warn('qed: unknown effect', kind);
    }
  };
  const toB64 = (buf) => { const b = new Uint8Array(buf); let out = ''; for (let i = 0; i < b.length; i += 12288) out += btoa(String.fromCharCode(...b.subarray(i, i + 12288))); return out; };
  const pickFile = (accept, id, maxBytes, asBytes) => {
    const input = Object.assign(document.createElement('input'), { type: 'file', ...(accept ? { accept } : {}) });
    const reply = (v) => !disposed && effectDone(id, typeof v === 'string' ? v : JSON.stringify(v));
    const cancel = () => reply('{"error":"cancelled"}');
    input.addEventListener('cancel', cancel);
    input.onchange = () => {
      const f = input.files?.[0]; if (!f) return cancel();
      if (asBytes && maxBytes > 0 && f.size > maxBytes) return reply({ error: `file too large (${f.size} bytes; max ${maxBytes})` });
      const fail = () => reply('{"error":"read failed"}');
      const done = (v) => reply({ name: f.name, mime: f.type, size: f.size, ...(asBytes ? { base64: toB64(v) } : { text: String(v) }) });
      if (asBytes && typeof f.arrayBuffer === 'function') f.arrayBuffer().then(done, fail);
      else { const r = new FileReader(); r.onload = () => done(r.result); r.onerror = fail; asBytes ? r.readAsArrayBuffer(f) : r.readAsText(f); }
    };
    input.click();
  };
  g.effectResult = (kind, a, b, id) => {
    if (disposed) return;
    switch (kind) {
      case 'storage.get': effectDone(id, JSON.stringify(tryRun(() => localStorage.getItem(a), null))); break;
      case 'clipboard.read': (navigator.clipboard ? navigator.clipboard.readText() : Promise.resolve('')).then((t) => !disposed && effectDone(id, t), () => !disposed && effectDone(id, '')); break;
      case 'timer.after': { const tid = setTimeout(() => { rawTimers.delete(tid); if (!disposed) effectDone(id, ''); }, int0(a)); rawTimers.add(tid); break; }
      case 'timer.afterKeyed': clearKeyed(a); timers[a] = setTimeout(() => { delete timers[a]; if (!disposed) effectDone(id, ''); }, int0(b)); break;
      case 'random.int': { const lo = int0(a), hi = int0(b); effectDone(id, String(lo + Math.floor(Math.random() * (hi - lo + 1)))); break; }
      case 'file.pick': pickFile(a, id, 0, false); break;
      case 'file.pickBytes': pickFile(a, id, int0(b), true); break;
      default: console.warn('qed: unknown result effect', kind);
    }
  };
  g.send = (name, payload) => !disposed && portRecv(name, String(payload));
  g.wsOpen = (cid, url, isBin) => {
    if (disposed) return;
    let ws;
    try { ws = new WebSocket(resolveWsUrl(url)); } catch (err) { return app.qed_ws_close(cid, String(err), BigInt(Date.now()), W); }
    if (isBin) ws.binaryType = 'arraybuffer';
    wsConns.set(cid, ws);
    const live = () => !disposed && wsConns.get(cid) === ws;
    ws.onopen = () => live() && app.qed_ws_open(cid, W); ws.onerror = () => {};
    ws.onmessage = ({ data }) => {
      if (!live()) return;
      if (!isBin) return wsText(cid, typeof data === 'string' ? data : textDec.decode(new Uint8Array(data)));
      if (data instanceof Blob) data.arrayBuffer().then((ab) => live() && wsBytes(cid, new Uint8Array(ab)));
      else wsBytes(cid, data instanceof ArrayBuffer ? new Uint8Array(data) : textEnc.encode(String(data)));
    };
    ws.onclose = () => { if (live()) { wsConns.delete(cid); app.qed_ws_close(cid, '', BigInt(Date.now()), W); } };
  };
  const wsSend = (cid, data) => { const ws = wsConns.get(cid); if (ws?.readyState === 1) ws.send(data); };
  g.wsSendBytes = (cid, p) => wsSend(cid, p instanceof Uint8Array ? p : new Uint8Array(0)); g.wsSendText = (cid, t) => wsSend(cid, String(t));
  g.wsClose = (cid) => { const ws = wsConns.get(cid); if (ws) { wsConns.delete(cid); tryRun(() => ws.close()); } };

  const fire = (t, id, ...v) => {
    const k = t.closest('[data-qed-local]')?.getAttribute('data-qed-local');
    return v.length ? (k != null ? localDispatchStr(k, id, v[0]) : dispatchStr(id, v[0])) : (k != null ? localDispatch(k, id) : dispatch(id));
  };
  ensureEvent('click');
  const teardown = () => {
    disposed = true;
    for (const c of aborts.values()) c.abort(); aborts.clear();
    for (const k of Object.keys(timers)) clearKeyed(k);
    for (const tid of rawTimers) clearTimeout(tid); rawTimers.clear();
    for (const ws of wsConns.values()) tryRun(() => ws.close()); wsConns.clear();
  };
  const api = { init, dispatch, dispatchStr, urlChanged, snapshot: localSnapshot, restore: localRestore, dehydrate };
  active = { ...api, fire, teardown }; window.qed = api;
  app.__main(W); init(); emitDev('mount', { isTimeTravel });
  return active;
}

let oneTapStarted = false;
function initGoogleOneTap() {
  if (oneTapStarted || typeof document === 'undefined' || !document.querySelector('a[href^="/_qed/auth/login"]')) return;
  oneTapStarted = true;
  fetch('/_qed/auth/onetap', { credentials: 'same-origin' })
    .then((r) => (r.ok ? r.json() : null))
    .then((cfg) => {
      if (!cfg?.enabled || !cfg.clientId || !cfg.nonce) return;
      const start = () => {
        const gsi = globalThis.google?.accounts?.id;
        if (!gsi) return;
        gsi.initialize({
          client_id: cfg.clientId,
          nonce: cfg.nonce,
          use_fedcm_for_prompt: true,
          auto_select: false,
          callback: (resp) => {
            if (!resp?.credential) return;
            fetch('/_qed/auth/onetap', {
              method: 'POST',
              credentials: 'same-origin',
              headers: { 'Content-Type': 'application/json' },
              body: JSON.stringify({ credential: resp.credential }),
            }).then((res) => { if (res.ok) location.reload(); }).catch(() => {});
          },
        });
        gsi.prompt();
      };
      if (globalThis.google?.accounts?.id) return start();
      const s = document.createElement('script');
      s.src = 'https://accounts.google.com/gsi/client';
      s.async = true; s.defer = true; s.onload = start;
      document.head.appendChild(s);
    })
    .catch(() => {});
}

export function boot() { mountApp(initialApp); initGoogleOneTap(); }
if (typeof document !== 'undefined') document.readyState === 'loading' ? document.addEventListener('DOMContentLoaded', boot) : boot();
