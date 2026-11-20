import * as app from './app.mjs';
import * as $ from './qed_rt.mjs';
import { dom } from './qed_dom.mjs';

export function boot() {
  $.registerDom(dom);
  $.assertExterns(app.__externs, $);
  const W = 0;
  const init        = () => app.qed_init(W);
  const dispatch    = (id) => app.qed_dispatch(id, W);
  const dispatchStr = (id, v) => app.qed_dispatch_str(id, v, W);
  const streamChunk = (cid, data) => app.qed_stream_chunk(cid, data, W);
  const streamDone    = (did) => app.qed_stream_done(did, W);
  const httpDone      = (id, ok, text) => app.qed_http_done(id, ok, text, W);
  const httpBytesDone = (id, ok, bytes) => app.qed_http_bytes_done(id, ok, bytes, W);
  const urlChanged    = (path) => app.qed_url_changed(path, W);
  const localDispatch    = (key, id) => app.qed_local_dispatch(key, id, W);
  const localDispatchStr = (key, id, v) => app.qed_local_dispatch_str(key, id, v, W);
  const localSnapshot = () => $.ioVal(app.qed_local_snapshot(W));
  const localRestore  = (s) => app.qed_local_restore(s, W);
  const effectDone  = (id, result) => app.qed_effect_done(id, result, W);
  const portRecv    = (name, payload) => app.qed_port_recv(name, payload, W);
  const wsOpen      = (cid) => app.qed_ws_open(cid, W);
  const wsBytes     = (cid, bytes) => app.qed_ws_bytes(cid, bytes, W);
  const wsText      = (cid, text) => app.qed_ws_text(cid, text, W);
  const wsClose     = (cid, err, nowMs) => app.qed_ws_close(cid, err, BigInt(nowMs), W);

  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null]; g.sig ||= new Map(); g.sigVals ||= new Map();

  const textEnc = new TextEncoder(), textDec = new TextDecoder();
  // Thin browser AbortController handle table; HTTP timeout policy & single-settlement live in Lean (`Qed.Driver.Runtime`).
  const aborts = new Map();
  const trackAbort = (k) => { const c = new AbortController(); aborts.set(k, c); return c.signal; };
  window.addEventListener('pagehide', () => { for (const c of aborts.values()) c.abort(); });

  g.fetchStream = (url, body, cid, did) => {
    const k = 's:' + did;
    fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body, signal: trackAbort(k) }).then(async (resp) => {
      if (!resp.ok || !resp.body) { streamDone(did); return; }
      const reader = resp.body.getReader(), dec = new TextDecoder();
      for (;;) { const { done, value } = await reader.read(); if (done) break;
        const t = dec.decode(value, { stream: true }); if (t) streamChunk(cid, t); }
      const tail = dec.decode(); if (tail) streamChunk(cid, tail);
      streamDone(did);
    }).catch(() => streamDone(did)).finally(() => aborts.delete(k));
  };
  g.httpSend = (method, url, body, id) => {
    const k = String(id), opts = { method, headers: { 'Content-Type': 'application/json' }, signal: trackAbort(k) };
    if (method !== 'GET' && method !== 'HEAD') opts.body = body;
    fetch(url, opts).then(async (r) => { const t = await r.text(); httpDone(id, r.ok ? 1 : 0, t); })
      .catch((e) => httpDone(id, 0, String(e))).finally(() => aborts.delete(k));
  };
  g.httpSendBytes = (method, url, body, id) => {
    const k = String(id), opts = { method, headers: { 'Content-Type': 'application/x-protobuf', 'Accept': 'application/x-protobuf' }, signal: trackAbort(k) };
    if (method !== 'GET' && method !== 'HEAD') opts.body = body;
    fetch(url, opts).then(async (r) => {
      const buf = new Uint8Array(await r.arrayBuffer());
      httpBytesDone(id, r.ok ? 1 : 0, buf);
    }).catch((e) => httpBytesDone(id, 0, textEnc.encode(String(e)))).finally(() => aborts.delete(k));
  };
  g.setSignal = (name, v) => {
    const s = String(v); g.sigVals.set(name, s); const b = g.sig.get(name);
    if (!b || !b.el || !b.el.isConnected) return;
    if (b.attr === 'value') { if (b.el.value !== s) b.el.value = s; }
    else if (b.attr === 'checked') { const on = (s !== '' && s !== 'false'); if (b.el.checked !== on) b.el.checked = on; }
    else if (b.attr) { if (b.el.getAttribute(b.attr) !== s) b.el.setAttribute(b.attr, s); }
    else if (b.el.textContent !== s) b.el.textContent = s;
  };
  const timers = {};
  g.effect = (kind, a, b, c) => {
    switch (kind) {
      case 'timer.cancel': if (timers[a]) { clearTimeout(timers[a]); delete timers[a]; } break;
      case 'http.abort': { const c = aborts.get(a); if (c) c.abort(); break; }
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
      case 'css.inject': { if (a && !document.getElementById('qed-styles') && !document.querySelector('link[data-qed-styles]')) { const s = document.createElement('style'); s.id = 'qed-styles'; s.textContent = a; document.head.appendChild(s); } break; }
      default: console.warn('qed: unknown effect', kind);
    }
  };
  g.effectResult = (kind, a, b, id) => {
    switch (kind) {
      case 'storage.get': { let v = null; try { v = localStorage.getItem(a); } catch (_) {} effectDone(id, JSON.stringify(v)); break; }
      case 'clipboard.read': (navigator.clipboard ? navigator.clipboard.readText() : Promise.resolve('')).then((t) => effectDone(id, t)).catch(() => effectDone(id, '')); break;
      case 'timer.after': setTimeout(() => effectDone(id, ''), parseInt(a, 10) || 0); break;
      case 'timer.afterKeyed': { if (timers[a]) clearTimeout(timers[a]); timers[a] = setTimeout(() => { delete timers[a]; effectDone(id, ''); }, parseInt(b, 10) || 0); break; }
      case 'random.int': { const lo = parseInt(a, 10) || 0, hi = parseInt(b, 10) || 0; effectDone(id, String(lo + Math.floor(Math.random() * (hi - lo + 1)))); break; }
      case 'file.pick': { const input = document.createElement('input'); input.type = 'file'; if (a) input.accept = a;
        input.addEventListener('cancel', () => effectDone(id, '{"error":"cancelled"}'));
        input.onchange = () => { const f = input.files && input.files[0]; if (!f) { effectDone(id, '{"error":"cancelled"}'); return; }
          const reader = new FileReader(); reader.onload = () => effectDone(id, JSON.stringify({ name: f.name, mime: f.type, size: f.size, text: String(reader.result) }));
          reader.onerror = () => effectDone(id, '{"error":"read failed"}'); reader.readAsText(f); }; input.click(); break; }
      default: console.warn('qed: unknown result effect', kind);
    }
  };
  g.ports ||= {};
  g.send = (name, payload) => portRecv(name, String(payload));

  // Stateless browser WebSocket transport pipe; mux framing (`Qed.WsMuxFrame`), pool routing,
  // and reconnect policies (`Qed.Reconnect.nextDelayMs`) all execute in verified Lean.
  const resolveWsUrl = (u) => u.startsWith('/') ? (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + u : u;
  const wsConns = new Map();
  g.wsOpen = (cid, url, isBinary) => {
    let ws;
    try { ws = new WebSocket(resolveWsUrl(url)); }
    catch (err) { wsClose(cid, String(err), Date.now()); return; }
    if (isBinary) ws.binaryType = 'arraybuffer';
    wsConns.set(cid, ws);
    ws.onopen = () => { if (wsConns.get(cid) === ws) wsOpen(cid); };
    ws.onmessage = (e) => {
      if (wsConns.get(cid) !== ws) return;
      if (isBinary) {
        if (e.data instanceof ArrayBuffer) wsBytes(cid, new Uint8Array(e.data));
        else if (e.data instanceof Blob) e.data.arrayBuffer().then((ab) => { if (wsConns.get(cid) === ws) wsBytes(cid, new Uint8Array(ab)); });
        else wsBytes(cid, textEnc.encode(String(e.data)));
      } else {
        wsText(cid, typeof e.data === 'string' ? e.data : textDec.decode(new Uint8Array(e.data)));
      }
    };
    ws.onerror = () => {};
    ws.onclose = () => {
      if (wsConns.get(cid) !== ws) return;
      wsConns.delete(cid);
      wsClose(cid, '', Date.now());
    };
  };
  g.wsSendBytes = (cid, payload) => {
    const ws = wsConns.get(cid);
    if (ws && ws.readyState === 1) ws.send(payload instanceof Uint8Array ? payload : new Uint8Array(0));
  };
  g.wsSendText = (cid, text) => {
    const ws = wsConns.get(cid);
    if (ws && ws.readyState === 1) ws.send(String(text));
  };
  g.wsClose = (cid) => {
    const ws = wsConns.get(cid);
    if (!ws) return;
    wsConns.delete(cid);
    try { ws.close(); } catch (_) {}
  };

  const root = document.getElementById('app');
  const fire = (t, id) => { const lh = t.closest('[data-qed-local]'); if (lh) localDispatch(lh.getAttribute('data-qed-local'), id); else dispatch(id); };
  const fireStr = (t, id, v) => { const lh = t.closest('[data-qed-local]'); if (lh) localDispatchStr(lh.getAttribute('data-qed-local'), id, v); else dispatchStr(id, v); };
  const payloadFor = (event, t, e) => {
    if (event === 'keydown' || event === 'keyup' || event === 'keypress') return e.key;
    if (event === 'change' && t.type === 'checkbox') return t.checked ? 'true' : 'false';
    return (t.value !== undefined && t.value !== null) ? String(t.value) : '';
  };
  const attached = new Set();
  function ensureEvent(event) {
    if (attached.has(event)) return; attached.add(event);
    root.addEventListener(event, (e) => {
      const et = e.target; if (!et || !et.closest) return;
      if (event === 'click' && e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey) {
        const a = et.closest('a[href], [data-qed-link]');
        if (a && !a.target && !a.hasAttribute('download')) {
          const href = a.getAttribute('href') || '';
          if (a.hasAttribute('data-qed-link') || (href.startsWith('/') && !href.startsWith('//'))) {
            e.preventDefault(); history.pushState({}, '', href); urlChanged(href); return;
          }
        }
      }
      const nt = et.closest('[data-qed-on-' + event + ']');
      if (nt) { if (event === 'submit') e.preventDefault(); const id = parseInt(nt.getAttribute('data-qed-on-' + event), 10); if (!Number.isNaN(id)) fire(nt, id); }
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
            fireStr(rt, listId, evIdx + ':' + rowIdx);
          }
        }
      }
      const vt = et.closest('[data-qed-onv-' + event + ']');
      if (vt) { const id = parseInt(vt.getAttribute('data-qed-onv-' + event), 10); if (!Number.isNaN(id)) fireStr(vt, id, payloadFor(event, vt, e)); }
    }, true);
  }
  ensureEvent('click');
  window.addEventListener('popstate', () => urlChanged(location.pathname + location.search));
  window.qed = { init, dispatch, dispatchStr, urlChanged, snapshot: localSnapshot, restore: localRestore };

  app.__main(W);
  init();
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
}
