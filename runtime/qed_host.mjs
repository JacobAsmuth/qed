// qed_host.mjs: boots the transpiled-from-Lean driver:
// it marshals browser events into the exported qed_* entry points and supplies the
// native effects. All UI logic — render, diff, the driver loop — is transpiled Lean.
import * as app from './app.mjs';
import * as $ from './qed_rt.mjs';
import { dom } from './qed_dom.mjs';

export function boot() {
  $.registerDom(dom);                       // wire the DOM externs
  const W = 0;                              // IO world token
  // Export wrappers (each entry takes the world token last).
  const init        = () => app.qed_init(W);
  const dispatch    = (id) => app.qed_dispatch(id, W);
  const dispatchStr = (id, v) => app.qed_dispatch_str(id, v, W);
  const streamChunk = (cid, data) => app.qed_stream_chunk(cid, data, W);
  const streamDone  = (did) => app.qed_stream_done(did, W);
  const httpDone    = (id, ok, text) => app.qed_http_done(id, ok, text, W);
  const urlChanged  = (path) => app.qed_url_changed(path, W);
  const localDispatch    = (key, id) => app.qed_local_dispatch(key, id, W);
  const localDispatchStr = (key, id, v) => app.qed_local_dispatch_str(key, id, v, W);
  const localSnapshot = () => $.ioVal(app.qed_local_snapshot(W));   // local state → JSON string
  const localRestore  = (s) => app.qed_local_restore(s, W);
  const effectDone  = (id, result) => app.qed_effect_done(id, result, W);
  const portRecv    = (name, payload) => app.qed_port_recv(name, payload, W);

  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null]; g.sig ||= new Map(); g.sigVals ||= new Map();

  // Streaming POST as SSE, feeding each `data:` payload back to Lean.
  g.fetchStream = (url, body, cid, did) => {
    fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body }).then(async (resp) => {
      const reader = resp.body.getReader(); const dec = new TextDecoder(); let buf = '';
      for (;;) { const { done, value } = await reader.read(); if (done) break;
        buf += dec.decode(value, { stream: true }); let nl;
        while ((nl = buf.indexOf('\n')) >= 0) { const line = buf.slice(0, nl).trim(); buf = buf.slice(nl + 1);
          if (line.startsWith('data:')) { const p = line.slice(5).trim(); if (p && p !== '[DONE]') streamChunk(cid, p); } } }
      streamDone(did);
    }).catch(() => streamDone(did));
  };
  g.httpSend = (method, url, body, id) => {
    const opts = { method, headers: { 'Content-Type': 'application/json' } };
    if (method !== 'GET' && method !== 'HEAD') opts.body = body;
    fetch(url, opts).then(async (r) => { const t = await r.text(); httpDone(id, r.ok ? 1 : 0, t); })
      .catch((e) => httpDone(id, 0, String(e)));
  };
  g.setSignal = (name, v) => {
    const s = String(v); g.sigVals.set(name, s); const b = g.sig.get(name);
    if (!b || !b.el || !b.el.isConnected) return;
    if (b.attr === 'value') { if (b.el.value !== s) b.el.value = s; }
    else if (b.attr === 'checked') { const on = (s !== '' && s !== 'false'); if (b.el.checked !== on) b.el.checked = on; }
    else if (b.attr) { if (b.el.getAttribute(b.attr) !== s) b.el.setAttribute(b.attr, s); }
    else if (b.el.textContent !== s) b.el.textContent = s;
  };
  const timers = {}, sockets = {};
  const wsEvent = (key, event, data) => g.send('__ws', JSON.stringify({ key, event, data: data || '' }));
  g.effect = (kind, a, b, c) => {
    switch (kind) {
      case 'timer.cancel': if (timers[a]) { clearTimeout(timers[a]); delete timers[a]; } break;
      case 'storage.set': localStorage.setItem(a, b); break;
      case 'storage.remove': localStorage.removeItem(a); break;
      case 'storage.clear': localStorage.clear(); break;
      case 'history.replace': history.replaceState({}, '', a); urlChanged(a); break;
      case 'history.back': history.back(); break;
      case 'history.forward': history.forward(); break;
      case 'clipboard.write': if (navigator.clipboard) navigator.clipboard.writeText(a); break;
      case 'dom.focus': { const el = document.getElementById(a); if (el) el.focus(); break; }
      case 'dom.blur': { const el = document.getElementById(a); if (el) el.blur(); break; }
      case 'dom.select': { const el = document.getElementById(a); if (el && el.select) el.select(); break; }
      case 'dom.scrollIntoView': { const el = document.getElementById(a); if (el) el.scrollIntoView({ behavior: 'smooth' }); break; }
      case 'document.title': document.title = a; break;
      case 'signal.set': g.setSignal(a, b); break;
      case 'ws.open': { let url = b; if (url.startsWith('/')) url = (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + url;
        try { const s = new WebSocket(url); sockets[a] = s; s.onopen = () => wsEvent(a, 'open'); s.onmessage = (e) => wsEvent(a, 'message', String(e.data));
          s.onerror = () => wsEvent(a, 'error', 'socket error'); s.onclose = () => { delete sockets[a]; wsEvent(a, 'close'); }; }
        catch (err) { wsEvent(a, 'error', String(err)); } break; }
      case 'ws.send': { const s = sockets[a]; if (s && s.readyState === 1) s.send(b); break; }
      case 'ws.close': { const s = sockets[a]; if (s) s.close(); break; }
      case 'event.listen': ensureEvent(a); break;
      case 'file.download': { const url = URL.createObjectURL(new Blob([c], { type: b || 'text/plain' }));
        const el = document.createElement('a'); el.href = url; el.download = a; el.click(); URL.revokeObjectURL(url); break; }
      default: console.warn('qed: unknown effect', kind);
    }
  };
  g.effectResult = (kind, a, b, id) => {
    switch (kind) {
      case 'storage.get': effectDone(id, JSON.stringify(localStorage.getItem(a))); break;
      case 'clipboard.read': (navigator.clipboard ? navigator.clipboard.readText() : Promise.resolve('')).then((t) => effectDone(id, t)).catch(() => effectDone(id, '')); break;
      case 'timer.after': setTimeout(() => effectDone(id, ''), parseInt(a, 10) || 0); break;
      case 'timer.afterKeyed': { if (timers[a]) clearTimeout(timers[a]); timers[a] = setTimeout(() => { delete timers[a]; effectDone(id, ''); }, parseInt(b, 10) || 0); break; }
      case 'random.int': { const lo = parseInt(a, 10) || 0, hi = parseInt(b, 10) || 0; effectDone(id, String(lo + Math.floor(Math.random() * (hi - lo + 1)))); break; }
      case 'file.pick': { const input = document.createElement('input'); input.type = 'file'; if (a) input.accept = a;
        input.onchange = () => { const f = input.files && input.files[0]; if (!f) { effectDone(id, JSON.stringify({ error: 'cancelled' })); return; }
          const reader = new FileReader(); reader.onload = () => effectDone(id, JSON.stringify({ name: f.name, mime: f.type, size: f.size, text: String(reader.result) }));
          reader.onerror = () => effectDone(id, JSON.stringify({ error: 'read failed' })); reader.readAsText(f); }; input.click(); break; }
      default: console.warn('qed: unknown result effect', kind);
    }
  };
  g.ports ||= {};
  g.send = (name, payload) => portRecv(name, String(payload));

  // Event delegation (capture phase), identical to host.js.
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
      if (event === 'click') { const a = et.closest('[data-qed-link]'); if (a) { e.preventDefault(); const href = a.getAttribute('href'); history.pushState({}, '', href); urlChanged(href); return; } }
      const nt = et.closest('[data-qed-on-' + event + ']');
      if (nt) { if (event === 'submit') e.preventDefault(); const id = parseInt(nt.getAttribute('data-qed-on-' + event), 10); if (!Number.isNaN(id)) fire(nt, id); }
      const vt = et.closest('[data-qed-onv-' + event + ']');
      if (vt) { const id = parseInt(vt.getAttribute('data-qed-onv-' + event), 10); if (!Number.isNaN(id)) fireStr(vt, id, payloadFor(event, vt, e)); }
    }, true);
  }
  ensureEvent('click');
  window.addEventListener('popstate', () => urlChanged(location.pathname));
  window.qed = { init, dispatch, dispatchStr, urlChanged, snapshot: localSnapshot, restore: localRestore };

  app.__main(W);    // Qed.run app — set up the runtime
  init();           // initial render + startup effects
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
}
