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
  const wsJoin      = (sid, bytes) => app.qed_ws_join(sid, bytes, W);
  const wsMsgBytes  = (sid, bytes) => app.qed_ws_msg_bytes(sid, bytes, W);
  const wsMsgText   = (sid, text) => app.qed_ws_msg_text(sid, text, W);
  const wsStatus    = (sid, code, arg, err) => app.qed_ws_status(sid, code, arg, err, W);

  const g = (globalThis.__qed ||= {});
  g.nodes ||= [null]; g.sig ||= new Map(); g.sigVals ||= new Map();

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
  g.httpSendBytes = (method, url, body, id) => {
    const opts = { method, headers: { 'Content-Type': 'application/x-protobuf', 'Accept': 'application/x-protobuf' } };
    if (method !== 'GET' && method !== 'HEAD') opts.body = body;
    fetch(url, opts).then(async (r) => {
      const buf = new Uint8Array(await r.arrayBuffer());
      httpBytesDone(id, r.ok ? 1 : 0, buf);
    }).catch((e) => httpBytesDone(id, 0, new TextEncoder().encode(String(e))));
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
      case 'css.inject': { if (a && !document.getElementById('qed-styles') && !document.querySelector('link[data-qed-styles]')) { const s = document.createElement('style'); s.id = 'qed-styles'; s.textContent = a; document.head.appendChild(s); } break; }
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

  const wsEnc = new TextEncoder(), wsDec = new TextDecoder();
  const resolveWsUrl = (u) => u.startsWith('/') ? (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + u : u;
  const nextReconnectMs = (rec, attempt) => {
    if (!rec || rec.mode === 0) return -1;
    if (rec.lim > 0 && attempt >= rec.lim - 1) return -1;
    if (rec.mode === 1) return rec.initMs;
    const base = Math.min(rec.maxMs, rec.initMs * Math.pow(2, Math.min(attempt, 20)));
    return Math.round(base * (1 + Math.random() * 0.2));
  };
  const writeU32BE = (buf, off, v) => {
    buf[off] = (v >>> 24) & 0xff; buf[off + 1] = (v >>> 16) & 0xff;
    buf[off + 2] = (v >>> 8) & 0xff; buf[off + 3] = v & 0xff;
  };
  const readU32BE = (buf, off) =>
    ((buf[off] << 24) | (buf[off + 1] << 16) | (buf[off + 2] << 8) | buf[off + 3]) >>> 0;
  const buildMuxSub = (sid, ch, params) => {
    const chB = wsEnc.encode(ch), pB = params instanceof Uint8Array ? params : new Uint8Array(0);
    const out = new Uint8Array(7 + chB.length + pB.length);
    out[0] = 0x01; writeU32BE(out, 1, sid);
    out[5] = (chB.length >>> 8) & 0xff; out[6] = chB.length & 0xff;
    out.set(chB, 7); out.set(pB, 7 + chB.length);
    return out;
  };
  const buildMuxSimple = (op, sid, payload) => {
    const pB = payload instanceof Uint8Array ? payload : new Uint8Array(0);
    const out = new Uint8Array(5 + pB.length);
    out[0] = op; writeU32BE(out, 1, sid); out.set(pB, 5);
    return out;
  };

  const muxPools = new Map();
  const muxSubToPool = new Map();
  const ensureMuxConn = (pool) => {
    if (pool.ws && (pool.ws.readyState === 0 || pool.ws.readyState === 1)) return;
    if (pool.timer) { clearTimeout(pool.timer); pool.timer = null; }
    let ws;
    try { ws = new WebSocket(resolveWsUrl(pool.url)); }
    catch (err) {
      for (const sid of [...pool.subs.keys()]) {
        pool.subs.delete(sid); muxSubToPool.delete(sid);
        wsStatus(sid, 4, 0, String(err));
      }
      return;
    }
    ws.binaryType = 'arraybuffer';
    pool.ws = ws;
    ws.onopen = () => {
      if (pool.ws !== ws) return;
      for (const [sid, sub] of pool.subs) {
        sub.attempt = 0;
        sub.pendingRetry = false;
        sub.nextAt = 0;
        ws.send(buildMuxSub(sid, sub.channel, sub.params));
      }
    };
    ws.onmessage = (e) => {
      if (pool.ws !== ws || !(e.data instanceof ArrayBuffer)) return;
      const buf = new Uint8Array(e.data);
      if (buf.length < 5) return;
      const op = buf[0], sid = readU32BE(buf, 1);
      const sub = pool.subs.get(sid);
      if (!sub) return;
      const body = buf.subarray(5);
      if (op === 0x11) {
        sub.attempt = 0; sub.pendingRetry = false; sub.nextAt = 0;
        wsStatus(sid, 2, 0, ''); wsJoin(sid, new Uint8Array(body));
      } else if (op === 0x12) { wsMsgBytes(sid, new Uint8Array(body)); }
      else if (op === 0x13) {
        pool.subs.delete(sid); muxSubToPool.delete(sid);
        wsStatus(sid, 4, 0, wsDec.decode(body));
      } else if (op === 0x14) {
        pool.subs.delete(sid); muxSubToPool.delete(sid);
        wsStatus(sid, 0, 0, '');
      }
    };
    ws.onerror = () => {};
    ws.onclose = () => {
      if (pool.ws !== ws) return;
      pool.ws = null;
      if (pool.subs.size === 0) { muxPools.delete(pool.url); return; }
      const now = Date.now();
      let minDelay = -1;
      for (const [sid, sub] of [...pool.subs]) {
        if (sub.pendingRetry && now < sub.nextAt) {
          const rem = sub.nextAt - now;
          if (minDelay < 0 || rem < minDelay) minDelay = rem;
          continue;
        }
        const d = nextReconnectMs(sub.rec, sub.attempt);
        if (d < 0) {
          pool.subs.delete(sid); muxSubToPool.delete(sid);
          wsStatus(sid, sub.rec.mode === 0 ? 0 : 4, 0, sub.rec.mode === 0 ? '' : 'disconnected');
        } else {
          sub.attempt += 1;
          sub.pendingRetry = true;
          sub.nextAt = now + d;
          wsStatus(sid, 3, sub.attempt, '');
          if (minDelay < 0 || d < minDelay) minDelay = d;
        }
      }
      if (pool.subs.size === 0) { muxPools.delete(pool.url); return; }
      pool.timer = setTimeout(() => { pool.timer = null; if (pool.subs.size > 0) ensureMuxConn(pool); }, Math.max(0, minDelay));
    };
  };

  g.wsMuxSub = (sid, url, channel, params, rm, ri, rmax, rlim) => {
    let pool = muxPools.get(url);
    if (!pool) { pool = { url, ws: null, timer: null, subs: new Map() }; muxPools.set(url, pool); }
    const sub = { channel, params: params instanceof Uint8Array ? params : new Uint8Array(0), rec: { mode: rm, initMs: ri, maxMs: rmax, lim: rlim }, attempt: 0, pendingRetry: false, nextAt: 0 };
    pool.subs.set(sid, sub);
    muxSubToPool.set(sid, pool);
    wsStatus(sid, 1, 0, '');
    if (pool.ws && pool.ws.readyState === 1) pool.ws.send(buildMuxSub(sid, sub.channel, sub.params));
    else ensureMuxConn(pool);
  };
  g.wsMuxSend = (sid, payload) => {
    const pool = muxSubToPool.get(sid);
    if (pool && pool.ws && pool.ws.readyState === 1) pool.ws.send(buildMuxSimple(0x03, sid, payload));
  };
  g.wsMuxUnsub = (sid) => {
    const pool = muxSubToPool.get(sid);
    if (!pool) return;
    muxSubToPool.delete(sid);
    pool.subs.delete(sid);
    if (pool.ws && pool.ws.readyState === 1) pool.ws.send(buildMuxSimple(0x02, sid, null));
    if (pool.subs.size === 0) {
      if (pool.timer) { clearTimeout(pool.timer); pool.timer = null; }
      if (pool.ws) { const old = pool.ws; pool.ws = null; try { old.close(); } catch (_) {} }
      muxPools.delete(pool.url);
    }
  };

  const extConns = new Map();
  const openExtConn = (entry) => {
    if (entry.closed) return;
    if (entry.timer) { clearTimeout(entry.timer); entry.timer = null; }
    let ws;
    try { ws = new WebSocket(resolveWsUrl(entry.url)); }
    catch (err) {
      extConns.delete(entry.sid);
      wsStatus(entry.sid, 4, 0, String(err));
      return;
    }
    if (entry.isBinary) ws.binaryType = 'arraybuffer';
    entry.ws = ws;
    ws.onopen = () => {
      if (entry.ws !== ws || entry.closed) return;
      entry.attempt = 0;
      wsStatus(entry.sid, 2, 0, '');
      wsJoin(entry.sid, new Uint8Array(0));
    };
    ws.onmessage = (e) => {
      if (entry.ws !== ws || entry.closed) return;
      if (entry.isBinary) {
        if (e.data instanceof ArrayBuffer) wsMsgBytes(entry.sid, new Uint8Array(e.data));
        else if (e.data instanceof Blob) e.data.arrayBuffer().then((ab) => { if (!entry.closed && entry.ws === ws) wsMsgBytes(entry.sid, new Uint8Array(ab)); });
        else wsMsgBytes(entry.sid, wsEnc.encode(String(e.data)));
      } else {
        wsMsgText(entry.sid, typeof e.data === 'string' ? e.data : wsDec.decode(new Uint8Array(e.data)));
      }
    };
    ws.onerror = () => {};
    ws.onclose = () => {
      if (entry.ws !== ws) return;
      entry.ws = null;
      if (entry.closed) return;
      const d = nextReconnectMs(entry.rec, entry.attempt);
      if (d < 0) {
        extConns.delete(entry.sid);
        wsStatus(entry.sid, entry.rec.mode === 0 ? 0 : 4, 0, entry.rec.mode === 0 ? '' : 'disconnected');
      } else {
        entry.attempt += 1;
        wsStatus(entry.sid, 3, entry.attempt, '');
        entry.timer = setTimeout(() => { entry.timer = null; openExtConn(entry); }, d);
      }
    };
  };
  g.wsExtOpen = (sid, url, isBinary, rm, ri, rmax, rlim) => {
    const entry = { sid, url, isBinary: !!isBinary, rec: { mode: rm, initMs: ri, maxMs: rmax, lim: rlim }, attempt: 0, ws: null, timer: null, closed: false };
    extConns.set(sid, entry);
    wsStatus(sid, 1, 0, '');
    openExtConn(entry);
  };
  g.wsExtSendText = (sid, text) => {
    const entry = extConns.get(sid);
    if (entry && entry.ws && entry.ws.readyState === 1) entry.ws.send(String(text));
  };
  g.wsExtSendBytes = (sid, payload) => {
    const entry = extConns.get(sid);
    if (entry && entry.ws && entry.ws.readyState === 1) entry.ws.send(payload instanceof Uint8Array ? payload : new Uint8Array(0));
  };
  g.wsExtClose = (sid) => {
    const entry = extConns.get(sid);
    if (!entry) return;
    entry.closed = true;
    extConns.delete(sid);
    if (entry.timer) { clearTimeout(entry.timer); entry.timer = null; }
    if (entry.ws) { const old = entry.ws; entry.ws = null; try { old.close(); } catch (_) {} }
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
      const vt = et.closest('[data-qed-onv-' + event + ']');
      if (vt) { const id = parseInt(vt.getAttribute('data-qed-onv-' + event), 10); if (!Number.isNaN(id)) fireStr(vt, id, payloadFor(event, vt, e)); }
    }, true);
  }
  ensureEvent('click');
  window.addEventListener('popstate', () => urlChanged(location.pathname));
  window.qed = { init, dispatch, dispatchStr, urlChanged, snapshot: localSnapshot, restore: localRestore };

  app.__main(W);
  init();
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
}
