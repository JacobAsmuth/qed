// host.js — the JavaScript host that boots the Qed WASM module and wires events.
//
// All UI logic lives in Lean. This file only marshals events across the boundary:
//   • delegated `click`  → qed_run_dispatch(id)
//   • delegated `input`  → qed_run_dispatch_str(id, value)
//   • streaming fetch    → qed_run_stream_chunk(cid, data) … qed_run_stream_done(did)
// Lean's pure `update` runs and the verified diff patches only what changed.
(function () {
  function boot() {
    Qed({
      print:    (t) => console.log(t),
      printErr: (t) => console.error(t),
    }).then((Module) => {
      const init        = Module.cwrap('qed_run_init',         null, []);
      const dispatch    = Module.cwrap('qed_run_dispatch',     null, ['number']);
      const dispatchStr = Module.cwrap('qed_run_dispatch_str', null, ['number', 'string']);
      const streamChunk = Module.cwrap('qed_run_stream_chunk', null, ['number', 'string']);
      const streamDone  = Module.cwrap('qed_run_stream_done',  null, ['number']);
      const httpDone    = Module.cwrap('qed_run_http_done',    null, ['number', 'number', 'string']);
      const urlChanged  = Module.cwrap('qed_run_url_changed',  null, ['string']);
      // Local components: an event inside a [data-qed-local] host routes to that
      // instance (keyed by the attribute) instead of the root app.
      const localDispatch    = Module.cwrap('qed_run_local_dispatch',     null, ['string', 'number']);
      const localDispatchStr = Module.cwrap('qed_run_local_dispatch_str', null, ['string', 'number', 'string']);
      const localSnapshot    = Module.cwrap('qed_run_local_snapshot',     'string', []);
      const localRestore     = Module.cwrap('qed_run_local_restore',      null, ['string']);
      const effectDone       = Module.cwrap('qed_run_effect_done',        null, ['number', 'string']);
      const portRecv         = Module.cwrap('qed_run_port_recv',          null, ['string', 'string']);

      // Effects ask for a streaming POST; we read it as Server-Sent Events and
      // feed each `data:` payload back into Lean, then signal end-of-stream.
      globalThis.__qed = globalThis.__qed || {};
      globalThis.__qed.fetchStream = (url, body, cid, did) => {
        fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body })
          .then(async (resp) => {
            const reader = resp.body.getReader();
            const dec = new TextDecoder();
            let buf = '';
            for (;;) {
              const { done, value } = await reader.read();
              if (done) break;
              buf += dec.decode(value, { stream: true });
              let nl;
              while ((nl = buf.indexOf('\n')) >= 0) {
                const line = buf.slice(0, nl).trim();
                buf = buf.slice(nl + 1);
                if (line.startsWith('data:')) {
                  const payload = line.slice(5).trim();
                  if (payload && payload !== '[DONE]') streamChunk(cid, payload);
                }
              }
            }
            streamDone(did);
          })
          .catch((e) => { console.error('Qed stream failed:', e); streamDone(did); });
      };

      // Plain HTTP request: fetch, then hand the response text (and ok flag) back.
      globalThis.__qed.httpSend = (method, url, body, id) => {
        const opts = { method, headers: { 'Content-Type': 'application/json' } };
        if (method !== 'GET' && method !== 'HEAD') opts.body = body;
        fetch(url, opts)
          .then(async (r) => { const t = await r.text(); httpDone(id, r.ok ? 1 : 0, t); })
          .catch((e) => httpDone(id, 0, String(e)));
      };

      // Signals (fine-grained reactivity): set a named value and update only the element
      // bound to it — no dispatch, no diff. A binding is `{el, attr}`: `attr` null drives
      // the element's text (Attr.signalBind), otherwise an attribute (Attr.signalAttr).
      // The maps are created in qed_js_init; this just writes the value and the binding.
      globalThis.__qed.sig = globalThis.__qed.sig || new Map();
      globalThis.__qed.sigVals = globalThis.__qed.sigVals || new Map();
      globalThis.__qed.setSignal = (name, v) => {
        const s = String(v);
        globalThis.__qed.sigVals.set(name, s);
        const b = globalThis.__qed.sig.get(name);
        if (!b || !b.el || !b.el.isConnected) return;
        if (b.attr) { if (b.el.getAttribute(b.attr) !== s) b.el.setAttribute(b.attr, s); }
        else if (b.el.textContent !== s) b.el.textContent = s;
      };
      // Keyed timers (Cmd.afterKeyed / Cmd.cancel): scheduling a key clears its pending
      // timeout first, so a debounce keeps only the last one.
      const timers = {};
      // Native effects: the framework's typed Cmds (Cmd.storageSet, .copy, .focus, …)
      // arrive here as a `kind` switch. Fire-and-forget.
      globalThis.__qed.effect = (kind, a, b, c) => {
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
          case 'signal.set': globalThis.__qed.setSignal(a, b); break;
          case 'file.download': {
            const url = URL.createObjectURL(new Blob([c], { type: b || 'text/plain' }));
            const el = document.createElement('a');
            el.href = url; el.download = a; el.click();
            URL.revokeObjectURL(url);
            break;
          }
          default: console.warn('qed: unknown effect', kind);
        }
      };
      // Native effects that return a string result, delivered via effectDone(id, result).
      globalThis.__qed.effectResult = (kind, a, b, id) => {
        switch (kind) {
          case 'storage.get': effectDone(id, JSON.stringify(localStorage.getItem(a))); break;
          case 'clipboard.read':
            (navigator.clipboard ? navigator.clipboard.readText() : Promise.resolve(''))
              .then((t) => effectDone(id, t)).catch(() => effectDone(id, '')); break;
          case 'timer.after': setTimeout(() => effectDone(id, ''), parseInt(a, 10) || 0); break;
          case 'timer.afterKeyed': {
            if (timers[a]) clearTimeout(timers[a]);
            timers[a] = setTimeout(() => { delete timers[a]; effectDone(id, ''); }, parseInt(b, 10) || 0);
            break;
          }
          case 'random.int': {
            const lo = parseInt(a, 10) || 0, hi = parseInt(b, 10) || 0;
            effectDone(id, String(lo + Math.floor(Math.random() * (hi - lo + 1))));
            break;
          }
          case 'file.pick': {
            const input = document.createElement('input');
            input.type = 'file'; if (a) input.accept = a;
            input.onchange = () => {
              const f = input.files && input.files[0];
              if (!f) { effectDone(id, JSON.stringify({ error: 'cancelled' })); return; }
              const reader = new FileReader();
              reader.onload = () => effectDone(id, JSON.stringify({ name: f.name, mime: f.type, size: f.size, text: String(reader.result) }));
              reader.onerror = () => effectDone(id, JSON.stringify({ error: 'read failed' }));
              reader.readAsText(f);
            };
            input.click();
            break;
          }
          default: console.warn('qed: unknown result effect', kind);
        }
      };
      // Ports — the userland escape hatch. The app registers handlers on __qed.ports
      // (Cmd.port calls them) and pushes inbound messages with __qed.send (→ App.onPort).
      globalThis.__qed.ports = globalThis.__qed.ports || {};
      globalThis.__qed.send = (name, payload) => portRecv(name, String(payload));

      // Programmatic dispatch (timers, sockets, tests) + local-state snapshot/restore
      // (persistence, devtools, time-travel).
      window.qed = { init, dispatch, dispatchStr, urlChanged,
                     snapshot: localSnapshot, restore: localRestore,
                     setSignal: globalThis.__qed.setSignal };

      init(); // initial render + startup effect

      const root = document.getElementById('app');
      // If the handler element sits inside a local-component host, route the event to
      // that instance (keyed by data-qed-local); otherwise to the root app.
      const fire = (t, id) => {
        const lh = t.closest('[data-qed-local]');
        if (lh) localDispatch(lh.getAttribute('data-qed-local'), id);
        else dispatch(id);
      };
      const fireStr = (t, id, v) => {
        const lh = t.closest('[data-qed-local]');
        if (lh) localDispatchStr(lh.getAttribute('data-qed-local'), id, v);
        else dispatchStr(id, v);
      };
      // delegated handler for the no-argument event tables (click/submit/focus/blur)
      const onAt = (attr) => (e) => {
        const t = e.target.closest(`[${attr}]`);
        if (!t) return;
        const id = parseInt(t.getAttribute(attr), 10);
        if (!Number.isNaN(id)) fire(t, id);
      };
      root.addEventListener('click', (e) => {
        // internal navigation links: push the URL and route, no full page load
        const a = e.target.closest('[data-qed-link]');
        if (a) {
          e.preventDefault();
          const href = a.getAttribute('href');
          history.pushState({}, '', href);
          urlChanged(href);
          return;
        }
        const t = e.target.closest('[data-qed-click]');
        if (!t) return;
        const id = parseInt(t.getAttribute('data-qed-click'), 10);
        if (!Number.isNaN(id)) fire(t, id);
      });
      root.addEventListener('input', (e) => {
        const t = e.target.closest('[data-qed-input]');
        if (!t) return;
        const id = parseInt(t.getAttribute('data-qed-input'), 10);
        if (!Number.isNaN(id)) fireStr(t, id, t.value);
      });
      // checkboxes carry their state in `.checked`, not `.value` — send it as a
      // string into the same handler table (Lean parses "true"/"false").
      root.addEventListener('change', (e) => {
        const t = e.target.closest('[data-qed-check]');
        if (!t) return;
        const id = parseInt(t.getAttribute('data-qed-check'), 10);
        if (!Number.isNaN(id)) fireStr(t, id, t.checked ? 'true' : 'false');
      });
      // keydown/keyup send the pressed key's name into the string table
      const onKey = (attr) => (e) => {
        const t = e.target.closest(`[${attr}]`);
        if (!t) return;
        const id = parseInt(t.getAttribute(attr), 10);
        if (!Number.isNaN(id)) fireStr(t, id, e.key);
      };
      root.addEventListener('keydown', onKey('data-qed-keydown'));
      root.addEventListener('keyup', onKey('data-qed-keyup'));
      // submit always suppresses the page reload, then dispatches
      root.addEventListener('submit', (e) => {
        const t = e.target.closest('[data-qed-submit]');
        if (!t) return;
        e.preventDefault();
        const id = parseInt(t.getAttribute('data-qed-submit'), 10);
        if (!Number.isNaN(id)) fire(t, id);
      });
      // focus/blur don't bubble; focusin/focusout do, so delegate through them
      root.addEventListener('focusin', onAt('data-qed-focus'));
      root.addEventListener('focusout', onAt('data-qed-blur'));
      // back/forward: re-route to the new path
      window.addEventListener('popstate', () => urlChanged(location.pathname));
    }).catch((err) => {
      console.error('Qed boot failed:', err);
      const root = document.getElementById('app');
      if (root) root.textContent = 'Qed boot failed: ' + err;
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
