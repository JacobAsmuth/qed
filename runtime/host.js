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

      // Programmatic dispatch (timers, sockets, tests).
      window.qed = { init, dispatch, dispatchStr };

      init(); // initial render + startup effect

      const root = document.getElementById('app');
      root.addEventListener('click', (e) => {
        const t = e.target.closest('[data-qed-click]');
        if (!t) return;
        const id = parseInt(t.getAttribute('data-qed-click'), 10);
        if (!Number.isNaN(id)) dispatch(id);
      });
      root.addEventListener('input', (e) => {
        const t = e.target.closest('[data-qed-input]');
        if (!t) return;
        const id = parseInt(t.getAttribute('data-qed-input'), 10);
        if (!Number.isNaN(id)) dispatchStr(id, t.value);
      });
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
