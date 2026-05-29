// host.js — the JavaScript host that boots the Qed WASM module and wires events.
//
// Flow:
//   1. `Qed({...})` instantiates the module; Lean `main` runs during instantiation
//      and registers the app (no render yet).
//   2. We call `qed_run_init` to perform the initial render into `#app`.
//   3. A single delegated click listener maps `data-qed-click="<id>"` back to
//      `qed_run_dispatch(<id>)`, which runs the pure `update` and re-renders.
//
// All UI logic lives in Lean; this file only marshals events across the boundary.
(function () {
  function boot() {
    Qed({
      print:    (t) => console.log(t),
      printErr: (t) => console.error(t),
    }).then((Module) => {
      const init     = Module.cwrap('qed_run_init',     null, []);
      const dispatch = Module.cwrap('qed_run_dispatch', null, ['number']);

      // Expose for programmatic dispatch (timers, sockets, tests).
      window.qed = { init, dispatch };

      init(); // initial render

      const root = document.getElementById('app');
      root.addEventListener('click', (e) => {
        const target = e.target.closest('[data-qed-click]');
        if (!target) return;
        const id = parseInt(target.getAttribute('data-qed-click'), 10);
        if (!Number.isNaN(id)) dispatch(id);
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
