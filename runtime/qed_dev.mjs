// Qed Dev Live-Reload, State-Preserving HMR & Build/Invariant Error Overlay.
// Loaded only in `qed dev` mode; never emitted into production `dist/` bundles.

(() => {
  if (window.__qedDevClientActive) return;
  window.__qedDevClientActive = true;

  let lastId = null;
  let lastStatus = null;
  let lastError = '';
  let overlayDismissedFor = null;
  let toastTimer = null;
  let inFlight = false;
  let offlineCount = 0;

  // ---- Minimal Shadow-DOM UI (completely isolated from app styles & view invariants) ----
  const host = document.createElement('div');
  host.id = '__qed-dev-ui';
  const shadow = host.attachShadow({ mode: 'open' });
  shadow.innerHTML = `
    <style>
      :host { all: initial; }
      .toast {
        position: fixed; right: 14px; bottom: 14px; z-index: 2147483646;
        font: 500 12px/1.35 ui-sans-serif, system-ui, -apple-system, sans-serif;
        color: #f8fafc; background: rgba(15, 23, 42, 0.92);
        border: 1px solid rgba(148, 163, 184, 0.25); border-radius: 999px;
        padding: 6px 12px; display: flex; align-items: center; gap: 8px;
        box-shadow: 0 8px 24px rgba(0, 0, 0, 0.28);
        opacity: 0; transform: translateY(6px); pointer-events: none;
        transition: opacity 150ms ease, transform 150ms ease;
      }
      .toast.show { opacity: 1; transform: translateY(0); }
      .dot { width: 7px; height: 7px; border-radius: 50%; flex: none; }
      .dot.ok { background: #22c55e; }
      .dot.building { background: #f59e0b; animation: pulse 900ms ease-in-out infinite; }
      .dot.error { background: #ef4444; }
      @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.35; } }
      .backdrop {
        position: fixed; inset: 0; z-index: 2147483647;
        background: rgba(15, 23, 42, 0.78); backdrop-filter: blur(4px);
        display: none; align-items: flex-start; justify-content: center;
        padding: 48px 20px; overflow: auto;
        font-family: ui-sans-serif, system-ui, -apple-system, sans-serif;
      }
      .backdrop.open { display: flex; }
      .card {
        width: min(860px, 100%); background: #0f172a; color: #e2e8f0;
        border: 1px solid rgba(239, 68, 68, 0.45); border-radius: 12px;
        box-shadow: 0 24px 60px rgba(0, 0, 0, 0.55); overflow: hidden;
      }
      .hdr {
        display: flex; align-items: center; justify-content: space-between;
        padding: 14px 18px; background: rgba(239, 68, 68, 0.14);
        border-bottom: 1px solid rgba(239, 68, 68, 0.28);
      }
      .title { font-size: 14px; font-weight: 600; color: #fca5a5; display: flex; align-items: center; gap: 8px; }
      .close {
        all: unset; cursor: pointer; font-size: 12px; color: #cbd5e1;
        padding: 4px 10px; border-radius: 6px; border: 1px solid rgba(148, 163, 184, 0.3);
      }
      .close:hover { background: rgba(148, 163, 184, 0.16); color: #fff; }
      .body {
        margin: 0; padding: 18px; overflow-x: auto; max-height: 70vh;
        font: 13px/1.55 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
        white-space: pre-wrap; word-break: break-word; color: #f1f5f9;
      }
      .ftr {
        padding: 10px 18px; font-size: 12px; color: #94a3b8;
        border-top: 1px solid rgba(148, 163, 184, 0.14);
        display: flex; justify-content: space-between;
      }
    </style>
    <div class="toast" id="toast"><span class="dot" id="dot"></span><span id="msg"></span></div>
    <div class="backdrop" id="backdrop" role="dialog" aria-modal="true" aria-label="Qed build error">
      <div class="card">
        <div class="hdr">
          <div class="title"><span class="dot error"></span><span>Build / Proof Error</span></div>
          <button class="close" id="close">Dismiss (Esc)</button>
        </div>
        <pre class="body" id="errbody"></pre>
        <div class="ftr">
          <span>Fix the error and save — Qed will hot-reload automatically.</span>
          <span>Previous working build stays live underneath.</span>
        </div>
      </div>
    </div>
  `;

  const mountUi = () => { if (document.body && !host.isConnected) document.body.appendChild(host); };
  if (document.body) mountUi();
  else document.addEventListener('DOMContentLoaded', mountUi, { once: true });

  const toastEl = shadow.getElementById('toast');
  const dotEl = shadow.getElementById('dot');
  const msgEl = shadow.getElementById('msg');
  const backdropEl = shadow.getElementById('backdrop');
  const errBodyEl = shadow.getElementById('errbody');
  const closeBtn = shadow.getElementById('close');

  function showToast(kind, text, autoHideMs = 0) {
    mountUi();
    if (toastTimer) { clearTimeout(toastTimer); toastTimer = null; }
    dotEl.className = 'dot ' + kind;
    msgEl.textContent = text;
    toastEl.classList.add('show');
    if (autoHideMs > 0) {
      toastTimer = setTimeout(() => { toastEl.classList.remove('show'); }, autoHideMs);
    }
  }

  function hideToast() {
    if (toastTimer) { clearTimeout(toastTimer); toastTimer = null; }
    toastEl.classList.remove('show');
  }

  function showOverlay(errText) {
    mountUi();
    errBodyEl.textContent = errText || 'Build failed. Check terminal output for details.';
    backdropEl.classList.add('open');
  }

  function hideOverlay() {
    backdropEl.classList.remove('open');
  }

  closeBtn.addEventListener('click', () => {
    overlayDismissedFor = lastError;
    hideOverlay();
  });
  backdropEl.addEventListener('click', (e) => {
    if (e.target === backdropEl) { overlayDismissedFor = lastError; hideOverlay(); }
  });
  window.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && backdropEl.classList.contains('open')) {
      overlayDismissedFor = lastError;
      hideOverlay();
    }
  });

  async function applyUpdate(st) {
    const kind = st.kind || 'hmr';
    const ms = typeof st.durationMs === 'number' && st.durationMs > 0 ? ` · ${st.durationMs}ms` : '';
    if (kind === 'full' || typeof window.__qedHotReload !== 'function') {
      location.reload();
      return;
    }
    try {
      const res = await window.__qedHotReload(st.id, { kind });
      hideOverlay();
      if (res.mode === 'css') {
        showToast('ok', `Styles updated${ms}`, 1600);
      } else if (res.preserved) {
        showToast('ok', `Hot reloaded (state kept)${ms}`, 1800);
      } else {
        showToast('ok', `Hot reloaded${ms}`, 1800);
      }
    } catch (err) {
      console.warn('[qed dev] hot reload failed, falling back to full reload:', err);
      location.reload();
    }
  }

  async function poll() {
    if (inFlight) return;
    inFlight = true;
    try {
      const resp = await fetch('/__dev_status', { cache: 'no-store' });
      if (!resp.ok) throw new Error('status ' + resp.status);
      const st = await resp.json();
      offlineCount = 0;

      if (lastId === null) {
        lastId = st.id;
        lastStatus = st.status;
        if (st.status === 'error' && st.error) {
          lastError = st.error;
          showOverlay(st.error);
          showToast('error', 'Build failed');
        }
        return;
      }

      if (st.status === 'building') {
        if (lastStatus !== 'building') {
          showToast('building', 'Rebuilding…');
        }
        lastStatus = 'building';
        return;
      }

      if (st.status === 'error') {
        const errText = st.error || '';
        const isNewErr = errText !== lastError || lastStatus !== 'error';
        lastStatus = 'error';
        lastError = errText;
        if (isNewErr) {
          showToast('error', 'Build failed');
          if (errText !== overlayDismissedFor) showOverlay(errText);
        }
        return;
      }

      // status === 'ok'
      const recoveredFromErr = lastStatus === 'error';
      lastStatus = 'ok';
      lastError = '';
      overlayDismissedFor = null;
      if (recoveredFromErr) hideOverlay();

      if (st.id && st.id !== lastId) {
        lastId = st.id;
        await applyUpdate(st);
      } else if (recoveredFromErr) {
        hideToast();
      }
    } catch (_) {
      offlineCount++;
      if (offlineCount >= 2 && lastStatus !== 'reconnecting') {
        lastStatus = 'reconnecting';
        showToast('building', 'Restarting server…');
      }
    } finally {
      inFlight = false;
    }
  }

  const timer = setInterval(() => {
    if (!document.hidden) poll();
  }, 180);
  document.addEventListener('visibilitychange', () => {
    if (!document.hidden) poll();
  });
  window.addEventListener('beforeunload', () => clearInterval(timer));
  poll();
})();
