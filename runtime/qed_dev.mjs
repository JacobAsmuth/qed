// Qed Dev Live-Reload (SSE Push + Poll Fallback), State-Preserving HMR,
// Build/Proof Error Overlay & Shadow-DOM Time-Travel DevTools Drawer.
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

  // ---- SSE Push + Automatic Polling Fallback State ----
  let sseUrl = document.querySelector('meta[name="qed-dev-sse"]')?.getAttribute('content') || '';
  let eventSource = null;
  let sseConnected = false;
  let pollTimer = null;

  // ---- DevTools State & Time-Travel History ----
  const MAX_HISTORY = 200;
  let drawerOpen = false;
  let activeTab = 'state';
  let stateFilter = '';
  let restoreFn = typeof window.__qedDevRestore === 'function' ? window.__qedDevRestore : null;
  let history = [];
  let activeSnapIdx = -1;
  let timeTravelActive = false;
  let prevInFlightHttp = 0;
  let pendingPredictIdx = -1;

  // ---- Minimal Shadow-DOM UI (completely isolated from app styles & view invariants) ----
  const host = document.createElement('div');
  host.id = '__qed-dev-ui';
  const shadow = host.attachShadow({ mode: 'open' });
  shadow.innerHTML = `
    <style>
      :host { all: initial; }
      * { box-sizing: border-box; }
      .toast {
        position: fixed; right: 14px; bottom: 52px; z-index: 2147483645;
        font: 500 12px/1.35 ui-sans-serif, system-ui, -apple-system, sans-serif;
        color: #f8fafc; background: rgba(15, 23, 42, 0.94);
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

      /* Floating DevTools Pill */
      .pill {
        position: fixed; right: 14px; bottom: 14px; z-index: 2147483645;
        font: 600 11.5px/1 ui-sans-serif, system-ui, -apple-system, sans-serif;
        color: #e2e8f0; background: rgba(15, 23, 42, 0.92);
        border: 1px solid rgba(148, 163, 184, 0.3); border-radius: 999px;
        padding: 7px 11px; display: inline-flex; align-items: center; gap: 7px;
        cursor: pointer; user-select: none;
        box-shadow: 0 6px 20px rgba(0, 0, 0, 0.32);
        transition: background 140ms ease, border-color 140ms ease, transform 140ms ease;
      }
      .pill:hover { background: rgba(30, 41, 59, 0.98); border-color: rgba(148, 163, 184, 0.55); transform: translateY(-1px); }
      .pill-badge {
        font-size: 10px; font-weight: 600; padding: 2px 6px; border-radius: 999px;
        background: rgba(56, 189, 248, 0.16); color: #7dd3fc;
      }
      .pill-badge.tt { background: rgba(245, 158, 11, 0.22); color: #fcd34d; }

      /* Collapsible DevTools Drawer */
      .drawer {
        position: fixed; right: 14px; bottom: 52px; z-index: 2147483646;
        width: min(460px, calc(100vw - 28px)); height: min(520px, calc(100vh - 80px));
        background: rgba(15, 23, 42, 0.97); color: #e2e8f0;
        border: 1px solid rgba(148, 163, 184, 0.28); border-radius: 12px;
        box-shadow: 0 22px 56px rgba(0, 0, 0, 0.55);
        display: none; flex-direction: column; overflow: hidden;
        font-family: ui-sans-serif, system-ui, -apple-system, sans-serif;
        backdrop-filter: blur(8px);
      }
      .drawer.open { display: flex; }
      .dt-hdr {
        display: flex; align-items: center; justify-content: space-between;
        padding: 10px 12px; background: rgba(30, 41, 59, 0.72);
        border-bottom: 1px solid rgba(148, 163, 184, 0.18);
        gap: 8px;
      }
      .dt-brand { display: flex; align-items: center; gap: 8px; font-size: 12.5px; font-weight: 600; color: #f8fafc; }
      .dt-chip {
        font-size: 10px; font-weight: 600; padding: 2px 6px; border-radius: 4px;
        background: rgba(34, 197, 94, 0.16); color: #86efac; letter-spacing: 0.02em;
      }
      .dt-chip.poll { background: rgba(148, 163, 184, 0.18); color: #cbd5e1; }
      .dt-tabs {
        display: flex; gap: 4px; padding: 6px 10px;
        border-bottom: 1px solid rgba(148, 163, 184, 0.14);
        background: rgba(15, 23, 42, 0.6);
      }
      .dt-tab {
        all: unset; cursor: pointer; font-size: 12px; font-weight: 500;
        color: #94a3b8; padding: 5px 10px; border-radius: 6px;
        display: inline-flex; align-items: center; gap: 6px;
      }
      .dt-tab:hover { color: #e2e8f0; background: rgba(148, 163, 184, 0.1); }
      .dt-tab.active { color: #f8fafc; background: rgba(56, 189, 248, 0.18); }
      .dt-count {
        font-size: 10px; padding: 1px 5px; border-radius: 999px;
        background: rgba(148, 163, 184, 0.2); color: #cbd5e1;
      }
      .dt-btn {
        all: unset; cursor: pointer; font-size: 11px; font-weight: 500;
        color: #cbd5e1; padding: 4px 8px; border-radius: 6px;
        border: 1px solid rgba(148, 163, 184, 0.28);
        display: inline-flex; align-items: center; gap: 4px;
      }
      .dt-btn:hover { background: rgba(148, 163, 184, 0.16); color: #fff; }
      .dt-btn.primary { border-color: rgba(56, 189, 248, 0.5); color: #7dd3fc; background: rgba(56, 189, 248, 0.12); }
      .dt-btn.primary:hover { background: rgba(56, 189, 248, 0.24); color: #fff; }
      .dt-btn.warn { border-color: rgba(245, 158, 11, 0.55); color: #fcd34d; background: rgba(245, 158, 11, 0.16); }
      .dt-pane { display: none; flex: 1; min-height: 0; flex-direction: column; }
      .dt-pane.active { display: flex; }
      .dt-toolbar {
        display: flex; align-items: center; gap: 6px; padding: 8px 10px;
        border-bottom: 1px solid rgba(148, 163, 184, 0.12);
      }
      .dt-search {
        flex: 1; background: rgba(30, 41, 59, 0.9); color: #f1f5f9;
        border: 1px solid rgba(148, 163, 184, 0.24); border-radius: 6px;
        padding: 5px 8px; font-size: 12px; outline: none;
      }
      .dt-search:focus { border-color: #38bdf8; }
      .dt-json {
        margin: 0; padding: 10px 12px; flex: 1; overflow: auto;
        font: 12px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
        white-space: pre-wrap; word-break: break-word; color: #e2e8f0;
      }
      .dt-json mark { background: rgba(250, 204, 21, 0.35); color: #fef08a; border-radius: 2px; padding: 0 1px; }
      .dt-tt-banner {
        display: none; align-items: center; justify-content: space-between; gap: 8px;
        padding: 7px 10px; background: rgba(245, 158, 11, 0.16);
        border-bottom: 1px solid rgba(245, 158, 11, 0.35);
        font-size: 11.5px; color: #fde68a;
      }
      .dt-tt-banner.show { display: flex; }
      .dt-list { flex: 1; overflow: auto; padding: 6px 8px; display: flex; flex-direction: column; gap: 5px; }
      .dt-empty { padding: 24px 12px; text-align: center; color: #64748b; font-size: 12px; }
      .dt-row {
        padding: 7px 9px; border-radius: 8px;
        background: rgba(30, 41, 59, 0.6); border: 1px solid rgba(148, 163, 184, 0.14);
        display: flex; flex-direction: column; gap: 4px;
      }
      .dt-row.current { border-color: rgba(56, 189, 248, 0.55); background: rgba(14, 116, 144, 0.18); }
      .dt-row-top { display: flex; align-items: center; justify-content: space-between; gap: 6px; }
      .dt-row-title { display: flex; align-items: center; gap: 6px; font-size: 12px; font-weight: 600; color: #f1f5f9; min-width: 0; }
      .dt-idx { font-family: ui-monospace, monospace; font-size: 10.5px; color: #94a3b8; }
      .dt-time { font-family: ui-monospace, monospace; font-size: 10.5px; color: #64748b; }
      .dt-diff {
        font: 11px/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
        color: #94a3b8; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
      }
      .dt-pred {
        font-size: 10px; font-weight: 600; padding: 1px 5px; border-radius: 4px;
      }
      .dt-pred.pending { background: rgba(245, 158, 11, 0.2); color: #fcd34d; }
      .dt-pred.hit { background: rgba(34, 197, 94, 0.18); color: #86efac; }
      .dt-pred.rollback { background: rgba(239, 68, 68, 0.22); color: #fca5a5; }
      .dt-ftr {
        padding: 6px 10px; font-size: 10.5px; color: #64748b;
        border-top: 1px solid rgba(148, 163, 184, 0.12);
        display: flex; justify-content: space-between;
      }

      /* Build / Proof Error Overlay */
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
        display: flex; align-items: center; justify-content: space-between; gap: 10px;
        padding: 14px 18px; background: rgba(239, 68, 68, 0.14);
        border-bottom: 1px solid rgba(239, 68, 68, 0.28);
      }
      .hdr-actions { display: flex; align-items: center; gap: 8px; }
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
      .file-link {
        color: #7dd3fc; text-decoration: underline; text-decoration-style: dotted;
        cursor: pointer; border-radius: 3px; padding: 0 2px;
      }
      .file-link:hover { background: rgba(56, 189, 248, 0.18); color: #bae6fd; }
      .ftr {
        padding: 10px 18px; font-size: 12px; color: #94a3b8;
        border-top: 1px solid rgba(148, 163, 184, 0.14);
        display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap;
      }
    </style>

    <div class="toast" id="toast"><span class="dot" id="dot"></span><span id="msg"></span></div>

    <button class="pill" id="pill" title="Toggle Qed DevTools (Alt+Shift+Q)">
      <span class="dot ok" id="pill-dot"></span>
      <span>Qed</span>
      <span class="pill-badge" id="pill-badge">0</span>
    </button>

    <aside class="drawer" id="drawer" aria-label="Qed DevTools">
      <div class="dt-hdr">
        <div class="dt-brand">
          <span>Qed DevTools</span>
          <span class="dt-chip poll" id="dt-transport">Poll</span>
        </div>
        <div style="display:flex;gap:6px;align-items:center">
          <button class="dt-btn" id="dt-close" title="Close (Alt+Shift+Q)">Close</button>
        </div>
      </div>
      <div class="dt-tabs">
        <button class="dt-tab active" id="tab-state">State</button>
        <button class="dt-tab" id="tab-actions">Actions &amp; Time-Travel <span class="dt-count" id="tab-count">0</span></button>
      </div>
      <div class="dt-tt-banner" id="tt-banner">
        <span id="tt-label">Time-travel active</span>
        <button class="dt-btn warn" id="tt-resume">Resume Latest</button>
      </div>
      <div class="dt-pane active" id="pane-state">
        <div class="dt-toolbar">
          <input class="dt-search" id="state-filter" type="search" placeholder="Filter state keys or values…" />
          <button class="dt-btn" id="copy-state">Copy JSON</button>
        </div>
        <pre class="dt-json" id="state-json">{}</pre>
      </div>
      <div class="dt-pane" id="pane-actions">
        <div class="dt-toolbar">
          <span style="font-size:11.5px;color:#94a3b8;flex:1">Snapshots are rehydrated via verified Lean codecs</span>
          <button class="dt-btn" id="clear-actions">Clear</button>
        </div>
        <div class="dt-list" id="action-list"><div class="dt-empty">No actions recorded yet.</div></div>
      </div>
      <div class="dt-ftr">
        <span>Alt+Shift+Q to toggle</span>
        <span id="dt-meta">Dev only · excluded from dist/</span>
      </div>
    </aside>

    <div class="backdrop" id="backdrop" role="dialog" aria-modal="true" aria-label="Qed build error">
      <div class="card">
        <div class="hdr">
          <div class="title"><span class="dot error"></span><span>Build / Proof Error</span></div>
          <div class="hdr-actions">
            <button class="close" id="copy-err">Copy Error</button>
            <button class="close" id="close">Dismiss (Esc)</button>
          </div>
        </div>
        <pre class="body" id="errbody"></pre>
        <div class="ftr">
          <span>Fix the error and save — Qed will hot-reload automatically.</span>
          <span>Click any file:line to open in editor or copy location.</span>
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
  const pillEl = shadow.getElementById('pill');
  const pillDotEl = shadow.getElementById('pill-dot');
  const pillBadgeEl = shadow.getElementById('pill-badge');
  const drawerEl = shadow.getElementById('drawer');
  const dtTransportEl = shadow.getElementById('dt-transport');
  const dtCloseBtn = shadow.getElementById('dt-close');
  const tabStateBtn = shadow.getElementById('tab-state');
  const tabActionsBtn = shadow.getElementById('tab-actions');
  const tabCountEl = shadow.getElementById('tab-count');
  const paneStateEl = shadow.getElementById('pane-state');
  const paneActionsEl = shadow.getElementById('pane-actions');
  const stateFilterEl = shadow.getElementById('state-filter');
  const copyStateBtn = shadow.getElementById('copy-state');
  const stateJsonEl = shadow.getElementById('state-json');
  const ttBannerEl = shadow.getElementById('tt-banner');
  const ttLabelEl = shadow.getElementById('tt-label');
  const ttResumeBtn = shadow.getElementById('tt-resume');
  const clearActionsBtn = shadow.getElementById('clear-actions');
  const actionListEl = shadow.getElementById('action-list');
  const backdropEl = shadow.getElementById('backdrop');
  const errBodyEl = shadow.getElementById('errbody');
  const copyErrBtn = shadow.getElementById('copy-err');
  const closeBtn = shadow.getElementById('close');

  const escapeHtml = (s) => String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');

  function copyText(text, btn, origLabel) {
    const done = () => {
      btn.textContent = 'Copied!';
      setTimeout(() => { btn.textContent = origLabel; }, 1200);
    };
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(done).catch(() => {});
    } else {
      try {
        const ta = document.createElement('textarea');
        ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
        document.body.appendChild(ta); ta.select(); document.execCommand('copy'); ta.remove();
        done();
      } catch (_) {}
    }
  }

  function showToast(kind, text, autoHideMs = 0) {
    mountUi();
    if (toastTimer) { clearTimeout(toastTimer); toastTimer = null; }
    dotEl.className = 'dot ' + kind;
    pillDotEl.className = 'dot ' + kind;
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

  function renderErrorBody(errText) {
    const raw = errText || 'Build failed. Check terminal output for details.';
    const locRe = /([A-Za-z0-9_./-]+\.(?:lean|mjs|rs|css)):(\d+)(?::(\d+))?/g;
    let html = '';
    let last = 0;
    for (const m of raw.matchAll(locRe)) {
      const idx = m.index ?? 0;
      html += escapeHtml(raw.slice(last, idx));
      const full = m[0], file = m[1], line = m[2], col = m[3] || '1';
      html += `<a class="file-link" data-loc="${escapeHtml(full)}" href="vscode://file/${encodeURI(file)}:${line}:${col}" title="Click to open ${escapeHtml(full)} (Alt+click to copy)">${escapeHtml(full)}</a>`;
      last = idx + full.length;
    }
    html += escapeHtml(raw.slice(last));
    errBodyEl.innerHTML = html;
  }

  errBodyEl.addEventListener('click', (e) => {
    const link = e.target && e.target.closest ? e.target.closest('a.file-link') : null;
    if (!link) return;
    const loc = link.getAttribute('data-loc') || '';
    if (e.altKey || e.metaKey || e.ctrlKey) {
      e.preventDefault();
      if (navigator.clipboard) navigator.clipboard.writeText(loc).catch(() => {});
      showToast('ok', `Copied ${loc}`, 1400);
    }
  });

  function showOverlay(errText) {
    mountUi();
    renderErrorBody(errText);
    backdropEl.classList.add('open');
  }

  function hideOverlay() {
    backdropEl.classList.remove('open');
  }

  // ---- JSON Formatting & State Diff Helpers ----
  function tryParseJson(str) {
    if (!str) return null;
    try { return JSON.parse(str); } catch (_) { return null; }
  }

  function formatValShort(v) {
    if (v === null) return 'null';
    if (v === undefined) return '∅';
    if (typeof v === 'string') return v.length > 22 ? JSON.stringify(v.slice(0, 20) + '…') : JSON.stringify(v);
    if (typeof v === 'number' || typeof v === 'boolean') return String(v);
    if (Array.isArray(v)) return `[${v.length}]`;
    if (typeof v === 'object') return `{${Object.keys(v).length}}`;
    return String(v);
  }

  function summarizeDiff(prevRaw, nextRaw) {
    if (prevRaw === nextRaw) return '(no state change)';
    const a = tryParseJson(prevRaw);
    const b = tryParseJson(nextRaw);
    if (a && b && typeof a === 'object' && typeof b === 'object' && !Array.isArray(a) && !Array.isArray(b)) {
      const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
      const parts = [];
      for (const k of keys) {
        const va = JSON.stringify(a[k]);
        const vb = JSON.stringify(b[k]);
        if (va !== vb) {
          parts.push(`${k}: ${formatValShort(a[k])} → ${formatValShort(b[k])}`);
          if (parts.length >= 3) break;
        }
      }
      if (parts.length > 0) return parts.join(' · ');
    }
    return `${formatValShort(a)} → ${formatValShort(b)}`;
  }

  function formatTime(ts) {
    const d = new Date(ts);
    const p2 = (n) => String(n).padStart(2, '0');
    const p3 = (n) => String(n).padStart(3, '0');
    return `${p2(d.getHours())}:${p2(d.getMinutes())}:${p2(d.getSeconds())}.${p3(d.getMilliseconds())}`;
  }

  function actionLabel(detail) {
    switch (detail.kind) {
      case 'mount': return 'init';
      case 'dispatch': return `dispatch #${detail.id}`;
      case 'dispatchStr': {
        const val = detail.value !== undefined ? ` ${formatValShort(String(detail.value))}` : '';
        return `input #${detail.id}${val}`;
      }
      case 'http': return `http #${detail.id} (${detail.ok ? 'ok' : 'err'})`;
      case 'httpBytes': return `rpc #${detail.id} (${detail.ok ? 'ok' : 'err'})`;
      case 'url': return `url ${detail.path || '/'}`;
      case 'local': return `local ${detail.key}#${detail.id}`;
      case 'localStr': return `local ${detail.key}#${detail.id}`;
      case 'wsText': return `ws text #${detail.cid}`;
      case 'wsBytes': return `ws bin #${detail.cid}`;
      case 'effect': return `effect #${detail.id}`;
      case 'port': return `port ${detail.name || ''}`;
      default: return detail.kind || 'update';
    }
  }

  function currentSnapshot() {
    if (activeSnapIdx >= 0 && activeSnapIdx < history.length) return history[activeSnapIdx];
    return history.length > 0 ? history[history.length - 1] : null;
  }

  function prettyCurrentState() {
    const snap = currentSnapshot();
    const raw = snap ? snap.state : (window.qed && typeof window.qed.dehydrate === 'function' ? window.qed.dehydrate() : '');
    if (!raw) return '(empty — no dehydrated state)';
    const parsed = tryParseJson(raw);
    return parsed !== null ? JSON.stringify(parsed, null, 2) : raw;
  }

  function renderStatePane() {
    const text = prettyCurrentState();
    const q = stateFilter.trim().toLowerCase();
    if (!q) {
      stateJsonEl.textContent = text;
      return;
    }
    const lines = text.split('\n');
    const matched = lines.filter((ln) => ln.toLowerCase().includes(q));
    if (matched.length === 0) {
      stateJsonEl.textContent = `(no matches for "${stateFilter}")`;
      return;
    }
    const re = new RegExp(q.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi');
    stateJsonEl.innerHTML = matched
      .map((ln) => escapeHtml(ln).replace(re, (m) => `<mark>${m}</mark>`))
      .join('\n');
  }

  function renderActionsPane() {
    tabCountEl.textContent = String(history.length);
    pillBadgeEl.textContent = timeTravelActive ? `TT #${activeSnapIdx}` : String(history.length);
    pillBadgeEl.className = timeTravelActive ? 'pill-badge tt' : 'pill-badge';

    if (timeTravelActive && activeSnapIdx >= 0 && activeSnapIdx < history.length) {
      ttLabelEl.textContent = `Time-travel: snapshot #${activeSnapIdx} of #${history.length - 1}`;
      ttBannerEl.classList.add('show');
    } else {
      ttBannerEl.classList.remove('show');
    }

    if (history.length === 0) {
      actionListEl.innerHTML = '<div class="dt-empty">No actions recorded yet.</div>';
      return;
    }
    const frag = document.createDocumentFragment();
    for (let i = history.length - 1; i >= 0; i--) {
      const entry = history[i];
      const row = document.createElement('div');
      row.className = 'dt-row' + (i === activeSnapIdx ? ' current' : '');
      const predBadge = entry.predict
        ? `<span class="dt-pred ${entry.predict}">${entry.predict === 'pending' ? 'predict' : entry.predict === 'hit' ? 'predict hit' : 'rollback'}</span>`
        : '';
      row.innerHTML = `
        <div class="dt-row-top">
          <div class="dt-row-title">
            <span class="dt-idx">#${i}</span>
            <span>${escapeHtml(entry.label)}</span>
            ${predBadge}
          </div>
          <div style="display:flex;align-items:center;gap:6px">
            <span class="dt-time">${formatTime(entry.ts)}</span>
            <button class="dt-btn ${i === activeSnapIdx ? '' : 'primary'}" data-jump="${i}">${i === activeSnapIdx ? 'Current' : 'Jump'}</button>
          </div>
        </div>
        <div class="dt-diff" title="${escapeHtml(entry.diff)}">${escapeHtml(entry.diff)}</div>
      `;
      frag.appendChild(row);
    }
    actionListEl.innerHTML = '';
    actionListEl.appendChild(frag);
  }

  function renderDevTools() {
    if (drawerOpen) {
      renderStatePane();
      renderActionsPane();
    } else {
      pillBadgeEl.textContent = timeTravelActive ? `TT #${activeSnapIdx}` : String(history.length);
      pillBadgeEl.className = timeTravelActive ? 'pill-badge tt' : 'pill-badge';
    }
  }

  function jumpToSnapshot(idx) {
    if (idx < 0 || idx >= history.length) return;
    const fn = restoreFn || window.__qedDevRestore;
    if (typeof fn !== 'function') {
      showToast('error', 'State restore hook unavailable', 1800);
      return;
    }
    const snap = history[idx];
    activeSnapIdx = idx;
    timeTravelActive = idx !== history.length - 1;
    fn(snap.state, snap.locals);
    renderDevTools();
    showToast('ok', timeTravelActive ? `Jumped to snapshot #${idx}` : 'Resumed latest state', 1500);
  }

  function resumeLatest() {
    if (history.length === 0) return;
    jumpToSnapshot(history.length - 1);
  }

  function toggleDrawer(force) {
    mountUi();
    drawerOpen = typeof force === 'boolean' ? force : !drawerOpen;
    drawerEl.classList.toggle('open', drawerOpen);
    if (drawerOpen) renderDevTools();
  }

  function setTab(name) {
    activeTab = name;
    tabStateBtn.classList.toggle('active', name === 'state');
    tabActionsBtn.classList.toggle('active', name === 'actions');
    paneStateEl.classList.toggle('active', name === 'state');
    paneActionsEl.classList.toggle('active', name === 'actions');
    renderDevTools();
  }

  // ---- Register Dev Hook for `runtime/qed_host.mjs` ----
  window.__qedDevHook = function (kind, detail) {
    if (!detail) return;
    if (typeof detail.restoreState === 'function') restoreFn = detail.restoreState;
    if (kind === 'mount') {
      if (detail.isTimeTravel) return;
      const entry = {
        label: history.length === 0 ? 'init' : 'hmr mount',
        state: detail.state || '',
        locals: detail.locals || '',
        diff: history.length === 0 ? 'initial state' : summarizeDiff(history[history.length - 1].state, detail.state || ''),
        predict: null,
        ts: detail.ts || Date.now(),
      };
      history.push(entry);
      if (history.length > MAX_HISTORY) history.shift();
      activeSnapIdx = history.length - 1;
      timeTravelActive = false;
      renderDevTools();
      return;
    }
    if (kind === 'action') {
      const prev = history.length > 0 ? history[history.length - 1] : null;
      const nextState = detail.state || '';
      const diff = prev ? summarizeDiff(prev.state, nextState) : 'initial state';
      const inFlightNow = typeof detail.inFlightHttp === 'number' ? detail.inFlightHttp : 0;
      let predict = null;
      if ((detail.kind === 'dispatch' || detail.kind === 'dispatchStr') && inFlightNow > prevInFlightHttp && prev && prev.state !== nextState) {
        predict = 'pending';
      } else if ((detail.kind === 'http' || detail.kind === 'httpBytes') && pendingPredictIdx >= 0 && pendingPredictIdx < history.length) {
        const predictedState = history[pendingPredictIdx].state;
        const hit = nextState === predictedState;
        history[pendingPredictIdx].predict = hit ? 'hit' : 'rollback';
        predict = hit ? 'hit' : 'rollback';
        pendingPredictIdx = -1;
      }
      prevInFlightHttp = inFlightNow;
      const entry = {
        label: actionLabel(detail),
        state: nextState,
        locals: detail.locals || '',
        diff,
        predict,
        ts: detail.ts || Date.now(),
      };
      history.push(entry);
      if (history.length > MAX_HISTORY) {
        history.shift();
        if (pendingPredictIdx >= 0) pendingPredictIdx--;
      }
      if (predict === 'pending') pendingPredictIdx = history.length - 1;
      activeSnapIdx = history.length - 1;
      timeTravelActive = false;
      renderDevTools();
    }
  };

  // Capture initial state if `qed_host.mjs` already booted before `qed_dev.mjs` loaded
  if (window.qed && typeof window.qed.dehydrate === 'function' && history.length === 0) {
    try {
      const st = window.qed.dehydrate() || '';
      const loc = typeof window.qed.snapshot === 'function' ? window.qed.snapshot() || '' : '';
      history.push({ label: 'init', state: st, locals: loc, diff: 'initial state', predict: null, ts: Date.now() });
      activeSnapIdx = 0;
      renderDevTools();
    } catch (_) {}
  }

  // ---- UI Event Listeners ----
  pillEl.addEventListener('click', () => toggleDrawer());
  dtCloseBtn.addEventListener('click', () => toggleDrawer(false));
  tabStateBtn.addEventListener('click', () => setTab('state'));
  tabActionsBtn.addEventListener('click', () => setTab('actions'));
  stateFilterEl.addEventListener('input', (e) => {
    stateFilter = e.target.value || '';
    renderStatePane();
  });
  copyStateBtn.addEventListener('click', () => copyText(prettyCurrentState(), copyStateBtn, 'Copy JSON'));
  ttResumeBtn.addEventListener('click', () => resumeLatest());
  clearActionsBtn.addEventListener('click', () => {
    const cur = currentSnapshot();
    history = cur ? [{ ...cur, label: 'snapshot', diff: 'baseline' }] : [];
    activeSnapIdx = history.length - 1;
    timeTravelActive = false;
    pendingPredictIdx = -1;
    renderDevTools();
  });
  actionListEl.addEventListener('click', (e) => {
    const btn = e.target && e.target.closest ? e.target.closest('button[data-jump]') : null;
    if (!btn) return;
    const idx = parseInt(btn.getAttribute('data-jump'), 10);
    if (!Number.isNaN(idx)) jumpToSnapshot(idx);
  });

  copyErrBtn.addEventListener('click', () => copyText(lastError || errBodyEl.textContent || '', copyErrBtn, 'Copy Error'));
  closeBtn.addEventListener('click', () => {
    overlayDismissedFor = lastError;
    hideOverlay();
  });
  backdropEl.addEventListener('click', (e) => {
    if (e.target === backdropEl) { overlayDismissedFor = lastError; hideOverlay(); }
  });
  window.addEventListener('keydown', (e) => {
    if (e.altKey && e.shiftKey && (e.key === 'Q' || e.key === 'q')) {
      e.preventDefault();
      toggleDrawer();
      return;
    }
    if (e.key === 'Escape' && backdropEl.classList.contains('open')) {
      overlayDismissedFor = lastError;
      hideOverlay();
    }
  });

  // ---- HMR Apply & Status Handling ----
  function updateTransportBadge() {
    dtTransportEl.textContent = sseConnected ? 'SSE' : 'Poll';
    dtTransportEl.className = sseConnected ? 'dt-chip' : 'dt-chip poll';
  }

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

  async function handleStatus(st) {
    if (!st || typeof st !== 'object') return;
    offlineCount = 0;

    if (st.sseUrl && st.sseUrl !== sseUrl) {
      sseUrl = st.sseUrl;
      connectSse();
    }

    if (lastId === null) {
      lastId = st.id;
      lastStatus = st.status;
      if (st.status === 'error' && st.error) {
        lastError = st.error;
        showOverlay(st.error);
        showToast('error', 'Build failed');
      } else {
        pillDotEl.className = 'dot ok';
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
    pillDotEl.className = 'dot ok';
    if (recoveredFromErr) hideOverlay();

    if (st.id && st.id !== lastId) {
      lastId = st.id;
      await applyUpdate(st);
    } else if (recoveredFromErr) {
      hideToast();
    }
  }

  function startFallbackPolling() {
    if (pollTimer) return;
    pollTimer = setInterval(() => {
      if (!document.hidden && !sseConnected) poll();
    }, 180);
  }

  function stopFallbackPolling() {
    if (pollTimer) {
      clearInterval(pollTimer);
      pollTimer = null;
    }
  }

  function connectSse() {
    if (!sseUrl || typeof EventSource === 'undefined') {
      startFallbackPolling();
      return;
    }
    if (eventSource) {
      try { eventSource.close(); } catch (_) {}
      eventSource = null;
    }
    try {
      const es = new EventSource(sseUrl);
      eventSource = es;
      es.onopen = () => {
        sseConnected = true;
        stopFallbackPolling();
        updateTransportBadge();
      };
      es.onmessage = (ev) => {
        if (!ev.data) return;
        try {
          const st = JSON.parse(ev.data);
          handleStatus(st);
        } catch (_) {}
      };
      es.onerror = () => {
        sseConnected = false;
        updateTransportBadge();
        startFallbackPolling();
      };
    } catch (_) {
      sseConnected = false;
      updateTransportBadge();
      startFallbackPolling();
    }
  }

  async function poll() {
    if (inFlight) return;
    inFlight = true;
    try {
      const resp = await fetch('/__dev_status', { cache: 'no-store' });
      if (!resp.ok) throw new Error('status ' + resp.status);
      const st = await resp.json();
      await handleStatus(st);
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

  document.addEventListener('visibilitychange', () => {
    if (!document.hidden && !sseConnected) poll();
  });
  window.addEventListener('beforeunload', () => {
    stopFallbackPolling();
    if (eventSource) { try { eventSource.close(); } catch (_) {} }
  });

  if (sseUrl) {
    connectSse();
  } else {
    startFallbackPolling();
  }
  poll();
})();
