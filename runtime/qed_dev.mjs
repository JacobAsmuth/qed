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
  let stateFilter = '';
  let history = [];
  let activeSnapIdx = -1;
  let timeTravelActive = false;
  let prevInFlightHttp = 0;
  let pendingPredictIdx = -1;

  // ---- Minimal Shadow-DOM UI (isolated from app styles & view invariants) ----
  const host = document.createElement('div');
  host.id = '__qed-dev-ui';
  const shadow = host.attachShadow({ mode: 'open' });
  shadow.innerHTML = `
    <style>
      :host {
        all: initial;
        --bg: rgba(15, 23, 42, 0.94);
        --bg2: rgba(30, 41, 59, 0.72);
        --bd: rgba(148, 163, 184, 0.28);
        --bd-soft: rgba(148, 163, 184, 0.14);
        --fg: #e2e8f0;
        --fg-hi: #f8fafc;
        --mut: #94a3b8;
        --dim: #64748b;
        --acc: #7dd3fc;
        --acc-bg: rgba(56, 189, 248, 0.16);
        --ok: #22c55e;
        --warn: #f59e0b;
        --err: #ef4444;
        --sans: ui-sans-serif, system-ui, -apple-system, sans-serif;
        --mono: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      }
      * { box-sizing: border-box; }

      .toast, .pill {
        position: fixed; right: 14px; z-index: 2147483645;
        background: var(--bg); border: 1px solid var(--bd); border-radius: 999px;
        display: inline-flex; align-items: center;
      }
      .toast {
        bottom: 52px; padding: 6px 12px; gap: 8px; color: var(--fg-hi);
        font: 500 12px/1.35 var(--sans);
        box-shadow: 0 8px 24px rgba(0, 0, 0, 0.28);
        opacity: 0; transform: translateY(6px); pointer-events: none;
        transition: opacity 150ms ease, transform 150ms ease;
      }
      .toast.show { opacity: 1; transform: translateY(0); }
      .dot { width: 7px; height: 7px; border-radius: 50%; flex: none; }
      .dot.ok { background: var(--ok); }
      .dot.building { background: var(--warn); animation: pulse 900ms ease-in-out infinite; }
      .dot.error { background: var(--err); }
      @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.35; } }

      .pill {
        bottom: 14px; padding: 7px 11px; gap: 7px; color: var(--fg);
        font: 600 11.5px/1 var(--sans); cursor: pointer; user-select: none;
        box-shadow: 0 6px 20px rgba(0, 0, 0, 0.32);
        transition: background 140ms ease, border-color 140ms ease, transform 140ms ease;
      }
      .pill:hover { background: rgba(30, 41, 59, 0.98); border-color: rgba(148, 163, 184, 0.55); transform: translateY(-1px); }
      .pill-badge {
        font-size: 10px; font-weight: 600; padding: 2px 6px; border-radius: 999px;
        background: var(--acc-bg); color: var(--acc);
      }
      .pill-badge.tt { background: rgba(245, 158, 11, 0.22); color: #fcd34d; }

      .drawer, .card {
        color: var(--fg); border-radius: 12px; overflow: hidden;
        box-shadow: 0 22px 56px rgba(0, 0, 0, 0.55);
      }
      .drawer {
        position: fixed; right: 14px; bottom: 52px; z-index: 2147483646;
        width: min(460px, calc(100vw - 28px)); height: min(520px, calc(100vh - 80px));
        background: rgba(15, 23, 42, 0.97); border: 1px solid var(--bd);
        display: none; flex-direction: column;
        font-family: var(--sans); backdrop-filter: blur(8px);
      }
      .drawer.open, .backdrop.open, .dt-pane.active, .dt-tt-banner.show { display: flex; }

      .dt-hdr, .hdr {
        display: flex; align-items: center; justify-content: space-between; gap: 8px;
      }
      .dt-hdr { padding: 10px 12px; background: var(--bg2); border-bottom: 1px solid var(--bd-soft); }
      .dt-brand { display: flex; align-items: center; gap: 8px; font-size: 12.5px; font-weight: 600; color: var(--fg-hi); }
      .dt-chip {
        font-size: 10px; font-weight: 600; padding: 2px 6px; border-radius: 4px;
        background: rgba(34, 197, 94, 0.16); color: #86efac; letter-spacing: 0.02em;
      }
      .dt-chip.poll { background: rgba(148, 163, 184, 0.18); color: #cbd5e1; }
      .dt-tabs {
        display: flex; gap: 4px; padding: 6px 10px;
        border-bottom: 1px solid var(--bd-soft); background: rgba(15, 23, 42, 0.6);
      }
      .dt-tab {
        all: unset; cursor: pointer; font-size: 12px; font-weight: 500;
        color: var(--mut); padding: 5px 10px; border-radius: 6px;
        display: inline-flex; align-items: center; gap: 6px;
      }
      .dt-tab:hover { color: var(--fg); background: rgba(148, 163, 184, 0.1); }
      .dt-tab.active { color: var(--fg-hi); background: var(--acc-bg); }
      .dt-count {
        font-size: 10px; padding: 1px 5px; border-radius: 999px;
        background: rgba(148, 163, 184, 0.2); color: #cbd5e1;
      }

      .dt-btn, .close {
        all: unset; cursor: pointer; color: #cbd5e1;
        border-radius: 6px; border: 1px solid var(--bd);
        display: inline-flex; align-items: center; gap: 4px;
      }
      .dt-btn { font-size: 11px; font-weight: 500; padding: 4px 8px; }
      .close { font-size: 12px; padding: 4px 10px; }
      .dt-btn:hover, .close:hover { background: rgba(148, 163, 184, 0.16); color: #fff; }
      .dt-btn.primary { border-color: rgba(56, 189, 248, 0.5); color: var(--acc); background: rgba(56, 189, 248, 0.12); }
      .dt-btn.primary:hover { background: rgba(56, 189, 248, 0.24); color: #fff; }
      .dt-btn.warn { border-color: rgba(245, 158, 11, 0.55); color: #fcd34d; background: rgba(245, 158, 11, 0.16); }

      .dt-pane { display: none; flex: 1; min-height: 0; flex-direction: column; }
      .dt-toolbar {
        display: flex; align-items: center; gap: 6px; padding: 8px 10px;
        border-bottom: 1px solid var(--bd-soft);
      }
      .dt-search {
        flex: 1; background: rgba(30, 41, 59, 0.9); color: #f1f5f9;
        border: 1px solid var(--bd); border-radius: 6px;
        padding: 5px 8px; font-size: 12px; outline: none;
      }
      .dt-search:focus { border-color: #38bdf8; }

      .dt-json, .body {
        margin: 0; overflow: auto; font-family: var(--mono);
        white-space: pre-wrap; word-break: break-word;
      }
      .dt-json { padding: 10px 12px; flex: 1; font-size: 12px; line-height: 1.5; color: var(--fg); }
      .dt-json mark { background: rgba(250, 204, 21, 0.35); color: #fef08a; border-radius: 2px; padding: 0 1px; }
      .dt-tt-banner {
        display: none; align-items: center; justify-content: space-between; gap: 8px;
        padding: 7px 10px; background: rgba(245, 158, 11, 0.16);
        border-bottom: 1px solid rgba(245, 158, 11, 0.35);
        font-size: 11.5px; color: #fde68a;
      }
      .dt-list { flex: 1; overflow: auto; padding: 6px 8px; display: flex; flex-direction: column; gap: 5px; }
      .dt-empty { padding: 24px 12px; text-align: center; color: var(--dim); font-size: 12px; }
      .dt-row {
        padding: 7px 9px; border-radius: 8px;
        background: rgba(30, 41, 59, 0.6); border: 1px solid var(--bd-soft);
        display: flex; flex-direction: column; gap: 4px;
      }
      .dt-row.current { border-color: rgba(56, 189, 248, 0.55); background: rgba(14, 116, 144, 0.18); }
      .dt-row-top { display: flex; align-items: center; justify-content: space-between; gap: 6px; }
      .dt-row-title { display: flex; align-items: center; gap: 6px; font-size: 12px; font-weight: 600; color: #f1f5f9; min-width: 0; }
      .dt-idx, .dt-time { font-family: var(--mono); font-size: 10.5px; }
      .dt-idx { color: var(--mut); }
      .dt-time { color: var(--dim); }
      .dt-diff {
        font: 11px/1.4 var(--mono); color: var(--mut);
        white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
      }
      .dt-pred { font-size: 10px; font-weight: 600; padding: 1px 5px; border-radius: 4px; }
      .dt-pred.pending { background: rgba(245, 158, 11, 0.2); color: #fcd34d; }
      .dt-pred.hit { background: rgba(34, 197, 94, 0.18); color: #86efac; }
      .dt-pred.rollback { background: rgba(239, 68, 68, 0.22); color: #fca5a5; }

      .dt-ftr, .ftr { display: flex; justify-content: space-between; border-top: 1px solid var(--bd-soft); }
      .dt-ftr { padding: 6px 10px; font-size: 10.5px; color: var(--dim); }

      .backdrop {
        position: fixed; inset: 0; z-index: 2147483647;
        background: rgba(15, 23, 42, 0.78); backdrop-filter: blur(4px);
        display: none; align-items: flex-start; justify-content: center;
        padding: 48px 20px; overflow: auto; font-family: var(--sans);
      }
      .card { width: min(860px, 100%); background: #0f172a; border: 1px solid rgba(239, 68, 68, 0.45); }
      .hdr { padding: 14px 18px; background: rgba(239, 68, 68, 0.14); border-bottom: 1px solid rgba(239, 68, 68, 0.28); }
      .hdr-actions { display: flex; align-items: center; gap: 8px; }
      .title { font-size: 14px; font-weight: 600; color: #fca5a5; display: flex; align-items: center; gap: 8px; }
      .body { padding: 18px; max-height: 70vh; font-size: 13px; line-height: 1.55; color: #f1f5f9; }
      .file-link {
        color: var(--acc); text-decoration: underline; text-decoration-style: dotted;
        cursor: pointer; border-radius: 3px; padding: 0 2px;
      }
      .file-link:hover { background: var(--acc-bg); color: #bae6fd; }
      .ftr { padding: 10px 18px; font-size: 12px; color: var(--mut); gap: 12px; flex-wrap: wrap; }
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
        <button class="dt-btn" id="dt-close" title="Close (Alt+Shift+Q)">Close</button>
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

  const $ = (id) => shadow.getElementById(id);
  const escapeHtml = (s) => String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

  function copyText(text, onDone) {
    if (navigator.clipboard?.writeText) {
      navigator.clipboard.writeText(text).then(onDone).catch(() => {});
      return;
    }
    try {
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.style.cssText = 'position:fixed;opacity:0';
      document.body.appendChild(ta);
      ta.select();
      document.execCommand('copy');
      ta.remove();
      onDone();
    } catch (_) {}
  }

  function copyFromBtn(text, btn, origLabel) {
    copyText(text, () => {
      btn.textContent = 'Copied!';
      setTimeout(() => { btn.textContent = origLabel; }, 1200);
    });
  }

  function showToast(kind, text, autoHideMs = 0) {
    mountUi();
    if (toastTimer) { clearTimeout(toastTimer); toastTimer = null; }
    $('dot').className = 'dot ' + kind;
    $('pill-dot').className = 'dot ' + kind;
    $('msg').textContent = text;
    $('toast').classList.add('show');
    if (autoHideMs > 0) {
      toastTimer = setTimeout(() => { $('toast').classList.remove('show'); }, autoHideMs);
    }
  }

  function hideToast() {
    if (toastTimer) { clearTimeout(toastTimer); toastTimer = null; }
    $('toast').classList.remove('show');
  }

  function renderErrorBody(errText) {
    const raw = errText || 'Build failed. Check terminal output for details.';
    const locRe = /([A-Za-z0-9_./-]+\.(?:lean|mjs|rs|css)):(\d+)(?::(\d+))?/g;
    let html = '', last = 0;
    for (const m of raw.matchAll(locRe)) {
      const idx = m.index ?? 0;
      html += escapeHtml(raw.slice(last, idx));
      const full = m[0], file = m[1], line = m[2], col = m[3] || '1';
      html += `<a class="file-link" data-loc="${escapeHtml(full)}" href="vscode://file/${encodeURI(file)}:${line}:${col}" title="Click to open ${escapeHtml(full)} (Alt+click to copy)">${escapeHtml(full)}</a>`;
      last = idx + full.length;
    }
    $('errbody').innerHTML = html + escapeHtml(raw.slice(last));
  }

  const showOverlay = (errText) => { mountUi(); renderErrorBody(errText); $('backdrop').classList.add('open'); };
  const hideOverlay = () => $('backdrop').classList.remove('open');
  const dismissOverlay = () => { overlayDismissedFor = lastError; hideOverlay(); };

  // ---- JSON Formatting & State Diff Helpers ----
  const tryParseJson = (str) => { if (!str) return null; try { return JSON.parse(str); } catch (_) { return null; } };

  function formatValShort(v) {
    if (v === null) return 'null';
    if (v === undefined) return '∅';
    if (typeof v === 'string') return JSON.stringify(v.length > 22 ? v.slice(0, 20) + '…' : v);
    if (typeof v === 'number' || typeof v === 'boolean') return String(v);
    if (Array.isArray(v)) return `[${v.length}]`;
    if (typeof v === 'object') return `{${Object.keys(v).length}}`;
    return String(v);
  }

  function summarizeDiff(prevRaw, nextRaw) {
    if (prevRaw === nextRaw) return '(no state change)';
    const a = tryParseJson(prevRaw), b = tryParseJson(nextRaw);
    if (a && b && typeof a === 'object' && typeof b === 'object' && !Array.isArray(a) && !Array.isArray(b)) {
      const parts = [];
      for (const k of new Set([...Object.keys(a), ...Object.keys(b)])) {
        if (JSON.stringify(a[k]) !== JSON.stringify(b[k])) {
          parts.push(`${k}: ${formatValShort(a[k])} → ${formatValShort(b[k])}`);
          if (parts.length >= 3) break;
        }
      }
      if (parts.length > 0) return parts.join(' · ');
    }
    return `${formatValShort(a)} → ${formatValShort(b)}`;
  }

  const formatTime = (ts) => {
    const d = new Date(ts), p = (n, w = 2) => String(n).padStart(w, '0');
    return `${p(d.getHours())}:${p(d.getMinutes())}:${p(d.getSeconds())}.${p(d.getMilliseconds(), 3)}`;
  };

  const ACTION_LABELS = {
    mount: () => 'init',
    dispatch: (d) => `dispatch #${d.id}`,
    dispatchStr: (d) => `input #${d.id}${d.value !== undefined ? ` ${formatValShort(String(d.value))}` : ''}`,
    http: (d) => `http #${d.id} (${d.ok ? 'ok' : 'err'})`,
    httpBytes: (d) => `rpc #${d.id} (${d.ok ? 'ok' : 'err'})`,
    url: (d) => `url ${d.path || '/'}`,
    local: (d) => `local ${d.key}#${d.id}`,
    localStr: (d) => `local ${d.key}#${d.id}`,
    wsText: (d) => `ws text #${d.cid}`,
    wsBytes: (d) => `ws bin #${d.cid}`,
    effect: (d) => `effect #${d.id}`,
    port: (d) => `port ${d.name || ''}`,
  };
  const actionLabel = (d) => (ACTION_LABELS[d.kind] ? ACTION_LABELS[d.kind](d) : d.kind || 'update');

  const currentSnapshot = () =>
    (activeSnapIdx >= 0 && activeSnapIdx < history.length) ? history[activeSnapIdx]
      : (history.length > 0 ? history[history.length - 1] : null);

  function prettyCurrentState() {
    const snap = currentSnapshot();
    const raw = snap ? snap.state : (window.qed?.dehydrate ? window.qed.dehydrate() : '');
    if (!raw) return '(empty — no dehydrated state)';
    const parsed = tryParseJson(raw);
    return parsed !== null ? JSON.stringify(parsed, null, 2) : raw;
  }

  function renderStatePane() {
    const el = $('state-json');
    const text = prettyCurrentState();
    const q = stateFilter.trim().toLowerCase();
    if (!q) { el.textContent = text; return; }
    const matched = text.split('\n').filter((ln) => ln.toLowerCase().includes(q));
    if (matched.length === 0) { el.textContent = `(no matches for "${stateFilter}")`; return; }
    const re = new RegExp(q.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi');
    el.innerHTML = matched.map((ln) => escapeHtml(ln).replace(re, (m) => `<mark>${m}</mark>`)).join('\n');
  }

  function updateBadge() {
    const badge = $('pill-badge');
    badge.textContent = timeTravelActive ? `TT #${activeSnapIdx}` : String(history.length);
    badge.className = timeTravelActive ? 'pill-badge tt' : 'pill-badge';
  }

  function renderActionsPane() {
    $('tab-count').textContent = String(history.length);
    updateBadge();

    const showTt = timeTravelActive && activeSnapIdx >= 0 && activeSnapIdx < history.length;
    if (showTt) $('tt-label').textContent = `Time-travel: snapshot #${activeSnapIdx} of #${history.length - 1}`;
    $('tt-banner').classList.toggle('show', showTt);

    const listEl = $('action-list');
    if (history.length === 0) {
      listEl.innerHTML = '<div class="dt-empty">No actions recorded yet.</div>';
      return;
    }
    const predText = { pending: 'predict', hit: 'predict hit', rollback: 'rollback' };
    const frag = document.createDocumentFragment();
    for (let i = history.length - 1; i >= 0; i--) {
      const entry = history[i], isCur = i === activeSnapIdx;
      const row = document.createElement('div');
      row.className = 'dt-row' + (isCur ? ' current' : '');
      const predBadge = entry.predict ? `<span class="dt-pred ${entry.predict}">${predText[entry.predict] || entry.predict}</span>` : '';
      row.innerHTML = `
        <div class="dt-row-top">
          <div class="dt-row-title">
            <span class="dt-idx">#${i}</span>
            <span>${escapeHtml(entry.label)}</span>
            ${predBadge}
          </div>
          <div style="display:flex;align-items:center;gap:6px">
            <span class="dt-time">${formatTime(entry.ts)}</span>
            <button class="dt-btn ${isCur ? '' : 'primary'}" data-jump="${i}">${isCur ? 'Current' : 'Jump'}</button>
          </div>
        </div>
        <div class="dt-diff" title="${escapeHtml(entry.diff)}">${escapeHtml(entry.diff)}</div>
      `;
      frag.appendChild(row);
    }
    listEl.innerHTML = '';
    listEl.appendChild(frag);
  }

  function renderDevTools() {
    if (drawerOpen) { renderStatePane(); renderActionsPane(); }
    else updateBadge();
  }

  function jumpToSnapshot(idx) {
    if (idx < 0 || idx >= history.length) return;
    if (!window.__qedHost) { showToast('error', 'State restore hook unavailable', 1800); return; }
    const snap = history[idx];
    activeSnapIdx = idx;
    timeTravelActive = idx !== history.length - 1;
    window.__qedDevRestore(snap.state, snap.locals);
    renderDevTools();
    showToast('ok', timeTravelActive ? `Jumped to snapshot #${idx}` : 'Resumed latest state', 1500);
  }

  function toggleDrawer(force) {
    mountUi();
    drawerOpen = typeof force === 'boolean' ? force : !drawerOpen;
    $('drawer').classList.toggle('open', drawerOpen);
    if (drawerOpen) renderDevTools();
  }

  function setTab(name) {
    for (const t of ['state', 'actions']) {
      $('tab-' + t).classList.toggle('active', t === name);
      $('pane-' + t).classList.toggle('active', t === name);
    }
    renderDevTools();
  }

  function pushHistory(entry) {
    history.push(entry);
    if (history.length > MAX_HISTORY) {
      history.shift();
      if (pendingPredictIdx >= 0) pendingPredictIdx--;
    }
    if (entry.predict === 'pending') pendingPredictIdx = history.length - 1;
    activeSnapIdx = history.length - 1;
    timeTravelActive = false;
    renderDevTools();
  }

  // ---- Dev-Only State-Preserving Hot Swap (`__qedHotReload` & `__qedDevRestore`) ----
  function captureFocus() {
    const el = document.activeElement, root = document.getElementById('app');
    if (!el || !root || !root.contains(el)) return null;
    return {
      id: el.id || null,
      name: el.getAttribute('name') || null,
      tag: el.tagName,
      selStart: typeof el.selectionStart === 'number' ? el.selectionStart : null,
      selEnd: typeof el.selectionEnd === 'number' ? el.selectionEnd : null,
      idx: Array.prototype.indexOf.call(root.querySelectorAll(el.tagName), el),
    };
  }

  function restoreFocus(info) {
    const root = info && document.getElementById('app');
    if (!root) return;
    const target = (info.id && document.getElementById(info.id))
      || (info.name && root.querySelector(`${info.tag.toLowerCase()}[name="${CSS.escape(info.name)}"]`))
      || (info.idx >= 0 ? root.querySelectorAll(info.tag)[info.idx] : null);
    if (!target || typeof target.focus !== 'function') return;
    try {
      target.focus({ preventScroll: true });
      if (info.selStart !== null && typeof target.setSelectionRange === 'function') {
        target.setSelectionRange(info.selStart, info.selEnd ?? info.selStart);
      }
    } catch (_) {}
  }

  function hotSwapStyles(buildId) {
    const loads = [];
    for (const oldLink of [...document.querySelectorAll('link[rel="stylesheet"]')]) {
      const rawHref = oldLink.getAttribute('href') || '';
      if (!rawHref.startsWith('/') || rawHref.startsWith('//')) continue;
      const nextLink = oldLink.cloneNode(false);
      nextLink.setAttribute('href', `${rawHref.split('?')[0]}?t=${encodeURIComponent(buildId)}`);
      loads.push(new Promise((resolve) => {
        const done = () => { if (oldLink.parentNode) oldLink.remove(); resolve(); };
        nextLink.addEventListener('load', done, { once: true });
        nextLink.addEventListener('error', done, { once: true });
        oldLink.after(nextLink);
        setTimeout(done, 1200);
      }));
    }
    return Promise.all(loads);
  }

  window.__qedDevRestore = (stateJson, localsJson) =>
    !!(window.__qedHost && window.__qedHost.remount(undefined, stateJson, localsJson, true));

  window.__qedHotReload = async function (buildId, opts = {}) {
    const kind = opts.kind || 'hmr';
    if (kind === 'css') {
      await hotSwapStyles(buildId);
      return { mode: 'css', preserved: true };
    }
    if (!window.__qedHost) throw new Error('qed host unavailable');
    const scrollX = window.scrollX, scrollY = window.scrollY;
    const focus = captureFocus();
    const cur = window.__qedHost.active();
    let savedState = '', savedLocals = '';
    if (cur) {
      try { savedState = cur.dehydrate() || ''; } catch (_) {}
      try { savedLocals = cur.snapshot() || ''; } catch (_) {}
    }
    const nextApp = await import(`/app.mjs?t=${encodeURIComponent(buildId)}`);
    await hotSwapStyles(buildId);
    const next = window.__qedHost.remount(nextApp, savedState, savedLocals);
    let preserved = false;
    if (savedState && next) {
      try { preserved = next.dehydrate() === savedState; } catch (_) {}
    }
    window.scrollTo(scrollX, scrollY);
    restoreFocus(focus);
    return { mode: 'hmr', preserved };
  };

  // ---- Register Dev Hook for `runtime/qed_host.mjs` ----
  window.__qedDevHook = function (kind, detail) {
    if (!detail) return;
    if (kind === 'mount') {
      if (detail.isTimeTravel) return;
      const state = detail.state || '';
      pushHistory({
        label: history.length === 0 ? 'init' : 'hmr mount',
        state,
        locals: detail.locals || '',
        diff: history.length === 0 ? 'initial state' : summarizeDiff(history[history.length - 1].state, state),
        predict: null,
        ts: detail.ts || Date.now(),
      });
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
        predict = nextState === history[pendingPredictIdx].state ? 'hit' : 'rollback';
        history[pendingPredictIdx].predict = predict;
        pendingPredictIdx = -1;
      }
      prevInFlightHttp = inFlightNow;
      pushHistory({ label: actionLabel(detail), state: nextState, locals: detail.locals || '', diff, predict, ts: detail.ts || Date.now() });
    }
  };

  // Capture initial state if `qed_host.mjs` already booted before `qed_dev.mjs` loaded
  if (window.qed?.dehydrate && history.length === 0) {
    try {
      pushHistory({
        label: 'init',
        state: window.qed.dehydrate() || '',
        locals: window.qed.snapshot ? window.qed.snapshot() || '' : '',
        diff: 'initial state',
        predict: null,
        ts: Date.now(),
      });
    } catch (_) {}
  }

  // ---- UI Event Listeners ----
  const clickHandlers = {
    pill: () => toggleDrawer(),
    'dt-close': () => toggleDrawer(false),
    'tab-state': () => setTab('state'),
    'tab-actions': () => setTab('actions'),
    'copy-state': () => copyFromBtn(prettyCurrentState(), $('copy-state'), 'Copy JSON'),
    'tt-resume': () => { if (history.length > 0) jumpToSnapshot(history.length - 1); },
    'clear-actions': () => {
      const cur = currentSnapshot();
      history = cur ? [{ ...cur, label: 'snapshot', diff: 'baseline' }] : [];
      activeSnapIdx = history.length - 1;
      timeTravelActive = false;
      pendingPredictIdx = -1;
      renderDevTools();
    },
    'copy-err': () => copyFromBtn(lastError || $('errbody').textContent || '', $('copy-err'), 'Copy Error'),
    close: dismissOverlay,
  };
  for (const [id, fn] of Object.entries(clickHandlers)) $(id).addEventListener('click', fn);

  $('state-filter').addEventListener('input', (e) => { stateFilter = e.target.value || ''; renderStatePane(); });
  $('action-list').addEventListener('click', (e) => {
    const btn = e.target?.closest?.('button[data-jump]');
    const idx = btn ? parseInt(btn.getAttribute('data-jump'), 10) : NaN;
    if (!Number.isNaN(idx)) jumpToSnapshot(idx);
  });
  $('errbody').addEventListener('click', (e) => {
    const link = e.target?.closest?.('a.file-link');
    if (link && (e.altKey || e.metaKey || e.ctrlKey)) {
      e.preventDefault();
      const loc = link.getAttribute('data-loc') || '';
      copyText(loc, () => showToast('ok', `Copied ${loc}`, 1400));
    }
  });
  $('backdrop').addEventListener('click', (e) => { if (e.target === $('backdrop')) dismissOverlay(); });
  window.addEventListener('keydown', (e) => {
    if (e.altKey && e.shiftKey && (e.key === 'Q' || e.key === 'q')) { e.preventDefault(); toggleDrawer(); }
    else if (e.key === 'Escape' && $('backdrop').classList.contains('open')) dismissOverlay();
  });

  // ---- HMR Apply & Status Handling ----
  function updateTransportBadge() {
    const el = $('dt-transport');
    el.textContent = sseConnected ? 'SSE' : 'Poll';
    el.className = sseConnected ? 'dt-chip' : 'dt-chip poll';
  }

  async function applyUpdate(st) {
    const kind = st.kind || 'hmr';
    const ms = typeof st.durationMs === 'number' && st.durationMs > 0 ? ` · ${st.durationMs}ms` : '';
    if (kind === 'full' || typeof window.__qedHotReload !== 'function') { location.reload(); return; }
    try {
      const res = await window.__qedHotReload(st.id, { kind });
      hideOverlay();
      const label = res.mode === 'css' ? 'Styles updated'
        : res.preserved ? 'Hot reloaded (state kept)' : 'Hot reloaded';
      showToast('ok', `${label}${ms}`, res.mode === 'css' ? 1600 : 1800);
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
        $('pill-dot').className = 'dot ok';
      }
      return;
    }

    if (st.status === 'building') {
      if (lastStatus !== 'building') showToast('building', 'Rebuilding…');
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

    const recoveredFromErr = lastStatus === 'error';
    lastStatus = 'ok';
    lastError = '';
    overlayDismissedFor = null;
    $('pill-dot').className = 'dot ok';
    if (recoveredFromErr) hideOverlay();

    if (st.id && st.id !== lastId) {
      lastId = st.id;
      await applyUpdate(st);
    } else if (recoveredFromErr) {
      hideToast();
    }
  }

  function startFallbackPolling() {
    if (!pollTimer) pollTimer = setInterval(() => { if (!document.hidden && !sseConnected) poll(); }, 180);
  }
  function stopFallbackPolling() {
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
  }
  function onSseDown() {
    sseConnected = false;
    updateTransportBadge();
    startFallbackPolling();
  }

  function connectSse() {
    if (!sseUrl || typeof EventSource === 'undefined') { startFallbackPolling(); return; }
    if (eventSource) { try { eventSource.close(); } catch (_) {} eventSource = null; }
    try {
      const es = new EventSource(sseUrl);
      eventSource = es;
      es.onopen = () => { sseConnected = true; stopFallbackPolling(); updateTransportBadge(); };
      es.onmessage = (ev) => { if (ev.data) { try { handleStatus(JSON.parse(ev.data)); } catch (_) {} } };
      es.onerror = onSseDown;
    } catch (_) {
      onSseDown();
    }
  }

  async function poll() {
    if (inFlight) return;
    inFlight = true;
    try {
      const resp = await fetch('/__dev_status', { cache: 'no-store' });
      if (!resp.ok) throw new Error('status ' + resp.status);
      await handleStatus(await resp.json());
    } catch (_) {
      if (++offlineCount >= 2 && lastStatus !== 'reconnecting') {
        lastStatus = 'reconnecting';
        showToast('building', 'Restarting server…');
      }
    } finally {
      inFlight = false;
    }
  }

  document.addEventListener('visibilitychange', () => { if (!document.hidden && !sseConnected) poll(); });
  window.addEventListener('beforeunload', () => {
    stopFallbackPolling();
    if (eventSource) { try { eventSource.close(); } catch (_) {} }
  });

  if (sseUrl) connectSse();
  else startFallbackPolling();
  poll();
})();
