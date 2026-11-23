// Qed Dev Live-Reload (SSE Push + Poll Fallback), State-Preserving HMR,
// Build/Proof Error Overlay & Shadow-DOM Time-Travel DevTools Drawer.
// Loaded only in `qed dev` mode; never emitted into production `dist/` bundles.
(() => {
  if (window.__qedDevClientActive) return;
  window.__qedDevClientActive = true;

  let lastId = null, lastStatus = null, lastError = '', overlayDismissedFor = null, toastTimer = null, inFlight = false, offlineCount = 0;
  let sseUrl = document.querySelector('meta[name="qed-dev-sse"]')?.getAttribute('content') || '', eventSource = null, sseConnected = false, pollTimer = null;
  let drawerOpen = false, stateFilter = '', history = [], activeSnapIdx = -1, timeTravelActive = false, prevInFlightHttp = 0, pendingPredictIdx = -1;
  const MAX_HISTORY = 200;

  // ---- Shadow-DOM UI (isolated from app styles & view invariants) ----
  const host = Object.assign(document.createElement('div'), { id: '__qed-dev-ui' }), shadow = host.attachShadow({ mode: 'open' });
  shadow.innerHTML = `<style>
    :host { all: initial; --bg: rgba(15,23,42,.94); --bd: rgba(148,163,184,.28); --bds: rgba(148,163,184,.14); --fg: #e2e8f0; --hi: #f8fafc; --mut: #94a3b8; --dim: #64748b; --acc: #7dd3fc; --abg: rgba(56,189,248,.16); --ok: #86efac; --warn: #fcd34d; --err: #fca5a5; --sans: ui-sans-serif,system-ui,-apple-system,sans-serif; --mono: ui-monospace,SFMono-Regular,Menlo,Consolas,monospace; }
    * { box-sizing: border-box; }
    .drawer.open, .backdrop.open, .dt-pane.active, .dt-tt-banner.show { display: flex; }
    .dt-brand, .dt-toolbar, .dt-row-title, .dt-row-meta, .hdr-actions, .title { display: flex; align-items: center; }
    .dt-hdr, .hdr, .dt-row-top, .dt-tt-banner { display: flex; align-items: center; justify-content: space-between; gap: 8px; }
    .dt-list, .dt-row, .dt-pane { display: flex; flex-direction: column; } .dt-pane { display: none; flex: 1; min-height: 0; }
    .toast, .pill { position: fixed; right: 14px; z-index: 2147483645; background: var(--bg); border: 1px solid var(--bd); border-radius: 999px; display: inline-flex; align-items: center; }
    .toast { bottom: 52px; padding: 6px 12px; gap: 8px; color: var(--hi); font: 500 12px/1.35 var(--sans); box-shadow: 0 8px 24px rgba(0,0,0,.28); opacity: 0; transform: translateY(6px); pointer-events: none; transition: .15s ease; } .toast.show { opacity: 1; transform: none; }
    .dot { width: 7px; height: 7px; border-radius: 50%; flex: none; } .dot.ok { background: #22c55e; } .dot.error { background: #ef4444; } .dot.building { background: #f59e0b; animation: pulse 900ms ease-in-out infinite; } @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: .35; } }
    .pill { bottom: 14px; padding: 7px 11px; gap: 7px; color: var(--fg); font: 600 11.5px/1 var(--sans); cursor: pointer; user-select: none; box-shadow: 0 6px 20px rgba(0,0,0,.32); transition: .14s ease; } .pill:hover { background: rgba(30,41,59,.98); border-color: rgba(148,163,184,.55); transform: translateY(-1px); }
    .pill-badge, .dt-chip, .dt-pred { font-size: 10px; font-weight: 600; } .pill-badge { padding: 2px 6px; border-radius: 999px; background: var(--abg); color: var(--acc); } .pill-badge.tt { background: rgba(245,158,11,.22); color: var(--warn); }
    .drawer, .card { color: var(--fg); border-radius: 12px; overflow: hidden; box-shadow: 0 22px 56px rgba(0,0,0,.55); }
    .drawer { position: fixed; right: 14px; bottom: 52px; z-index: 2147483646; width: min(460px, calc(100vw - 28px)); height: min(520px, calc(100vh - 80px)); background: rgba(15,23,42,.97); border: 1px solid var(--bd); display: none; flex-direction: column; font-family: var(--sans); backdrop-filter: blur(8px); }
    .dt-hdr { padding: 10px 12px; background: rgba(30,41,59,.72); border-bottom: 1px solid var(--bds); } .dt-brand { gap: 8px; font-size: 12.5px; font-weight: 600; color: var(--hi); }
    .dt-chip { padding: 2px 6px; border-radius: 4px; background: rgba(34,197,94,.16); color: var(--ok); letter-spacing: .02em; } .dt-chip.poll { background: rgba(148,163,184,.18); color: #cbd5e1; }
    .dt-tabs { display: flex; gap: 4px; padding: 6px 10px; border-bottom: 1px solid var(--bds); background: rgba(15,23,42,.6); }
    .dt-tab, .dt-btn, .close { all: unset; cursor: pointer; border-radius: 6px; display: inline-flex; align-items: center; }
    .dt-tab { font-size: 12px; font-weight: 500; color: var(--mut); padding: 5px 10px; gap: 6px; } .dt-tab:hover { color: var(--fg); background: rgba(148,163,184,.1); } .dt-tab.active { color: var(--hi); background: var(--abg); } .dt-count { font-size: 10px; padding: 1px 5px; border-radius: 999px; background: rgba(148,163,184,.2); color: #cbd5e1; }
    .dt-btn, .close { color: #cbd5e1; border: 1px solid var(--bd); gap: 4px; } .dt-btn { font-size: 11px; font-weight: 500; padding: 4px 8px; } .close { font-size: 12px; padding: 4px 10px; } .dt-btn:hover, .close:hover { background: rgba(148,163,184,.16); color: #fff; }
    .dt-btn.primary { border-color: rgba(56,189,248,.5); color: var(--acc); background: rgba(56,189,248,.12); } .dt-btn.primary:hover { background: rgba(56,189,248,.24); color: #fff; } .dt-btn.warn { border-color: rgba(245,158,11,.55); color: var(--warn); background: rgba(245,158,11,.16); }
    .dt-toolbar { gap: 6px; padding: 8px 10px; border-bottom: 1px solid var(--bds); } .dt-search { flex: 1; background: rgba(30,41,59,.9); color: #f1f5f9; border: 1px solid var(--bd); border-radius: 6px; padding: 5px 8px; font-size: 12px; outline: none; } .dt-search:focus { border-color: #38bdf8; }
    .dt-json, .body { margin: 0; overflow: auto; font-family: var(--mono); white-space: pre-wrap; word-break: break-word; } .dt-json { padding: 10px 12px; flex: 1; font-size: 12px; line-height: 1.5; color: var(--fg); } .dt-json mark { background: rgba(250,204,21,.35); color: #fef08a; border-radius: 2px; padding: 0 1px; }
    .dt-tt-banner { display: none; padding: 7px 10px; background: rgba(245,158,11,.16); border-bottom: 1px solid rgba(245,158,11,.35); font-size: 11.5px; color: #fde68a; }
    .dt-list { flex: 1; overflow: auto; padding: 6px 8px; gap: 5px; } .dt-empty { padding: 24px 12px; text-align: center; color: var(--dim); font-size: 12px; }
    .dt-row { padding: 7px 9px; border-radius: 8px; background: rgba(30,41,59,.6); border: 1px solid var(--bds); gap: 4px; } .dt-row.current { border-color: rgba(56,189,248,.55); background: rgba(14,116,144,.18); }
    .dt-row-top, .dt-row-title, .dt-row-meta { gap: 6px; } .dt-row-title { font-size: 12px; font-weight: 600; color: #f1f5f9; min-width: 0; } .dt-idx, .dt-time { font-family: var(--mono); font-size: 10.5px; } .dt-idx { color: var(--mut); } .dt-time { color: var(--dim); } .dt-diff { font: 11px/1.4 var(--mono); color: var(--mut); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .dt-pred { padding: 1px 5px; border-radius: 4px; } .dt-pred.pending { background: rgba(245,158,11,.2); color: var(--warn); } .dt-pred.hit { background: rgba(34,197,94,.18); color: var(--ok); } .dt-pred.rollback { background: rgba(239,68,68,.22); color: var(--err); }
    .dt-ftr, .ftr { display: flex; justify-content: space-between; border-top: 1px solid var(--bds); } .dt-ftr { padding: 6px 10px; font-size: 10.5px; color: var(--dim); }
    .backdrop { position: fixed; inset: 0; z-index: 2147483647; background: rgba(15,23,42,.78); backdrop-filter: blur(4px); display: none; align-items: flex-start; justify-content: center; padding: 48px 20px; overflow: auto; font-family: var(--sans); }
    .card { width: min(860px, 100%); background: #0f172a; border: 1px solid rgba(239,68,68,.45); } .hdr { padding: 14px 18px; background: rgba(239,68,68,.14); border-bottom: 1px solid rgba(239,68,68,.28); } .hdr-actions, .title { gap: 8px; } .title { font-size: 14px; font-weight: 600; color: var(--err); }
    .body { padding: 18px; max-height: 70vh; font-size: 13px; line-height: 1.55; color: #f1f5f9; } .file-link { color: var(--acc); text-decoration: underline dotted; cursor: pointer; border-radius: 3px; padding: 0 2px; } .file-link:hover { background: var(--abg); color: #bae6fd; } .ftr { padding: 10px 18px; font-size: 12px; color: var(--mut); gap: 12px; flex-wrap: wrap; }
  </style>
  <div class="toast" id="toast"><span class="dot" id="dot"></span><span id="msg"></span></div>
  <button class="pill" id="pill" title="Toggle Qed DevTools (Alt+Shift+Q)"><span class="dot ok" id="pill-dot"></span><span>Qed</span><span class="pill-badge" id="pill-badge">0</span></button>
  <aside class="drawer" id="drawer" aria-label="Qed DevTools">
    <div class="dt-hdr"><div class="dt-brand"><span>Qed DevTools</span><span class="dt-chip poll" id="dt-transport">Poll</span></div><button class="dt-btn" id="dt-close" title="Close (Alt+Shift+Q)">Close</button></div>
    <div class="dt-tabs"><button class="dt-tab active" id="tab-state">State</button><button class="dt-tab" id="tab-actions">Actions &amp; Time-Travel <span class="dt-count" id="tab-count">0</span></button></div>
    <div class="dt-tt-banner" id="tt-banner"><span id="tt-label">Time-travel active</span><button class="dt-btn warn" id="tt-resume">Resume Latest</button></div>
    <div class="dt-pane active" id="pane-state"><div class="dt-toolbar"><input class="dt-search" id="state-filter" type="search" placeholder="Filter state keys or values…" /><button class="dt-btn" id="copy-state">Copy JSON</button></div><pre class="dt-json" id="state-json">{}</pre></div>
    <div class="dt-pane" id="pane-actions"><div class="dt-toolbar"><span style="font-size:11.5px;color:#94a3b8;flex:1">Snapshots are rehydrated via verified Lean codecs</span><button class="dt-btn" id="clear-actions">Clear</button></div><div class="dt-list" id="action-list"><div class="dt-empty">No actions recorded yet.</div></div></div>
    <div class="dt-ftr"><span>Alt+Shift+Q to toggle</span><span id="dt-meta">Dev only · excluded from dist/</span></div>
  </aside>
  <div class="backdrop" id="backdrop" role="dialog" aria-modal="true" aria-label="Qed build error"><div class="card">
    <div class="hdr"><div class="title"><span class="dot error"></span><span>Build / Proof Error</span></div><div class="hdr-actions"><button class="close" id="copy-err">Copy Error</button><button class="close" id="close">Dismiss (Esc)</button></div></div>
    <pre class="body" id="errbody"></pre>
    <div class="ftr"><span>Fix the error and save — Qed will hot-reload automatically.</span><span>Click any file:line to open in editor or copy location.</span></div>
  </div></div>`;

  const mountUi = () => { if (document.body && !host.isConnected) document.body.appendChild(host); };
  document.body ? mountUi() : document.addEventListener('DOMContentLoaded', mountUi, { once: true });
  const $ = (id) => shadow.getElementById(id), tryCall = (fn, fb) => { try { return fn(); } catch (_) { return fb; } };
  const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }, esc = (s) => String(s).replace(/[&<>"]/g, (c) => ESC[c]);
  const setChip = (id, textContent, className) => Object.assign($(id), { textContent, className });
  const copyText = (text, onDone) => navigator.clipboard?.writeText ? navigator.clipboard.writeText(text).then(onDone, () => {}) : tryCall(() => {
    const ta = Object.assign(document.createElement('textarea'), { value: text }); ta.style.cssText = 'position:fixed;opacity:0';
    document.body.appendChild(ta); ta.select(); document.execCommand('copy'); ta.remove(); onDone();
  });
  const copyFromBtn = (text, btn, orig) => copyText(text, () => { btn.textContent = 'Copied!'; setTimeout(() => { btn.textContent = orig; }, 1200); });
  const hideToast = () => { clearTimeout(toastTimer); toastTimer = null; $('toast').classList.remove('show'); };
  const showToast = (kind, text, ms = 0) => { mountUi(); hideToast(); $('dot').className = $('pill-dot').className = 'dot ' + kind; $('msg').textContent = text; $('toast').classList.add('show'); if (ms > 0) toastTimer = setTimeout(hideToast, ms); };
  const showOverlay = (errText) => {
    mountUi(); $('backdrop').classList.add('open');
    $('errbody').innerHTML = esc(errText || 'Build failed. Check terminal output for details.').replace(/([A-Za-z0-9_./-]+\.(?:lean|mjs|rs|css)):(\d+)(?::(\d+))?/g,
      (full, f, l, c) => `<a class="file-link" data-loc="${full}" href="vscode://file/${encodeURI(f)}:${l}:${c || '1'}" title="Click to open ${full} (Alt+click to copy)">${full}</a>`);
  };
  const hideOverlay = () => $('backdrop').classList.remove('open'), dismissOverlay = () => { overlayDismissedFor = lastError; hideOverlay(); };

  // ---- JSON Formatting, State Diff & Time-Travel DevTools ----
  const tryJson = (s) => s ? tryCall(() => JSON.parse(s), null) : null;
  const fmtShort = (v) => v === null ? 'null' : v === undefined ? '∅' : typeof v === 'string' ? JSON.stringify(v.length > 22 ? v.slice(0, 20) + '…' : v)
    : Array.isArray(v) ? `[${v.length}]` : typeof v === 'object' ? `{${Object.keys(v).length}}` : String(v);
  const summarizeDiff = (prev, next) => {
    if (prev === next) return '(no state change)';
    const a = tryJson(prev), b = tryJson(next);
    if (a && b && typeof a === 'object' && typeof b === 'object' && !Array.isArray(a) && !Array.isArray(b)) {
      const parts = [];
      for (const k of new Set([...Object.keys(a), ...Object.keys(b)])) if (JSON.stringify(a[k]) !== JSON.stringify(b[k]) && parts.push(`${k}: ${fmtShort(a[k])} → ${fmtShort(b[k])}`) >= 3) break;
      if (parts.length) return parts.join(' · ');
    }
    return `${fmtShort(a)} → ${fmtShort(b)}`;
  };
  const fmtTime = (ts) => { const d = new Date(ts); return `${d.toTimeString().slice(0, 8)}.${String(d.getMilliseconds()).padStart(3, '0')}`; };
  const okTag = (p) => (d) => `${p} #${d.id} (${d.ok ? 'ok' : 'err'})`, locTag = (d) => `local ${d.key}#${d.id}`;
  const LABELS = {
    mount: () => 'init', dispatch: (d) => `dispatch #${d.id}`, effect: (d) => `effect #${d.id}`, url: (d) => `url ${d.path || '/'}`,
    dispatchStr: (d) => `input #${d.id}${d.value !== undefined ? ' ' + fmtShort(String(d.value)) : ''}`, http: okTag('http'), httpBytes: okTag('rpc'),
    local: locTag, localStr: locTag, wsText: (d) => `ws text #${d.cid}`, wsBytes: (d) => `ws bin #${d.cid}`, port: (d) => `port ${d.name || ''}`,
  };
  const PRED_TEXT = { pending: 'predict', hit: 'predict hit', rollback: 'rollback' };
  const curSnap = () => (activeSnapIdx >= 0 && activeSnapIdx < history.length) ? history[activeSnapIdx] : (history[history.length - 1] ?? null);
  const prettyState = () => { const raw = curSnap()?.state ?? (window.qed?.dehydrate?.() || ''); if (!raw) return '(empty — no dehydrated state)'; const p = tryJson(raw); return p !== null ? JSON.stringify(p, null, 2) : raw; };
  const renderStatePane = () => {
    const el = $('state-json'), text = prettyState(), q = stateFilter.trim().toLowerCase();
    if (!q) return (el.textContent = text);
    const matched = text.split('\n').filter((ln) => ln.toLowerCase().includes(q));
    if (!matched.length) return (el.textContent = `(no matches for "${stateFilter}")`);
    const re = new RegExp(q.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi');
    el.innerHTML = matched.map((ln) => esc(ln).replace(re, (m) => `<mark>${m}</mark>`)).join('\n');
  };
  const updateBadge = () => setChip('pill-badge', timeTravelActive ? `TT #${activeSnapIdx}` : String(history.length), timeTravelActive ? 'pill-badge tt' : 'pill-badge');
  const renderActionsPane = () => {
    $('tab-count').textContent = String(history.length); updateBadge();
    const showTt = timeTravelActive && activeSnapIdx >= 0 && activeSnapIdx < history.length;
    if (showTt) $('tt-label').textContent = `Time-travel: snapshot #${activeSnapIdx} of #${history.length - 1}`;
    $('tt-banner').classList.toggle('show', showTt);
    $('action-list').innerHTML = !history.length ? '<div class="dt-empty">No actions recorded yet.</div>' : history.map((e, i) => {
      const cur = i === activeSnapIdx, diff = esc(e.diff), pred = e.predict ? `<span class="dt-pred ${e.predict}">${PRED_TEXT[e.predict] || e.predict}</span>` : '';
      return `<div class="dt-row${cur ? ' current' : ''}"><div class="dt-row-top"><div class="dt-row-title"><span class="dt-idx">#${i}</span><span>${esc(e.label)}</span>${pred}</div><div class="dt-row-meta"><span class="dt-time">${fmtTime(e.ts)}</span><button class="dt-btn${cur ? '' : ' primary'}" data-jump="${i}">${cur ? 'Current' : 'Jump'}</button></div></div><div class="dt-diff" title="${diff}">${diff}</div></div>`;
    }).reverse().join('');
  };
  const renderDevTools = () => drawerOpen ? (renderStatePane(), renderActionsPane()) : updateBadge();
  const jumpToSnapshot = (idx) => {
    if (idx < 0 || idx >= history.length) return;
    if (!window.__qedHost) return showToast('error', 'State restore hook unavailable', 1800);
    activeSnapIdx = idx; timeTravelActive = idx !== history.length - 1;
    window.__qedDevRestore(history[idx].state, history[idx].locals); renderDevTools();
    showToast('ok', timeTravelActive ? `Jumped to snapshot #${idx}` : 'Resumed latest state', 1500);
  };
  const toggleDrawer = (force) => { mountUi(); drawerOpen = typeof force === 'boolean' ? force : !drawerOpen; $('drawer').classList.toggle('open', drawerOpen); if (drawerOpen) renderDevTools(); };
  const setTab = (name) => { for (const t of ['state', 'actions']) { $('tab-' + t).classList.toggle('active', t === name); $('pane-' + t).classList.toggle('active', t === name); } renderDevTools(); };
  const resetToLatest = () => { activeSnapIdx = history.length - 1; timeTravelActive = false; renderDevTools(); };

  // ---- Dev-Only State-Preserving Hot Swap (`__qedHotReload` & `__qedDevRestore`) ----
  const captureFocus = () => {
    const el = document.activeElement, root = document.getElementById('app');
    if (!el || !root?.contains(el)) return null;
    return { id: el.id || null, name: el.getAttribute('name') || null, tag: el.tagName, idx: [...root.querySelectorAll(el.tagName)].indexOf(el),
      sel: typeof el.selectionStart === 'number' ? [el.selectionStart, el.selectionEnd ?? el.selectionStart] : null };
  };
  const restoreFocus = (info) => {
    const root = info && document.getElementById('app');
    const target = root && ((info.id && document.getElementById(info.id)) || (info.name && root.querySelector(`${info.tag.toLowerCase()}[name="${CSS.escape(info.name)}"]`)) || (info.idx >= 0 ? root.querySelectorAll(info.tag)[info.idx] : null));
    if (typeof target?.focus === 'function') tryCall(() => { target.focus({ preventScroll: true }); if (info.sel && typeof target.setSelectionRange === 'function') target.setSelectionRange(...info.sel); });
  };
  const hotSwapStyles = (buildId) => Promise.all([...document.querySelectorAll('link[rel="stylesheet"]')].flatMap((oldLink) => {
    const href = oldLink.getAttribute('href') || '';
    if (!href.startsWith('/') || href.startsWith('//')) return [];
    const next = oldLink.cloneNode(false); next.setAttribute('href', `${href.split('?')[0]}?t=${encodeURIComponent(buildId)}`);
    return [new Promise((resolve) => {
      let settled = false; const done = () => { if (!settled) { settled = true; oldLink.remove(); resolve(); } };
      next.addEventListener('load', done, { once: true }); next.addEventListener('error', done, { once: true }); oldLink.after(next); setTimeout(done, 1200);
    })];
  }));
  window.__qedDevRestore = (stateJson, localsJson) => !!window.__qedHost?.remount(undefined, stateJson, localsJson, true);
  window.__qedHotReload = async function (buildId, opts = {}) {
    if ((opts.kind || 'hmr') === 'css') { await hotSwapStyles(buildId); return { mode: 'css', preserved: true }; }
    if (!window.__qedHost) throw new Error('qed host unavailable');
    const { scrollX, scrollY } = window, focus = captureFocus(), cur = window.__qedHost.active();
    const savedState = cur ? (tryCall(() => cur.dehydrate(), '') || '') : '', savedLocals = cur ? (tryCall(() => cur.snapshot(), '') || '') : '';
    const nextApp = await import(`/app.mjs?t=${encodeURIComponent(buildId)}`);
    await hotSwapStyles(buildId);
    const next = window.__qedHost.remount(nextApp, savedState, savedLocals);
    const preserved = !!(savedState && next && tryCall(() => next.dehydrate() === savedState, false));
    window.scrollTo(scrollX, scrollY); restoreFocus(focus);
    return { mode: 'hmr', preserved };
  };
  window.__qedDevHook = function (kind, d) {
    if (!d || (kind === 'mount' && d.isTimeTravel) || (kind !== 'mount' && kind !== 'action')) return;
    const prev = history[history.length - 1] ?? null, state = d.state || '', diff = prev ? summarizeDiff(prev.state, state) : 'initial state';
    let label = prev ? 'hmr mount' : 'init', predict = null;
    if (kind === 'action') {
      label = LABELS[d.kind]?.(d) ?? (d.kind || 'update');
      const inFlightNow = typeof d.inFlightHttp === 'number' ? d.inFlightHttp : 0;
      if ((d.kind === 'dispatch' || d.kind === 'dispatchStr') && inFlightNow > prevInFlightHttp && prev && prev.state !== state) predict = 'pending';
      else if ((d.kind === 'http' || d.kind === 'httpBytes') && pendingPredictIdx >= 0 && pendingPredictIdx < history.length) {
        predict = history[pendingPredictIdx].predict = state === history[pendingPredictIdx].state ? 'hit' : 'rollback'; pendingPredictIdx = -1;
      }
      prevInFlightHttp = inFlightNow;
    }
    history.push({ label, state, locals: d.locals || '', diff, predict, ts: d.ts || Date.now() });
    if (history.length > MAX_HISTORY) { history.shift(); if (pendingPredictIdx >= 0) pendingPredictIdx--; }
    if (predict === 'pending') pendingPredictIdx = history.length - 1;
    resetToLatest();
  };
  if (window.qed?.dehydrate && !history.length) tryCall(() => window.__qedDevHook('mount', { state: window.qed.dehydrate(), locals: window.qed.snapshot?.() }));

  // ---- UI Event Listeners ----
  const clicks = {
    pill: () => toggleDrawer(), 'dt-close': () => toggleDrawer(false), 'tab-state': () => setTab('state'), 'tab-actions': () => setTab('actions'),
    'copy-state': () => copyFromBtn(prettyState(), $('copy-state'), 'Copy JSON'), 'tt-resume': () => history.length && jumpToSnapshot(history.length - 1),
    'clear-actions': () => { const c = curSnap(); history = c ? [{ ...c, label: 'snapshot', diff: 'baseline' }] : []; pendingPredictIdx = -1; resetToLatest(); },
    'copy-err': () => copyFromBtn(lastError || $('errbody').textContent || '', $('copy-err'), 'Copy Error'), close: dismissOverlay,
    backdrop: (e) => e.target === $('backdrop') && dismissOverlay(),
    'action-list': (e) => { const idx = parseInt(e.target?.closest?.('button[data-jump]')?.getAttribute('data-jump'), 10); if (!Number.isNaN(idx)) jumpToSnapshot(idx); },
    errbody: (e) => { const a = e.target?.closest?.('a.file-link'); if (a && (e.altKey || e.metaKey || e.ctrlKey)) { e.preventDefault(); const loc = a.getAttribute('data-loc') || ''; copyText(loc, () => showToast('ok', `Copied ${loc}`, 1400)); } },
  };
  for (const [id, fn] of Object.entries(clicks)) $(id).addEventListener('click', fn);
  $('state-filter').addEventListener('input', (e) => { stateFilter = e.target.value || ''; renderStatePane(); });
  window.addEventListener('keydown', (e) => {
    if (e.altKey && e.shiftKey && (e.key === 'Q' || e.key === 'q')) { e.preventDefault(); toggleDrawer(); }
    else if (e.key === 'Escape' && $('backdrop').classList.contains('open')) dismissOverlay();
  });

  // ---- HMR Apply, Status Handling & SSE / Poll Transport ----
  const updateTransport = () => setChip('dt-transport', sseConnected ? 'SSE' : 'Poll', sseConnected ? 'dt-chip' : 'dt-chip poll');
  async function applyUpdate(st) {
    const kind = st.kind || 'hmr', ms = typeof st.durationMs === 'number' && st.durationMs > 0 ? ` · ${st.durationMs}ms` : '';
    if (kind === 'full' || typeof window.__qedHotReload !== 'function') return location.reload();
    try {
      const res = await window.__qedHotReload(st.id, { kind }); hideOverlay();
      showToast('ok', `${res.mode === 'css' ? 'Styles updated' : res.preserved ? 'Hot reloaded (state kept)' : 'Hot reloaded'}${ms}`, res.mode === 'css' ? 1600 : 1800);
    } catch (err) { console.warn('[qed dev] hot reload failed, falling back to full reload:', err); location.reload(); }
  }
  async function handleStatus(st) {
    if (!st || typeof st !== 'object') return;
    offlineCount = 0;
    if (st.sseUrl && st.sseUrl !== sseUrl) { sseUrl = st.sseUrl; connectSse(); }
    const first = lastId === null; if (first) lastId = st.id;
    if (st.status === 'building') { if (!first && lastStatus !== 'building') showToast('building', 'Rebuilding…'); else if (first) $('pill-dot').className = 'dot ok'; return (lastStatus = 'building'); }
    if (st.status === 'error') {
      const errText = st.error || '', isNew = errText !== lastError || lastStatus !== 'error';
      lastStatus = 'error'; lastError = errText;
      if (isNew && (!first || errText)) { showToast('error', 'Build failed'); if (errText !== overlayDismissedFor) showOverlay(errText); }
      else if (first) $('pill-dot').className = 'dot ok';
      return;
    }
    const recovered = lastStatus === 'error';
    lastStatus = 'ok'; lastError = ''; overlayDismissedFor = null; $('pill-dot').className = 'dot ok';
    if (recovered) hideOverlay();
    if (st.id && st.id !== lastId) { lastId = st.id; await applyUpdate(st); } else if (recovered) hideToast();
  }
  const pollIfVisible = () => !document.hidden && !sseConnected && poll();
  const startPoll = () => { if (!pollTimer) pollTimer = setInterval(pollIfVisible, 180); }, stopPoll = () => { clearInterval(pollTimer); pollTimer = null; };
  const closeSse = () => { if (eventSource) { tryCall(() => eventSource.close()); eventSource = null; } }, onSseDown = () => { sseConnected = false; updateTransport(); startPoll(); };
  function connectSse() {
    if (!sseUrl || typeof EventSource === 'undefined') return startPoll();
    closeSse();
    try {
      const es = eventSource = new EventSource(sseUrl);
      es.onopen = () => { sseConnected = true; stopPoll(); updateTransport(); };
      es.onmessage = (ev) => ev.data && tryCall(() => handleStatus(JSON.parse(ev.data))); es.onerror = onSseDown;
    } catch (_) { onSseDown(); }
  }
  async function poll() {
    if (inFlight) return;
    inFlight = true;
    try { const r = await fetch('/__dev_status', { cache: 'no-store' }); if (!r.ok) throw new Error('status ' + r.status); await handleStatus(await r.json()); }
    catch (_) { if (++offlineCount >= 2 && lastStatus !== 'reconnecting') { lastStatus = 'reconnecting'; showToast('building', 'Restarting server…'); } }
    finally { inFlight = false; }
  }
  document.addEventListener('visibilitychange', pollIfVisible); window.addEventListener('beforeunload', () => { stopPoll(); closeSse(); });
  sseUrl ? connectSse() : startPoll(); poll();
})();
