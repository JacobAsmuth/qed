/*
  qed_dom.c — the entire impure boundary between Lean and the browser.

  Lean → JS: the `qed_dom_*` functions implement the `@[extern]` declarations in
  `Qed/Dom.lean`. DOM nodes live in a JS-side table (`globalThis.__qed.nodes`);
  Lean refers to them by integer handle. The signatures here match exactly what
  the Lean code generator emits (UInt32 args unboxed; String args as
  `lean_object*`; the IO world token last; results boxed).

  JS → Lean: `qed_run_init` / `qed_run_dispatch` are the wrappers the JS host
  calls; they supply the IO world token and surface IO errors, then invoke the
  `@[export]`ed `qed_init` / `qed_dispatch`.
*/
#include <lean/lean.h>
#include <emscripten.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* ---- JS-side DOM node handle table --------------------------------------- */
EM_JS(void, qed_js_init, (void), {
  if (!globalThis.__qed) globalThis.__qed = {};
  if (!globalThis.__qed.nodes) globalThis.__qed.nodes = [null]; /* index 0 reserved */
});

EM_JS(int, qed_js_create_element, (const char *tag), {
  var N = globalThis.__qed.nodes;
  N.push(document.createElement(UTF8ToString(tag)));
  return N.length - 1;
});

EM_JS(int, qed_js_create_text, (const char *s), {
  var N = globalThis.__qed.nodes;
  N.push(document.createTextNode(UTF8ToString(s)));
  return N.length - 1;
});

EM_JS(void, qed_js_set_attribute, (int node, const char *k, const char *v), {
  var el = globalThis.__qed.nodes[node];
  var key = UTF8ToString(k), val = UTF8ToString(v);
  /* guard: re-setting an unchanged attribute (e.g. type="number" on every patch)
     resets a typed input's caret, so only touch it when it actually differs */
  if (el && el.getAttribute(key) !== val) el.setAttribute(key, val);
});

EM_JS(void, qed_js_remove_attribute, (int node, const char *k), {
  var el = globalThis.__qed.nodes[node];
  if (el) el.removeAttribute(UTF8ToString(k));
});

EM_JS(void, qed_js_set_value, (int node, const char *v), {
  var el = globalThis.__qed.nodes[node];
  var s = UTF8ToString(v);
  if (el && el.value !== s) el.value = s; /* guard keeps the caret when unchanged */
});

/* The current local date as ISO YYYY-MM-DD (Lean parses it into a Qed.Date). The
   returned buffer is malloc'd by stringToNewUTF8 and freed by the caller. */
EM_JS(char *, qed_js_today, (void), {
  var d = new Date();
  var p = (n) => (n < 10 ? '0' : '') + n;
  return stringToNewUTF8(d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate()));
});

/* Streaming POST. The SSE parsing + the Lean callbacks live in host.js
   (globalThis.__qed.fetchStream), so this shim is a thin delegation. */
EM_JS(void, qed_js_fetch_stream, (const char *url, const char *body, int cid, int did), {
  if (globalThis.__qed && globalThis.__qed.fetchStream)
    globalThis.__qed.fetchStream(UTF8ToString(url), UTF8ToString(body), cid, did);
});

/* HTTP request. The fetch + the Lean callback live in host.js
   (globalThis.__qed.httpSend); this shim is a thin delegation. */
EM_JS(void, qed_js_http_send, (const char *method, const char *url, const char *body, int id), {
  if (globalThis.__qed && globalThis.__qed.httpSend)
    globalThis.__qed.httpSend(UTF8ToString(method), UTF8ToString(url), UTF8ToString(body), id);
});

/* The current URL path. The returned buffer is malloc'd by stringToNewUTF8 and
   freed by the caller. */
EM_JS(char *, qed_js_current_path, (void), {
  return stringToNewUTF8(location.pathname);
});

EM_JS(void, qed_js_push_path, (const char *p), {
  history.pushState({}, '', UTF8ToString(p));
});

EM_JS(void, qed_js_append_child, (int parent, int child), {
  var N = globalThis.__qed.nodes;
  if (N[parent] && N[child]) N[parent].appendChild(N[child]);
});

EM_JS(void, qed_js_set_text, (int node, const char *s), {
  var el = globalThis.__qed.nodes[node];
  var str = UTF8ToString(s);
  /* guard: assigning textContent replaces the text node even when unchanged (and
     invalidates layout), so only touch it when it actually differs — like the
     setAttribute/setValue guards. Big win when a diff re-patches unchanged rows. */
  if (el && el.textContent !== str) el.textContent = str;
});

EM_JS(int, qed_js_child_at, (int parent, int index), {
  var p = globalThis.__qed.nodes[parent];
  if (!p) return 0;
  var c = p.childNodes[index];
  if (!c) return 0;
  var N = globalThis.__qed.nodes;
  N.push(c);
  return N.length - 1;
});

EM_JS(int, qed_js_child_count, (int parent), {
  var p = globalThis.__qed.nodes[parent];
  return p ? p.childNodes.length : 0;
});

EM_JS(void, qed_js_remove_child, (int parent, int index), {
  var p = globalThis.__qed.nodes[parent];
  if (p && p.childNodes[index]) p.removeChild(p.childNodes[index]);
});

EM_JS(void, qed_js_replace_child, (int parent, int index, int newChild), {
  var N = globalThis.__qed.nodes;
  var p = N[parent];
  if (p && N[newChild] && p.childNodes[index]) p.replaceChild(N[newChild], p.childNodes[index]);
});

EM_JS(void, qed_js_insert_before, (int parent, int index, int child), {
  var N = globalThis.__qed.nodes;
  var p = N[parent], c = N[child];
  if (!p || !c) return;
  var ref = p.childNodes[index] || null; /* null reference ⇒ append at the end */
  if (ref === c) return;                  /* already in place */
  /* Reordering an already-attached child: `moveBefore` (Chrome 133+) relocates it
     atomically, preserving focus, selection, and running animations. Plain
     `insertBefore` works everywhere but is a remove+insert, so it blurs a focused
     descendant on a move. Use moveBefore when relocating within `p`; otherwise (a
     freshly-built node, or no support) insert. */
  if (c.parentNode === p && p.moveBefore) {
    try { p.moveBefore(c, ref); return; } catch (e) { /* fall through to insertBefore */ }
  }
  p.insertBefore(c, ref);
});

EM_JS(void, qed_js_mount_root, (int node), {
  var root = document.getElementById('app');
  var el = globalThis.__qed.nodes[node];
  if (root && el) { root.replaceChildren(el); }
});

EM_JS(int, qed_js_is_connected, (int node), {
  var el = globalThis.__qed.nodes[node];
  return (el && el.isConnected) ? 1 : 0;
});

/* Native effects + ports: the switch over `kind` and the JS APIs live in host.js
   (globalThis.__qed.effect / .effectResult / .ports); these shims are thin delegations. */
EM_JS(void, qed_js_effect, (const char *kind, const char *a, const char *b, const char *c), {
  if (globalThis.__qed && globalThis.__qed.effect)
    globalThis.__qed.effect(UTF8ToString(kind), UTF8ToString(a), UTF8ToString(b), UTF8ToString(c));
});

EM_JS(void, qed_js_effect_result, (const char *kind, const char *a, const char *b, int id), {
  if (globalThis.__qed && globalThis.__qed.effectResult)
    globalThis.__qed.effectResult(UTF8ToString(kind), UTF8ToString(a), UTF8ToString(b), id);
});

EM_JS(void, qed_js_port_send, (const char *name, const char *payload), {
  var p = globalThis.__qed && globalThis.__qed.ports && globalThis.__qed.ports[UTF8ToString(name)];
  if (p) p(UTF8ToString(payload));
});

/* ---- @[extern] implementations (signatures per generated C) -------------- */
LEAN_EXPORT lean_object *qed_dom_create_element(lean_object *tag, lean_object *world) {
  (void) world;
  qed_js_init();
  uint32_t h = (uint32_t) qed_js_create_element(lean_string_cstr(tag));
  lean_dec(tag);
  return lean_io_result_mk_ok(lean_box_uint32(h));
}

LEAN_EXPORT lean_object *qed_dom_create_text(lean_object *s, lean_object *world) {
  (void) world;
  qed_js_init();
  uint32_t h = (uint32_t) qed_js_create_text(lean_string_cstr(s));
  lean_dec(s);
  return lean_io_result_mk_ok(lean_box_uint32(h));
}

LEAN_EXPORT lean_object *qed_dom_set_attribute(uint32_t node, lean_object *k, lean_object *v, lean_object *world) {
  (void) world;
  qed_js_set_attribute((int) node, lean_string_cstr(k), lean_string_cstr(v));
  lean_dec(k); lean_dec(v);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_remove_attribute(uint32_t node, lean_object *k, lean_object *world) {
  (void) world;
  qed_js_remove_attribute((int) node, lean_string_cstr(k));
  lean_dec(k);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_today(lean_object *world) {
  (void) world;
  char *s = qed_js_today();
  lean_object *r = lean_mk_string(s);
  free(s);
  return lean_io_result_mk_ok(r);
}

LEAN_EXPORT lean_object *qed_dom_set_value(uint32_t node, lean_object *v, lean_object *world) {
  (void) world;
  qed_js_set_value((int) node, lean_string_cstr(v));
  lean_dec(v);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_fetch_stream(lean_object *url, lean_object *body,
                                              uint32_t cid, uint32_t did, lean_object *world) {
  (void) world;
  qed_js_fetch_stream(lean_string_cstr(url), lean_string_cstr(body), (int) cid, (int) did);
  lean_dec(url); lean_dec(body);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_http_send(lean_object *method, lean_object *url,
                                           lean_object *body, uint32_t id, lean_object *world) {
  (void) world;
  qed_js_http_send(lean_string_cstr(method), lean_string_cstr(url), lean_string_cstr(body), (int) id);
  lean_dec(method); lean_dec(url); lean_dec(body);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_current_path(lean_object *world) {
  (void) world;
  char *s = qed_js_current_path();
  lean_object *r = lean_mk_string(s);
  free(s);
  return lean_io_result_mk_ok(r);
}

LEAN_EXPORT lean_object *qed_dom_push_path(lean_object *path, lean_object *world) {
  (void) world;
  qed_js_push_path(lean_string_cstr(path));
  lean_dec(path);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_append_child(uint32_t parent, uint32_t child, lean_object *world) {
  (void) world;
  qed_js_append_child((int) parent, (int) child);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_set_text(uint32_t node, lean_object *s, lean_object *world) {
  (void) world;
  qed_js_set_text((int) node, lean_string_cstr(s));
  lean_dec(s);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_child_at(uint32_t parent, uint32_t index, lean_object *world) {
  (void) world;
  uint32_t h = (uint32_t) qed_js_child_at((int) parent, (int) index);
  return lean_io_result_mk_ok(lean_box_uint32(h));
}

LEAN_EXPORT lean_object *qed_dom_child_count(uint32_t parent, lean_object *world) {
  (void) world;
  uint32_t n = (uint32_t) qed_js_child_count((int) parent);
  return lean_io_result_mk_ok(lean_box_uint32(n));
}

LEAN_EXPORT lean_object *qed_dom_remove_child(uint32_t parent, uint32_t index, lean_object *world) {
  (void) world;
  qed_js_remove_child((int) parent, (int) index);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_replace_child(uint32_t parent, uint32_t index, uint32_t newChild, lean_object *world) {
  (void) world;
  qed_js_replace_child((int) parent, (int) index, (int) newChild);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_insert_before(uint32_t parent, uint32_t index, uint32_t child, lean_object *world) {
  (void) world;
  qed_js_insert_before((int) parent, (int) index, (int) child);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_mount_root(uint32_t node, lean_object *world) {
  (void) world;
  qed_js_mount_root((int) node);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_is_connected(uint32_t node, lean_object *world) {
  (void) world;
  uint8_t b = (uint8_t) (qed_js_is_connected((int) node) ? 1 : 0);
  return lean_io_result_mk_ok(lean_box(b));
}

LEAN_EXPORT lean_object *qed_dom_effect(lean_object *kind, lean_object *a, lean_object *b,
                                        lean_object *c, lean_object *world) {
  (void) world;
  qed_js_effect(lean_string_cstr(kind), lean_string_cstr(a), lean_string_cstr(b), lean_string_cstr(c));
  lean_dec(kind); lean_dec(a); lean_dec(b); lean_dec(c);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_effect_result(lean_object *kind, lean_object *a, lean_object *b,
                                               uint32_t id, lean_object *world) {
  (void) world;
  qed_js_effect_result(lean_string_cstr(kind), lean_string_cstr(a), lean_string_cstr(b), (int) id);
  lean_dec(kind); lean_dec(a); lean_dec(b);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_port_send(lean_object *name, lean_object *payload, lean_object *world) {
  (void) world;
  qed_js_port_send(lean_string_cstr(name), lean_string_cstr(payload));
  lean_dec(name); lean_dec(payload);
  return lean_io_result_mk_ok(lean_box(0));
}

/* ---- JS → Lean entry points (defined by Lean codegen) -------------------- */
extern lean_object *qed_init(lean_object *world);
extern lean_object *qed_dispatch(uint32_t id, lean_object *world);
extern lean_object *qed_dispatch_str(uint32_t id, lean_object *s, lean_object *world);
extern lean_object *qed_stream_chunk(uint32_t cid, lean_object *chunk, lean_object *world);
extern lean_object *qed_stream_done(uint32_t did, lean_object *world);
extern lean_object *qed_http_done(uint32_t id, uint32_t ok, lean_object *text, lean_object *world);
extern lean_object *qed_url_changed(lean_object *path, lean_object *world);
extern lean_object *qed_local_dispatch(lean_object *key, uint32_t id, lean_object *world);
extern lean_object *qed_local_dispatch_str(lean_object *key, uint32_t id, lean_object *s, lean_object *world);
extern lean_object *qed_local_snapshot(lean_object *world);
extern lean_object *qed_local_restore(lean_object *s, lean_object *world);
extern lean_object *qed_effect_done(uint32_t id, lean_object *result, lean_object *world);
extern lean_object *qed_port_recv(lean_object *name, lean_object *payload, lean_object *world);

static void qed_run_io(lean_object *res) {
  if (lean_io_result_is_error(res)) lean_io_result_show_error(res);
  lean_dec(res);
}

EMSCRIPTEN_KEEPALIVE
void qed_run_init(void) { qed_run_io(qed_init(lean_io_mk_world())); }

EMSCRIPTEN_KEEPALIVE
void qed_run_dispatch(uint32_t id) { qed_run_io(qed_dispatch(id, lean_io_mk_world())); }

/* Input event: dispatch the field's current value to its handler. */
EMSCRIPTEN_KEEPALIVE
void qed_run_dispatch_str(uint32_t id, const char *s) {
  qed_run_io(qed_dispatch_str(id, lean_mk_string(s), lean_io_mk_world()));
}

/* Streamed chunk / end-of-stream, called by host.js as the fetch resolves. */
EMSCRIPTEN_KEEPALIVE
void qed_run_stream_chunk(uint32_t cid, const char *chunk) {
  qed_run_io(qed_stream_chunk(cid, lean_mk_string(chunk), lean_io_mk_world()));
}

EMSCRIPTEN_KEEPALIVE
void qed_run_stream_done(uint32_t did) {
  qed_run_io(qed_stream_done(did, lean_io_mk_world()));
}

/* HTTP response: dispatch the body (and ok flag) to the request's handler. */
EMSCRIPTEN_KEEPALIVE
void qed_run_http_done(uint32_t id, int ok, const char *text) {
  qed_run_io(qed_http_done(id, (uint32_t) (ok ? 1 : 0), lean_mk_string(text), lean_io_mk_world()));
}

/* URL changed (link click, back/forward, programmatic push): re-route. */
EMSCRIPTEN_KEEPALIVE
void qed_run_url_changed(const char *path) {
  qed_run_io(qed_url_changed(lean_mk_string(path), lean_io_mk_world()));
}

/* A no-arg event (click/submit/focus/blur) fired inside local instance `key`. */
EMSCRIPTEN_KEEPALIVE
void qed_run_local_dispatch(const char *key, uint32_t id) {
  qed_run_io(qed_local_dispatch(lean_mk_string(key), id, lean_io_mk_world()));
}

/* A value event (input/check/key) fired inside local instance `key`. */
EMSCRIPTEN_KEEPALIVE
void qed_run_local_dispatch_str(const char *key, uint32_t id, const char *s) {
  qed_run_io(qed_local_dispatch_str(lean_mk_string(key), id, lean_mk_string(s), lean_io_mk_world()));
}

/* Snapshot the local-state store as a JSON string. The returned buffer lives until the
   next snapshot call (cwrap reads it synchronously as a UTF8 string). */
static char *qed_snapshot_buf = 0;
EMSCRIPTEN_KEEPALIVE
const char *qed_run_local_snapshot(void) {
  lean_object *res = qed_local_snapshot(lean_io_mk_world());
  if (lean_io_result_is_error(res)) { lean_io_result_show_error(res); lean_dec(res); return ""; }
  lean_object *s = lean_io_result_get_value(res);
  if (qed_snapshot_buf) free(qed_snapshot_buf);
  qed_snapshot_buf = strdup(lean_string_cstr(s));
  lean_dec(res);
  return qed_snapshot_buf;
}

/* Restore the local-state store from a snapshot string and re-render every instance. */
EMSCRIPTEN_KEEPALIVE
void qed_run_local_restore(const char *s) {
  qed_run_io(qed_local_restore(lean_mk_string(s), lean_io_mk_world()));
}

/* A result-returning native effect resolved (host calls this with the effect id + the
   result string); dispatch it to the effect's callback. */
EMSCRIPTEN_KEEPALIVE
void qed_run_effect_done(uint32_t id, const char *result) {
  qed_run_io(qed_effect_done(id, lean_mk_string(result), lean_io_mk_world()));
}

/* An inbound port message (the app's JS called globalThis.__qed.send). */
EMSCRIPTEN_KEEPALIVE
void qed_run_port_recv(const char *name, const char *payload) {
  qed_run_io(qed_port_recv(lean_mk_string(name), lean_mk_string(payload), lean_io_mk_world()));
}
