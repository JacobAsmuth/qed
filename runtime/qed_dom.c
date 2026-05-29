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

/* ---- JS-side DOM node handle table --------------------------------------- */
EM_JS(void, qed_js_init, (void), {
  if (!globalThis.__qed) globalThis.__qed = { nodes: [null] }; /* index 0 reserved */
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
  if (el) el.setAttribute(UTF8ToString(k), UTF8ToString(v));
});

EM_JS(void, qed_js_clear_attributes, (int node), {
  var el = globalThis.__qed.nodes[node];
  if (el && el.attributes) {
    while (el.attributes.length > 0) el.removeAttribute(el.attributes[0].name);
  }
});

EM_JS(void, qed_js_append_child, (int parent, int child), {
  var N = globalThis.__qed.nodes;
  if (N[parent] && N[child]) N[parent].appendChild(N[child]);
});

EM_JS(void, qed_js_set_text, (int node, const char *s), {
  var el = globalThis.__qed.nodes[node];
  if (el) el.textContent = UTF8ToString(s);
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

EM_JS(void, qed_js_replace_child, (int parent, int index, int newChild), {
  var N = globalThis.__qed.nodes;
  var p = N[parent];
  if (p && N[newChild] && p.childNodes[index]) p.replaceChild(N[newChild], p.childNodes[index]);
});

EM_JS(void, qed_js_mount_root, (int node), {
  var root = document.getElementById('app');
  var el = globalThis.__qed.nodes[node];
  if (root && el) { root.replaceChildren(el); }
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

LEAN_EXPORT lean_object *qed_dom_clear_attributes(uint32_t node, lean_object *world) {
  (void) world;
  qed_js_clear_attributes((int) node);
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

LEAN_EXPORT lean_object *qed_dom_replace_child(uint32_t parent, uint32_t index, uint32_t newChild, lean_object *world) {
  (void) world;
  qed_js_replace_child((int) parent, (int) index, (int) newChild);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *qed_dom_mount_root(uint32_t node, lean_object *world) {
  (void) world;
  qed_js_mount_root((int) node);
  return lean_io_result_mk_ok(lean_box(0));
}

/* ---- JS → Lean entry points (defined by Lean codegen) -------------------- */
extern lean_object *qed_init(lean_object *world);
extern lean_object *qed_dispatch(uint32_t id, lean_object *world);

static void qed_run_io(lean_object *res) {
  if (lean_io_result_is_error(res)) lean_io_result_show_error(res);
  lean_dec(res);
}

EMSCRIPTEN_KEEPALIVE
void qed_run_init(void) { qed_run_io(qed_init(lean_io_mk_world())); }

EMSCRIPTEN_KEEPALIVE
void qed_run_dispatch(uint32_t id) { qed_run_io(qed_dispatch(id, lean_io_mk_world())); }
