#include <lean/lean.h>
#include <string.h>

lean_object *qed_lean_io_mk_ok(lean_object *v) { return lean_io_result_mk_ok(v); }
lean_object *qed_lean_io_mk_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
int qed_lean_io_is_ok(lean_object *r) { return lean_io_result_is_ok(r) ? 1 : 0; }
lean_object *qed_lean_io_val(lean_object *r) { return lean_io_result_get_value(r); }

lean_object *qed_lean_mk_opt_none(void) { return lean_box(0); }
lean_object *qed_lean_mk_opt_some(lean_object *v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}
lean_object *qed_lean_mk_except_err_str(const char *msg, size_t len) {
    lean_object *o = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(o, 0, lean_mk_string_from_bytes(msg, len));
    return o;
}
lean_object *qed_lean_mk_except_ok(lean_object *v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}
lean_object *qed_lean_mk_prod(lean_object *a, lean_object *b) {
    lean_object *o = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(o, 0, a);
    lean_ctor_set(o, 1, b);
    return o;
}

lean_object *qed_lean_mk_ba(const uint8_t *data, size_t len) {
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len > 0 && data) memcpy(lean_sarray_cptr(ba), data, len);
    return ba;
}
const uint8_t *qed_lean_ba_ptr(lean_object *ba) { return lean_sarray_cptr(ba); }
size_t qed_lean_ba_len(lean_object *ba) { return lean_sarray_size(ba); }

lean_object *qed_lean_mk_str_bytes(const uint8_t *data, size_t len) {
    return lean_mk_string_from_bytes((const char *)data, len);
}
const char *qed_lean_str_cstr(lean_object *s) { return lean_string_cstr(s); }
size_t qed_lean_str_len(lean_object *s) { size_t n = lean_string_size(s); return n > 0 ? n - 1 : 0; }

lean_object *qed_lean_array_empty(void) { return lean_mk_empty_array(); }
lean_object *qed_lean_array_push(lean_object *a, lean_object *v) { return lean_array_push(a, v); }
size_t qed_lean_array_size(lean_object *a) { return lean_array_size(a); }
lean_object *qed_lean_array_uget(lean_object *a, size_t i) { return lean_array_uget(a, i); }

lean_object *qed_lean_ctor_get(lean_object *o, unsigned i) { return lean_ctor_get(o, i); }
unsigned qed_lean_obj_tag(lean_object *o) { return lean_obj_tag(o); }
lean_object *qed_lean_usize_to_nat(size_t n) { return lean_usize_to_nat(n); }
size_t qed_lean_usize_of_nat(lean_object *o) { return lean_usize_of_nat(o); }

lean_object *qed_lean_box(size_t n) { return lean_box(n); }
size_t qed_lean_unbox(lean_object *o) { return lean_unbox(o); }
lean_object *qed_lean_box_u32(uint32_t n) { return lean_box_uint32(n); }
lean_object *qed_lean_box_u64(uint64_t n) { return lean_box_uint64(n); }

void qed_lean_inc(lean_object *o) { lean_inc(o); }
void qed_lean_dec(lean_object *o) { lean_dec(o); }
void qed_lean_dec_ref(lean_object *o) { lean_dec_ref(o); }
void qed_lean_mark_mt(lean_object *o) { lean_mark_mt(o); }

lean_object *qed_lean_apply_1(lean_object *f, lean_object *a) { return lean_apply_1(f, a); }
lean_object *qed_lean_apply_3(lean_object *f, lean_object *a, lean_object *b, lean_object *c) {
    return lean_apply_3(f, a, b, c);
}
lean_object *qed_lean_apply_4(lean_object *f, lean_object *a, lean_object *b, lean_object *c, lean_object *d) {
    return lean_apply_4(f, a, b, c, d);
}
lean_object *qed_lean_apply_5(lean_object *f, lean_object *a, lean_object *b, lean_object *c, lean_object *d, lean_object *e) {
    return lean_apply_5(f, a, b, c, d, e);
}

lean_external_class *qed_lean_register_ext(lean_external_finalize_proc fin, lean_external_foreach_proc fe) {
    return lean_register_external_class(fin, fe);
}
lean_object *qed_lean_alloc_ext(lean_external_class *cls, void *data) { return lean_alloc_external(cls, data); }
void *qed_lean_get_ext(lean_object *o) { return lean_get_external_data(o); }
