#include <lean/lean.h>
#include <string.h>

lean_object *qed_lean_io_mk_ok(lean_object *v) { return lean_io_result_mk_ok(v); }
lean_object *qed_lean_io_mk_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
int qed_lean_io_is_ok(lean_object *r) { return lean_io_result_is_ok(r) ? 1 : 0; }
lean_object *qed_lean_io_val(lean_object *r) { return lean_io_result_get_value(r); }

lean_object *qed_lean_mk_ctor_1(unsigned tag, lean_object *a) {
    lean_object *o = lean_alloc_ctor(tag, 1, 0);
    lean_ctor_set(o, 0, a);
    return o;
}
lean_object *qed_lean_mk_opt_none(void) { return lean_box(0); }
lean_object *qed_lean_mk_opt_some(lean_object *v) { return qed_lean_mk_ctor_1(1, v); }
lean_object *qed_lean_mk_except_err_str(const char *msg, size_t len) {
    return qed_lean_mk_ctor_1(0, lean_mk_string_from_bytes(msg, len));
}
lean_object *qed_lean_mk_except_ok(lean_object *v) { return qed_lean_mk_ctor_1(1, v); }
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
uint8_t qed_lean_ctor_get_u8(lean_object *o, unsigned offset) { return lean_ctor_get_uint8(o, offset); }
unsigned qed_lean_obj_tag(lean_object *o) { return lean_obj_tag(o); }
lean_object *qed_lean_usize_to_nat(size_t n) { return lean_usize_to_nat(n); }
size_t qed_lean_usize_of_nat(lean_object *o) { return lean_usize_of_nat(o); }
lean_object *qed_lean_int64_to_int(int64_t n) { return lean_int64_to_int(n); }
int qed_lean_int_to_i64_checked(lean_object *o, int64_t *out) {
    int64_t v = (int64_t)lean_int64_of_int(o);
    if (!lean_is_scalar(o)) {
        lean_object *rt = lean_int64_to_int(v);
        bool ok = lean_int_eq(o, rt);
        lean_dec(rt);
        if (!ok) return 0;
    }
    *out = v;
    return 1;
}

lean_object *qed_lean_box(size_t n) { return lean_box(n); }
size_t qed_lean_unbox(lean_object *o) { return lean_unbox(o); }
lean_object *qed_lean_box_u32(uint32_t n) { return lean_box_uint32(n); }
lean_object *qed_lean_box_u64(uint64_t n) { return lean_box_uint64(n); }

void qed_lean_inc(lean_object *o) { lean_inc(o); }
void qed_lean_dec(lean_object *o) { lean_dec(o); }
void qed_lean_dec_ref(lean_object *o) { lean_dec_ref(o); }
void qed_lean_mark_mt(lean_object *o) { lean_mark_mt(o); }
void qed_lean_mark_persistent(lean_object *o) { lean_mark_persistent(o); }

lean_object *qed_lean_apply_1(lean_object *f, lean_object *a) { return lean_apply_1(f, a); }
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

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
#include <stdarg.h>
/* Lean's bundled glibc 2.27 sysroot lacks `fcntl64`, while host glibc >= 2.28 headers
   redirect `libsqlite3-sys`'s `fcntl` calls to `fcntl64`. On 64-bit Linux, `off_t` and
   `struct flock` are already 64-bit, so `fcntl64` is identical to `fcntl`. */
extern int fcntl(int fd, int cmd, ...);
__attribute__((weak)) int fcntl64(int fd, int cmd, ...) {
    va_list ap;
    va_start(ap, cmd);
    void *arg = va_arg(ap, void *);
    va_end(ap);
    return fcntl(fd, cmd, arg);
}
#endif
