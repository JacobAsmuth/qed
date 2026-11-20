use std::ffi::c_void;
use std::slice;

#[repr(C)]
pub struct LeanObj { _priv: [u8; 0] }

#[repr(C)]
pub struct LeanExtClass { _priv: [u8; 0] }

pub type FinalizeProc = extern "C" fn(*mut c_void);
pub type ForeachProc = extern "C" fn(*mut c_void, *mut LeanObj);

extern "C" {
    pub fn qed_lean_io_mk_ok(v: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_io_mk_err(msg: *const libc::c_char) -> *mut LeanObj;
    pub fn qed_lean_io_is_ok(r: *mut LeanObj) -> libc::c_int;
    pub fn qed_lean_io_val(r: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_mk_opt_none() -> *mut LeanObj;
    pub fn qed_lean_mk_opt_some(v: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_mk_except_err_str(msg: *const u8, len: usize) -> *mut LeanObj;
    pub fn qed_lean_mk_except_ok(v: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_mk_prod(a: *mut LeanObj, b: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_mk_ba(data: *const u8, len: usize) -> *mut LeanObj;
    pub fn qed_lean_ba_ptr(ba: *mut LeanObj) -> *const u8;
    pub fn qed_lean_ba_len(ba: *mut LeanObj) -> usize;
    pub fn qed_lean_mk_str_bytes(data: *const u8, len: usize) -> *mut LeanObj;
    pub fn qed_lean_str_cstr(s: *mut LeanObj) -> *const libc::c_char;
    pub fn qed_lean_str_len(s: *mut LeanObj) -> usize;
    pub fn qed_lean_array_empty() -> *mut LeanObj;
    pub fn qed_lean_array_push(arr: *mut LeanObj, v: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_array_size(arr: *mut LeanObj) -> usize;
    pub fn qed_lean_array_uget(arr: *mut LeanObj, i: usize) -> *mut LeanObj;
    pub fn qed_lean_ctor_get(o: *mut LeanObj, i: libc::c_uint) -> *mut LeanObj;
    pub fn qed_lean_obj_tag(o: *mut LeanObj) -> libc::c_uint;
    pub fn qed_lean_usize_to_nat(n: usize) -> *mut LeanObj;
    pub fn qed_lean_usize_of_nat(o: *mut LeanObj) -> usize;
    pub fn qed_lean_box(n: usize) -> *mut LeanObj;
    pub fn qed_lean_unbox(o: *mut LeanObj) -> usize;
    pub fn qed_lean_box_u32(n: u32) -> *mut LeanObj;
    pub fn qed_lean_box_u64(n: u64) -> *mut LeanObj;
    pub fn qed_lean_inc(o: *mut LeanObj);
    pub fn qed_lean_dec(o: *mut LeanObj);
    pub fn qed_lean_dec_ref(o: *mut LeanObj);
    pub fn qed_lean_mark_mt(o: *mut LeanObj);
    pub fn qed_lean_mark_persistent(o: *mut LeanObj);
    pub fn qed_lean_apply_1(f: *mut LeanObj, a: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_apply_4(f: *mut LeanObj, a: *mut LeanObj, b: *mut LeanObj, c: *mut LeanObj, d: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_apply_5(f: *mut LeanObj, a: *mut LeanObj, b: *mut LeanObj, c: *mut LeanObj, d: *mut LeanObj, e: *mut LeanObj) -> *mut LeanObj;
    pub fn qed_lean_register_ext(fin: FinalizeProc, fe: ForeachProc) -> *mut LeanExtClass;
    pub fn qed_lean_alloc_ext(cls: *mut LeanExtClass, data: *mut c_void) -> *mut LeanObj;
    pub fn qed_lean_get_ext(o: *mut LeanObj) -> *mut c_void;
    pub fn lean_initialize_thread();
    pub fn lean_finalize_thread();
}

#[inline]
pub unsafe fn ba_slice<'a>(ba: *mut LeanObj) -> &'a [u8] {
    let len = qed_lean_ba_len(ba);
    if len == 0 { &[] } else { slice::from_raw_parts(qed_lean_ba_ptr(ba), len) }
}

#[inline]
pub unsafe fn str_slice<'a>(s: *mut LeanObj) -> &'a str {
    let len = qed_lean_str_len(s);
    if len == 0 { "" } else { std::str::from_utf8_unchecked(slice::from_raw_parts(qed_lean_str_cstr(s) as *const u8, len)) }
}

#[inline]
pub unsafe fn mk_ba(data: &[u8]) -> *mut LeanObj { qed_lean_mk_ba(data.as_ptr(), data.len()) }

#[inline]
pub unsafe fn mk_str(s: &str) -> *mut LeanObj { qed_lean_mk_str_bytes(s.as_ptr(), s.len()) }

#[inline]
pub unsafe fn mk_io_except_err(msg: &str) -> *mut LeanObj {
    qed_lean_io_mk_ok(qed_lean_mk_except_err_str(msg.as_ptr(), msg.len()))
}

#[inline]
pub unsafe fn mk_io_except_ok(val: *mut LeanObj) -> *mut LeanObj {
    qed_lean_io_mk_ok(qed_lean_mk_except_ok(val))
}

/// Owned reference to a `lean_object*` (decrefs on drop).
pub struct LeanRef(pub *mut LeanObj);
unsafe impl Send for LeanRef {}
unsafe impl Sync for LeanRef {}

impl LeanRef {
    #[inline]
    pub unsafe fn new_persistent(ptr: *mut LeanObj) -> Self { qed_lean_mark_persistent(ptr); Self(ptr) }
    #[inline]
    pub unsafe fn clone_ptr(&self) -> *mut LeanObj { qed_lean_inc(self.0); self.0 }
}

/// Zero-copy owned view of a Lean `ByteArray` passed between handler threads and I/O workers.
pub struct WireBytes(pub LeanRef);

impl WireBytes {
    #[inline]
    pub unsafe fn from_borrowed(ba: *mut LeanObj) -> Self {
        qed_lean_inc(ba);
        qed_lean_mark_mt(ba);
        Self(LeanRef(ba))
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { ba_slice(self.0 .0) }
    }
}

impl Clone for LeanRef {
    fn clone(&self) -> Self { unsafe { qed_lean_inc(self.0) }; Self(self.0) }
}

impl Drop for LeanRef {
    fn drop(&mut self) { if !self.0.is_null() { unsafe { qed_lean_dec(self.0) }; } }
}
