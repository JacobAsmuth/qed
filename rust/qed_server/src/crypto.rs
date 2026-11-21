use std::ffi::{c_void, CString};
use std::io::Read;
use std::os::fd::FromRawFd;
use std::sync::{OnceLock, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};

use ring::digest;
use ring::hmac;
use ring::pbkdf2;
use ring::rand::{SecureRandom, SystemRandom};
use ring::signature::{KeyPair, RsaKeyPair, UnparsedPublicKey, RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_SHA256};

use crate::{last_errno, parse_pem_blocks};
use crate::lean_ffi::*;

const MAX_STATIC_FILE_BYTES: u64 = 256 * 1024 * 1024;

struct ExtClassCell(*mut LeanExtClass);
unsafe impl Send for ExtClassCell {}
unsafe impl Sync for ExtClassCell {}

static STATE_BOX_CLASS: OnceLock<ExtClassCell> = OnceLock::new();
static STATIC_DIR_CLASS: OnceLock<ExtClassCell> = OnceLock::new();

// ---- Thread-Safe Shared StateBox ----

struct StateBoxInner(RwLock<Option<*mut LeanObj>>);

extern "C" fn state_box_finalize(ptr: *mut c_void) {
    if !ptr.is_null() {
        unsafe {
            if let Ok(Some(obj)) = Box::from_raw(ptr as *mut StateBoxInner).0.into_inner() {
                qed_lean_dec(obj);
            }
        }
    }
}

extern "C" fn state_box_foreach(ptr: *mut c_void, f: *mut LeanObj) {
    if ptr.is_null() { return; }
    unsafe {
        if let Ok(g) = (*(ptr as *const StateBoxInner)).0.read() {
            if let Some(obj) = *g {
                qed_lean_inc(f);
                qed_lean_inc(obj);
                qed_lean_dec(qed_lean_apply_1(f, obj));
            }
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_new(init: *mut LeanObj) -> *mut LeanObj {
    let cls = STATE_BOX_CLASS.get_or_init(|| ExtClassCell(qed_lean_register_ext(state_box_finalize, state_box_foreach))).0;
    qed_lean_mark_mt(init);
    let inner = Box::new(StateBoxInner(RwLock::new(Some(init))));
    qed_lean_io_mk_ok(qed_lean_alloc_ext(cls, Box::into_raw(inner) as *mut c_void))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_read(box_obj: *mut LeanObj, f: *mut LeanObj) -> *mut LeanObj {
    let b = &*(qed_lean_get_ext(box_obj) as *const StateBoxInner);
    let snap = {
        let g = b.0.read().unwrap_or_else(|e| e.into_inner());
        let ptr = g.expect("StateBox empty");
        qed_lean_inc(ptr);
        ptr
    };
    qed_lean_io_mk_ok(qed_lean_apply_1(f, snap))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_modify(box_obj: *mut LeanObj, f: *mut LeanObj) -> *mut LeanObj {
    let b = &*(qed_lean_get_ext(box_obj) as *const StateBoxInner);
    let mut g = b.0.write().unwrap_or_else(|e| e.into_inner());
    let pair = qed_lean_apply_1(f, g.take().expect("StateBox empty"));
    let (new_st, ret_val) = (qed_lean_ctor_get(pair, 0), qed_lean_ctor_get(pair, 1));
    qed_lean_inc(new_st);
    qed_lean_inc(ret_val);
    qed_lean_dec_ref(pair);
    qed_lean_mark_mt(new_st);
    *g = Some(new_st);
    qed_lean_io_mk_ok(ret_val)
}

// ---- Anchored Static File Reader (`dirfd` + `openat2` / `openat` + `O_NOFOLLOW`) ----

struct StaticDirInner(libc::c_int);

extern "C" fn static_dir_finalize(ptr: *mut c_void) {
    if !ptr.is_null() {
        unsafe {
            let fd = Box::from_raw(ptr as *mut StaticDirInner).0;
            if fd >= 0 { libc::close(fd); }
        }
    }
}

extern "C" fn static_dir_foreach(_: *mut c_void, _: *mut LeanObj) {}

#[no_mangle]
pub unsafe extern "C" fn qed_server_open_static_dir(path_obj: *mut LeanObj) -> *mut LeanObj {
    let cls = STATIC_DIR_CLASS.get_or_init(|| ExtClassCell(qed_lean_register_ext(static_dir_finalize, static_dir_foreach))).0;
    let fd = CString::new(str_slice(path_obj))
        .ok()
        .map(|cs| libc::open(cs.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC))
        .unwrap_or(-1);
    qed_lean_io_mk_ok(qed_lean_alloc_ext(cls, Box::into_raw(Box::new(StaticDirInner(fd))) as *mut c_void))
}

fn open_beneath_nofollow(dirfd: libc::c_int, rel_path: &str) -> Option<libc::c_int> {
    if dirfd < 0 || rel_path.is_empty() || rel_path.starts_with('/') || rel_path.contains('\0') {
        return None;
    }
    #[cfg(target_os = "linux")]
    {
        #[repr(C)]
        struct OpenHow { flags: u64, mode: u64, resolve: u64 }
        if let Ok(cs) = CString::new(rel_path) {
            let how = OpenHow { flags: (libc::O_RDONLY | libc::O_CLOEXEC) as u64, mode: 0, resolve: 0x0C };
            let fd = unsafe {
                libc::syscall(libc::SYS_openat2, dirfd, cs.as_ptr(), &how as *const OpenHow, std::mem::size_of::<OpenHow>())
            };
            if fd >= 0 { return Some(fd as libc::c_int); }
            if last_errno() != libc::ENOSYS { return None; }
        }
    }
    // Portable fallback (macOS & pre-5.6 Linux): segment-by-segment `openat` + `O_NOFOLLOW`.
    let segs: Vec<&str> = rel_path.split('/').collect();
    let (mut cur, mut owned) = (dirfd, false);
    for (i, seg) in segs.iter().enumerate() {
        let cs = if seg.is_empty() || *seg == "." || *seg == ".." { None } else { CString::new(*seg).ok() };
        let Some(cs) = cs else {
            if owned { unsafe { libc::close(cur) }; }
            return None;
        };
        let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC
            | if i + 1 == segs.len() { 0 } else { libc::O_DIRECTORY };
        let next = unsafe { libc::openat(cur, cs.as_ptr(), flags) };
        if owned { unsafe { libc::close(cur) }; }
        if next < 0 { return None; }
        cur = next;
        owned = true;
    }
    Some(cur)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_read_static_file(
    dir_obj: *mut LeanObj,
    rel_obj: *mut LeanObj,
    head_only: u8,
) -> *mut LeanObj {
    let dirfd = (*(qed_lean_get_ext(dir_obj) as *const StaticDirInner)).0;
    let Some(fd) = open_beneath_nofollow(dirfd, str_slice(rel_obj)) else {
        return qed_lean_io_mk_ok(qed_lean_mk_opt_none());
    };
    let mut file = std::fs::File::from_raw_fd(fd);
    let Ok(meta) = file.metadata() else { return qed_lean_io_mk_ok(qed_lean_mk_opt_none()); };
    if !meta.is_file() || meta.len() > MAX_STATIC_FILE_BYTES {
        return qed_lean_io_mk_ok(qed_lean_mk_opt_none());
    }
    let fsize = meta.len() as usize;
    let mtime_ms = meta
        .modified()
        .ok()
        .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
        .map_or(0usize, |d| d.as_millis().min(usize::MAX as u128) as usize);
    if head_only != 0 {
        let inner = qed_lean_mk_prod(qed_lean_usize_to_nat(mtime_ms), mk_ba(&[]));
        let triple = qed_lean_mk_prod(qed_lean_usize_to_nat(fsize), inner);
        return qed_lean_io_mk_ok(qed_lean_mk_opt_some(triple));
    }
    let mut buf = Vec::with_capacity(fsize);
    if file.read_to_end(&mut buf).is_err() || (buf.len() as u64) > MAX_STATIC_FILE_BYTES {
        return qed_lean_io_mk_ok(qed_lean_mk_opt_none());
    }
    let inner = qed_lean_mk_prod(qed_lean_usize_to_nat(mtime_ms), mk_ba(&buf));
    let triple = qed_lean_mk_prod(qed_lean_usize_to_nat(buf.len()), inner);
    qed_lean_io_mk_ok(qed_lean_mk_opt_some(triple))
}

// ---- Environment, Clock, CSPRNG, HMAC-SHA256 & RS256 ----

#[no_mangle]
pub unsafe extern "C" fn qed_server_get_env(name_obj: *mut LeanObj) -> *mut LeanObj {
    let res = match std::env::var(str_slice(name_obj)) {
        Ok(val) => qed_lean_mk_opt_some(mk_str(&val)),
        Err(_) => qed_lean_mk_opt_none(),
    };
    qed_lean_io_mk_ok(res)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_now_ms() -> *mut LeanObj {
    let ms = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64);
    qed_lean_io_mk_ok(qed_lean_box_u64(ms))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_random_hex(num_bytes: u32) -> *mut LeanObj {
    if num_bytes == 0 { return qed_lean_io_mk_ok(mk_str("")); }
    let mut raw = vec![0u8; (num_bytes as usize).min(65536)];
    if SystemRandom::new().fill(&mut raw).is_err() {
        return qed_lean_io_mk_err(c"CSPRNG failure".as_ptr());
    }
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(raw.len() * 2);
    for b in raw {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0F) as usize]);
    }
    qed_lean_io_mk_ok(qed_lean_mk_str_bytes(out.as_ptr(), out.len()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_hmac_sha256(key_obj: *mut LeanObj, msg_obj: *mut LeanObj) -> *mut LeanObj {
    let key = hmac::Key::new(hmac::HMAC_SHA256, ba_slice(key_obj));
    let tag = hmac::sign(&key, ba_slice(msg_obj));
    qed_lean_io_mk_ok(mk_ba(tag.as_ref()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_hmac_sha256_verify(
    key_obj: *mut LeanObj,
    msg_obj: *mut LeanObj,
    sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    let key = hmac::Key::new(hmac::HMAC_SHA256, ba_slice(key_obj));
    let ok: usize = if hmac::verify(&key, ba_slice(msg_obj), ba_slice(sig_obj)).is_ok() { 1 } else { 0 };
    qed_lean_io_mk_ok(qed_lean_box(ok))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_rsa_sha256_sign(pem_obj: *mut LeanObj, msg_obj: *mut LeanObj) -> *mut LeanObj {
    let pem = str_slice(pem_obj);
    let key_pair = parse_pem_blocks(pem, "PRIVATE KEY")
        .into_iter()
        .next()
        .and_then(|der| RsaKeyPair::from_pkcs8(&der).ok())
        .or_else(|| {
            parse_pem_blocks(pem, "RSA PRIVATE KEY")
                .into_iter()
                .next()
                .and_then(|der| RsaKeyPair::from_der(&der).ok())
        });
    let Some(key_pair) = key_pair else {
        return mk_io_except_err("failed to parse RSA private key PEM");
    };
    let rng = SystemRandom::new();
    let mut sig = vec![0u8; key_pair.public().modulus_len()];
    match key_pair.sign(&RSA_PKCS1_SHA256, &rng, ba_slice(msg_obj), &mut sig) {
        Ok(()) => mk_io_except_ok(mk_ba(&sig)),
        Err(_) => mk_io_except_err("RSA-SHA256 signing failed"),
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_rsa_sha256_verify(
    pem_obj: *mut LeanObj,
    msg_obj: *mut LeanObj,
    sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    let pem = str_slice(pem_obj);
    let key_pair = parse_pem_blocks(pem, "PRIVATE KEY")
        .into_iter()
        .next()
        .and_then(|der| RsaKeyPair::from_pkcs8(&der).ok())
        .or_else(|| {
            parse_pem_blocks(pem, "RSA PRIVATE KEY")
                .into_iter()
                .next()
                .and_then(|der| RsaKeyPair::from_der(&der).ok())
        });
    let ok: usize = match key_pair {
        Some(kp) => {
            let pk = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, kp.public_key().as_ref());
            if pk.verify(ba_slice(msg_obj), ba_slice(sig_obj)).is_ok() { 1 } else { 0 }
        }
        None => 0,
    };
    qed_lean_io_mk_ok(qed_lean_box(ok))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sha256(data_obj: *mut LeanObj) -> *mut LeanObj {
    let d = digest::digest(&digest::SHA256, ba_slice(data_obj));
    qed_lean_io_mk_ok(mk_ba(d.as_ref()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_pbkdf2_sha256(
    password_obj: *mut LeanObj,
    salt_obj: *mut LeanObj,
    iterations: u32,
) -> *mut LeanObj {
    let iters = std::num::NonZeroU32::new(iterations.max(1)).unwrap();
    let mut out = [0u8; 32];
    pbkdf2::derive(
        pbkdf2::PBKDF2_HMAC_SHA256,
        iters,
        ba_slice(salt_obj),
        ba_slice(password_obj),
        &mut out,
    );
    qed_lean_io_mk_ok(mk_ba(&out))
}
