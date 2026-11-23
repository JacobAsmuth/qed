use std::cell::RefCell;
use std::ffi::{c_void, CString};
use std::io::Read;
use std::os::fd::FromRawFd;
use std::sync::{OnceLock, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};

use ring::{digest, hmac, pbkdf2};
use ring::rand::{SecureRandom, SystemRandom};
use ring::signature::{
    EcdsaKeyPair, KeyPair, RsaKeyPair, UnparsedPublicKey,
    ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA256_FIXED_SIGNING,
    RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_SHA256,
};

use crate::lean_ffi::*;
use crate::{last_errno, parse_pem_blocks, read_unpoison, write_unpoison};

const MAX_STATIC_FILE_BYTES: u64 = 256 * 1024 * 1024;

struct ExtClassCell(*mut LeanExtClass);
unsafe impl Send for ExtClassCell {}
unsafe impl Sync for ExtClassCell {}

static STATE_BOX_CLASS: OnceLock<ExtClassCell> = OnceLock::new();
static STATIC_DIR_CLASS: OnceLock<ExtClassCell> = OnceLock::new();

extern "C" fn drop_ext<T>(ptr: *mut c_void) {
    if !ptr.is_null() { unsafe { drop(Box::from_raw(ptr as *mut T)); } }
}

extern "C" fn noop_foreach(_: *mut c_void, _: *mut LeanObj) {}

unsafe fn alloc_ext_io<T>(cell: &OnceLock<ExtClassCell>, foreach: ForeachProc, val: T) -> *mut LeanObj {
    let cls = cell.get_or_init(|| ExtClassCell(lean_register_external_class(drop_ext::<T>, foreach))).0;
    qed_lean_io_mk_ok(qed_lean_alloc_ext(cls, Box::into_raw(Box::new(val)) as *mut c_void))
}

// ---- Thread-Safe Shared StateBox ----

struct StateBoxInner(RwLock<Option<*mut LeanObj>>);

impl Drop for StateBoxInner {
    fn drop(&mut self) {
        if let Some(obj) = self.0.get_mut().unwrap_or_else(|e| e.into_inner()).take() {
            unsafe { qed_lean_dec(obj) };
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
                qed_lean_dec(lean_apply_1(f, obj));
            }
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_new(init: *mut LeanObj) -> *mut LeanObj {
    lean_mark_mt(init);
    alloc_ext_io(&STATE_BOX_CLASS, state_box_foreach, StateBoxInner(RwLock::new(Some(init))))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_read(box_obj: *mut LeanObj, f: *mut LeanObj) -> *mut LeanObj {
    let b = &*(qed_lean_get_ext(box_obj) as *const StateBoxInner);
    let snap = {
        let g = read_unpoison(&b.0);
        let ptr = g.expect("StateBox empty");
        qed_lean_inc(ptr);
        ptr
    };
    qed_lean_io_mk_ok(lean_apply_1(f, snap))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_state_modify(box_obj: *mut LeanObj, f: *mut LeanObj) -> *mut LeanObj {
    let b = &*(qed_lean_get_ext(box_obj) as *const StateBoxInner);
    let mut g = write_unpoison(&b.0);
    let pair = lean_apply_1(f, g.take().expect("StateBox empty"));
    let (new_st, ret_val) = (qed_lean_ctor_get(pair, 0), qed_lean_ctor_get(pair, 1));
    qed_lean_inc(new_st);
    qed_lean_inc(ret_val);
    qed_lean_dec_ref(pair);
    lean_mark_mt(new_st);
    *g = Some(new_st);
    qed_lean_io_mk_ok(ret_val)
}

// ---- Anchored Static File Reader (`dirfd` + `openat2` / `openat` + `O_NOFOLLOW`) ----

struct StaticDirInner(libc::c_int);

impl Drop for StaticDirInner {
    fn drop(&mut self) { if self.0 >= 0 { unsafe { libc::close(self.0) }; } }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_open_static_dir(path_obj: *mut LeanObj) -> *mut LeanObj {
    let fd = CString::new(str_slice(path_obj)).ok()
        .map_or(-1, |cs| libc::open(cs.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC));
    alloc_ext_io(&STATIC_DIR_CLASS, noop_foreach, StaticDirInner(fd))
}

fn open_beneath_nofollow(dirfd: libc::c_int, rel_path: &str) -> Option<libc::c_int> {
    if dirfd < 0 || rel_path.is_empty() || rel_path.starts_with('/') { return None; }
    #[cfg(target_os = "linux")]
    {
        #[repr(C)]
        struct OpenHow { flags: u64, mode: u64, resolve: u64 }
        let bytes = rel_path.as_bytes();
        if bytes.contains(&0) { return None; }
        let how = OpenHow { flags: (libc::O_RDONLY | libc::O_CLOEXEC) as u64, mode: 0, resolve: 0x0C };
        const STACK_PATH_CAP: usize = 512;
        let mut stack_buf = std::mem::MaybeUninit::<[u8; STACK_PATH_CAP]>::uninit();
        let heap_cstr;
        let cptr = if bytes.len() < STACK_PATH_CAP {
            let dst = stack_buf.as_mut_ptr() as *mut u8;
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
                *dst.add(bytes.len()) = 0;
            }
            dst as *const libc::c_char
        } else {
            heap_cstr = CString::new(bytes).ok()?;
            heap_cstr.as_ptr()
        };
        let fd = unsafe {
            libc::syscall(libc::SYS_openat2, dirfd, cptr, &how as *const OpenHow, std::mem::size_of::<OpenHow>())
        };
        if fd >= 0 { return Some(fd as libc::c_int); }
        if last_errno() != libc::ENOSYS { return None; }
    }
    // Portable fallback (macOS & pre-5.6 Linux): segment-by-segment `openat` + `O_NOFOLLOW`.
    let mut segs = rel_path.split('/').peekable();
    let (mut cur, mut owned) = (dirfd, false);
    while let Some(seg) = segs.next() {
        let cs = (!seg.is_empty() && seg != "." && seg != "..").then(|| CString::new(seg).ok()).flatten();
        let Some(cs) = cs else {
            if owned { unsafe { libc::close(cur) }; }
            return None;
        };
        let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC
            | if segs.peek().is_none() { 0 } else { libc::O_DIRECTORY };
        let next = unsafe { libc::openat(cur, cs.as_ptr(), flags) };
        if owned { unsafe { libc::close(cur) }; }
        if next < 0 { return None; }
        cur = next;
        owned = true;
    }
    Some(cur)
}

fn read_exact_or_eof(file: &mut std::fs::File, dst: &mut [u8]) -> Option<usize> {
    let mut filled = 0;
    while filled < dst.len() {
        match file.read(&mut dst[filled..]) {
            Ok(0) => break,
            Ok(n) => filled += n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(_) => return None,
        }
    }
    Some(filled)
}

fn read_tail_capped(file: &mut std::fs::File, head: &[u8], extra: &[u8]) -> Option<Vec<u8>> {
    let base_len = head.len().checked_add(extra.len())?;
    if (base_len as u64) > MAX_STATIC_FILE_BYTES { return None; }
    let mut out = Vec::with_capacity(base_len);
    out.extend_from_slice(head);
    out.extend_from_slice(extra);
    let limit = MAX_STATIC_FILE_BYTES - (base_len as u64) + 1;
    (file.by_ref().take(limit).read_to_end(&mut out).is_ok() && (out.len() as u64) <= MAX_STATIC_FILE_BYTES)
        .then_some(out)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_read_static_file(
    dir_obj: *mut LeanObj,
    rel_obj: *mut LeanObj,
    head_only: u8,
) -> *mut LeanObj {
    let dirfd = (*(qed_lean_get_ext(dir_obj) as *const StaticDirInner)).0;
    let res = (|| -> Option<*mut LeanObj> {
        let mut file = std::fs::File::from_raw_fd(open_beneath_nofollow(dirfd, str_slice(rel_obj))?);
        let meta = file.metadata().ok()?;
        if !meta.is_file() || meta.len() > MAX_STATIC_FILE_BYTES { return None; }
        let mtime_ms = meta.modified().ok()
            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
            .map_or(0usize, |d| d.as_millis().min(usize::MAX as u128) as usize);
        let meta_len = meta.len() as usize;
        let (size, ba_obj) = if head_only != 0 {
            (meta_len, mk_ba(&[]))
        } else {
            let ba = (meta_len > 0).then(|| LeanRef(qed_lean_alloc_ba_uninit(meta_len)));
            let dst = ba.as_ref().map_or(&mut [][..], |b| std::slice::from_raw_parts_mut(qed_lean_ba_ptr(b.0), meta_len));
            let filled = read_exact_or_eof(&mut file, dst)?;
            let mut extra = [0u8; 64];
            let extra_n = if filled == meta_len { read_exact_or_eof(&mut file, &mut extra)? } else { 0 };
            if extra_n > 0 {
                let grown = read_tail_capped(&mut file, &dst[..filled], &extra[..extra_n])?;
                (grown.len(), mk_ba(&grown))
            } else if filled == 0 {
                (0, mk_ba(&[]))
            } else {
                let b = ba.unwrap();
                qed_lean_ba_set_size(b.0, filled);
                (filled, b.into_raw())
            }
        };
        let inner = qed_lean_mk_prod(qed_lean_usize_to_nat(mtime_ms), ba_obj);
        Some(qed_lean_mk_prod(qed_lean_usize_to_nat(size), inner))
    })();
    qed_lean_io_mk_ok(mk_opt(res))
}

// ---- Environment, Clock, CSPRNG, HMAC-SHA256 & RS256 ----

#[no_mangle]
pub unsafe extern "C" fn qed_server_get_env(name_obj: *mut LeanObj) -> *mut LeanObj {
    qed_lean_io_mk_ok(mk_opt(std::env::var(str_slice(name_obj)).ok().map(|v| mk_str(&v))))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_now_ms() -> *mut LeanObj {
    let ms = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64);
    qed_lean_io_mk_ok(qed_lean_box_u64(ms))
}

fn write_hex(src: &[u8], dst: &mut [u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    debug_assert_eq!(dst.len(), src.len() * 2);
    for (&b, pair) in src.iter().zip(dst.chunks_exact_mut(2)) {
        pair[0] = HEX[(b >> 4) as usize];
        pair[1] = HEX[(b & 0x0F) as usize];
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_random_hex(num_bytes: u32) -> *mut LeanObj {
    let n = (num_bytes as usize).min(65536);
    if n == 0 { return qed_lean_io_mk_ok(mk_str("")); }
    let mut s_raw = [0u8; 64];
    let mut s_hex = [0u8; 128];
    let mut h_raw = Vec::new();
    let mut h_hex = Vec::new();
    let (raw, hex): (&mut [u8], &mut [u8]) = if n <= 64 {
        (&mut s_raw[..n], &mut s_hex[..n * 2])
    } else {
        h_raw.resize(n, 0);
        h_hex.resize(n * 2, 0);
        (&mut h_raw, &mut h_hex)
    };
    if SystemRandom::new().fill(raw).is_err() {
        return qed_lean_io_mk_err(c"CSPRNG failure".as_ptr());
    }
    write_hex(raw, hex);
    qed_lean_io_mk_ok(mk_str(std::str::from_utf8_unchecked(hex)))
}

const HMAC_CACHE_SLOTS: usize = 4;
const HMAC_CACHE_MAX_KEY: usize = 256;

struct HmacCacheEntry { len: usize, raw: [u8; HMAC_CACHE_MAX_KEY], key: hmac::Key }
struct HmacKeyCache { slots: Vec<HmacCacheEntry>, order: [u8; HMAC_CACHE_SLOTS] }

fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && std::hint::black_box(a.iter().zip(b).fold(0u8, |d, (&x, &y)| d | (x ^ y))) == 0
}

impl HmacKeyCache {
    const fn new() -> Self { Self { slots: Vec::new(), order: [0, 1, 2, 3] } }

    fn get_or_insert(&mut self, key_bytes: &[u8]) -> &hmac::Key {
        let len = self.slots.len();
        for rank in 0..len {
            let idx = self.order[rank] as usize;
            let e = &self.slots[idx];
            if ct_eq(&e.raw[..e.len], key_bytes) {
                if rank > 0 { self.order[..=rank].rotate_right(1); }
                return &self.slots[idx].key;
            }
        }
        let key = hmac::Key::new(hmac::HMAC_SHA256, key_bytes);
        let idx = if len < HMAC_CACHE_SLOTS {
            self.slots.push(HmacCacheEntry { len: 0, raw: [0; HMAC_CACHE_MAX_KEY], key });
            self.order[..=len].rotate_right(1);
            self.order[0] = len as u8;
            len
        } else {
            let victim = self.order[HMAC_CACHE_SLOTS - 1] as usize;
            self.slots[victim].key = key;
            self.order.rotate_right(1);
            victim
        };
        let slot = &mut self.slots[idx];
        slot.len = key_bytes.len();
        slot.raw[..key_bytes.len()].copy_from_slice(key_bytes);
        &slot.key
    }
}

thread_local! {
    static HMAC_KEY_CACHE: RefCell<HmacKeyCache> = const { RefCell::new(HmacKeyCache::new()) };
}

fn with_hmac_key<R>(key_bytes: &[u8], f: impl FnOnce(&hmac::Key) -> R) -> R {
    if key_bytes.len() > HMAC_CACHE_MAX_KEY {
        return f(&hmac::Key::new(hmac::HMAC_SHA256, key_bytes));
    }
    HMAC_KEY_CACHE.with(|cell| f(cell.borrow_mut().get_or_insert(key_bytes)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_hmac_sha256(key_obj: *mut LeanObj, msg_obj: *mut LeanObj) -> *mut LeanObj {
    let tag = with_hmac_key(ba_slice(key_obj), |k| hmac::sign(k, ba_slice(msg_obj)));
    qed_lean_io_mk_ok(mk_ba(tag.as_ref()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_hmac_sha256_verify(
    key_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    mk_io_bool(with_hmac_key(ba_slice(key_obj), |k| hmac::verify(k, ba_slice(msg_obj), ba_slice(sig_obj)).is_ok()))
}

fn parse_rsa_keypair(pem: &str) -> Option<RsaKeyPair> {
    parse_pem_blocks(pem, "PRIVATE KEY").into_iter().next().and_then(|d| RsaKeyPair::from_pkcs8(&d).ok())
        .or_else(|| parse_pem_blocks(pem, "RSA PRIVATE KEY").into_iter().next().and_then(|d| RsaKeyPair::from_der(&d).ok()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_rsa_sha256_sign(pem_obj: *mut LeanObj, msg_obj: *mut LeanObj) -> *mut LeanObj {
    let res: Result<Vec<u8>, &'static str> = (|| {
        let kp = parse_rsa_keypair(str_slice(pem_obj)).ok_or("failed to parse RSA private key PEM")?;
        let mut sig = vec![0u8; kp.public().modulus_len()];
        kp.sign(&RSA_PKCS1_SHA256, &SystemRandom::new(), ba_slice(msg_obj), &mut sig)
            .map_err(|_| "RSA-SHA256 signing failed")?;
        Ok(sig)
    })();
    mk_io_except(res, |sig| mk_ba(&sig))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_rsa_sha256_verify(
    pem_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    let ok = parse_rsa_keypair(str_slice(pem_obj)).is_some_and(|kp| {
        UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, kp.public_key().as_ref())
            .verify(ba_slice(msg_obj), ba_slice(sig_obj)).is_ok()
    });
    mk_io_bool(ok)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sha256(data_obj: *mut LeanObj) -> *mut LeanObj {
    qed_lean_io_mk_ok(mk_ba(digest::digest(&digest::SHA256, ba_slice(data_obj)).as_ref()))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_pbkdf2_sha256(
    password_obj: *mut LeanObj, salt_obj: *mut LeanObj, iterations: u32,
) -> *mut LeanObj {
    let iters = std::num::NonZeroU32::new(iterations.max(1)).unwrap();
    let mut out = [0u8; 32];
    pbkdf2::derive(pbkdf2::PBKDF2_HMAC_SHA256, iters, ba_slice(salt_obj), ba_slice(password_obj), &mut out);
    qed_lean_io_mk_ok(mk_ba(&out))
}

// ---- RFC 7517 JWK Verification (RS256 & ES256) & Ephemeral P-256 Keygen/Sign ----

const RSA_DER_BUF_CAP: usize = 1120;

fn der_write_tlv_hdr(out: &mut [u8], pos: &mut usize, tag: u8, len: usize) {
    let hdr: &[u8] = if len < 0x80 { &[tag, len as u8] }
        else if len < 0x100 { &[tag, 0x81, len as u8] }
        else { &[tag, 0x82, (len >> 8) as u8, len as u8] };
    out[*pos..*pos + hdr.len()].copy_from_slice(hdr);
    *pos += hdr.len();
}

fn encode_rsa_pub_der<'a>(n: &[u8], e: &[u8], buf: &'a mut [u8; RSA_DER_BUF_CAP]) -> Option<&'a [u8]> {
    if n.is_empty() || e.is_empty() || n.len() > 1024 || e.len() > 64 { return None; }
    let mut pos = 4; // reserve up to 4 bytes for outer SEQUENCE (0x30 + 1..3 len bytes)
    for raw in [n, e] {
        let trimmed = raw.iter().position(|&b| b != 0).map_or(&[0u8][..], |i| &raw[i..]);
        let pad = trimmed[0] & 0x80 != 0;
        der_write_tlv_hdr(buf, &mut pos, 0x02, trimmed.len() + usize::from(pad));
        if pad { buf[pos] = 0; pos += 1; }
        buf[pos..pos + trimmed.len()].copy_from_slice(trimmed);
        pos += trimmed.len();
    }
    let body_len = pos - 4;
    let hdr_len = if body_len < 0x80 { 2 } else if body_len < 0x100 { 3 } else { 4 };
    let mut start = 4 - hdr_len;
    der_write_tlv_hdr(buf, &mut start, 0x30, body_len);
    Some(&buf[4 - hdr_len..pos])
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_rsa_jwk_verify(
    n_obj: *mut LeanObj, e_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    let mut der_buf = [0u8; RSA_DER_BUF_CAP];
    let ok = encode_rsa_pub_der(ba_slice(n_obj), ba_slice(e_obj), &mut der_buf).is_some_and(|der| {
        UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, der)
            .verify(ba_slice(msg_obj), ba_slice(sig_obj)).is_ok()
    });
    mk_io_bool(ok)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ec_p256_jwk_verify(
    x_obj: *mut LeanObj, y_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj,
) -> *mut LeanObj {
    let (x, y) = (ba_slice(x_obj), ba_slice(y_obj));
    let ok = x.len() == 32 && y.len() == 32 && {
        let mut uncompressed = [0u8; 65];
        uncompressed[0] = 0x04;
        uncompressed[1..33].copy_from_slice(x);
        uncompressed[33..65].copy_from_slice(y);
        UnparsedPublicKey::new(&ECDSA_P256_SHA256_FIXED, &uncompressed)
            .verify(ba_slice(msg_obj), ba_slice(sig_obj)).is_ok()
    };
    mk_io_bool(ok)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ec_p256_keygen() -> *mut LeanObj {
    let res: Result<(ring::pkcs8::Document, [u8; 32], [u8; 32]), &'static str> = (|| {
        let rng = SystemRandom::new();
        let doc = EcdsaKeyPair::generate_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, &rng)
            .map_err(|_| "P-256 keygen failed")?;
        let kp = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, doc.as_ref(), &rng)
            .map_err(|_| "P-256 key parse failed")?;
        let pb = kp.public_key().as_ref();
        if pb.len() != 65 || pb[0] != 0x04 { return Err("unexpected P-256 public key format"); }
        Ok((doc, pb[1..33].try_into().unwrap(), pb[33..65].try_into().unwrap()))
    })();
    mk_io_except(res, |(doc, x, y)| qed_lean_mk_prod(mk_ba(doc.as_ref()), qed_lean_mk_prod(mk_ba(&x), mk_ba(&y))))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ec_p256_sign(pkcs8_obj: *mut LeanObj, msg_obj: *mut LeanObj) -> *mut LeanObj {
    let rng = SystemRandom::new();
    let res = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, ba_slice(pkcs8_obj), &rng)
        .map_err(|_| "invalid P-256 PKCS#8 private key")
        .and_then(|kp| kp.sign(&rng, ba_slice(msg_obj)).map_err(|_| "ES256 signing failed"));
    mk_io_except(res, |sig| mk_ba(sig.as_ref()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_rsa_pub_der_edge_cases() {
        let mut buf = [0u8; RSA_DER_BUF_CAP];
        for (n, e) in [(&[][..], &[1u8][..]), (&[1], &[]), (&[1; 1025], &[1]), (&[1], &[1; 65])] {
            assert!(encode_rsa_pub_der(n, e, &mut buf).is_none());
        }
        // Leading zeros stripped + all-zeros -> 0x00 + high-bit 0x00 pad
        assert_eq!(
            encode_rsa_pub_der(&[0, 0, 0x80, 0x01], &[0, 0], &mut buf).unwrap(),
            &[0x30, 0x08, 0x02, 0x03, 0x00, 0x80, 0x01, 0x02, 0x01, 0x00],
        );
        // 1-byte long length (0x81) for 128-byte high-bit n (vlen = 129)
        let der = encode_rsa_pub_der(&[0x80u8; 128], &[0x01, 0x00, 0x01], &mut buf).unwrap();
        assert_eq!(&der[..7], &[0x30, 0x81, 0x89, 0x02, 0x81, 0x81, 0x00]);
        assert_eq!(der.len(), 140);
        // 2-byte long length (0x82) at max bounds (n=1024 high-bit, e=64 high-bit) -> 1100 <= 1120
        let der = encode_rsa_pub_der(&[0xFFu8; 1024], &[0xFFu8; 64], &mut buf).unwrap();
        assert_eq!(&der[..8], &[0x30, 0x82, 0x04, 0x48, 0x02, 0x82, 0x04, 0x01]);
        assert_eq!(der.len(), 1100);
    }

    #[test]
    fn write_hex_and_hmac_key_cache() {
        let mut out = [0u8; 10];
        write_hex(&[0x00, 0x0f, 0x10, 0xab, 0xff], &mut out);
        assert_eq!(&out, b"000f10abff");
        write_hex(&[], &mut []);

        // Cache hit, MRU promotion, eviction past 4 slots, and >256B uncached fallback
        let msg = b"session-payload-v2";
        let keys: Vec<Vec<u8>> = (0u8..6).map(|i| vec![b'k' + i; 32]).collect();
        let mut cache = HmacKeyCache::new();
        for k in &keys[..4] {
            assert_eq!(
                hmac::sign(cache.get_or_insert(k), msg).as_ref(),
                hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, k), msg).as_ref(),
            );
        }
        assert_eq!(cache.slots.len(), 4);
        // Promote keys[0] (currently LRU) to MRU, then insert keys[4] -> evicts keys[1]
        let _ = cache.get_or_insert(&keys[0]);
        let mru = &cache.slots[cache.order[0] as usize];
        assert_eq!(&mru.raw[..mru.len], &keys[0][..]);
        let _ = cache.get_or_insert(&keys[4]);
        assert_eq!(cache.slots.len(), 4);
        assert!(!cache.slots.iter().any(|e| &e.raw[..e.len] == &keys[1][..]));

        for k in [keys[0].as_slice(), keys[5].as_slice(), &[0x42u8; 300][..]] {
            let tag = with_hmac_key(k, |hk| hmac::sign(hk, msg));
            assert!(with_hmac_key(k, |hk| hmac::verify(hk, msg, tag.as_ref()).is_ok()));
            assert_eq!(tag.as_ref(), hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, k), msg).as_ref());
        }
    }
}
