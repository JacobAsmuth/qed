use std::{cell::RefCell, ffi::{c_void, CString}, io::Read, os::fd::FromRawFd, sync::{OnceLock, RwLock}, time::{SystemTime, UNIX_EPOCH}};
use ring::{digest, hmac, pbkdf2, rand::{SecureRandom, SystemRandom}};
use ring::signature::{
    EcdsaKeyPair, KeyPair, RsaKeyPair, UnparsedPublicKey, VerificationAlgorithm,
    ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA256_FIXED_SIGNING, RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_SHA256,
};

use crate::lean_ffi::*;
use crate::{close_fd, parse_pem_blocks, read_unpoison, write_unpoison};

const MAX_STATIC_FILE_BYTES: u64 = 256 * 1024 * 1024;
const HMAC_CACHE_SLOTS: usize = 4;
const HMAC_CACHE_MAX_KEY: usize = 256;
const RSA_DER_BUF_CAP: usize = 1120;

struct ExtClassCell(*mut LeanExtClass);
unsafe impl Send for ExtClassCell {}
unsafe impl Sync for ExtClassCell {}
static STATE_BOX_CLASS: OnceLock<ExtClassCell> = OnceLock::new();
static STATIC_DIR_CLASS: OnceLock<ExtClassCell> = OnceLock::new();

extern "C" fn drop_ext<T>(ptr: *mut c_void) { if !ptr.is_null() { unsafe { drop(Box::from_raw(ptr as *mut T)); } } }
extern "C" fn noop_foreach(_: *mut c_void, _: *mut LeanObj) {}
unsafe fn ext_ref<'a, T>(o: *mut LeanObj) -> &'a T { &*(qed_lean_get_ext(o) as *const T) }
unsafe fn alloc_ext_io<T>(cell: &OnceLock<ExtClassCell>, foreach: ForeachProc, val: T) -> *mut LeanObj {
    let cls = cell.get_or_init(|| ExtClassCell(lean_register_external_class(drop_ext::<T>, foreach))).0;
    qed_lean_io_mk_ok(qed_lean_alloc_ext(cls, Box::into_raw(Box::new(val)) as *mut c_void))
}

// ---- Thread-Safe Shared StateBox & Anchored Static File Reader ----

struct StateBoxInner(RwLock<Option<*mut LeanObj>>);
impl Drop for StateBoxInner {
    fn drop(&mut self) { if let Some(o) = self.0.get_mut().unwrap_or_else(|e| e.into_inner()).take() { unsafe { qed_lean_dec(o) }; } }
}
extern "C" fn state_box_foreach(ptr: *mut c_void, f: *mut LeanObj) {
    if let Some(p) = (!ptr.is_null()).then_some(ptr as *const StateBoxInner) {
        if let Ok(g) = unsafe { (*p).0.read() } {
            if let Some(o) = *g { unsafe { qed_lean_inc(f); qed_lean_inc(o); qed_lean_dec(lean_apply_1(f, o)); } }
        }
    }
}

struct StaticDirInner(libc::c_int);
impl Drop for StaticDirInner { fn drop(&mut self) { close_fd(self.0); } }

fn open_beneath_nofollow(dirfd: libc::c_int, rel_path: &str) -> Option<libc::c_int> {
    if dirfd < 0 || rel_path.is_empty() || rel_path.starts_with('/') { return None; }
    #[cfg(target_os = "linux")]
    {
        #[repr(C)] struct OpenHow { flags: u64, mode: u64, resolve: u64 }
        let bytes = rel_path.as_bytes();
        if bytes.contains(&0) { return None; }
        let how = OpenHow { flags: (libc::O_RDONLY | libc::O_CLOEXEC) as u64, mode: 0, resolve: 0x0C };
        let (mut stack, heap) = ([0u8; 512], (bytes.len() >= 512).then(|| CString::new(bytes).ok()).flatten());
        let cptr = if bytes.len() < 512 { stack[..bytes.len()].copy_from_slice(bytes); stack.as_ptr() as *const libc::c_char } else { heap.as_ref()?.as_ptr() };
        let fd = unsafe { libc::syscall(libc::SYS_openat2, dirfd, cptr, &how as *const OpenHow, std::mem::size_of::<OpenHow>()) };
        if fd >= 0 { return Some(fd as libc::c_int); }
        if crate::last_errno() != libc::ENOSYS { return None; }
    }
    let (mut segs, mut cur, mut owned) = (rel_path.split('/').peekable(), dirfd, false);
    while let Some(seg) = segs.next() {
        let Some(cs) = (!seg.is_empty() && seg != "." && seg != "..").then(|| CString::new(seg).ok()).flatten() else {
            if owned { close_fd(cur); } return None;
        };
        let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | if segs.peek().is_none() { 0 } else { libc::O_DIRECTORY };
        let next = unsafe { libc::openat(cur, cs.as_ptr(), flags) };
        if owned { close_fd(cur); }
        if next < 0 { return None; }
        (cur, owned) = (next, true);
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

// ---- CSPRNG Hex, MRU HMAC-SHA256 Key Cache, RSA/ECDSA & DER ----

fn write_hex(src: &[u8], dst: &mut [u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for (&b, p) in src.iter().zip(dst.chunks_exact_mut(2)) { (p[0], p[1]) = (HEX[(b >> 4) as usize], HEX[(b & 0x0F) as usize]); }
}
fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && std::hint::black_box(a.iter().zip(b).fold(0u8, |d, (&x, &y)| d | (x ^ y))) == 0
}

struct HmacCacheEntry { len: usize, raw: [u8; HMAC_CACHE_MAX_KEY], key: hmac::Key }
struct HmacKeyCache { slots: Vec<HmacCacheEntry>, order: [u8; HMAC_CACHE_SLOTS] }
impl HmacKeyCache {
    const fn new() -> Self { Self { slots: Vec::new(), order: [0, 1, 2, 3] } }
    fn get_or_insert(&mut self, kb: &[u8]) -> &hmac::Key {
        if let Some(rank) = (0..self.slots.len()).find(|&r| { let s = &self.slots[self.order[r] as usize]; ct_eq(&s.raw[..s.len], kb) }) {
            if rank > 0 { self.order[..=rank].rotate_right(1); }
            return &self.slots[self.order[0] as usize].key;
        }
        let (len, key) = (self.slots.len(), hmac::Key::new(hmac::HMAC_SHA256, kb));
        let idx = if len < HMAC_CACHE_SLOTS {
            self.slots.push(HmacCacheEntry { len: 0, raw: [0; HMAC_CACHE_MAX_KEY], key });
            self.order[..=len].rotate_right(1); self.order[0] = len as u8; len
        } else {
            let v = self.order[HMAC_CACHE_SLOTS - 1] as usize;
            self.slots[v].key = key; self.order.rotate_right(1); v
        };
        let s = &mut self.slots[idx];
        s.len = kb.len(); s.raw[..kb.len()].copy_from_slice(kb);
        &s.key
    }
}
thread_local! { static HMAC_KEY_CACHE: RefCell<HmacKeyCache> = const { RefCell::new(HmacKeyCache::new()) }; }

fn with_hmac_key<R>(kb: &[u8], f: impl FnOnce(&hmac::Key) -> R) -> R {
    if kb.len() > HMAC_CACHE_MAX_KEY { return f(&hmac::Key::new(hmac::HMAC_SHA256, kb)); }
    HMAC_KEY_CACHE.with(|c| f(c.borrow_mut().get_or_insert(kb)))
}
fn parse_rsa_keypair(pem: &str) -> Option<RsaKeyPair> {
    parse_pem_blocks(pem, "PRIVATE KEY").into_iter().next().and_then(|d| RsaKeyPair::from_pkcs8(&d).ok())
        .or_else(|| parse_pem_blocks(pem, "RSA PRIVATE KEY").into_iter().next().and_then(|d| RsaKeyPair::from_der(&d).ok()))
}
unsafe fn verify_pub<A: VerificationAlgorithm>(alg: &'static A, key: &[u8], msg: *mut LeanObj, sig: *mut LeanObj) -> bool {
    UnparsedPublicKey::new(alg, key).verify(ba_slice(msg), ba_slice(sig)).is_ok()
}
fn der_write_tlv_hdr(out: &mut [u8], pos: &mut usize, tag: u8, len: usize) {
    let h: &[u8] = if len < 0x80 { &[tag, len as u8] } else if len < 0x100 { &[tag, 0x81, len as u8] }
        else { &[tag, 0x82, (len >> 8) as u8, len as u8] };
    out[*pos..*pos + h.len()].copy_from_slice(h);
    *pos += h.len();
}
fn encode_rsa_pub_der<'a>(n: &[u8], e: &[u8], buf: &'a mut [u8; RSA_DER_BUF_CAP]) -> Option<&'a [u8]> {
    if n.is_empty() || e.is_empty() || n.len() > 1024 || e.len() > 64 { return None; }
    let mut pos = 4; // reserve up to 4 bytes for outer SEQUENCE header
    for raw in [n, e] {
        let trimmed = raw.iter().position(|&b| b != 0).map_or(&[0u8][..], |i| &raw[i..]);
        let pad = trimmed[0] & 0x80 != 0;
        der_write_tlv_hdr(buf, &mut pos, 0x02, trimmed.len() + usize::from(pad));
        if pad { buf[pos] = 0; pos += 1; }
        buf[pos..pos + trimmed.len()].copy_from_slice(trimmed);
        pos += trimmed.len();
    }
    let body_len = pos - 4;
    let hdr_len = 2 + usize::from(body_len >= 0x80) + usize::from(body_len >= 0x100);
    let mut start = 4 - hdr_len;
    der_write_tlv_hdr(buf, &mut start, 0x30, body_len);
    Some(&buf[4 - hdr_len..pos])
}

ffi_export! {
    qed_server_state_new(init: *mut LeanObj) => {
        lean_mark_mt(init);
        alloc_ext_io(&STATE_BOX_CLASS, state_box_foreach, StateBoxInner(RwLock::new(Some(init))))
    };
    qed_server_state_read(box_obj: *mut LeanObj, f: *mut LeanObj) => {
        let snap = { let ptr = read_unpoison(&ext_ref::<StateBoxInner>(box_obj).0).expect("StateBox empty"); qed_lean_inc(ptr); ptr };
        qed_lean_io_mk_ok(lean_apply_1(f, snap))
    };
    qed_server_state_modify(box_obj: *mut LeanObj, f: *mut LeanObj) => {
        let mut g = write_unpoison(&ext_ref::<StateBoxInner>(box_obj).0);
        let pair = lean_apply_1(f, g.take().expect("StateBox empty"));
        let (new_st, ret_val) = (qed_lean_ctor_get(pair, 0), qed_lean_ctor_get(pair, 1));
        qed_lean_inc(new_st); qed_lean_inc(ret_val); qed_lean_dec(pair); lean_mark_mt(new_st);
        *g = Some(new_st);
        qed_lean_io_mk_ok(ret_val)
    };
    qed_server_open_static_dir(path_obj: *mut LeanObj) => {
        let fd = CString::new(str_slice(path_obj)).ok().map_or(-1, |cs| libc::open(cs.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC));
        alloc_ext_io(&STATIC_DIR_CLASS, noop_foreach, StaticDirInner(fd))
    };
    qed_server_read_static_file(dir_obj: *mut LeanObj, rel_obj: *mut LeanObj, head_only: u8) => {
        let dirfd = ext_ref::<StaticDirInner>(dir_obj).0;
        let res = (|| -> Option<*mut LeanObj> {
            let mut file = std::fs::File::from_raw_fd(open_beneath_nofollow(dirfd, str_slice(rel_obj))?);
            let meta = file.metadata().ok()?;
            if !meta.is_file() || meta.len() > MAX_STATIC_FILE_BYTES { return None; }
            let mtime_ms = meta.modified().ok().and_then(|t| t.duration_since(UNIX_EPOCH).ok()).map_or(0usize, |d| d.as_millis().min(usize::MAX as u128) as usize);
            let meta_len = meta.len() as usize;
            let (size, ba_obj) = if head_only != 0 { (meta_len, mk_ba(&[])) } else {
                let ba = (meta_len > 0).then(|| LeanRef(qed_lean_alloc_ba_uninit(meta_len)));
                let mut _n = 0;
                let dst = ba.as_ref().map_or(&mut [][..], |b| std::slice::from_raw_parts_mut(qed_lean_ba_slice(b.0, &mut _n), meta_len));
                let filled = read_exact_or_eof(&mut file, dst)?;
                let mut extra = [0u8; 64];
                let extra_n = if filled == meta_len { read_exact_or_eof(&mut file, &mut extra)? } else { 0 };
                if extra_n > 0 {
                    let base = filled.checked_add(extra_n)?;
                    if (base as u64) > MAX_STATIC_FILE_BYTES { return None; }
                    let mut out = [&dst[..filled], &extra[..extra_n]].concat();
                    file.by_ref().take(MAX_STATIC_FILE_BYTES - base as u64 + 1).read_to_end(&mut out).ok()?;
                    if (out.len() as u64) > MAX_STATIC_FILE_BYTES { return None; }
                    (out.len(), mk_ba(&out))
                } else if filled == 0 { (0, mk_ba(&[])) } else {
                    let b = ba.unwrap(); qed_lean_ba_set_size(b.0, filled); (filled, b.into_raw())
                }
            };
            Some(qed_lean_mk_prod(qed_lean_usize_to_nat(size), qed_lean_mk_prod(qed_lean_usize_to_nat(mtime_ms), ba_obj)))
        })();
        qed_lean_io_mk_ok(mk_opt(res))
    };
    qed_server_get_env(name_obj: *mut LeanObj) => qed_lean_io_mk_ok(mk_opt(std::env::var(str_slice(name_obj)).ok().map(|v| mk_str(&v))));
    qed_server_now_ms() => qed_lean_io_mk_ok(qed_lean_box_u64(SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64)));
    qed_server_random_hex(num_bytes: u32) => {
        let n = (num_bytes as usize).min(65536);
        if n == 0 { return qed_lean_io_mk_ok(mk_str("")); }
        let (mut sr, mut sh, mut hr, mut hh) = ([0u8; 64], [0u8; 128], Vec::new(), Vec::new());
        let (raw, hex): (&mut [u8], &mut [u8]) = if n <= 64 { (&mut sr[..n], &mut sh[..n * 2]) }
            else { hr.resize(n, 0); hh.resize(n * 2, 0); (&mut hr, &mut hh) };
        if SystemRandom::new().fill(raw).is_err() { return qed_lean_io_mk_err(c"CSPRNG failure".as_ptr()); }
        write_hex(raw, hex);
        qed_lean_io_mk_ok(mk_str(std::str::from_utf8_unchecked(hex)))
    };
    qed_server_hmac_sha256(key_obj: *mut LeanObj, msg_obj: *mut LeanObj) =>
        qed_lean_io_mk_ok(mk_ba(with_hmac_key(ba_slice(key_obj), |k| hmac::sign(k, ba_slice(msg_obj))).as_ref()));
    qed_server_hmac_sha256_verify(key_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj) =>
        mk_io_bool(with_hmac_key(ba_slice(key_obj), |k| hmac::verify(k, ba_slice(msg_obj), ba_slice(sig_obj)).is_ok()));
    qed_server_rsa_sha256_sign(pem_obj: *mut LeanObj, msg_obj: *mut LeanObj) => mk_io_except(
        parse_rsa_keypair(str_slice(pem_obj)).ok_or("failed to parse RSA private key PEM").and_then(|kp| {
            let mut sig = vec![0u8; kp.public().modulus_len()];
            kp.sign(&RSA_PKCS1_SHA256, &SystemRandom::new(), ba_slice(msg_obj), &mut sig).map_err(|_| "RSA-SHA256 signing failed")?;
            Ok(sig)
        }), |sig| mk_ba(&sig));
    qed_server_rsa_sha256_verify(pem_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj) =>
        mk_io_bool(parse_rsa_keypair(str_slice(pem_obj)).is_some_and(|kp| verify_pub(&RSA_PKCS1_2048_8192_SHA256, kp.public_key().as_ref(), msg_obj, sig_obj)));
    qed_server_sha256(data_obj: *mut LeanObj) => qed_lean_io_mk_ok(mk_ba(digest::digest(&digest::SHA256, ba_slice(data_obj)).as_ref()));
    qed_server_pbkdf2_sha256(password_obj: *mut LeanObj, salt_obj: *mut LeanObj, iterations: u32) => {
        let mut out = [0u8; 32];
        pbkdf2::derive(pbkdf2::PBKDF2_HMAC_SHA256, std::num::NonZeroU32::new(iterations.max(1)).unwrap(), ba_slice(salt_obj), ba_slice(password_obj), &mut out);
        qed_lean_io_mk_ok(mk_ba(&out))
    };
    qed_server_rsa_jwk_verify(n_obj: *mut LeanObj, e_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj) => {
        let mut der_buf = [0u8; RSA_DER_BUF_CAP];
        mk_io_bool(encode_rsa_pub_der(ba_slice(n_obj), ba_slice(e_obj), &mut der_buf).is_some_and(|der| verify_pub(&RSA_PKCS1_2048_8192_SHA256, der, msg_obj, sig_obj)))
    };
    qed_server_ec_p256_jwk_verify(x_obj: *mut LeanObj, y_obj: *mut LeanObj, msg_obj: *mut LeanObj, sig_obj: *mut LeanObj) => {
        let (x, y) = (ba_slice(x_obj), ba_slice(y_obj));
        mk_io_bool(x.len() == 32 && y.len() == 32 && {
            let mut raw = [0u8; 65]; raw[0] = 0x04; raw[1..33].copy_from_slice(x); raw[33..65].copy_from_slice(y);
            verify_pub(&ECDSA_P256_SHA256_FIXED, &raw, msg_obj, sig_obj)
        })
    };
    qed_server_ec_p256_keygen() => {
        let res = (|| -> Result<_, &'static str> {
            let rng = SystemRandom::new();
            let doc = EcdsaKeyPair::generate_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, &rng).map_err(|_| "P-256 keygen failed")?;
            let kp = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, doc.as_ref(), &rng).map_err(|_| "P-256 key parse failed")?;
            let pb = kp.public_key().as_ref();
            if pb.len() != 65 || pb[0] != 0x04 { return Err("unexpected P-256 public key format"); }
            Ok((doc, <[u8; 32]>::try_from(&pb[1..33]).unwrap(), <[u8; 32]>::try_from(&pb[33..65]).unwrap()))
        })();
        mk_io_except(res, |(doc, x, y)| qed_lean_mk_prod(mk_ba(doc.as_ref()), qed_lean_mk_prod(mk_ba(&x), mk_ba(&y))))
    };
    qed_server_ec_p256_sign(pkcs8_obj: *mut LeanObj, msg_obj: *mut LeanObj) => {
        let rng = SystemRandom::new();
        mk_io_except(EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, ba_slice(pkcs8_obj), &rng)
            .map_err(|_| "invalid P-256 PKCS#8 private key")
            .and_then(|kp| kp.sign(&rng, ba_slice(msg_obj)).map_err(|_| "ES256 signing failed")), |sig| mk_ba(sig.as_ref()))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_rsa_pub_der_edge_cases() {
        let mut buf = [0u8; RSA_DER_BUF_CAP];
        for (n, e) in [(&[][..], &[1u8][..]), (&[1], &[]), (&[1; 1025], &[1]), (&[1], &[1; 65])] { assert!(encode_rsa_pub_der(n, e, &mut buf).is_none()); }
        assert_eq!(encode_rsa_pub_der(&[0, 0, 0x80, 0x01], &[0, 0], &mut buf).unwrap(), &[0x30, 0x08, 0x02, 0x03, 0x00, 0x80, 0x01, 0x02, 0x01, 0x00]);
        let d1 = encode_rsa_pub_der(&[0x80u8; 128], &[0x01, 0x00, 0x01], &mut buf).unwrap();
        assert_eq!((&d1[..7], d1.len()), (&[0x30, 0x81, 0x89, 0x02, 0x81, 0x81, 0x00][..], 140));
        let d2 = encode_rsa_pub_der(&[0xFFu8; 1024], &[0xFFu8; 64], &mut buf).unwrap();
        assert_eq!((&d2[..8], d2.len()), (&[0x30, 0x82, 0x04, 0x48, 0x02, 0x82, 0x04, 0x01][..], 1100));
    }

    #[test]
    fn write_hex_and_hmac_key_cache() {
        let mut out = [0u8; 10];
        write_hex(&[0x00, 0x0f, 0x10, 0xab, 0xff], &mut out);
        assert_eq!(&out, b"000f10abff");
        write_hex(&[], &mut []);

        let (msg, keys, mut cache) = (b"session-payload-v2", (0u8..6).map(|i| vec![b'k' + i; 32]).collect::<Vec<_>>(), HmacKeyCache::new());
        for k in &keys[..4] { assert_eq!(hmac::sign(cache.get_or_insert(k), msg).as_ref(), hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, k), msg).as_ref()); }
        assert_eq!(cache.slots.len(), 4);
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
