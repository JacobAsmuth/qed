use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock};

mod crypto;
mod gzip;
mod lean_ffi;
mod outbound;
mod server;
mod sqlite;
mod watch;

pub(crate) fn last_errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

pub(crate) fn is_wouldblock(e: i32) -> bool {
    e == libc::EAGAIN || e == libc::EWOULDBLOCK
}

pub(crate) fn lock_unpoison<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

pub(crate) struct HandleTable<T> {
    next: AtomicU64,
    map: OnceLock<Mutex<HashMap<u64, T>>>,
}

impl<T> HandleTable<T> {
    pub(crate) const fn new() -> Self {
        Self { next: AtomicU64::new(1), map: OnceLock::new() }
    }
    fn lock(&self) -> MutexGuard<'_, HashMap<u64, T>> {
        lock_unpoison(self.map.get_or_init(|| Mutex::new(HashMap::new())))
    }
    pub(crate) fn insert(&self, val: T) -> u64 {
        let id = self.next.fetch_add(1, Ordering::Relaxed).max(1);
        self.lock().insert(id, val);
        id
    }
    pub(crate) fn insert_at(&self, id: u64, val: T) { self.lock().insert(id, val); }
    pub(crate) fn remove(&self, id: u64) -> Option<T> { self.lock().remove(&id) }
    pub(crate) fn with<R>(&self, id: u64, f: impl FnOnce(&T) -> R) -> Option<R> { self.lock().get(&id).map(f) }
}

impl<T: Clone> HandleTable<T> {
    pub(crate) fn get(&self, id: u64) -> Option<T> { self.lock().get(&id).cloned() }
}

pub(crate) fn encode_hex(bs: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bs.len() * 2);
    for &b in bs {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0F) as usize] as char);
    }
    out
}

pub(crate) fn decode_b64_pem_body(body: &str) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(body.len() * 3 / 4);
    let mut buf: u32 = 0;
    let mut bits: u8 = 0;
    for b in body.bytes() {
        let val = match b {
            b'A'..=b'Z' => b - b'A',
            b'a'..=b'z' => b - b'a' + 26,
            b'0'..=b'9' => b - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            b'=' | b'\r' | b'\n' | b' ' | b'\t' => continue,
            _ => return None,
        };
        buf = (buf << 6) | (val as u32);
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push(((buf >> bits) & 0xFF) as u8);
        }
    }
    if out.is_empty() { None } else { Some(out) }
}

pub(crate) fn parse_pem_blocks(pem: &str, label: &str) -> Vec<Vec<u8>> {
    let begin = format!("-----BEGIN {label}-----");
    let end = format!("-----END {label}-----");
    let mut blocks = Vec::new();
    let mut rest = pem;
    while let Some(start) = rest.find(&begin) {
        let after_begin = &rest[start + begin.len()..];
        let Some(end_idx) = after_begin.find(&end) else { break };
        if let Some(der) = decode_b64_pem_body(&after_begin[..end_idx]) {
            blocks.push(der);
        }
        rest = &after_begin[end_idx + end.len()..];
    }
    blocks
}
