mod crypto;
mod gzip;
mod lean_ffi;
mod outbound;
mod server;
mod sqlite;

pub(crate) fn last_errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

pub(crate) fn is_wouldblock(e: i32) -> bool {
    e == libc::EAGAIN || e == libc::EWOULDBLOCK
}

pub(crate) fn lock_unpoison<T>(m: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
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
