use std::collections::HashMap;
use std::net::TcpListener;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex, MutexGuard, OnceLock, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::time::Instant;

mod crypto;
mod gzip;
mod lean_ffi;
mod outbound;
mod server;
mod sqlite;
mod watch;

pub(crate) fn last_errno() -> i32 { std::io::Error::last_os_error().raw_os_error().unwrap_or(0) }
pub(crate) fn is_wouldblock(e: i32) -> bool { e == libc::EAGAIN || e == libc::EWOULDBLOCK }

#[inline]
pub(crate) fn lock_unpoison<T>(m: &Mutex<T>) -> MutexGuard<'_, T> { m.lock().unwrap_or_else(|e| e.into_inner()) }
#[inline]
pub(crate) fn read_unpoison<T>(rw: &RwLock<T>) -> RwLockReadGuard<'_, T> { rw.read().unwrap_or_else(|e| e.into_inner()) }
#[inline]
pub(crate) fn write_unpoison<T>(rw: &RwLock<T>) -> RwLockWriteGuard<'_, T> { rw.write().unwrap_or_else(|e| e.into_inner()) }
#[inline]
pub(crate) fn wait_unpoison<'a, T>(cv: &Condvar, g: MutexGuard<'a, T>) -> MutexGuard<'a, T> {
    cv.wait(g).unwrap_or_else(|e| e.into_inner())
}

pub(crate) unsafe fn set_sockopt(fd: libc::c_int, level: libc::c_int, name: libc::c_int, val: libc::c_int) {
    let _ = libc::setsockopt(fd, level, name, &val as *const _ as *const _, std::mem::size_of::<libc::c_int>() as libc::socklen_t);
}

#[cfg(not(target_os = "linux"))]
pub(crate) fn set_nonblocking(fd: libc::c_int) {
    unsafe {
        let f = libc::fcntl(fd, libc::F_GETFL, 0);
        if f >= 0 { let _ = libc::fcntl(fd, libc::F_SETFL, f | libc::O_NONBLOCK); }
    }
}

pub(crate) fn poll_in(fd: libc::c_int, timeout_ms: libc::c_int) -> libc::c_int {
    let mut pfd = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
    unsafe { libc::poll(&mut pfd, 1, timeout_ms) }
}

pub(crate) fn rem_timeout_ms(deadline: Instant, min_ms: u128) -> Option<i32> {
    deadline.checked_duration_since(Instant::now())
        .filter(|d| !d.is_zero())
        .map(|d| d.as_millis().clamp(min_ms, i32::MAX as u128) as i32)
}

pub(crate) fn bind_loopback_nonblock(port: u16) -> Result<(TcpListener, u16), String> {
    let listener = TcpListener::bind(("127.0.0.1", port))
        .map_err(|e| format!("failed to bind 127.0.0.1:{port}: {e}"))?;
    let actual_port = listener.local_addr()
        .map_err(|e| format!("failed to query local TCP address: {e}"))?.port();
    let _ = listener.set_nonblocking(true);
    Ok((listener, actual_port))
}

pub(crate) struct WakeFd { rfd: libc::c_int, wfd: libc::c_int }

impl WakeFd {
    pub(crate) fn new() -> Self {
        #[cfg(target_os = "linux")]
        let (rfd, wfd) = {
            let fd = unsafe { libc::eventfd(0, libc::EFD_NONBLOCK | libc::EFD_CLOEXEC) };
            (fd, fd)
        };
        #[cfg(not(target_os = "linux"))]
        let (rfd, wfd) = {
            let mut fds = [-1 as libc::c_int; 2];
            if unsafe { libc::pipe(fds.as_mut_ptr()) } == 0 {
                for fd in fds {
                    set_nonblocking(fd);
                    unsafe { let _ = libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC); }
                }
                (fds[0], fds[1])
            } else {
                (-1, -1)
            }
        };
        Self { rfd, wfd }
    }

    #[inline]
    pub(crate) fn read_fd(&self) -> libc::c_int { self.rfd }

    pub(crate) fn wake(&self) {
        if self.wfd >= 0 {
            let v: u64 = 1;
            let _ = unsafe { libc::write(self.wfd, &v as *const u64 as *const libc::c_void, 8) };
        }
    }

    pub(crate) fn drain(&self) {
        if self.rfd < 0 { return; }
        #[cfg(target_os = "linux")]
        {
            let mut v: u64 = 0;
            let _ = unsafe { libc::read(self.rfd, &mut v as *mut u64 as *mut libc::c_void, 8) };
        }
        #[cfg(not(target_os = "linux"))]
        {
            let mut buf = [0u8; 64];
            while unsafe { libc::read(self.rfd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) } > 0 {}
        }
    }
}

impl Drop for WakeFd {
    fn drop(&mut self) {
        if self.rfd >= 0 { unsafe { libc::close(self.rfd) }; }
        if self.wfd >= 0 && self.wfd != self.rfd { unsafe { libc::close(self.wfd) }; }
    }
}

const HANDLE_SHARDS: usize = 16;

pub(crate) struct HandleTable<T> {
    next: AtomicU64,
    shards: OnceLock<[RwLock<HashMap<u64, T>>; HANDLE_SHARDS]>,
}

impl<T> HandleTable<T> {
    pub(crate) const fn new() -> Self { Self { next: AtomicU64::new(1), shards: OnceLock::new() } }
    #[inline]
    fn shard(&self, id: u64) -> &RwLock<HashMap<u64, T>> {
        &self.shards.get_or_init(|| std::array::from_fn(|_| RwLock::new(HashMap::new())))[(id as usize) & (HANDLE_SHARDS - 1)]
    }
    pub(crate) fn insert(&self, val: T) -> u64 {
        let id = self.next.fetch_add(1, Ordering::Relaxed).max(1);
        self.insert_at(id, val);
        id
    }
    pub(crate) fn insert_at(&self, id: u64, val: T) { write_unpoison(self.shard(id)).insert(id, val); }
    pub(crate) fn remove(&self, id: u64) -> Option<T> { write_unpoison(self.shard(id)).remove(&id) }
}

impl<T: Clone> HandleTable<T> {
    pub(crate) fn get(&self, id: u64) -> Option<T> { read_unpoison(self.shard(id)).get(&id).cloned() }
}

fn decode_b64_pem_body(body: &str) -> Option<Vec<u8>> {
    let (mut out, mut buf, mut bits) = (Vec::with_capacity(body.len() * 3 / 4), 0u32, 0u8);
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
        if bits >= 8 { bits -= 8; out.push((buf >> bits) as u8); }
    }
    (!out.is_empty()).then_some(out)
}

pub(crate) fn parse_pem_blocks(pem: &str, label: &str) -> Vec<Vec<u8>> {
    let (begin, end) = (format!("-----BEGIN {label}-----"), format!("-----END {label}-----"));
    let (mut blocks, mut rest) = (Vec::new(), pem);
    while let Some(start) = rest.find(&begin) {
        let after = &rest[start + begin.len()..];
        let Some(end_idx) = after.find(&end) else { break };
        if let Some(der) = decode_b64_pem_body(&after[..end_idx]) { blocks.push(der); }
        rest = &after[end_idx + end.len()..];
    }
    blocks
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_table_sharded_crud() {
        let tbl = HandleTable::new();
        let ids: Vec<u64> = (0u64..48).map(|v| tbl.insert(v * 10)).collect();
        for (i, &id) in ids.iter().enumerate() { assert_eq!(tbl.get(id), Some((i as u64) * 10)); }
        tbl.insert_at(ids[3], 999);
        assert_eq!(tbl.get(ids[3]), Some(999));
        for &id in &ids {
            assert!(tbl.remove(id).is_some());
            assert_eq!(tbl.get(id), None);
        }
    }

    #[test]
    fn wake_fd_signal_and_drain() {
        let w = WakeFd::new();
        assert!(w.read_fd() >= 0);
        assert_eq!(poll_in(w.read_fd(), 0), 0);
        w.wake();
        w.wake();
        assert_eq!(poll_in(w.read_fd(), 50), 1);
        w.drain();
        assert_eq!(poll_in(w.read_fd(), 0), 0);
    }
}
