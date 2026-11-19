mod crypto;
mod lean_ffi;
mod outbound;
mod server;

pub(crate) fn last_errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

pub(crate) fn is_wouldblock(e: i32) -> bool {
    e == libc::EAGAIN || e == libc::EWOULDBLOCK
}

pub(crate) fn lock_unpoison<T>(m: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}
