//! OS-native event-driven file watcher (`inotify` on Linux, `kqueue` on macOS)
//! and lightweight localhost SSE dev-event push server (`qed dev`).
//!
//! Zero external crates beyond `std` and `libc`.

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::lean_ffi::*;
use crate::{HandleTable, lock_unpoison};

pub const CHANGE_LEAN: u32 = 1;
pub const CHANGE_CSS: u32 = 2;
pub const CHANGE_RUNTIME: u32 = 4;
pub const CHANGE_ERROR: u32 = 8;

fn classify_file_name(name: &str, is_runtime: bool) -> u32 {
    if is_runtime {
        if name.ends_with(".mjs") { CHANGE_RUNTIME } else { 0 }
    } else if name.ends_with(".lean") {
        CHANGE_LEAN
    } else if name.ends_with(".css") {
        CHANGE_CSS
    } else {
        0
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn watch_roots(project_dir: &str, runtime_dir: &str, mut add: impl FnMut(&Path, bool)) {
    for (dir, is_rt) in [(project_dir, false), (runtime_dir, true)] {
        if !dir.is_empty() {
            let p = PathBuf::from(dir);
            if p.exists() { add(&p, is_rt); }
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn walk_tree(
    dir: &Path,
    is_runtime: bool,
    skip: &HashSet<String>,
    mut visit: impl FnMut(&Path, Option<u32>) -> bool,
) {
    let mut stack = vec![dir.to_path_buf()];
    while let Some(cur) = stack.pop() {
        if !visit(&cur, None) { continue; }
        let Ok(entries) = std::fs::read_dir(&cur) else { continue };
        for entry in entries.flatten() {
            let Ok(ft) = entry.file_type() else { continue };
            let name_os = entry.file_name();
            let name = name_os.to_string_lossy();
            if ft.is_dir() {
                if !is_runtime && skip.contains(name.as_ref()) { continue; }
                stack.push(entry.path());
            } else {
                let fmask = classify_file_name(&name, is_runtime);
                if fmask != 0 { let _ = visit(&entry.path(), Some(fmask)); }
            }
        }
    }
}

// ============================================================================
// Linux `inotify` Implementation
// ============================================================================

#[cfg(target_os = "linux")]
mod os_watch {
    use super::*;
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    const WATCH_MASK: u32 = libc::IN_MODIFY
        | libc::IN_CLOSE_WRITE
        | libc::IN_MOVED_TO
        | libc::IN_MOVED_FROM
        | libc::IN_CREATE
        | libc::IN_DELETE
        | libc::IN_ATTRIB
        | libc::IN_DELETE_SELF
        | libc::IN_MOVE_SELF;

    pub struct OsWatcher {
        fd: i32,
        skip: HashSet<String>,
        wds: HashMap<i32, (PathBuf, bool)>,
        paths: HashSet<PathBuf>,
    }

    impl Drop for OsWatcher {
        fn drop(&mut self) {
            if self.fd >= 0 {
                unsafe { libc::close(self.fd); }
            }
        }
    }

    impl OsWatcher {
        pub fn open(project_dir: &str, runtime_dir: &str, skip: HashSet<String>) -> Result<Self, String> {
            let fd = unsafe { libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC) };
            if fd < 0 {
                return Err(format!("inotify_init1 failed: {}", std::io::Error::last_os_error()));
            }
            let mut w = Self { fd, skip, wds: HashMap::new(), paths: HashSet::new() };
            watch_roots(project_dir, runtime_dir, |p, is_rt| { let _ = w.add_tree(p, is_rt, false); });
            Ok(w)
        }

        fn add_single_dir(
            fd: i32,
            wds: &mut HashMap<i32, (PathBuf, bool)>,
            paths: &mut HashSet<PathBuf>,
            dir: &Path,
            is_runtime: bool,
        ) -> Result<(), String> {
            let canonical = dir.to_path_buf();
            if paths.contains(&canonical) {
                return Ok(());
            }
            let Ok(cpath) = CString::new(dir.as_os_str().as_bytes()) else {
                return Ok(());
            };
            let wd = unsafe { libc::inotify_add_watch(fd, cpath.as_ptr(), WATCH_MASK) };
            if wd < 0 {
                return Err(format!("inotify_add_watch({}) failed: {}", dir.display(), std::io::Error::last_os_error()));
            }
            wds.insert(wd, (canonical.clone(), is_runtime));
            paths.insert(canonical);
            Ok(())
        }

        /// Recursively adds `dir` and subdirectories (respecting `self.skip`).
        /// When `report_existing` is true (used when a new directory appears at runtime),
        /// returns a bitmask of matching files already present inside.
        fn add_tree(&mut self, dir: &Path, is_runtime: bool, report_existing: bool) -> u32 {
            let mut mask = 0u32;
            let (fd, wds, paths, skip) = (self.fd, &mut self.wds, &mut self.paths, &self.skip);
            walk_tree(dir, is_runtime, skip, |p, fmask| match fmask {
                None => Self::add_single_dir(fd, wds, paths, p, is_runtime).is_ok(),
                Some(m) => { if report_existing { mask |= m; } true }
            });
            mask
        }

        fn drain_events(&mut self) -> u32 {
            let mut buf = [0u8; 16384];
            let mut mask = 0u32;
            loop {
                let n = unsafe { libc::read(self.fd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
                if n <= 0 {
                    break;
                }
                let total = n as usize;
                let mut offset = 0usize;
                let ev_size = std::mem::size_of::<libc::inotify_event>();
                while offset + ev_size <= total {
                    let ev = unsafe {
                        std::ptr::read_unaligned(buf.as_ptr().add(offset) as *const libc::inotify_event)
                    };
                    let name_start = offset + ev_size;
                    let name_end = (name_start + ev.len as usize).min(total);
                    offset = name_end;

                    if (ev.mask & libc::IN_IGNORED) != 0 {
                        if let Some((old_path, _)) = self.wds.remove(&ev.wd) {
                            self.paths.remove(&old_path);
                        }
                        continue;
                    }

                    let name = if name_end > name_start {
                        let raw = &buf[name_start..name_end];
                        let nul = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
                        String::from_utf8_lossy(&raw[..nul]).into_owned()
                    } else {
                        String::new()
                    };

                    let Some((parent_dir, is_runtime)) = self.wds.get(&ev.wd).cloned() else {
                        continue;
                    };

                    if (ev.mask & libc::IN_ISDIR) != 0 {
                        if (ev.mask & (libc::IN_CREATE | libc::IN_MOVED_TO)) != 0
                            && !name.is_empty()
                            && (is_runtime || !self.skip.contains(&name))
                        {
                            let sub = parent_dir.join(&name);
                            mask |= self.add_tree(&sub, is_runtime, true);
                        }
                        continue;
                    }

                    if !name.is_empty() {
                        mask |= classify_file_name(&name, is_runtime);
                    }
                }
            }
            mask
        }

        pub fn wait(&mut self, timeout_ms: u32) -> u32 {
            let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
            let mut mask = self.drain_events();
            while mask == 0 {
                let now = Instant::now();
                if now >= deadline {
                    return 0;
                }
                let rem_ms = (deadline - now).as_millis().min(i32::MAX as u128) as i32;
                let mut pfd = libc::pollfd {
                    fd: self.fd,
                    events: libc::POLLIN,
                    revents: 0,
                };
                let rc = unsafe { libc::poll(&mut pfd, 1, rem_ms) };
                if rc < 0 {
                    let err = crate::last_errno();
                    if err == libc::EINTR {
                        continue;
                    }
                    return CHANGE_ERROR;
                }
                if rc == 0 {
                    return 0;
                }
                mask |= self.drain_events();
            }
            // Brief 20ms coalesce window for atomic editor saves (write temp + rename).
            let mut pfd = libc::pollfd {
                fd: self.fd,
                events: libc::POLLIN,
                revents: 0,
            };
            let rc = unsafe { libc::poll(&mut pfd, 1, 20) };
            if rc > 0 {
                mask |= self.drain_events();
            }
            mask
        }
    }
}

// ============================================================================
// macOS `kqueue` Implementation
// ============================================================================

#[cfg(target_os = "macos")]
mod os_watch {
    use super::*;
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    const MAX_KQ_FDS: usize = 1500;
    const VNODE_FLAGS: u32 = libc::NOTE_WRITE
        | libc::NOTE_EXTEND
        | libc::NOTE_ATTRIB
        | libc::NOTE_RENAME
        | libc::NOTE_DELETE
        | libc::NOTE_LINK;

    struct WatchedEntry {
        path: PathBuf,
        is_dir: bool,
        is_runtime: bool,
        file_mask: u32,
    }

    pub struct OsWatcher {
        kq: i32,
        skip: HashSet<String>,
        entries: HashMap<i32, WatchedEntry>,
        paths: HashSet<PathBuf>,
    }

    impl Drop for OsWatcher {
        fn drop(&mut self) {
            for &fd in self.entries.keys() {
                unsafe { libc::close(fd); }
            }
            if self.kq >= 0 {
                unsafe { libc::close(self.kq); }
            }
        }
    }

    impl OsWatcher {
        pub fn open(project_dir: &str, runtime_dir: &str, skip: HashSet<String>) -> Result<Self, String> {
            let kq = unsafe { libc::kqueue() };
            if kq < 0 {
                return Err(format!("kqueue failed: {}", std::io::Error::last_os_error()));
            }
            let mut w = Self { kq, skip, entries: HashMap::new(), paths: HashSet::new() };
            watch_roots(project_dir, runtime_dir, |p, is_rt| { let _ = w.add_tree(p, is_rt, false); });
            Ok(w)
        }

        fn register_path_raw(
            kq: i32,
            entries: &mut HashMap<i32, WatchedEntry>,
            paths: &mut HashSet<PathBuf>,
            path: &Path,
            is_dir: bool,
            is_runtime: bool,
            file_mask: u32,
        ) -> bool {
            if entries.len() >= MAX_KQ_FDS || paths.contains(path) {
                return false;
            }
            let Ok(cpath) = CString::new(path.as_os_str().as_bytes()) else {
                return false;
            };
            let fd = unsafe { libc::open(cpath.as_ptr(), libc::O_EVTONLY | libc::O_CLOEXEC) };
            if fd < 0 {
                return false;
            }
            let ev = libc::kevent {
                ident: fd as usize,
                filter: libc::EVFILT_VNODE,
                flags: libc::EV_ADD | libc::EV_ENABLE | libc::EV_CLEAR,
                fflags: VNODE_FLAGS,
                data: 0,
                udata: std::ptr::null_mut(),
            };
            let rc = unsafe {
                libc::kevent(kq, &ev, 1, std::ptr::null_mut(), 0, std::ptr::null())
            };
            if rc < 0 {
                unsafe { libc::close(fd); }
                return false;
            }
            let pb = path.to_path_buf();
            paths.insert(pb.clone());
            entries.insert(fd, WatchedEntry { path: pb, is_dir, is_runtime, file_mask });
            true
        }

        fn register_path(&mut self, path: &Path, is_dir: bool, is_runtime: bool, file_mask: u32) -> bool {
            Self::register_path_raw(self.kq, &mut self.entries, &mut self.paths, path, is_dir, is_runtime, file_mask)
        }

        fn add_tree(&mut self, dir: &Path, is_runtime: bool, report_new: bool) -> u32 {
            let mut mask = 0u32;
            let (kq, entries, paths, skip) = (self.kq, &mut self.entries, &mut self.paths, &self.skip);
            walk_tree(dir, is_runtime, skip, |p, fmask| match fmask {
                None => { Self::register_path_raw(kq, entries, paths, p, true, is_runtime, 0); true }
                Some(m) => {
                    if Self::register_path_raw(kq, entries, paths, p, false, is_runtime, m) && report_new {
                        mask |= m;
                    }
                    true
                }
            });
            mask
        }

        pub fn wait(&mut self, timeout_ms: u32) -> u32 {
            let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
            let mut mask = 0u32;
            let mut events: [libc::kevent; 64] = unsafe { std::mem::zeroed() };
            while mask == 0 {
                let now = Instant::now();
                if now >= deadline {
                    return 0;
                }
                let rem = deadline - now;
                let ts = libc::timespec {
                    tv_sec: rem.as_secs() as libc::time_t,
                    tv_nsec: rem.subsec_nanos() as libc::c_long,
                };
                let n = unsafe {
                    libc::kevent(self.kq, std::ptr::null(), 0, events.as_mut_ptr(), events.len() as i32, &ts)
                };
                if n < 0 {
                    if crate::last_errno() == libc::EINTR {
                        continue;
                    }
                    return CHANGE_ERROR;
                }
                if n == 0 {
                    return 0;
                }
                for ev in &events[..n as usize] {
                    let fd = ev.ident as i32;
                    let deleted = (ev.fflags & (libc::NOTE_DELETE | libc::NOTE_RENAME)) != 0;
                    if let Some(info) = self.entries.get(&fd) {
                        let is_dir = info.is_dir;
                        let is_rt = info.is_runtime;
                        let fmask = info.file_mask;
                        let path = info.path.clone();
                        if !is_dir {
                            mask |= fmask;
                        } else {
                            let new_mask = self.add_tree(&path, is_rt, true);
                            mask |= if new_mask != 0 {
                                new_mask
                            } else if is_rt {
                                CHANGE_RUNTIME
                            } else {
                                CHANGE_LEAN | CHANGE_CSS
                            };
                        }
                        if deleted {
                            self.entries.remove(&fd);
                            self.paths.remove(&path);
                            unsafe { libc::close(fd); }
                            if path.exists() {
                                self.register_path(&path, is_dir, is_rt, fmask);
                            }
                        }
                    }
                }
            }
            mask
        }
    }
}

// ============================================================================
// Unsupported Platform Stub
// ============================================================================

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
mod os_watch {
    use super::*;

    pub struct OsWatcher;

    impl OsWatcher {
        pub fn open(_project_dir: &str, _runtime_dir: &str, _skip: HashSet<String>) -> Result<Self, String> {
            Err("OS file watcher unsupported on this platform".to_owned())
        }
        pub fn wait(&mut self, _timeout_ms: u32) -> u32 { CHANGE_ERROR }
    }
}

static WATCHERS: HandleTable<Arc<Mutex<os_watch::OsWatcher>>> = HandleTable::new();

#[no_mangle]
pub unsafe extern "C" fn qed_watch_open(
    project_dir: *mut LeanObj,
    runtime_dir: *mut LeanObj,
    skip_dirs: *mut LeanObj,
) -> *mut LeanObj {
    let proj = str_slice(project_dir).to_owned();
    let rt = str_slice(runtime_dir).to_owned();
    let n = qed_lean_array_size(skip_dirs);
    let mut skip = HashSet::with_capacity(n);
    for i in 0..n {
        let elem = qed_lean_array_uget(skip_dirs, i);
        skip.insert(str_slice(elem).to_owned());
    }
    mk_io_except(os_watch::OsWatcher::open(&proj, &rt, skip), |w| {
        qed_lean_box_u64(WATCHERS.insert(Arc::new(Mutex::new(w))))
    })
}

#[no_mangle]
pub unsafe extern "C" fn qed_watch_wait(handle: u64, timeout_ms: u32) -> *mut LeanObj {
    let mask = WATCHERS.get(handle).map_or(CHANGE_ERROR, |w| lock_unpoison(&w).wait(timeout_ms));
    qed_lean_io_mk_ok(qed_lean_box_u32(mask))
}

#[no_mangle]
pub unsafe extern "C" fn qed_watch_close(handle: u64) -> *mut LeanObj {
    WATCHERS.remove(handle);
    qed_lean_io_mk_ok(qed_lean_box(0))
}

// ============================================================================
// Lightweight Localhost Dev-Event SSE Push Server
// ============================================================================

struct SseHub {
    closed: AtomicBool,
    last_event: Mutex<Option<String>>,
    clients: Mutex<Vec<TcpStream>>,
}

impl SseHub {
    fn format_frame(payload: &str) -> Vec<u8> {
        let clean = payload.trim();
        let mut out = Vec::with_capacity(clean.len() + 10);
        out.extend_from_slice(b"data: ");
        for line in clean.lines() {
            out.extend_from_slice(line.as_bytes());
        }
        out.extend_from_slice(b"\n\n");
        out
    }

    fn publish(&self, payload: &str) {
        let trimmed = payload.trim().to_owned();
        {
            let mut last = lock_unpoison(&self.last_event);
            *last = Some(trimmed.clone());
        }
        let frame = Self::format_frame(&trimmed);
        let mut clients = lock_unpoison(&self.clients);
        clients.retain_mut(|stream| {
            stream.write_all(&frame).is_ok() && stream.flush().is_ok()
        });
    }

    fn send_keepalive(&self) {
        let mut clients = lock_unpoison(&self.clients);
        clients.retain_mut(|stream| {
            stream.write_all(b": ping\n\n").is_ok() && stream.flush().is_ok()
        });
    }
}

fn handle_sse_connection(mut stream: TcpStream, hub: &Arc<SseHub>) {
    let _ = stream.set_nonblocking(false);
    let _ = stream.set_nodelay(true);
    let _ = stream.set_read_timeout(Some(Duration::from_millis(500)));
    let _ = stream.set_write_timeout(Some(Duration::from_millis(250)));

    let mut req_buf = [0u8; 2048];
    let n = match stream.read(&mut req_buf) {
        Ok(0) | Err(_) => return,
        Ok(n) => n,
    };
    let head = String::from_utf8_lossy(&req_buf[..n]);
    let first_line = head.lines().next().unwrap_or("");
    if first_line.starts_with("OPTIONS ") {
        let _ = stream.write_all(
            b"HTTP/1.1 204 No Content\r\nAccess-Control-Allow-Origin: *\r\nAccess-Control-Allow-Methods: GET, OPTIONS\r\nAccess-Control-Allow-Headers: *\r\nConnection: close\r\n\r\n",
        );
        return;
    }

    let hdr = concat!(
        "HTTP/1.1 200 OK\r\n",
        "Content-Type: text/event-stream; charset=utf-8\r\n",
        "Cache-Control: no-cache, no-store\r\n",
        "Connection: keep-alive\r\n",
        "Access-Control-Allow-Origin: *\r\n",
        "X-Accel-Buffering: no\r\n\r\n",
        "retry: 500\n\n"
    );
    let initial = lock_unpoison(&hub.last_event).clone();
    let mut response = Vec::with_capacity(hdr.len() + initial.as_ref().map_or(0, |s| s.len() + 10));
    response.extend_from_slice(hdr.as_bytes());
    if let Some(payload) = initial {
        response.extend_from_slice(&SseHub::format_frame(&payload));
    }
    if stream.write_all(&response).is_err() || stream.flush().is_err() {
        return;
    }

    let mut clients = lock_unpoison(&hub.clients);
    if clients.len() < 64 {
        clients.push(stream);
    }
}

static SSE_HUBS: HandleTable<Arc<SseHub>> = HandleTable::new();

#[no_mangle]
pub unsafe extern "C" fn qed_dev_sse_start(port: u16) -> *mut LeanObj {
    let listener = match TcpListener::bind(("127.0.0.1", port)) {
        Ok(l) => l,
        Err(e) => return mk_io_except_err(&format!("failed to bind dev SSE listener on 127.0.0.1:{port}: {e}")),
    };
    let actual_port = match listener.local_addr() {
        Ok(a) => a.port(),
        Err(e) => return mk_io_except_err(&format!("failed to read dev SSE local addr: {e}")),
    };
    let _ = listener.set_nonblocking(true);

    let hub = Arc::new(SseHub {
        closed: AtomicBool::new(false),
        last_event: Mutex::new(None),
        clients: Mutex::new(Vec::new()),
    });
    let hub_bg = hub.clone();

    std::thread::spawn(move || {
        let mut last_ping = Instant::now();
        while !hub_bg.closed.load(Ordering::Relaxed) {
            match listener.accept() {
                Ok((stream, _)) => {
                    handle_sse_connection(stream, &hub_bg);
                }
                Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(_) => {
                    std::thread::sleep(Duration::from_millis(50));
                }
            }
            if last_ping.elapsed() >= Duration::from_secs(15) {
                hub_bg.send_keepalive();
                last_ping = Instant::now();
            }
        }
        lock_unpoison(&hub_bg.clients).clear();
    });

    let id = SSE_HUBS.insert(hub);
    let pair = qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(actual_port as usize));
    mk_io_except_ok(pair)
}

#[no_mangle]
pub unsafe extern "C" fn qed_dev_sse_publish(handle: u64, payload: *mut LeanObj) -> *mut LeanObj {
    let msg = str_slice(payload).to_owned();
    if let Some(h) = SSE_HUBS.get(handle) {
        h.publish(&msg);
    }
    qed_lean_io_mk_ok(qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_dev_sse_stop(handle: u64) -> *mut LeanObj {
    if let Some(hub) = SSE_HUBS.remove(handle) {
        hub.closed.store(true, Ordering::Relaxed);
        lock_unpoison(&hub.clients).clear();
    }
    qed_lean_io_mk_ok(qed_lean_box(0))
}
