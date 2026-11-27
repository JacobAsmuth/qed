//! OS-native event-driven file watcher (`inotify` on Linux, `kqueue` on macOS) and localhost SSE dev push server.

use std::{collections::{HashMap, HashSet}, io::{Read, Write}, net::TcpStream, os::fd::AsRawFd, path::{Path, PathBuf}, sync::{atomic::{AtomicBool, Ordering}, Arc, Mutex}, time::{Duration, Instant}};

use crate::lean_ffi::*;
use crate::{HandleTable, WakeFd, bind_loopback_nonblock, close_fd, lock_unpoison, rem_timeout_ms};

const CHANGE_LEAN: u32 = 1;
const CHANGE_CSS: u32 = 2;
const CHANGE_RUNTIME: u32 = 4;
const CHANGE_ERROR: u32 = 8;

fn classify_file(name: &str, is_rt: bool) -> u32 {
    if is_rt { if name.ends_with(".mjs") { CHANGE_RUNTIME } else { 0 } }
    else if name.ends_with(".lean") { CHANGE_LEAN } else if name.ends_with(".css") { CHANGE_CSS } else { 0 }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn watch_roots(project_dir: &str, runtime_dir: &str, mut add: impl FnMut(&Path, bool)) {
    for (d, rt) in [(project_dir, false), (runtime_dir, true)] { if !d.is_empty() && Path::new(d).exists() { add(Path::new(d), rt); } }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn walk_tree(dir: &Path, is_rt: bool, skip: &HashSet<String>, visit_files: bool, mut visit: impl FnMut(&Path, Option<u32>) -> bool) {
    let mut stack = vec![dir.to_path_buf()];
    while let Some(cur) = stack.pop() {
        if !visit(&cur, None) { continue; }
        let Ok(entries) = std::fs::read_dir(&cur) else { continue };
        for e in entries.flatten() {
            let Ok(ft) = e.file_type() else { continue };
            if ft.is_dir() { if is_rt || !skip.contains(e.file_name().to_string_lossy().as_ref()) { stack.push(e.path()); } }
            else if visit_files { let m = classify_file(&e.file_name().to_string_lossy(), is_rt); if m != 0 { let _ = visit(&e.path(), Some(m)); } }
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn wait_with_coalesce(timeout_ms: u32, mut mask: u32, mut poll_once: impl FnMut(Duration) -> Result<Option<u32>, ()>) -> u32 {
    let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
    while mask == 0 {
        let Some(rem) = deadline.checked_duration_since(Instant::now()).filter(|d| !d.is_zero()) else { return 0 };
        match poll_once(rem) { Err(()) => return CHANGE_ERROR, Ok(None) => return 0, Ok(Some(m)) => mask |= m }
    }
    let cap = Instant::now() + Duration::from_millis(120);
    while let Some(rem) = cap.checked_duration_since(Instant::now()).filter(|d| !d.is_zero()) {
        match poll_once(rem.min(Duration::from_millis(35))) { Ok(Some(m)) => mask |= m, _ => break }
    }
    mask
}

#[cfg(target_os = "linux")]
mod os_watch {
    use super::*;
    use std::{ffi::CString, os::unix::ffi::OsStrExt};

    const WATCH_MASK: u32 = libc::IN_MODIFY | libc::IN_CLOSE_WRITE | libc::IN_MOVED_TO | libc::IN_MOVED_FROM
        | libc::IN_CREATE | libc::IN_DELETE | libc::IN_ATTRIB | libc::IN_DELETE_SELF | libc::IN_MOVE_SELF;

    pub struct OsWatcher { fd: i32, skip: HashSet<String>, wds: HashMap<i32, (PathBuf, bool)>, paths: HashSet<PathBuf> }
    impl Drop for OsWatcher { fn drop(&mut self) { close_fd(self.fd); } }
    impl OsWatcher {
        pub fn open(project_dir: &str, runtime_dir: &str, skip: HashSet<String>) -> Result<Self, String> {
            let fd = unsafe { libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC) };
            if fd < 0 { return Err(format!("inotify_init1 failed: {}", std::io::Error::last_os_error())); }
            let mut w = Self { fd, skip, wds: HashMap::new(), paths: HashSet::new() };
            watch_roots(project_dir, runtime_dir, |p, rt| { let _ = w.add_tree(p, rt, false); });
            Ok(w)
        }
        fn add_tree(&mut self, dir: &Path, is_rt: bool, report_existing: bool) -> u32 {
            let (mut mask, fd, skip, wds, paths) = (0u32, self.fd, &self.skip, &mut self.wds, &mut self.paths);
            walk_tree(dir, is_rt, skip, report_existing, |p, fm| match fm {
                Some(m) => { mask |= m; true }
                None => {
                    if paths.contains(p) { return true; }
                    let Ok(cs) = CString::new(p.as_os_str().as_bytes()) else { return true };
                    let wd = unsafe { libc::inotify_add_watch(fd, cs.as_ptr(), WATCH_MASK) };
                    if wd < 0 { return false; }
                    let pb = p.to_path_buf(); wds.insert(wd, (pb.clone(), is_rt)); paths.insert(pb); true
                }
            });
            mask
        }
        fn drain_events(&mut self) -> u32 {
            let (mut buf, mut mask, ev_sz) = ([0u8; 16384], 0u32, std::mem::size_of::<libc::inotify_event>());
            loop {
                let n = unsafe { libc::read(self.fd, buf.as_mut_ptr() as *mut _, buf.len()) };
                if n <= 0 { break; }
                let (total, mut off) = (n as usize, 0usize);
                while off + ev_sz <= total {
                    let ev = unsafe { std::ptr::read_unaligned(buf.as_ptr().add(off) as *const libc::inotify_event) };
                    let (start, end) = (off + ev_sz, (off + ev_sz + ev.len as usize).min(total));
                    off = end;
                    if (ev.mask & libc::IN_IGNORED) != 0 { if let Some((old, _)) = self.wds.remove(&ev.wd) { self.paths.remove(&old); } continue; }
                    let raw = &buf[start..end];
                    let name = String::from_utf8_lossy(&raw[..raw.iter().position(|&b| b == 0).unwrap_or(raw.len())]);
                    let Some(&(ref parent, is_rt)) = self.wds.get(&ev.wd) else { continue };
                    if (ev.mask & libc::IN_ISDIR) != 0 {
                        if (ev.mask & (libc::IN_CREATE | libc::IN_MOVED_TO)) != 0 && !name.is_empty() && (is_rt || !self.skip.contains(name.as_ref())) {
                            let sub = parent.join(name.as_ref()); mask |= self.add_tree(&sub, is_rt, true);
                        }
                    } else if !name.is_empty() { mask |= classify_file(&name, is_rt); }
                }
            }
            mask
        }
        pub fn wait(&mut self, timeout_ms: u32) -> u32 {
            let init = self.drain_events();
            wait_with_coalesce(timeout_ms, init, |d| match crate::poll_in(self.fd, d.as_millis().clamp(1, i32::MAX as u128) as i32) {
                rc if rc < 0 => if crate::last_errno() == libc::EINTR { Ok(Some(0)) } else { Err(()) },
                0 => Ok(None),
                _ => Ok(Some(self.drain_events())),
            })
        }
    }
}

#[cfg(target_os = "macos")]
mod os_watch {
    use super::*;
    use std::{ffi::CString, os::unix::ffi::OsStrExt};

    const VNODE_FLAGS: u32 = libc::NOTE_WRITE | libc::NOTE_EXTEND | libc::NOTE_ATTRIB | libc::NOTE_RENAME | libc::NOTE_DELETE | libc::NOTE_LINK;

    struct WatchedEntry { path: PathBuf, is_dir: bool, is_rt: bool, fmask: u32 }
    pub struct OsWatcher { kq: i32, skip: HashSet<String>, entries: HashMap<i32, WatchedEntry>, paths: HashSet<PathBuf> }
    impl Drop for OsWatcher { fn drop(&mut self) { for &fd in self.entries.keys() { close_fd(fd); } close_fd(self.kq); } }
    impl OsWatcher {
        pub fn open(project_dir: &str, runtime_dir: &str, skip: HashSet<String>) -> Result<Self, String> {
            let kq = unsafe { libc::kqueue() };
            if kq < 0 { return Err(format!("kqueue failed: {}", std::io::Error::last_os_error())); }
            let mut w = Self { kq, skip, entries: HashMap::new(), paths: HashSet::new() };
            watch_roots(project_dir, runtime_dir, |p, rt| { let _ = w.add_tree(p, rt, false); });
            Ok(w)
        }
        fn register(kq: i32, entries: &mut HashMap<i32, WatchedEntry>, paths: &mut HashSet<PathBuf>, path: &Path, is_dir: bool, is_rt: bool, fmask: u32) -> bool {
            if entries.len() >= 1500 || paths.contains(path) { return false; }
            let Ok(cs) = CString::new(path.as_os_str().as_bytes()) else { return false };
            let fd = unsafe { libc::open(cs.as_ptr(), libc::O_EVTONLY | libc::O_CLOEXEC) };
            if fd < 0 { return false; }
            let ev = libc::kevent { ident: fd as usize, filter: libc::EVFILT_VNODE, flags: libc::EV_ADD | libc::EV_ENABLE | libc::EV_CLEAR, fflags: VNODE_FLAGS, data: 0, udata: std::ptr::null_mut() };
            if unsafe { libc::kevent(kq, &ev, 1, std::ptr::null_mut(), 0, std::ptr::null()) } < 0 { close_fd(fd); return false; }
            let pb = path.to_path_buf(); paths.insert(pb.clone()); entries.insert(fd, WatchedEntry { path: pb, is_dir, is_rt, fmask }); true
        }
        fn add_tree(&mut self, dir: &Path, is_rt: bool, report_new: bool) -> u32 {
            let (mut mask, kq, skip, entries, paths) = (0u32, self.kq, &self.skip, &mut self.entries, &mut self.paths);
            walk_tree(dir, is_rt, skip, true, |p, fm| {
                if Self::register(kq, entries, paths, p, fm.is_none(), is_rt, fm.unwrap_or(0)) && report_new { if let Some(m) = fm { mask |= m; } }
                true
            });
            mask
        }
        fn poll_once(&mut self, evs: &mut [libc::kevent; 64], timeout: Duration) -> Result<Option<u32>, ()> {
            let ts = libc::timespec { tv_sec: timeout.as_secs() as libc::time_t, tv_nsec: timeout.subsec_nanos() as libc::c_long };
            let n = unsafe { libc::kevent(self.kq, std::ptr::null(), 0, evs.as_mut_ptr(), 64, &ts) };
            if n < 0 { return if crate::last_errno() == libc::EINTR { Ok(Some(0)) } else { Err(()) }; }
            if n == 0 { return Ok(None); }
            let mut mask = 0u32;
            for ev in &evs[..n as usize] {
                let (fd, deleted) = (ev.ident as i32, (ev.fflags & (libc::NOTE_DELETE | libc::NOTE_RENAME)) != 0);
                let Some(info) = self.entries.get(&fd) else { continue };
                let (is_dir, is_rt, fmask, path) = (info.is_dir, info.is_rt, info.fmask, info.path.clone());
                mask |= if !is_dir { fmask } else { let nm = self.add_tree(&path, is_rt, true); if nm != 0 { nm } else if is_rt { CHANGE_RUNTIME } else { CHANGE_LEAN | CHANGE_CSS } };
                if deleted {
                    self.entries.remove(&fd); self.paths.remove(&path); close_fd(fd);
                    if path.exists() { Self::register(self.kq, &mut self.entries, &mut self.paths, &path, is_dir, is_rt, fmask); }
                }
            }
            Ok(Some(mask))
        }
        pub fn wait(&mut self, timeout_ms: u32) -> u32 {
            let mut evs: [libc::kevent; 64] = unsafe { std::mem::zeroed() };
            wait_with_coalesce(timeout_ms, 0, |d| self.poll_once(&mut evs, d))
        }
    }
}

static WATCHERS: HandleTable<Arc<Mutex<os_watch::OsWatcher>>> = HandleTable::new();
static SSE_HUBS: HandleTable<Arc<SseHub>> = HandleTable::new();

// ---- Lightweight Localhost Dev-Event SSE Push Server ----

struct SseHub { closed: AtomicBool, wake: WakeFd, last_frame: Mutex<Option<Vec<u8>>>, clients: Mutex<Vec<TcpStream>> }
impl SseHub {
    fn new(clients: Vec<TcpStream>) -> Self { Self { closed: AtomicBool::new(false), wake: WakeFd::new(), last_frame: Mutex::new(None), clients: Mutex::new(clients) } }
    fn format_frame(payload: &str) -> Vec<u8> {
        let mut out = Vec::with_capacity(payload.len() + 8);
        out.extend_from_slice(b"data: ");
        for line in payload.trim().lines() { out.extend_from_slice(line.as_bytes()); }
        out.extend_from_slice(b"\n\n"); out
    }
    fn write_all(s: &mut TcpStream, mut data: &[u8]) -> bool {
        while !data.is_empty() {
            match s.write(data) {
                Ok(n @ 1..) => data = &data[n..],
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                _ => return false,
            }
        }
        true
    }
    fn broadcast(&self, frame: &[u8]) { lock_unpoison(&self.clients).retain_mut(|s| Self::write_all(s, frame)); }
    fn publish(&self, payload: &str) {
        let frame = Self::format_frame(payload);
        *lock_unpoison(&self.last_frame) = Some(frame.clone());
        self.broadcast(&frame);
    }
    fn clear(&self) { lock_unpoison(&self.clients).clear(); }
}

fn handle_sse_connection(mut stream: TcpStream, hub: &Arc<SseHub>) {
    let _ = (stream.set_nonblocking(false), stream.set_nodelay(true), stream.set_read_timeout(Some(Duration::from_millis(500))), stream.set_write_timeout(Some(Duration::from_millis(250))));
    let mut req_buf = [0u8; 2048];
    let Ok(n @ 1..) = stream.read(&mut req_buf) else { return };
    if req_buf[..n].starts_with(b"OPTIONS ") {
        let _ = stream.write_all(b"HTTP/1.1 204 No Content\r\nAccess-Control-Allow-Origin: *\r\nAccess-Control-Allow-Methods: GET, OPTIONS\r\nAccess-Control-Allow-Headers: *\r\nConnection: close\r\n\r\n");
        return;
    }
    const HDR: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Type: text/event-stream; charset=utf-8\r\nCache-Control: no-cache, no-store\r\nConnection: keep-alive\r\nAccess-Control-Allow-Origin: *\r\nX-Accel-Buffering: no\r\n\r\nretry: 500\n\n";
    let last = lock_unpoison(&hub.last_frame).clone();
    let ok = match last { Some(f) => stream.write_all(&[HDR, &f].concat()), None => stream.write_all(HDR) }.is_ok();
    if !ok || stream.set_nonblocking(true).is_err() { return; }
    let mut clients = lock_unpoison(&hub.clients);
    if !hub.closed.load(Ordering::Acquire) && clients.len() < 64 { clients.push(stream); }
}

ffi_export! {
    qed_watch_open(project_dir: *mut LeanObj, runtime_dir: *mut LeanObj, skip_dirs: *mut LeanObj) => {
        let skip: HashSet<String> = (0..qed_lean_array_size(skip_dirs)).map(|i| str_slice(qed_lean_array_get_core(skip_dirs, i)).to_owned()).collect();
        mk_io_except(os_watch::OsWatcher::open(str_slice(project_dir), str_slice(runtime_dir), skip), |w| qed_lean_box_u64(WATCHERS.insert(Arc::new(Mutex::new(w)))))
    };
    qed_watch_wait(handle: u64, timeout_ms: u32) =>
        qed_lean_io_mk_ok(qed_lean_box_u32(WATCHERS.get(handle).map_or(CHANGE_ERROR, |w| lock_unpoison(&w).wait(timeout_ms))));
    qed_watch_close(handle: u64) => { WATCHERS.remove(handle); mk_io_unit() };
    qed_dev_sse_start(port: u16) => mk_io_except(bind_loopback_nonblock(port).map(|(listener, actual_port)| {
        let hub = Arc::new(SseHub::new(Vec::new()));
        let hub_bg = hub.clone();
        std::thread::spawn(move || {
            let (lfd, wfd, mut last_ping) = (listener.as_raw_fd(), hub_bg.wake.read_fd(), Instant::now());
            while !hub_bg.closed.load(Ordering::Acquire) {
                loop {
                    match listener.accept() {
                        Ok((s, _)) => handle_sse_connection(s, &hub_bg),
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                        Err(_) => { std::thread::sleep(Duration::from_millis(50)); break; }
                    }
                }
                if hub_bg.closed.load(Ordering::Acquire) { break; }
                let Some(rem) = rem_timeout_ms(last_ping + Duration::from_secs(15), 1) else { hub_bg.broadcast(b": ping\n\n"); last_ping = Instant::now(); continue; };
                let mut pfds = [libc::pollfd { fd: lfd, events: libc::POLLIN, revents: 0 }, libc::pollfd { fd: wfd, events: libc::POLLIN, revents: 0 }];
                let nfds: libc::nfds_t = if wfd >= 0 { 2 } else { 1 };
                if unsafe { libc::poll(pfds.as_mut_ptr(), nfds, rem) } > 0 && nfds == 2 && (pfds[1].revents & libc::POLLIN) != 0 { hub_bg.wake.drain(); }
            }
            hub_bg.clear();
        });
        (SSE_HUBS.insert(hub), actual_port)
    }), |(id, p)| qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(p as usize)));
    qed_dev_sse_publish(handle: u64, payload: *mut LeanObj) => { if let Some(h) = SSE_HUBS.get(handle) { h.publish(str_slice(payload)); } mk_io_unit() };
    qed_dev_sse_stop(handle: u64) => {
        if let Some(h) = SSE_HUBS.remove(handle) { h.closed.store(true, Ordering::Release); h.wake.wake(); h.clear(); }
        mk_io_unit()
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::TempDir;

    #[test]
    fn sse_hub_format_and_drops_stalled_peer() {
        assert_eq!(SseHub::format_frame("  {\"a\":1}\n{\"b\":2}  "), b"data: {\"a\":1}{\"b\":2}\n\n");
        let listener = std::net::TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let addr = listener.local_addr().unwrap();
        let pair = || { let (c, s) = (TcpStream::connect(addr).unwrap(), listener.accept().unwrap().0); s.set_nonblocking(true).unwrap(); (c, s) };
        let ((mut healthy_cli, healthy_srv), (stalled_cli, mut stalled_srv)) = (pair(), pair());
        unsafe { crate::set_sockopt(stalled_srv.as_raw_fd(), libc::SOL_SOCKET, libc::SO_SNDBUF, 4096); crate::set_sockopt(stalled_cli.as_raw_fd(), libc::SOL_SOCKET, libc::SO_RCVBUF, 4096); }
        assert!((0..4096).any(|_| match stalled_srv.write(&[b'x'; 4096]) {
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => true, Ok(0) | Err(_) => panic!("unexpected write error before saturation"), Ok(_) => false,
        }), "failed to saturate loopback send buffer");
        let hub = SseHub::new(vec![stalled_srv, healthy_srv]);
        hub.publish("{\"status\":\"ok\"}");
        assert_eq!((lock_unpoison(&hub.clients).len(), lock_unpoison(&hub.last_frame).as_deref()), (1, Some(&b"data: {\"status\":\"ok\"}\n\n"[..])));
        healthy_cli.set_read_timeout(Some(Duration::from_secs(1))).unwrap();
        let mut got = [0u8; 64];
        let n = healthy_cli.read(&mut got).unwrap();
        assert_eq!((&got[..n], stalled_cli.peer_addr().is_ok()), (&b"data: {\"status\":\"ok\"}\n\n"[..], true));
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn os_watcher_coalesces_split_write_without_stale_followup() {
        let tmp = TempDir::new("watch");
        let (proj, rt) = (tmp.0.join("proj"), tmp.0.join("rt"));
        for d in [proj.join(".lake"), rt.clone()] { std::fs::create_dir_all(d).unwrap(); }
        let (lean_p, css_p, rt_p) = (proj.join("Demo.lean"), proj.join("site.css"), rt.join("qed_dev.mjs"));
        for (p, b) in [(&lean_p, &b"def x := 1\n"[..]), (&css_p, b"body{}\n"), (&rt_p, b"// v1\n")] { std::fs::write(p, b).unwrap(); }
        let watcher = Arc::new(Mutex::new(os_watch::OsWatcher::open(proj.to_str().unwrap(), rt.to_str().unwrap(), [".lake".into()].into()).unwrap()));
        let wait_bg = || { let w = watcher.clone(); std::thread::spawn(move || lock_unpoison(&w).wait(1500)) };
        let t = wait_bg();
        std::thread::sleep(Duration::from_millis(20));
        { let mut f = std::fs::File::create(&lean_p).unwrap(); std::thread::sleep(Duration::from_millis(10)); f.write_all(b"def x := 2\n").unwrap(); std::thread::sleep(Duration::from_millis(10)); }
        assert_eq!((t.join().unwrap(), lock_unpoison(&watcher).wait(60)), (CHANGE_LEAN, 0));
        for (path, bytes, want) in [(&css_p, &b"body{color:red}\n"[..], CHANGE_CSS), (&rt_p, b"// v2\n", CHANGE_RUNTIME)] {
            let tn = wait_bg(); std::thread::sleep(Duration::from_millis(20)); std::fs::write(path, bytes).unwrap();
            assert_eq!(tn.join().unwrap(), want);
        }
    }
}
