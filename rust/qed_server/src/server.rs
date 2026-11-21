use std::collections::{HashMap, VecDeque};
use std::io::{self, Write};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

use crate::lean_ffi::*;
use crate::{is_wouldblock, last_errno, lock_unpoison};

const MAX_REQ_HDR_BYTES: usize = 65536;
const MAX_RX_BUF_BYTES: usize = 34 * 1024 * 1024;
const MAX_TX_BUF_BYTES: usize = 8 * 1024 * 1024;
const MAX_INBOX_BCAST: usize = 16384;
const MAX_POOL_QUEUE: usize = 8192;
const MAX_WORKER_CONNS: usize = 4096;
const COMPACT_THRESHOLD: usize = 65536;
const HTTP_IDLE_TIMEOUT: Duration = Duration::from_secs(30);
const WS_PING_INTERVAL: Duration = Duration::from_secs(25);
const WS_DEAD_TIMEOUT: Duration = Duration::from_secs(75);
const TOKEN_LISTEN: u64 = 1;
const TOKEN_WAKE: u64 = 2;

const RESP_503_WIRE: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 19\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\nserver overloaded\r\n";

// ---- Sharded Per-IP Token-Bucket Rate Limiter (Configurable via QED_RATE_LIMIT_RPS / BURST) ----

const RL_SHARDS: usize = 16;
const RL_MAX_ENTRIES_PER_SHARD: usize = 4096;

struct IpBucket {
    tokens_milli: u64,
    last_ms: u64,
}

struct RateLimiter {
    rps: u64,
    burst_milli: u64,
    epoch: Instant,
    shards: [Mutex<HashMap<String, IpBucket>>; RL_SHARDS],
}

impl RateLimiter {
    fn from_env() -> Option<Arc<Self>> {
        let rps = std::env::var("QED_RATE_LIMIT_RPS")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .unwrap_or(0);
        if rps == 0 {
            return None;
        }
        let burst = std::env::var("QED_RATE_LIMIT_BURST")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .filter(|&b| b > 0)
            .unwrap_or_else(|| rps.saturating_mul(2).max(1));
        let shards = std::array::from_fn(|_| Mutex::new(HashMap::new()));
        Some(Arc::new(Self {
            rps,
            burst_milli: burst.saturating_mul(1000),
            epoch: Instant::now(),
            shards,
        }))
    }

    #[inline]
    fn shard_idx(ip: &str) -> usize {
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in ip.as_bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        (h as usize) & (RL_SHARDS - 1)
    }

    fn check(&self, ip: &str) -> Result<(), u64> {
        let now_ms = self.epoch.elapsed().as_millis() as u64;
        let shard = &self.shards[Self::shard_idx(ip)];
        let mut map = lock_unpoison(shard);
        if !map.contains_key(ip) && map.len() >= RL_MAX_ENTRIES_PER_SHARD {
            let cutoff = now_ms.saturating_sub(60_000);
            map.retain(|_, b| b.last_ms >= cutoff);
            if map.len() >= RL_MAX_ENTRIES_PER_SHARD {
                if let Some(oldest_k) = map.iter().min_by_key(|(_, b)| b.last_ms).map(|(k, _)| k.clone()) {
                    map.remove(&oldest_k);
                }
            }
        }
        let bucket = map.entry(ip.to_owned()).or_insert(IpBucket {
            tokens_milli: self.burst_milli,
            last_ms: now_ms,
        });
        let elapsed_ms = now_ms.saturating_sub(bucket.last_ms);
        if elapsed_ms > 0 {
            let add = elapsed_ms.saturating_mul(self.rps);
            bucket.tokens_milli = bucket.tokens_milli.saturating_add(add).min(self.burst_milli);
            bucket.last_ms = now_ms;
        }
        if bucket.tokens_milli >= 1000 {
            bucket.tokens_milli -= 1000;
            Ok(())
        } else {
            let deficit = 1000 - bucket.tokens_milli;
            let per_sec = self.rps.saturating_mul(1000).max(1);
            let retry_after = deficit.div_ceil(per_sec).max(1);
            Err(retry_after)
        }
    }
}

fn format_429_wire(retry_after: u64) -> String {
    format!(
        "HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 19\r\nRetry-After: {retry_after}\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\ntoo many requests\r\n"
    )
}

static STOP: AtomicBool = AtomicBool::new(false);
static INBOXES: RwLock<Vec<Arc<WorkerInbox>>> = RwLock::new(Vec::new());

extern "C" fn handle_stop_signal(_sig: libc::c_int) { STOP.store(true, Ordering::SeqCst); }

// ---- Cursor-Based Byte Queue (O(1) Consume, Bounded Idle Capacity) ----

struct ByteQueue {
    buf: Vec<u8>,
    pos: usize,
}

impl ByteQueue {
    fn new() -> Self { Self { buf: Vec::new(), pos: 0 } }
    fn with_capacity(cap: usize) -> Self { Self { buf: Vec::with_capacity(cap), pos: 0 } }

    #[inline]
    fn as_slice(&self) -> &[u8] { &self.buf[self.pos..] }
    #[inline]
    fn len(&self) -> usize { self.buf.len() - self.pos }
    #[inline]
    fn is_empty(&self) -> bool { self.pos >= self.buf.len() }

    fn extend_from_slice(&mut self, data: &[u8]) {
        if data.is_empty() { return; }
        if self.pos >= self.buf.len() {
            self.buf.clear();
            self.pos = 0;
        }
        self.buf.extend_from_slice(data);
    }

    fn consume(&mut self, n: usize) {
        let adv = n.min(self.len());
        self.pos += adv;
        if self.pos >= self.buf.len() {
            self.buf.clear();
            self.pos = 0;
            if self.buf.capacity() > COMPACT_THRESHOLD {
                self.buf.shrink_to(4096);
            }
        } else if self.pos >= COMPACT_THRESHOLD && self.pos * 2 >= self.buf.len() {
            let rem = self.buf.len() - self.pos;
            self.buf.copy_within(self.pos.., 0);
            self.buf.truncate(rem);
            self.pos = 0;
        }
    }
}

// ---- Cross-Worker WebSocket Broadcast & Blocking-Pool Completion Inbox ----

struct BcastMsg { topic: String, payload: Vec<u8> }
enum SubOp { Add(u32, String, String, Vec<u8>), Remove(u32) }

enum HeadOutcome {
    SendAndClose(WireBytes, usize),
    SendKeepAlive(WireBytes, usize),
    NeedBody { content_len: usize, keep_alive: bool, req: LeanRef, inline: bool },
    WsUpgrade { resp: WireBytes, ws_ctx: LeanRef },
    Defer,
    Fatal,
}

enum DoneEvent {
    Head { token: u64, outcome: HeadOutcome },
    Body { token: u64, resp: Option<WireBytes>, keep_alive: bool },
    WsStep {
        token: u64,
        ws_ctx: LeanRef,
        consumed: usize,
        out_wire: Option<WireBytes>,
        close: bool,
        new_frag: Option<LeanRef>,
        ops: Vec<SubOp>,
    },
}

struct WorkerInbox {
    done_queue: Mutex<Vec<DoneEvent>>,
    bcast_queue: Mutex<VecDeque<Arc<BcastMsg>>>,
    wake_rfd: libc::c_int,
    wake_wfd: libc::c_int,
    wake_pending: AtomicBool,
    ws_subs: AtomicUsize,
}

impl WorkerInbox {
    fn new() -> Self {
        #[cfg(target_os = "linux")]
        let (rfd, wfd) = { let fd = unsafe { libc::eventfd(0, libc::EFD_NONBLOCK | libc::EFD_CLOEXEC) }; (fd, fd) };
        #[cfg(not(target_os = "linux"))]
        let (rfd, wfd) = {
            let mut fds = [-1 as libc::c_int; 2];
            if unsafe { libc::pipe(fds.as_mut_ptr()) } == 0 {
                set_nonblocking(fds[0]); set_nonblocking(fds[1]); (fds[0], fds[1])
            } else { (-1, -1) }
        };
        Self {
            done_queue: Mutex::new(Vec::new()),
            bcast_queue: Mutex::new(VecDeque::new()),
            wake_rfd: rfd,
            wake_wfd: wfd,
            wake_pending: AtomicBool::new(false),
            ws_subs: AtomicUsize::new(0),
        }
    }

    fn push_done(&self, ev: DoneEvent) {
        lock_unpoison(&self.done_queue).push(ev);
        self.wake();
    }

    fn push_bcast(&self, msg: Arc<BcastMsg>) {
        let mut q = lock_unpoison(&self.bcast_queue);
        if q.len() >= MAX_INBOX_BCAST {
            q.pop_front();
        }
        q.push_back(msg);
        drop(q);
        self.wake();
    }

    fn wake(&self) {
        if !self.wake_pending.swap(true, Ordering::SeqCst) {
            self.force_wake();
        }
    }

    fn force_wake(&self) {
        if self.wake_wfd >= 0 {
            let v: u64 = 1;
            let _ = unsafe { libc::write(self.wake_wfd, &v as *const u64 as *const libc::c_void, 8) };
        }
    }

    fn drain_wake(&self) {
        if self.wake_rfd >= 0 {
            let mut buf = [0u8; 64];
            while unsafe { libc::read(self.wake_rfd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) } > 0 {}
        }
        self.wake_pending.store(false, Ordering::SeqCst);
    }
}

impl Drop for WorkerInbox {
    fn drop(&mut self) {
        if self.wake_rfd >= 0 { unsafe { libc::close(self.wake_rfd) }; }
        if self.wake_wfd >= 0 && self.wake_wfd != self.wake_rfd { unsafe { libc::close(self.wake_wfd) }; }
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ws_broadcast(topic_obj: *mut LeanObj, payload_obj: *mut LeanObj) -> *mut LeanObj {
    let inboxes = INBOXES.read().unwrap_or_else(|e| e.into_inner());
    let mut msg: Option<Arc<BcastMsg>> = None;
    for inbox in inboxes.iter() {
        if inbox.ws_subs.load(Ordering::Acquire) == 0 {
            continue;
        }
        let m = msg.get_or_insert_with(|| {
            Arc::new(BcastMsg {
                topic: str_slice(topic_obj).to_owned(),
                payload: ba_slice(payload_obj).to_vec(),
            })
        });
        inbox.push_bcast(m.clone());
    }
    qed_lean_io_mk_ok(qed_lean_box(0))
}

// ---- Dedicated Blocking Handler Pool (Keeps epoll/kqueue Non-Blocking) ----

struct Callbacks {
    init_frag: LeanRef,
    on_head: LeanRef,
    on_body: LeanRef,
    on_ws_bytes: LeanRef,
    on_ws_leave: LeanRef,
}

enum PoolJob {
    Head {
        token: u64,
        head_bytes: Vec<u8>,
        trailing: Vec<u8>,
        ip: String,
        inbox: Arc<WorkerInbox>,
    },
    Body {
        token: u64,
        req: LeanRef,
        body: Vec<u8>,
        ip: String,
        keep_alive: bool,
        inbox: Arc<WorkerInbox>,
    },
    WsStep {
        token: u64,
        ws_ctx: LeanRef,
        rx_bytes: Vec<u8>,
        frag: LeanRef,
        subs: Vec<(u32, String, Vec<u8>)>,
        inbox: Arc<WorkerInbox>,
    },
    WsLeave {
        ws_ctx: LeanRef,
        channel: String,
        params: Vec<u8>,
    },
}

struct PoolQueue {
    jobs: VecDeque<PoolJob>,
    closed: bool,
}

struct BlockingPool {
    state: Arc<(Mutex<PoolQueue>, Condvar)>,
    handles: Mutex<Vec<thread::JoinHandle<()>>>,
}

impl BlockingPool {
    fn new(num_threads: usize, cbs: Arc<Callbacks>) -> Arc<Self> {
        let state = Arc::new((
            Mutex::new(PoolQueue { jobs: VecDeque::new(), closed: false }),
            Condvar::new(),
        ));
        let mut handles = Vec::with_capacity(num_threads);
        for _ in 0..num_threads {
            let st = state.clone();
            let cbs_c = cbs.clone();
            handles.push(thread::spawn(move || {
                unsafe { lean_initialize_thread() };
                loop {
                    let job = {
                        let (lock, cv) = &*st;
                        let mut q = lock_unpoison(lock);
                        while q.jobs.is_empty() && !q.closed {
                            q = cv.wait(q).unwrap_or_else(|e| e.into_inner());
                        }
                        match q.jobs.pop_front() {
                            Some(j) => j,
                            None => break,
                        }
                    };
                    exec_pool_job(&cbs_c, job);
                }
                unsafe { lean_finalize_thread() };
            }));
        }
        Arc::new(Self { state, handles: Mutex::new(handles) })
    }

    fn try_submit(&self, job: PoolJob) -> bool {
        let (lock, cv) = &*self.state;
        let mut q = lock_unpoison(lock);
        if q.closed || q.jobs.len() >= MAX_POOL_QUEUE {
            return false;
        }
        q.jobs.push_back(job);
        cv.notify_one();
        true
    }

    fn submit_leave(&self, job: PoolJob) {
        let (lock, cv) = &*self.state;
        let mut q = lock_unpoison(lock);
        if !q.closed {
            q.jobs.push_back(job);
            cv.notify_one();
        }
    }

    fn shutdown(&self) {
        let (lock, cv) = &*self.state;
        {
            let mut q = lock_unpoison(lock);
            q.closed = true;
            cv.notify_all();
        }
        let handles = std::mem::take(&mut *lock_unpoison(&self.handles));
        for h in handles {
            let _ = h.join();
        }
    }
}

fn eval_body(cbs: &Callbacks, req_ptr: *mut LeanObj, body: &[u8], ip: &str) -> Option<WireBytes> {
    unsafe {
        let res = qed_lean_apply_4(
            cbs.on_body.clone_ptr(),
            req_ptr,
            mk_ba(body),
            mk_str(ip),
            qed_lean_box(0),
        );
        let out = if qed_lean_io_is_ok(res) != 0 {
            Some(WireBytes::from_borrowed(qed_lean_io_val(res)))
        } else {
            None
        };
        qed_lean_dec_ref(res);
        out
    }
}

fn eval_head(cbs: &Callbacks, head_bytes: &[u8], trailing: &[u8], ip: &str, inline: bool) -> HeadOutcome {
    unsafe {
        let res = qed_lean_apply_4(
            cbs.on_head.clone_ptr(),
            mk_ba(head_bytes),
            mk_str(ip),
            qed_lean_box(if inline { 1 } else { 0 }),
            qed_lean_box(0),
        );
        if qed_lean_io_is_ok(res) == 0 {
            qed_lean_dec_ref(res);
            return HeadOutcome::Fatal;
        }
        let act = qed_lean_io_val(res);
        let out = match qed_lean_obj_tag(act) {
            0 => HeadOutcome::SendAndClose(WireBytes::from_borrowed(qed_lean_ctor_get(act, 0)), 0),
            1 => HeadOutcome::SendKeepAlive(WireBytes::from_borrowed(qed_lean_ctor_get(act, 0)), 0),
            t @ (2 | 3) => {
                let cl = qed_lean_usize_of_nat(qed_lean_ctor_get(act, 0));
                let req_ptr = qed_lean_ctor_get(act, 1);
                let keep_alive = t == 3;
                if trailing.len() >= cl {
                    qed_lean_inc(req_ptr);
                    match eval_body(cbs, req_ptr, &trailing[..cl], ip) {
                        Some(w) if keep_alive => HeadOutcome::SendKeepAlive(w, cl),
                        Some(w) => HeadOutcome::SendAndClose(w, cl),
                        None => HeadOutcome::Fatal,
                    }
                } else {
                    qed_lean_inc(req_ptr);
                    if !inline { qed_lean_mark_mt(req_ptr); }
                    HeadOutcome::NeedBody { content_len: cl, keep_alive, req: LeanRef(req_ptr), inline }
                }
            }
            4 => {
                let resp = WireBytes::from_borrowed(qed_lean_ctor_get(act, 0));
                let ctx_ptr = qed_lean_ctor_get(act, 1);
                qed_lean_inc(ctx_ptr);
                qed_lean_mark_mt(ctx_ptr);
                HeadOutcome::WsUpgrade { resp, ws_ctx: LeanRef(ctx_ptr) }
            }
            5 => HeadOutcome::Defer,
            _ => HeadOutcome::Fatal,
        };
        qed_lean_dec_ref(res);
        out
    }
}

fn exec_pool_job(cbs: &Callbacks, job: PoolJob) {
    match job {
        PoolJob::Head { token, head_bytes, trailing, ip, inbox } => {
            let outcome = eval_head(cbs, &head_bytes, &trailing, &ip, false);
            inbox.push_done(DoneEvent::Head { token, outcome });
        }
        PoolJob::Body { token, req, body, ip, keep_alive, inbox } => {
            let resp = eval_body(cbs, unsafe { req.clone_ptr() }, &body, &ip);
            inbox.push_done(DoneEvent::Body { token, resp, keep_alive });
        }
        PoolJob::WsStep { token, ws_ctx, rx_bytes, frag, subs, inbox } => {
            let ev = unsafe {
                let mut subs_arr = qed_lean_array_empty();
                for (sid, ch, params) in &subs {
                    let entry = qed_lean_mk_prod(
                        qed_lean_usize_to_nat(*sid as usize),
                        qed_lean_mk_prod(mk_str(ch), mk_ba(params)),
                    );
                    subs_arr = qed_lean_array_push(subs_arr, entry);
                }
                let res = qed_lean_apply_5(
                    cbs.on_ws_bytes.clone_ptr(),
                    ws_ctx.clone_ptr(),
                    mk_ba(&rx_bytes),
                    frag.clone_ptr(),
                    subs_arr,
                    qed_lean_box(0),
                );
                if qed_lean_io_is_ok(res) == 0 {
                    qed_lean_dec_ref(res);
                    DoneEvent::WsStep {
                        token,
                        ws_ctx,
                        consumed: rx_bytes.len(),
                        out_wire: None,
                        close: true,
                        new_frag: None,
                        ops: Vec::new(),
                    }
                } else {
                    let out = qed_lean_io_val(res);
                    let consumed = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 0)).min(rx_bytes.len());
                    let out_wire = WireBytes::from_borrowed(qed_lean_ctor_get(out, 1));
                    let close_flag = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 2));
                    let new_frag_ptr = qed_lean_ctor_get(out, 3);
                    qed_lean_inc(new_frag_ptr);
                    qed_lean_mark_mt(new_frag_ptr);
                    let ops_arr = qed_lean_ctor_get(out, 4);
                    let mut ops = Vec::new();
                    for i in 0..qed_lean_array_size(ops_arr) {
                        let op = qed_lean_array_uget(ops_arr, i);
                        let sid = qed_lean_usize_of_nat(qed_lean_ctor_get(op, 0)) as u32;
                        match qed_lean_obj_tag(op) {
                            0 => ops.push(SubOp::Add(
                                sid,
                                str_slice(qed_lean_ctor_get(op, 1)).to_owned(),
                                str_slice(qed_lean_ctor_get(op, 2)).to_owned(),
                                ba_slice(qed_lean_ctor_get(op, 3)).to_vec(),
                            )),
                            1 => ops.push(SubOp::Remove(sid)),
                            _ => {}
                        }
                    }
                    qed_lean_dec_ref(res);
                    DoneEvent::WsStep {
                        token,
                        ws_ctx,
                        consumed,
                        out_wire: Some(out_wire),
                        close: close_flag != 0,
                        new_frag: Some(LeanRef(new_frag_ptr)),
                        ops,
                    }
                }
            };
            inbox.push_done(ev);
        }
        PoolJob::WsLeave { ws_ctx, channel, params } => {
            unsafe {
                qed_lean_dec_ref(qed_lean_apply_4(
                    cbs.on_ws_leave.clone_ptr(),
                    ws_ctx.clone_ptr(),
                    mk_str(&channel),
                    mk_ba(&params),
                    qed_lean_box(0),
                ));
            }
        }
    }
}

// ---- Platform Event Loop (Linux epoll / macOS kqueue) ----

struct PollEvent { token: u64, readable: bool, writable: bool, hangup: bool }
struct Poller(libc::c_int);

impl Poller {
    fn new() -> io::Result<Self> {
        #[cfg(target_os = "linux")]
        let fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
        #[cfg(target_os = "macos")]
        let fd = unsafe { libc::kqueue() };
        if fd < 0 { Err(io::Error::last_os_error()) } else { Ok(Self(fd)) }
    }

    fn add_read(&self, sock: libc::c_int, token: u64) -> bool {
        #[cfg(target_os = "linux")]
        unsafe {
            let mut ev = libc::epoll_event { events: (libc::EPOLLIN | libc::EPOLLRDHUP) as u32, u64: token };
            libc::epoll_ctl(self.0, libc::EPOLL_CTL_ADD, sock, &mut ev) == 0
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let kev = libc::kevent {
                ident: sock as usize, filter: libc::EVFILT_READ, flags: libc::EV_ADD | libc::EV_ENABLE,
                fflags: 0, data: 0, udata: token as *mut libc::c_void,
            };
            libc::kevent(self.0, &kev, 1, std::ptr::null_mut(), 0, std::ptr::null()) == 0
        }
    }

    fn set_write(&self, sock: libc::c_int, token: u64, want_write: bool) {
        #[cfg(target_os = "linux")]
        unsafe {
            let mut ev = libc::epoll_event {
                events: (libc::EPOLLIN | libc::EPOLLRDHUP | if want_write { libc::EPOLLOUT } else { 0 }) as u32,
                u64: token,
            };
            let _ = libc::epoll_ctl(self.0, libc::EPOLL_CTL_MOD, sock, &mut ev);
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let kev = libc::kevent {
                ident: sock as usize, filter: libc::EVFILT_WRITE,
                flags: if want_write { libc::EV_ADD | libc::EV_ENABLE } else { libc::EV_DELETE },
                fflags: 0, data: 0, udata: token as *mut libc::c_void,
            };
            let _ = libc::kevent(self.0, &kev, 1, std::ptr::null_mut(), 0, std::ptr::null());
        }
    }

    fn remove(&self, sock: libc::c_int) {
        #[cfg(target_os = "linux")]
        unsafe { let _ = libc::epoll_ctl(self.0, libc::EPOLL_CTL_DEL, sock, std::ptr::null_mut()); }
        #[cfg(target_os = "macos")]
        let _ = sock;
    }

    fn wait(&self, out: &mut Vec<PollEvent>, timeout_ms: i32) {
        out.clear();
        #[cfg(target_os = "linux")]
        unsafe {
            let mut evs: [libc::epoll_event; 128] = std::mem::zeroed();
            let n = libc::epoll_wait(self.0, evs.as_mut_ptr(), evs.len() as i32, timeout_ms);
            for ev in evs.iter().take(n.max(0) as usize) {
                let f = ev.events as i32;
                out.push(PollEvent {
                    token: ev.u64,
                    readable: (f & libc::EPOLLIN) != 0,
                    writable: (f & libc::EPOLLOUT) != 0,
                    hangup: (f & (libc::EPOLLERR | libc::EPOLLHUP | libc::EPOLLRDHUP)) != 0,
                });
            }
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let mut evs: [libc::kevent; 128] = std::mem::zeroed();
            let ts = libc::timespec { tv_sec: (timeout_ms / 1000) as libc::time_t, tv_nsec: ((timeout_ms % 1000) * 1_000_000) as libc::c_long };
            let n = libc::kevent(self.0, std::ptr::null(), 0, evs.as_mut_ptr(), evs.len() as i32, &ts);
            for ev in evs.iter().take(n.max(0) as usize) {
                out.push(PollEvent {
                    token: ev.udata as u64,
                    readable: ev.filter == libc::EVFILT_READ,
                    writable: ev.filter == libc::EVFILT_WRITE,
                    hangup: (ev.flags & (libc::EV_EOF | libc::EV_ERROR)) != 0,
                });
            }
        }
    }
}

impl Drop for Poller { fn drop(&mut self) { unsafe { libc::close(self.0) }; } }

// ---- Low-Level Socket Helpers (IPv4 & IPv6) ----

fn set_nonblocking(fd: libc::c_int) {
    unsafe {
        let f = libc::fcntl(fd, libc::F_GETFL, 0);
        if f >= 0 { let _ = libc::fcntl(fd, libc::F_SETFL, f | libc::O_NONBLOCK); }
    }
}

fn parse_bind_ip(host: &str) -> io::Result<IpAddr> {
    let trimmed = host.trim();
    if trimmed.is_empty() {
        return Ok(IpAddr::V4(Ipv4Addr::UNSPECIFIED));
    }
    let clean = trimmed.strip_prefix('[').and_then(|s| s.strip_suffix(']')).unwrap_or(trimmed);
    IpAddr::from_str(clean).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, format!("invalid bind IP `{host}`")))
}

fn create_listener(bind_ip: IpAddr, port: u16, allow_reuseport: bool) -> io::Result<libc::c_int> {
    unsafe {
        let domain = match bind_ip { IpAddr::V4(_) => libc::AF_INET, IpAddr::V6(_) => libc::AF_INET6 };
        let fd = libc::socket(domain, libc::SOCK_STREAM, 0);
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let one: libc::c_int = 1;
        let _ = libc::setsockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEADDR, &one as *const _ as *const _, 4);
        if allow_reuseport {
            let _ = libc::setsockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEPORT, &one as *const _ as *const _, 4);
        }
        let _ = libc::setsockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, &one as *const _ as *const _, 4);
        let bind_rc = match bind_ip {
            IpAddr::V4(v4) => {
                let mut addr: libc::sockaddr_in = std::mem::zeroed();
                addr.sin_family = libc::AF_INET as libc::sa_family_t;
                addr.sin_port = port.to_be();
                addr.sin_addr = libc::in_addr { s_addr: u32::from_ne_bytes(v4.octets()) };
                libc::bind(fd, &addr as *const _ as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t)
            }
            IpAddr::V6(v6) => {
                if v6.is_unspecified() {
                    let zero: libc::c_int = 0;
                    let _ = libc::setsockopt(fd, libc::IPPROTO_IPV6, libc::IPV6_V6ONLY, &zero as *const _ as *const _, 4);
                }
                let mut addr: libc::sockaddr_in6 = std::mem::zeroed();
                addr.sin6_family = libc::AF_INET6 as libc::sa_family_t;
                addr.sin6_port = port.to_be();
                addr.sin6_addr = libc::in6_addr { s6_addr: v6.octets() };
                libc::bind(fd, &addr as *const _ as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t)
            }
        };
        if bind_rc != 0 || libc::listen(fd, 1024) != 0 {
            let err = io::Error::last_os_error();
            libc::close(fd);
            return Err(err);
        }
        set_nonblocking(fd);
        Ok(fd)
    }
}

fn bound_port(fd: libc::c_int) -> u16 {
    unsafe {
        let mut storage: libc::sockaddr_storage = std::mem::zeroed();
        let mut len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if libc::getsockname(fd, &mut storage as *mut _ as *mut libc::sockaddr, &mut len) != 0 {
            return 0;
        }
        match storage.ss_family as libc::c_int {
            libc::AF_INET => {
                let addr = &*(&storage as *const _ as *const libc::sockaddr_in);
                u16::from_be(addr.sin_port)
            }
            libc::AF_INET6 => {
                let addr = &*(&storage as *const _ as *const libc::sockaddr_in6);
                u16::from_be(addr.sin6_port)
            }
            _ => 0,
        }
    }
}

fn peer_ip_string(storage: &libc::sockaddr_storage) -> String {
    unsafe {
        match storage.ss_family as libc::c_int {
            libc::AF_INET => {
                let addr = &*(storage as *const _ as *const libc::sockaddr_in);
                Ipv4Addr::from(addr.sin_addr.s_addr.to_ne_bytes()).to_string()
            }
            libc::AF_INET6 => {
                let addr = &*(storage as *const _ as *const libc::sockaddr_in6);
                let v6 = Ipv6Addr::from(addr.sin6_addr.s6_addr);
                if let Some(v4) = v6.to_ipv4_mapped() { v4.to_string() } else { v6.to_string() }
            }
            _ => "0.0.0.0".to_owned(),
        }
    }
}

#[cfg(target_os = "linux")]
const SEND_FLAGS: libc::c_int = libc::MSG_NOSIGNAL;
#[cfg(not(target_os = "linux"))]
const SEND_FLAGS: libc::c_int = 0;

fn send_nonblock(fd: libc::c_int, data: &[u8]) -> isize {
    unsafe { libc::send(fd, data.as_ptr() as *const libc::c_void, data.len(), SEND_FLAGS) }
}

fn send_two_nonblock(fd: libc::c_int, a: &[u8], b: &[u8]) -> isize {
    let iovs = [
        libc::iovec { iov_base: a.as_ptr() as *mut libc::c_void, iov_len: a.len() },
        libc::iovec { iov_base: b.as_ptr() as *mut libc::c_void, iov_len: b.len() },
    ];
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = iovs.as_ptr() as *mut libc::iovec;
    msg.msg_iovlen = 2 as _;
    unsafe { libc::sendmsg(fd, &msg, SEND_FLAGS) }
}

// ---- Per-Connection & Per-Worker State ----

struct WsSub { sub_id: u32, topic: String, channel: String, params: Vec<u8> }
struct PendingBody { content_len: usize, keep_alive: bool, req: LeanRef, inline: bool }

struct Conn {
    token: u64,
    fd: libc::c_int,
    ip: String,
    rx: ByteQueue,
    tx: ByteQueue,
    tx_armed: bool,
    peer_eof: bool,
    close_after_tx: bool,
    in_flight: bool,
    pending_body: Option<PendingBody>,
    is_ws: bool,
    ws_ctx: Option<LeanRef>,
    frag: Option<LeanRef>,
    subs: Vec<WsSub>,
    last_active: Instant,
    last_ping: Instant,
}

impl Conn {
    fn buffer_tx(&mut self, poller: &Poller, a: &[u8], b: &[u8]) -> bool {
        if self.tx.len().saturating_add(a.len().saturating_add(b.len())) > MAX_TX_BUF_BYTES {
            return false;
        }
        if !a.is_empty() { self.tx.extend_from_slice(a); }
        if !b.is_empty() { self.tx.extend_from_slice(b); }
        if !self.tx_armed {
            poller.set_write(self.fd, self.token, true);
            self.tx_armed = true;
        }
        true
    }

    fn queue_bytes(&mut self, poller: &Poller, data: &[u8]) -> bool {
        if data.is_empty() { return true; }
        let mut rem = data;
        if self.tx.is_empty() {
            while !rem.is_empty() {
                let n = send_nonblock(self.fd, rem);
                if n > 0 {
                    rem = &rem[n as usize..];
                } else if n < 0 {
                    let e = last_errno();
                    if e == libc::EINTR { continue; }
                    if is_wouldblock(e) { break; }
                    return false;
                } else {
                    return false;
                }
            }
            if rem.is_empty() { return true; }
        }
        self.buffer_tx(poller, rem, &[])
    }

    fn flush_tx(&mut self, poller: &Poller) -> bool {
        while !self.tx.is_empty() {
            let n = send_nonblock(self.fd, self.tx.as_slice());
            if n > 0 {
                self.tx.consume(n as usize);
            } else if n < 0 {
                let e = last_errno();
                if e == libc::EINTR { continue; }
                if is_wouldblock(e) { break; }
                return false;
            } else {
                return false;
            }
        }
        if self.tx.is_empty() && self.tx_armed {
            poller.set_write(self.fd, self.token, false);
            self.tx_armed = false;
        }
        true
    }

    fn queue_two(&mut self, poller: &Poller, a: &[u8], b: &[u8]) -> bool {
        if a.is_empty() { return self.queue_bytes(poller, b); }
        if b.is_empty() { return self.queue_bytes(poller, a); }
        let (mut rem_a, mut rem_b) = (a, b);
        if self.tx.is_empty() {
            let n = send_two_nonblock(self.fd, rem_a, rem_b);
            if n > 0 {
                let sent = n as usize;
                if sent >= rem_a.len() + rem_b.len() { return true; }
                if sent >= rem_a.len() {
                    rem_b = &rem_b[sent - rem_a.len()..];
                    rem_a = &[];
                } else {
                    rem_a = &rem_a[sent..];
                }
            } else if n < 0 {
                let e = last_errno();
                if !is_wouldblock(e) && e != libc::EINTR { return false; }
            }
        }
        self.buffer_tx(poller, rem_a, rem_b)
    }

    fn queue_ws_event(&mut self, poller: &Poller, sub_id: u32, payload: &[u8]) -> bool {
        let total = 5 + payload.len();
        let mut hdr = [0u8; 15];
        hdr[0] = 0x82;
        let hlen = if total < 126 {
            hdr[1] = total as u8;
            2
        } else if total <= 65535 {
            hdr[1] = 126;
            hdr[2..4].copy_from_slice(&(total as u16).to_be_bytes());
            4
        } else {
            hdr[1] = 127;
            hdr[2..10].copy_from_slice(&(total as u64).to_be_bytes());
            10
        };
        hdr[hlen] = 0x12;
        hdr[hlen + 1..hlen + 5].copy_from_slice(&sub_id.to_be_bytes());
        self.queue_two(poller, &hdr[..hlen + 5], payload)
    }

    fn ready_to_close(&self) -> bool {
        !self.in_flight && self.tx.is_empty() && (self.close_after_tx || (self.peer_eof && (self.rx.is_empty() || self.is_ws)))
    }
}

#[derive(Default)]
struct TopicSubs {
    entries: Vec<(u64, u32)>,
    index: HashMap<(u64, u32), usize>,
}

impl TopicSubs {
    fn insert(&mut self, key: (u64, u32)) -> bool {
        if self.index.contains_key(&key) { return false; }
        let idx = self.entries.len();
        self.entries.push(key);
        self.index.insert(key, idx);
        true
    }

    fn remove(&mut self, key: (u64, u32)) -> bool {
        let Some(idx) = self.index.remove(&key) else { return false };
        let last = self.entries.pop().unwrap();
        if idx < self.entries.len() {
            self.entries[idx] = last;
            self.index.insert(last, idx);
        }
        true
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

struct Worker {
    poller: Poller,
    listen_fd: libc::c_int,
    inbox: Arc<WorkerInbox>,
    pool: Arc<BlockingPool>,
    cbs: Arc<Callbacks>,
    rate_limiter: Option<Arc<RateLimiter>>,
    next_token: u64,
    conns: HashMap<u64, Conn>,
    topics: HashMap<String, TopicSubs>,
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum ConnStep { Continue, Done, Close }

impl Conn {
    fn apply_body_outcome(&mut self, poller: &Poller, resp: Option<WireBytes>, keep_alive: bool) -> ConnStep {
        let sent = resp.as_ref().is_some_and(|w| self.queue_bytes(poller, w.as_slice()));
        if !sent || !keep_alive {
            self.close_after_tx = true;
            if !sent || self.tx.is_empty() { ConnStep::Close } else { ConnStep::Done }
        } else if self.ready_to_close() {
            ConnStep::Close
        } else if self.rx.is_empty() {
            ConnStep::Done
        } else {
            ConnStep::Continue
        }
    }

    fn apply_head_outcome(&mut self, poller: &Poller, init_frag: &LeanRef, consume_head: usize, outcome: HeadOutcome) -> ConnStep {
        match outcome {
            HeadOutcome::SendKeepAlive(wire, body_consumed) => {
                if consume_head + body_consumed > 0 { self.rx.consume(consume_head + body_consumed); }
                self.apply_body_outcome(poller, Some(wire), true)
            }
            HeadOutcome::SendAndClose(wire, body_consumed) => {
                if consume_head + body_consumed > 0 { self.rx.consume(consume_head + body_consumed); }
                self.apply_body_outcome(poller, Some(wire), false)
            }
            HeadOutcome::NeedBody { content_len, keep_alive, req, inline } => {
                if consume_head > 0 { self.rx.consume(consume_head); }
                self.pending_body = Some(PendingBody { content_len, keep_alive, req, inline });
                if self.rx.len() >= content_len { ConnStep::Continue }
                else if self.peer_eof { ConnStep::Close }
                else { ConnStep::Done }
            }
            HeadOutcome::WsUpgrade { resp, ws_ctx } => {
                if consume_head > 0 { self.rx.consume(consume_head); }
                if !self.queue_bytes(poller, resp.as_slice()) {
                    self.close_after_tx = true;
                    return ConnStep::Close;
                }
                let now = Instant::now();
                self.is_ws = true;
                self.ws_ctx = Some(ws_ctx);
                self.frag = Some(init_frag.clone());
                self.last_active = now;
                self.last_ping = now;
                if self.rx.is_empty() { ConnStep::Done } else { ConnStep::Continue }
            }
            HeadOutcome::Defer | HeadOutcome::Fatal => {
                if consume_head > 0 { self.rx.consume(consume_head); }
                self.close_after_tx = true;
                if self.tx.is_empty() { ConnStep::Close } else { ConnStep::Done }
            }
        }
    }
}

fn topic_remove_from(topics: &mut HashMap<String, TopicSubs>, inbox: &WorkerInbox, topic: &str, token: u64, sub_id: u32) {
    if let Some(subs) = topics.get_mut(topic) {
        if subs.remove((token, sub_id)) {
            inbox.ws_subs.fetch_sub(1, Ordering::Release);
        }
        if subs.is_empty() { topics.remove(topic); }
    }
}

impl Worker {
    fn topic_remove(&mut self, topic: &str, token: u64, sub_id: u32) {
        topic_remove_from(&mut self.topics, &self.inbox, topic, token, sub_id);
    }

    fn accept_all(&mut self) {
        loop {
            let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
            let mut len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
            let fd = unsafe { libc::accept(self.listen_fd, &mut storage as *mut _ as *mut libc::sockaddr, &mut len) };
            if fd < 0 { break; }
            if self.conns.len() >= MAX_WORKER_CONNS { unsafe { libc::close(fd) }; continue; }
            set_nonblocking(fd);
            let one: libc::c_int = 1;
            unsafe { libc::setsockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, &one as *const _ as *const _, 4) };
            let token = self.next_token;
            self.next_token += 1;
            if !self.poller.add_read(fd, token) { unsafe { libc::close(fd) }; continue; }
            let ip = peer_ip_string(&storage);
            let now = Instant::now();
            self.conns.insert(token, Conn {
                token, fd, ip, rx: ByteQueue::with_capacity(4096), tx: ByteQueue::new(), tx_armed: false,
                peer_eof: false, close_after_tx: false, in_flight: false, pending_body: None, is_ws: false,
                ws_ctx: None, frag: None, subs: Vec::new(), last_active: now, last_ping: now,
            });
        }
    }

    fn close_conn(&mut self, token: u64) {
        let Some(conn) = self.conns.remove(&token) else { return };
        self.poller.remove(conn.fd);
        unsafe { libc::close(conn.fd) };
        if let Some(ws_ctx) = conn.ws_ctx {
            for sub in conn.subs {
                self.topic_remove(&sub.topic, token, sub.sub_id);
                self.pool.submit_leave(PoolJob::WsLeave {
                    ws_ctx: ws_ctx.clone(),
                    channel: sub.channel,
                    params: sub.params,
                });
            }
        }
    }

    fn drain_inbox(&mut self) {
        self.inbox.drain_wake();

        let done_events = std::mem::take(&mut *lock_unpoison(&self.inbox.done_queue));
        for ev in done_events {
            self.handle_done_event(ev);
        }

        let bcast_msgs = std::mem::take(&mut *lock_unpoison(&self.inbox.bcast_queue));
        let mut to_close = Vec::new();
        {
            let Worker { conns, topics, poller, .. } = self;
            for msg in bcast_msgs {
                let Some(targets) = topics.get(&msg.topic) else { continue };
                for &(token, sub_id) in &targets.entries {
                    if let Some(c) = conns.get_mut(&token) {
                        if c.is_ws && !c.close_after_tx {
                            if !c.queue_ws_event(poller, sub_id, &msg.payload) {
                                to_close.push(token);
                            }
                        }
                    }
                }
            }
        }
        for t in to_close { self.close_conn(t); }
    }

    fn finish_step(&mut self, token: u64, step: ConnStep) {
        match step {
            ConnStep::Close => self.close_conn(token),
            ConnStep::Continue => self.process_rx(token),
            ConnStep::Done => {}
        }
    }

    fn handle_done_event(&mut self, ev: DoneEvent) {
        match ev {
            DoneEvent::Head { token, outcome } => {
                let step = if let Some(conn) = self.conns.get_mut(&token) {
                    conn.in_flight = false;
                    conn.last_active = Instant::now();
                    conn.apply_head_outcome(&self.poller, &self.cbs.init_frag, 0, outcome)
                } else { ConnStep::Done };
                self.finish_step(token, step);
            }
            DoneEvent::Body { token, resp, keep_alive } => {
                let step = if let Some(conn) = self.conns.get_mut(&token) {
                    conn.in_flight = false;
                    conn.last_active = Instant::now();
                    conn.apply_body_outcome(&self.poller, resp, keep_alive)
                } else { ConnStep::Done };
                self.finish_step(token, step);
            }
            DoneEvent::WsStep { token, ws_ctx, consumed, out_wire, close, new_frag, ops } => {
                let step = {
                    let Worker { conns, topics, inbox, poller, pool, .. } = self;
                    let Some(conn) = conns.get_mut(&token) else {
                        // Connection closed while step was in flight: clean up any newly joined channels.
                        for op in ops {
                            if let SubOp::Add(_, _, channel, params) = op {
                                pool.submit_leave(PoolJob::WsLeave {
                                    ws_ctx: ws_ctx.clone(),
                                    channel,
                                    params,
                                });
                            }
                        }
                        return;
                    };
                    for op in ops {
                        let sid = match &op { SubOp::Add(s, ..) | SubOp::Remove(s) => *s };
                        if let Some(i) = conn.subs.iter().position(|s| s.sub_id == sid) {
                            let ot = conn.subs.swap_remove(i).topic;
                            topic_remove_from(topics, inbox, &ot, token, sid);
                        }
                        if let SubOp::Add(sid, topic, channel, params) = op {
                            conn.subs.push(WsSub { sub_id: sid, topic: topic.clone(), channel, params });
                            if topics.entry(topic).or_default().insert((token, sid)) {
                                inbox.ws_subs.fetch_add(1, Ordering::Release);
                            }
                        }
                    }
                    conn.in_flight = false;
                    if consumed > 0 {
                        conn.rx.consume(consumed);
                        conn.last_active = Instant::now();
                    }
                    if let Some(f) = new_frag { conn.frag = Some(f); }
                    let sent = out_wire.as_ref().map_or(true, |w| conn.queue_bytes(poller, w.as_slice()));
                    if !sent || close {
                        conn.close_after_tx = true;
                        if !sent || conn.tx.is_empty() { ConnStep::Close } else { ConnStep::Done }
                    } else if conn.ready_to_close() {
                        ConnStep::Close
                    } else if !conn.rx.is_empty() && consumed > 0 {
                        ConnStep::Continue
                    } else {
                        ConnStep::Done
                    }
                };
                self.finish_step(token, step);
            }
        }
    }

    fn sweep_idle(&mut self, now: Instant) {
        let mut to_close = Vec::new();
        for (&token, c) in &mut self.conns {
            if c.in_flight { continue; }
            if c.is_ws {
                if now.duration_since(c.last_active) > WS_DEAD_TIMEOUT {
                    to_close.push(token);
                } else if !c.close_after_tx && now.duration_since(c.last_ping) >= WS_PING_INTERVAL {
                    c.last_ping = now;
                    if !c.queue_bytes(&self.poller, &[0x89, 0x00]) { to_close.push(token); }
                }
            } else if now.duration_since(c.last_active) > HTTP_IDLE_TIMEOUT {
                to_close.push(token);
            }
        }
        for t in to_close { self.close_conn(t); }
    }

    fn reject_overloaded(&mut self, token: u64) {
        let close = self.conns.get_mut(&token).is_some_and(|conn| {
            conn.in_flight = false;
            let sent = conn.queue_bytes(&self.poller, RESP_503_WIRE);
            conn.close_after_tx = true;
            !sent || conn.tx.is_empty()
        });
        if close { self.close_conn(token); }
    }

    fn process_rx(&mut self, token: u64) {
        loop {
            let Some(conn) = self.conns.get_mut(&token) else { return };
            if conn.close_after_tx || conn.in_flight { return; }

            if conn.is_ws {
                if conn.rx.is_empty() { return; }
                let (Some(ws_ctx), Some(frag)) = (conn.ws_ctx.clone(), conn.frag.clone()) else {
                    self.close_conn(token);
                    return;
                };
                let rx_bytes = conn.rx.as_slice().to_vec();
                let subs = conn.subs.iter().map(|s| (s.sub_id, s.channel.clone(), s.params.clone())).collect();
                conn.in_flight = true;
                if !self.pool.try_submit(PoolJob::WsStep {
                    token,
                    ws_ctx,
                    rx_bytes,
                    frag,
                    subs,
                    inbox: self.inbox.clone(),
                }) {
                    conn.in_flight = false;
                    self.close_conn(token);
                }
                return;
            }

            if let Some(pb) = &conn.pending_body {
                if conn.rx.len() < pb.content_len {
                    if conn.peer_eof { self.close_conn(token); }
                    return;
                }
                let pb = conn.pending_body.take().unwrap();
                if pb.inline {
                    let resp = eval_body(
                        &self.cbs,
                        unsafe { pb.req.clone_ptr() },
                        &conn.rx.as_slice()[..pb.content_len],
                        &conn.ip,
                    );
                    conn.rx.consume(pb.content_len);
                    match conn.apply_body_outcome(&self.poller, resp, pb.keep_alive) {
                        ConnStep::Continue => continue,
                        ConnStep::Done => return,
                        ConnStep::Close => { self.close_conn(token); return; }
                    }
                }
                let body = conn.rx.as_slice()[..pb.content_len].to_vec();
                conn.rx.consume(pb.content_len);
                let ip = conn.ip.clone();
                conn.in_flight = true;
                if !self.pool.try_submit(PoolJob::Body {
                    token,
                    req: pb.req,
                    body,
                    ip,
                    keep_alive: pb.keep_alive,
                    inbox: self.inbox.clone(),
                }) {
                    self.reject_overloaded(token);
                }
                return;
            }

            let slice = conn.rx.as_slice();
            let (head_end, consume_len) = match slice.windows(4).position(|w| w == b"\r\n\r\n") {
                Some(pos) => (pos, pos + 4),
                None if slice.len() > MAX_REQ_HDR_BYTES => (MAX_REQ_HDR_BYTES + 1, slice.len()),
                None => {
                    if conn.peer_eof { self.close_conn(token); }
                    return;
                }
            };
            if let Some(rl) = &self.rate_limiter {
                let is_health = slice[..head_end].starts_with(b"GET /_qed/health ");
                if !is_health {
                    if let Err(retry_after) = rl.check(&conn.ip) {
                        let resp = format_429_wire(retry_after);
                        let sent = conn.queue_bytes(&self.poller, resp.as_bytes());
                        conn.close_after_tx = true;
                        let close_now = !sent || conn.tx.is_empty();
                        if close_now { self.close_conn(token); }
                        return;
                    }
                }
            }
            let trailing_slice = if consume_len < slice.len() && slice.len() - consume_len <= 65536 {
                &slice[consume_len..]
            } else {
                &[]
            };
            // Fast inline execution on the I/O worker for non-blocking endpoints (health, cached
            // static assets, and pure in-memory RPC/SSR). Blocking disk/network endpoints return
            // `HeadOutcome::Defer` and offload cleanly to the per-worker `BlockingPool`.
            match eval_head(&self.cbs, &slice[..head_end], trailing_slice, &conn.ip, true) {
                HeadOutcome::Defer => {
                    let head_bytes = slice[..head_end].to_vec();
                    conn.rx.consume(consume_len);
                    let trailing = if !conn.rx.is_empty() && conn.rx.len() <= 65536 {
                        conn.rx.as_slice().to_vec()
                    } else {
                        Vec::new()
                    };
                    let ip = conn.ip.clone();
                    conn.in_flight = true;
                    if !self.pool.try_submit(PoolJob::Head {
                        token,
                        head_bytes,
                        trailing,
                        ip,
                        inbox: self.inbox.clone(),
                    }) {
                        self.reject_overloaded(token);
                    }
                    return;
                }
                outcome => match conn.apply_head_outcome(&self.poller, &self.cbs.init_frag, consume_len, outcome) {
                    ConnStep::Continue => continue,
                    ConnStep::Done => return,
                    ConnStep::Close => { self.close_conn(token); return; }
                },
            }
        }
    }

    fn handle_readable(&mut self, token: u64, hangup: bool) {
        let mut buf = [0u8; 16384];
        let (mut closed, mut got_bytes) = (false, false);
        if let Some(c) = self.conns.get_mut(&token) {
            loop {
                let n = unsafe { libc::read(c.fd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
                if n > 0 {
                    c.rx.extend_from_slice(&buf[..n as usize]);
                    got_bytes = true;
                    if c.rx.len() >= MAX_RX_BUF_BYTES { closed = true; break; }
                } else if n == 0 {
                    c.peer_eof = true;
                    break;
                } else {
                    let e = last_errno();
                    if e == libc::EINTR { continue; }
                    if is_wouldblock(e) { break; }
                    closed = true;
                    break;
                }
            }
            if got_bytes { c.last_active = Instant::now(); }
        } else { return; }
        if closed { self.close_conn(token); return; }
        if got_bytes { self.process_rx(token); }
        if self.conns.get(&token).is_some_and(|c| {
            !c.in_flight && c.tx.is_empty() && (c.close_after_tx || ((c.peer_eof || hangup) && (c.rx.is_empty() || c.is_ws)))
        }) {
            self.close_conn(token);
        }
    }

    fn handle_writable(&mut self, token: u64) {
        let close = self.conns.get_mut(&token).is_some_and(|c| {
            !c.flush_tx(&self.poller) || c.ready_to_close()
        });
        if close { self.close_conn(token); }
    }

    fn run(mut self) {
        let mut events = Vec::with_capacity(128);
        let mut last_sweep = Instant::now();
        while !STOP.load(Ordering::Relaxed) {
            self.poller.wait(&mut events, 250);
            for ev in events.drain(..) {
                match ev.token {
                    TOKEN_LISTEN => self.accept_all(),
                    TOKEN_WAKE => self.drain_inbox(),
                    t => {
                        if ev.readable || ev.hangup { self.handle_readable(t, ev.hangup); }
                        if ev.writable && self.conns.contains_key(&t) { self.handle_writable(t); }
                    }
                }
            }
            let now = Instant::now();
            if now.duration_since(last_sweep) >= Duration::from_secs(5) {
                last_sweep = now;
                self.sweep_idle(now);
            }
        }
        for t in self.conns.keys().copied().collect::<Vec<_>>() { self.close_conn(t); }
        unsafe { libc::close(self.listen_fd) };
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_run(
    host_obj: *mut LeanObj,
    port_in: u16,
    num_workers_in: u32,
    init_frag: *mut LeanObj,
    on_head: *mut LeanObj,
    on_body: *mut LeanObj,
    on_ws_bytes: *mut LeanObj,
    on_ws_leave: *mut LeanObj,
) -> *mut LeanObj {
    libc::signal(libc::SIGPIPE, libc::SIG_IGN);
    let mut sa: libc::sigaction = std::mem::zeroed();
    sa.sa_sigaction = handle_stop_signal as *const () as usize;
    libc::sigaction(libc::SIGINT, &sa, std::ptr::null_mut());
    libc::sigaction(libc::SIGTERM, &sa, std::ptr::null_mut());
    STOP.store(false, Ordering::SeqCst);

    let host_str = str_slice(host_obj).to_owned();
    let bind_ip = match parse_bind_ip(&host_str) {
        Ok(ip) => ip,
        Err(e) => {
            eprintln!("✗ {e}");
            qed_lean_dec(init_frag);
            qed_lean_dec(on_head);
            qed_lean_dec(on_body);
            qed_lean_dec(on_ws_bytes);
            qed_lean_dec(on_ws_leave);
            return qed_lean_io_mk_ok(qed_lean_box_u32(1));
        }
    };

    // Mark long-lived server closures persistent (`m_rc = 0`) so multi-core handler threads
    // avoid atomic MT refcount cache-line bouncing on every request.
    let cbs = Arc::new(Callbacks {
        init_frag: LeanRef::new_persistent(init_frag),
        on_head: LeanRef::new_persistent(on_head),
        on_body: LeanRef::new_persistent(on_body),
        on_ws_bytes: LeanRef::new_persistent(on_ws_bytes),
        on_ws_leave: LeanRef::new_persistent(on_ws_leave),
    });
    let num_workers = if num_workers_in == 0 {
        thread::available_parallelism().map_or(2, |n| n.get()).clamp(1, 16) as u32
    } else { num_workers_in };

    let default_per_worker: usize = if num_workers <= 2 { 4 } else { 2 };
    let per_worker_threads: usize = std::env::var("QED_BLOCKING_THREADS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .map(|n| n.clamp(1, 256).div_ceil(num_workers as usize).max(1))
        .unwrap_or(default_per_worker);
    let pool_threads = per_worker_threads * (num_workers as usize);

    #[cfg(target_os = "linux")]
    let use_reuseport = num_workers > 1;
    #[cfg(not(target_os = "linux"))]
    let use_reuseport = false;

    let first_fd = match create_listener(bind_ip, port_in, use_reuseport) {
        Ok(fd) => fd,
        Err(e) => {
            eprintln!("✗ failed to bind {bind_ip}:{port_in}: {e}");
            return qed_lean_io_mk_ok(qed_lean_box_u32(1));
        }
    };
    let port = if port_in == 0 { bound_port(first_fd) } else { port_in };
    let inboxes: Vec<Arc<WorkerInbox>> = (0..num_workers).map(|_| Arc::new(WorkerInbox::new())).collect();
    *INBOXES.write().unwrap_or_else(|e| e.into_inner()) = inboxes.clone();
    // Dedicated handler pool per I/O worker eliminates cross-worker `PoolQueue` mutex contention.
    let pools: Vec<Arc<BlockingPool>> = (0..num_workers)
        .map(|_| BlockingPool::new(per_worker_threads, cbs.clone()))
        .collect();

    let display_host = match bind_ip {
        IpAddr::V4(v4) => v4.to_string(),
        IpAddr::V6(v6) => format!("[{v6}]"),
    };
    println!(
        "▸ qed native server listening on http://{display_host}:{port} ({num_workers} I/O worker{}, {pool_threads} handler threads)",
        if num_workers == 1 { "" } else { "s" }
    );
    let _ = io::stdout().flush();

    let rate_limiter = RateLimiter::from_env();
    let run_worker = |lfd: libc::c_int, inbox: Arc<WorkerInbox>, pool_c: Arc<BlockingPool>, cbs_c: Arc<Callbacks>, rl_c: Option<Arc<RateLimiter>>| {
        let Ok(poller) = Poller::new() else {
            eprintln!("✗ failed to initialize poller");
            unsafe { libc::close(lfd) };
            return;
        };
        poller.add_read(lfd, TOKEN_LISTEN);
        if inbox.wake_rfd >= 0 { poller.add_read(inbox.wake_rfd, TOKEN_WAKE); }
        Worker {
            poller,
            listen_fd: lfd,
            inbox,
            pool: pool_c,
            cbs: cbs_c,
            rate_limiter: rl_c,
            next_token: 16,
            conns: HashMap::new(),
            topics: HashMap::new(),
        }.run();
    };

    let handles: Vec<_> = (1..num_workers).map(|i| {
        let (inbox, pool_c, cbs_c, rl_c) = (inboxes[i as usize].clone(), pools[i as usize].clone(), cbs.clone(), rate_limiter.clone());
        #[cfg(not(target_os = "linux"))]
        let shared_fd = libc::dup(first_fd);
        thread::spawn(move || {
            unsafe { lean_initialize_thread() };
            #[cfg(target_os = "linux")]
            match create_listener(bind_ip, port, true) {
                Ok(lfd) => run_worker(lfd, inbox, pool_c, cbs_c, rl_c),
                Err(e) => eprintln!("✗ worker {i} failed to bind {bind_ip}:{port}: {e}"),
            }
            #[cfg(not(target_os = "linux"))]
            {
                if shared_fd >= 0 {
                    run_worker(shared_fd, inbox, pool_c, cbs_c, rl_c);
                } else {
                    eprintln!("✗ worker {i} failed to dup listener socket");
                }
            }
            unsafe { lean_finalize_thread() };
        })
    }).collect();

    run_worker(first_fd, inboxes[0].clone(), pools[0].clone(), cbs.clone(), rate_limiter);
    STOP.store(true, Ordering::SeqCst);
    for inbox in &inboxes { inbox.force_wake(); }
    for h in handles { let _ = h.join(); }
    for p in &pools { p.shutdown(); }
    INBOXES.write().unwrap_or_else(|e| e.into_inner()).clear();
    qed_lean_io_mk_ok(qed_lean_box_u32(0))
}
