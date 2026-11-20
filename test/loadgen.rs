//! Zero-dependency multi-threaded HTTP/1.1 keep-alive load generator.
//!
//! Usage:
//!   loadgen <host:port> <conns> <duration_ms> <warmup_ms> <method> <path> [content_type] [body_hex]

use std::env;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

fn decode_hex(s: &str) -> Vec<u8> {
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len() / 2);
    let mut i = 0;
    while i + 1 < b.len() {
        let hi = (b[i] as char).to_digit(16).unwrap_or(0);
        let lo = (b[i + 1] as char).to_digit(16).unwrap_or(0);
        out.push(((hi << 4) | lo) as u8);
        i += 2;
    }
    out
}

fn find_crlf2(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n")
}

fn parse_status_and_len(head: &[u8]) -> (u16, Option<usize>, bool) {
    let text = std::str::from_utf8(head).unwrap_or("");
    let mut lines = text.split("\r\n");
    let status = lines
        .next()
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|s| s.parse::<u16>().ok())
        .unwrap_or(0);
    let mut content_len = None;
    let mut chunked = false;
    for line in lines {
        if let Some((k, v)) = line.split_once(':') {
            if k.eq_ignore_ascii_case("content-length") {
                content_len = v.trim().parse::<usize>().ok();
            } else if k.eq_ignore_ascii_case("transfer-encoding")
                && v.to_ascii_lowercase().contains("chunked")
            {
                chunked = true;
            }
        }
    }
    (status, content_len, chunked)
}

fn read_response(stream: &mut TcpStream, buf: &mut Vec<u8>, carry: &mut Vec<u8>) -> Option<u16> {
    buf.clear();
    if !carry.is_empty() {
        buf.extend_from_slice(carry);
        carry.clear();
    }
    let mut tmp = [0u8; 8192];
    let head_end = loop {
        if let Some(pos) = find_crlf2(buf) {
            break pos + 4;
        }
        let n = stream.read(&mut tmp).ok()?;
        if n == 0 {
            return None;
        }
        buf.extend_from_slice(&tmp[..n]);
    };
    let (status, content_len, chunked) = parse_status_and_len(&buf[..head_end - 4]);
    let total_end = if let Some(cl) = content_len {
        let need = head_end + cl;
        while buf.len() < need {
            let n = stream.read(&mut tmp).ok()?;
            if n == 0 {
                return None;
            }
            buf.extend_from_slice(&tmp[..n]);
        }
        need
    } else if chunked {
        let mut pos = head_end;
        loop {
            while !buf[pos..].windows(2).any(|w| w == b"\r\n") {
                let n = stream.read(&mut tmp).ok()?;
                if n == 0 {
                    return None;
                }
                buf.extend_from_slice(&tmp[..n]);
            }
            let rel = buf[pos..].windows(2).position(|w| w == b"\r\n").unwrap();
            let sz_str = std::str::from_utf8(&buf[pos..pos + rel]).unwrap_or("0").trim();
            let sz_hex = sz_str.split(';').next().unwrap_or("0").trim();
            let sz = usize::from_str_radix(sz_hex, 16).ok()?;
            pos += rel + 2;
            let need = pos + sz + 2;
            while buf.len() < need {
                let n = stream.read(&mut tmp).ok()?;
                if n == 0 {
                    return None;
                }
                buf.extend_from_slice(&tmp[..n]);
            }
            pos = need;
            if sz == 0 {
                break pos;
            }
        }
    } else {
        head_end
    };
    if buf.len() > total_end {
        carry.extend_from_slice(&buf[total_end..]);
    }
    Some(status)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 7 {
        eprintln!("usage: loadgen <addr> <conns> <duration_ms> <warmup_ms> <method> <path> [content_type] [body_hex]");
        std::process::exit(2);
    }
    let addr = args[1].clone();
    let conns: usize = args[2].parse().expect("conns");
    let duration_ms: u64 = args[3].parse().expect("duration_ms");
    let warmup_ms: u64 = args[4].parse().expect("warmup_ms");
    let method = &args[5];
    let path = &args[6];
    let ctype = args.get(7).map(String::as_str).unwrap_or("");
    let body = args.get(8).map(|s| decode_hex(s)).unwrap_or_default();

    let mut req = Vec::new();
    let _ = write!(
        req,
        "{method} {path} HTTP/1.1\r\nHost: {addr}\r\nConnection: keep-alive\r\n"
    );
    if !ctype.is_empty() {
        let _ = write!(
            req,
            "Content-Type: {ctype}\r\nOrigin: http://{addr}\r\nSec-Fetch-Site: same-origin\r\nContent-Length: {}\r\n",
            body.len()
        );
    }
    req.extend_from_slice(b"\r\n");
    req.extend_from_slice(&body);
    let req = Arc::new(req);

    let record = Arc::new(AtomicBool::new(false));
    let stop = Arc::new(AtomicBool::new(false));

    let mut handles = Vec::with_capacity(conns);
    for _ in 0..conns {
        let addr = addr.clone();
        let req = Arc::clone(&req);
        let record = Arc::clone(&record);
        let stop = Arc::clone(&stop);
        handles.push(thread::spawn(move || {
            let mut stream = TcpStream::connect(&addr).expect("connect");
            let _ = stream.set_nodelay(true);
            let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
            let mut buf = Vec::with_capacity(16384);
            let mut carry = Vec::new();
            let mut ok: u64 = 0;
            let mut err: u64 = 0;
            let mut lats: Vec<u32> = Vec::with_capacity(8192);
            let mut seq: u64 = 0;
            while !stop.load(Ordering::Relaxed) {
                let t0 = Instant::now();
                let res = if stream.write_all(&req).is_ok() {
                    read_response(&mut stream, &mut buf, &mut carry)
                } else {
                    None
                };
                let us = t0.elapsed().as_micros().min(u32::MAX as u128) as u32;
                let rec = record.load(Ordering::Relaxed);
                match res {
                    Some(200..=399) => {
                        if rec {
                            ok += 1;
                            // Sample up to ~20k latencies/thread cleanly
                            if lats.len() < 20000 || (seq & 7) == 0 {
                                lats.push(us);
                            }
                            seq += 1;
                        }
                    }
                    _ => {
                        if rec {
                            err += 1;
                        }
                        if let Ok(s) = TcpStream::connect(&addr) {
                            let _ = s.set_nodelay(true);
                            let _ = s.set_read_timeout(Some(Duration::from_secs(5)));
                            stream = s;
                            carry.clear();
                        }
                    }
                }
            }
            (ok, err, lats)
        }));
    }

    thread::sleep(Duration::from_millis(warmup_ms));
    let start = Instant::now();
    record.store(true, Ordering::Release);
    thread::sleep(Duration::from_millis(duration_ms));
    stop.store(true, Ordering::Release);
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

    let mut total_ok: u64 = 0;
    let mut total_err: u64 = 0;
    let mut all_lats: Vec<u32> = Vec::new();
    for h in handles {
        let (ok, err, lats) = h.join().unwrap();
        total_ok += ok;
        total_err += err;
        all_lats.extend(lats);
    }
    all_lats.sort_unstable();
    let pct = |p: f64| -> u32 {
        if all_lats.is_empty() {
            return 0;
        }
        let idx = ((all_lats.len() - 1) as f64 * p).round() as usize;
        all_lats[idx]
    };
    let rps = (total_ok as f64) / (elapsed_ms / 1000.0);
    println!(
        "{{\"reqs\":{},\"errors\":{},\"elapsed_ms\":{:.2},\"rps\":{:.1},\"p50_us\":{},\"p90_us\":{},\"p99_us\":{},\"max_us\":{}}}",
        total_ok,
        total_err,
        elapsed_ms,
        rps,
        pct(0.50),
        pct(0.90),
        pct(0.99),
        pct(1.00)
    );
}
