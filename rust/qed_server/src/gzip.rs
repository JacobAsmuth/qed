use std::cell::RefCell;

use crate::lean_ffi::*;

const HASH_SIZE: usize = 32768;
const WINDOW: usize = 32768;
const MAX_MATCH: usize = 258;
const MAX_CHAIN: usize = 16;
const MAX_RETAINED_OUT_CAP: usize = 131_072;

const CRC32_TABLES: [[u32; 256]; 8] = build_crc32_tables();
const LITLEN_LUT: [(u16, u8); 286] = build_litlen_lut();
const LEN_LUT: [(u16, u8); 259] = build_len_lut();
const DIST_INFO: [(u16, u8, u8); 30] = build_dist_info();
const DIST_CODE_LUT: [u8; 512] = build_dist_code_lut();

const fn build_crc32_tables() -> [[u32; 256]; 8] {
    let mut t = [[0u32; 256]; 8];
    let mut i = 0;
    while i < 256 {
        let (mut c, mut k) = (i as u32, 0);
        while k < 8 {
            c = (c >> 1) ^ (0xEDB8_8320 & (c & 1).wrapping_neg());
            k += 1;
        }
        t[0][i] = c;
        i += 1;
    }
    let mut s = 1;
    while s < 8 {
        let mut j = 0;
        while j < 256 {
            let prev = t[s - 1][j];
            t[s][j] = (prev >> 8) ^ t[0][(prev & 0xFF) as usize];
            j += 1;
        }
        s += 1;
    }
    t
}

const fn build_litlen_lut() -> [(u16, u8); 286] {
    let mut lut = [(0u16, 0u8); 286];
    let mut sym = 0usize;
    while sym < 286 {
        let s = sym as u32;
        let (code, bits) = if sym <= 143 { (0x30 + s, 8) }
            else if sym <= 255 { (0x190 + (s - 144), 9) }
            else if sym <= 279 { (s - 256, 7) }
            else { (0xC0 + (s - 280), 8) };
        lut[sym] = ((code.reverse_bits() >> (32 - bits)) as u16, bits);
        sym += 1;
    }
    lut
}

const fn build_len_lut() -> [(u16, u8); 259] {
    let mut lut = [(0u16, 0u8); 259];
    let (mut idx, mut base) = (0usize, 3usize);
    while idx < 28 {
        let extra = if idx < 8 { 0u8 } else { ((idx - 4) / 4) as u8 };
        let (hcode, hbits) = LITLEN_LUT[257 + idx];
        let (span, mut off) = (1usize << extra, 0usize);
        while off < span {
            lut[base + off] = (hcode | ((off as u16) << hbits), hbits + extra);
            off += 1;
        }
        base += span;
        idx += 1;
    }
    lut[258] = LITLEN_LUT[285];
    lut
}

const fn build_dist_info() -> [(u16, u8, u8); 30] {
    let mut info = [(0u16, 0u8, 0u8); 30];
    let (mut i, mut base) = (0usize, 1u16);
    while i < 30 {
        let extra = if i < 4 { 0u8 } else { ((i - 2) / 2) as u8 };
        info[i] = (base, ((i as u8).reverse_bits() >> 3) & 0x1F, extra);
        base = base.wrapping_add(1u16 << extra);
        i += 1;
    }
    info
}

const fn build_dist_code_lut() -> [u8; 512] {
    let mut lut = [0u8; 512];
    let (mut idx, mut d) = (0usize, 0usize);
    while d < 256 {
        while idx + 1 < 16 && DIST_INFO[idx + 1].0 <= (d + 1) as u16 { idx += 1; }
        lut[d] = idx as u8;
        d += 1;
    }
    let (mut idx, mut hi) = (16usize, 2usize);
    while hi < 256 {
        while idx + 1 < 30 && DIST_INFO[idx + 1].0 <= ((hi << 7) + 1) as u16 { idx += 1; }
        lut[256 + hi] = idx as u8;
        hi += 1;
    }
    lut
}

fn crc32(data: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    let mut chunks = data.chunks_exact(8);
    for c in &mut chunks {
        let lo = u32::from_le_bytes([c[0], c[1], c[2], c[3]]) ^ crc;
        let hi = u32::from_le_bytes([c[4], c[5], c[6], c[7]]);
        crc = CRC32_TABLES[7][(lo & 0xFF) as usize]
            ^ CRC32_TABLES[6][((lo >> 8) & 0xFF) as usize]
            ^ CRC32_TABLES[5][((lo >> 16) & 0xFF) as usize]
            ^ CRC32_TABLES[4][(lo >> 24) as usize]
            ^ CRC32_TABLES[3][(hi & 0xFF) as usize]
            ^ CRC32_TABLES[2][((hi >> 8) & 0xFF) as usize]
            ^ CRC32_TABLES[1][((hi >> 16) & 0xFF) as usize]
            ^ CRC32_TABLES[0][(hi >> 24) as usize];
    }
    for &b in chunks.remainder() {
        crc = (crc >> 8) ^ CRC32_TABLES[0][((crc as u8) ^ b) as usize];
    }
    !crc
}

struct BitWriter<'a> { out: &'a mut Vec<u8>, bit_buf: u64, bit_cnt: u8 }

impl<'a> BitWriter<'a> {
    #[inline]
    fn write_bits(&mut self, val: u32, n: u8) {
        self.bit_buf |= (val as u64) << self.bit_cnt;
        self.bit_cnt += n;
        if self.bit_cnt >= 32 {
            self.out.extend_from_slice(&(self.bit_buf as u32).to_le_bytes());
            self.bit_buf >>= 32;
            self.bit_cnt -= 32;
        }
    }

    fn flush_pad(&mut self) {
        while self.bit_cnt > 0 {
            self.out.push(self.bit_buf as u8);
            self.bit_buf >>= 8;
            self.bit_cnt = self.bit_cnt.saturating_sub(8);
        }
    }
}

#[inline]
fn load3(data: &[u8], pos: usize) -> u32 {
    if pos + 4 <= data.len() {
        u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap()) & 0x00FF_FFFF
    } else {
        (data[pos] as u32) | ((data[pos + 1] as u32) << 8) | ((data[pos + 2] as u32) << 16)
    }
}

#[inline]
fn hash3_val(v: u32) -> usize { (v.wrapping_mul(0x1E35_A7BD) >> 17) as usize }

#[inline]
fn match_len(a: &[u8], b: &[u8]) -> usize {
    let max_l = a.len().min(b.len());
    let mut l = 3usize;
    while l + 8 <= max_l {
        let diff = u64::from_le_bytes(a[l..l + 8].try_into().unwrap())
            ^ u64::from_le_bytes(b[l..l + 8].try_into().unwrap());
        if diff != 0 { return l + (diff.trailing_zeros() >> 3) as usize; }
        l += 8;
    }
    while l < max_l && a[l] == b[l] { l += 1; }
    l
}

struct GzipScratch {
    head: Box<[u32; HASH_SIZE]>,
    prev: Box<[u32; WINDOW]>,
    out: Vec<u8>,
    base: u32,
}

impl GzipScratch {
    fn new() -> Box<Self> {
        Box::new(Self {
            head: vec![0u32; HASH_SIZE].into_boxed_slice().try_into().unwrap(),
            prev: vec![0u32; WINDOW].into_boxed_slice().try_into().unwrap(),
            out: Vec::new(),
            base: 1,
        })
    }

    /// Zero-dependency RFC 1952 gzip encoder using RFC 1951 LZ77 + fixed Huffman DEFLATE.
    fn compress_into(&mut self, input: &[u8]) {
        const MAX_EPOCH_INPUT: usize = (u32::MAX / 2) as usize;
        let n = input.len();
        let (base, after_base) = match (n < MAX_EPOCH_INPUT)
            .then(|| self.base.checked_add((n as u32).saturating_add(1)))
            .flatten()
        {
            Some(nb) => (self.base, nb),
            None => {
                self.head.fill(0);
                self.prev.fill(0);
                (1u32, if n >= MAX_EPOCH_INPUT { u32::MAX } else { 2 + n as u32 })
            }
        };
        self.base = after_base;

        self.out.clear();
        let want_cap = n / 2 + 32;
        if self.out.capacity() < want_cap { self.out.reserve(want_cap); }
        // RFC 1952 10-byte gzip header (DEFLATE, no flags, mtime=0, xfl=0, os=unknown)
        self.out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);

        let (head, prev) = (&mut *self.head, &mut *self.prev);
        let mut bw = BitWriter { out: &mut self.out, bit_buf: 0, bit_cnt: 0 };
        // Single final fixed-Huffman DEFLATE block: BFINAL=1 (1 bit), BTYPE=01 (2 bits)
        bw.write_bits(0b011, 3);

        let hash_limit = n.min((u32::MAX - 1) as usize).saturating_sub(2);
        let mut i = 0usize;
        while i < n {
            let (mut best_len, mut best_dist) = (2usize, 0usize);
            if i < hash_limit {
                let cur3 = load3(input, i);
                let h = hash3_val(cur3);
                let max_l = (n - i).min(MAX_MATCH);
                let min_cand = base + i.saturating_sub(WINDOW) as u32;
                let mut cur_end = input[i + 2];
                let mut cand = head[h];
                let mut steps = 0usize;
                while cand >= min_cand && steps < MAX_CHAIN {
                    let c = (cand - base) as usize;
                    if c >= i { break; }
                    if input[c + best_len] == cur_end
                        && (u32::from_le_bytes(input[c..c + 4].try_into().unwrap()) & 0x00FF_FFFF) == cur3
                    {
                        let l = match_len(&input[c..c + max_l], &input[i..i + max_l]);
                        if l > best_len {
                            best_len = l;
                            best_dist = i - c;
                            if l == max_l { break; }
                            cur_end = input[i + l];
                        }
                    }
                    let next_cand = prev[c & (WINDOW - 1)];
                    if next_cand >= cand { break; }
                    cand = next_cand;
                    steps += 1;
                }
                prev[i & (WINDOW - 1)] = head[h];
                head[h] = base + i as u32;
            }

            if best_len >= 3 {
                let (lcode, lbits) = LEN_LUT[best_len];
                let d = best_dist - 1;
                let didx = if d < 256 { DIST_CODE_LUT[d] } else { DIST_CODE_LUT[256 + (d >> 7)] } as usize;
                let (dbase, rev5, dbits) = DIST_INFO[didx];
                let dcode = (rev5 as u32) | (((best_dist as u32) - (dbase as u32)) << 5);
                bw.write_bits((lcode as u32) | (dcode << lbits), lbits + 5 + dbits);
                for j in (i + 1)..(i + best_len).min(hash_limit) {
                    let hj = hash3_val(load3(input, j));
                    prev[j & (WINDOW - 1)] = head[hj];
                    head[hj] = base + j as u32;
                }
                i += best_len;
            } else {
                let (code, bits) = LITLEN_LUT[input[i] as usize];
                bw.write_bits(code as u32, bits);
                i += 1;
            }
        }

        let (eob_code, eob_bits) = LITLEN_LUT[256];
        bw.write_bits(eob_code as u32, eob_bits);
        bw.flush_pad();

        self.out.extend_from_slice(&crc32(input).to_le_bytes());
        self.out.extend_from_slice(&(n as u32).to_le_bytes());
    }
}

thread_local! {
    static SCRATCH: RefCell<Option<Box<GzipScratch>>> = const { RefCell::new(None) };
}

fn gzip_compress<R>(input: &[u8], f: impl FnOnce(&[u8]) -> R) -> R {
    SCRATCH.with(|cell| {
        let mut slot = cell.borrow_mut();
        let scratch = slot.get_or_insert_with(GzipScratch::new);
        scratch.compress_into(input);
        let res = f(&scratch.out);
        if scratch.out.capacity() > MAX_RETAINED_OUT_CAP { scratch.out = Vec::new(); }
        res
    })
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_gzip_compress(data_obj: *mut LeanObj) -> *mut LeanObj {
    qed_lean_io_mk_ok(gzip_compress(ba_slice(data_obj), |gz| mk_ba(gz)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    fn gunzip(gz: &[u8]) -> Vec<u8> {
        let mut child = Command::new("gzip").arg("-dc")
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
            .spawn().expect("spawn gzip -dc");
        let mut stdin = child.stdin.take().unwrap();
        let payload = gz.to_vec();
        let writer = std::thread::spawn(move || { let _ = stdin.write_all(&payload); });
        let out = child.wait_with_output().expect("wait gzip -dc");
        writer.join().unwrap();
        assert!(out.status.success(), "gzip -dc failed: {}", String::from_utf8_lossy(&out.stderr));
        out.stdout
    }

    fn crc32_ref(data: &[u8]) -> u32 {
        let mut crc = 0xFFFF_FFFFu32;
        for &b in data {
            crc ^= b as u32;
            for _ in 0..8 { crc = (crc >> 1) ^ (0xEDB8_8320 & (crc & 1).wrapping_neg()); }
        }
        !crc
    }

    fn mk_repetitive_40k(rows: u32, modulo: u32) -> Vec<u8> {
        let mut out = Vec::with_capacity(42000);
        for i in 0..rows {
            out.extend_from_slice(format!("<div class=\"row\" data-id=\"{i}\">item-{}-payload</div>\n", i % modulo).as_bytes());
        }
        out
    }

    #[test]
    fn crc32_vectors_and_alignments() {
        assert_eq!(crc32(b""), 0x0000_0000);
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        let buf: Vec<u8> = (0..64u8).map(|i| i.wrapping_mul(37).wrapping_add(13)).collect();
        for start in 0..8 {
            for len in 0..=33 {
                let s = &buf[start..start + len];
                assert_eq!(crc32(s), crc32_ref(s), "mismatch at start={start}, len={len}");
            }
        }
    }

    #[test]
    fn gzip_roundtrip_table() {
        let mut rng = 0x9E37_79B9_7F4A_7C15u64;
        let random_16k: Vec<u8> = (0..16384).map(|_| {
            rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
            (rng >> 24) as u8
        }).collect();
        let cases: &[(&str, Vec<u8>)] = &[
            ("empty", Vec::new()), ("1B", vec![b'z']), ("3B", b"abc".to_vec()),
            ("258B_max_match", vec![b'A'; 258]), ("40KiB_window_wrap", mk_repetitive_40k(700, 53)),
            ("16KiB_random", random_16k), ("8KiB_repetitive", b"hello-qed-gzip-runtime!".repeat(360)),
        ];
        for (name, input) in cases {
            assert_eq!(&gunzip(&gzip_compress(input, |b| b.to_vec())), input, "round-trip failed for `{name}`");
        }
    }

    #[test]
    fn gzip_base_epoch_wrap_equivalence() {
        let payload = mk_repetitive_40k(750, 41);
        let (mut fresh, mut dirty) = (GzipScratch::new(), GzipScratch::new());
        fresh.compress_into(&payload);
        let expected = fresh.out.clone();
        dirty.compress_into(&b"seed-different-data-for-hash-tables-1234567890".repeat(900));
        dirty.base = u32::MAX - 10;
        dirty.compress_into(&payload);
        assert_eq!(dirty.out, expected, "epoch wrap must match fresh scratch byte-for-byte");

        let small = b"{\"status\":\"ok\",\"items\":[1,2,3,4,5,1,2,3,4,5]}";
        fresh.compress_into(small);
        dirty.base = u32::MAX - (small.len() as u32 + 1);
        dirty.compress_into(small);
        assert_eq!(dirty.out, fresh.out);
        assert_eq!(dirty.base, u32::MAX);
        dirty.compress_into(small);
        assert_eq!(dirty.out, fresh.out);
    }
}
