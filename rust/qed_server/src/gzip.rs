use std::cell::RefCell;
use crate::lean_ffi::*;

const WINDOW: usize = 32768; // == HASH_SIZE
const MAX_MATCH: usize = 258;
const MAX_CHAIN: usize = 16;

const CRC32_TABLES: [[u32; 256]; 8] = {
    let (mut t, mut i, mut s) = ([[0u32; 256]; 8], 0, 1);
    while i < 256 {
        let (mut c, mut k) = (i as u32, 0);
        while k < 8 { c = (c >> 1) ^ (0xEDB8_8320 & (c & 1).wrapping_neg()); k += 1; }
        t[0][i] = c; i += 1;
    }
    while s < 8 { let mut j = 0; while j < 256 { let p = t[s - 1][j]; t[s][j] = (p >> 8) ^ t[0][(p & 0xFF) as usize]; j += 1; } s += 1; }
    t
};

const LITLEN_LUT: [(u16, u8); 286] = {
    let (mut lut, mut sym) = ([(0u16, 0u8); 286], 0usize);
    while sym < 286 {
        let s = sym as u32;
        let (code, bits) = if sym <= 143 { (0x30 + s, 8) } else if sym <= 255 { (0x190 + (s - 144), 9) }
            else if sym <= 279 { (s - 256, 7) } else { (0xC0 + (s - 280), 8) };
        lut[sym] = ((code.reverse_bits() >> (32 - bits)) as u16, bits); sym += 1;
    }
    lut
};

const LEN_LUT: [(u16, u8); 259] = {
    let (mut lut, mut idx, mut base) = ([(0u16, 0u8); 259], 0usize, 3usize);
    while idx < 28 {
        let extra = if idx < 8 { 0u8 } else { ((idx - 4) / 4) as u8 };
        let ((hcode, hbits), span, mut off) = (LITLEN_LUT[257 + idx], 1usize << extra, 0usize);
        while off < span { lut[base + off] = (hcode | ((off as u16) << hbits), hbits + extra); off += 1; }
        base += span; idx += 1;
    }
    lut[258] = LITLEN_LUT[285]; lut
};

const DIST_INFO: [(u16, u8, u8); 30] = {
    let (mut info, mut i, mut base) = ([(0u16, 0u8, 0u8); 30], 0usize, 1u16);
    while i < 30 {
        let extra = if i < 4 { 0u8 } else { ((i - 2) / 2) as u8 };
        info[i] = (base, ((i as u8).reverse_bits() >> 3) & 0x1F, extra);
        base = base.wrapping_add(1u16 << extra); i += 1;
    }
    info
};

const DIST_CODE_LUT: [u8; 512] = {
    let (mut lut, mut i, mut d, mut hi) = ([0u8; 512], 0usize, 0usize, 2usize);
    while d < 256 { while i + 1 < 16 && DIST_INFO[i + 1].0 <= (d + 1) as u16 { i += 1; } lut[d] = i as u8; d += 1; }
    i = 16;
    while hi < 256 { while i + 1 < 30 && DIST_INFO[i + 1].0 <= ((hi << 7) + 1) as u16 { i += 1; } lut[256 + hi] = i as u8; hi += 1; }
    lut
};

fn crc32(data: &[u8]) -> u32 {
    let (mut crc, mut chunks) = (!0u32, data.chunks_exact(8));
    for c in &mut chunks {
        let lo = (u32::from_le_bytes(c[..4].try_into().unwrap()) ^ crc).to_le_bytes();
        crc = CRC32_TABLES[7][lo[0] as usize] ^ CRC32_TABLES[6][lo[1] as usize]
            ^ CRC32_TABLES[5][lo[2] as usize] ^ CRC32_TABLES[4][lo[3] as usize]
            ^ CRC32_TABLES[3][c[4] as usize] ^ CRC32_TABLES[2][c[5] as usize]
            ^ CRC32_TABLES[1][c[6] as usize] ^ CRC32_TABLES[0][c[7] as usize];
    }
    for &b in chunks.remainder() { crc = (crc >> 8) ^ CRC32_TABLES[0][(crc as u8 ^ b) as usize]; }
    !crc
}

struct BitWriter<'a> { out: &'a mut Vec<u8>, buf: u64, cnt: u8 }
impl<'a> BitWriter<'a> {
    #[inline] fn write_bits(&mut self, val: u32, n: u8) {
        self.buf |= (val as u64) << self.cnt; self.cnt += n;
        if self.cnt >= 32 { self.out.extend_from_slice(&(self.buf as u32).to_le_bytes()); self.buf >>= 32; self.cnt -= 32; }
    }
    fn flush_pad(&mut self) { while self.cnt > 0 { self.out.push(self.buf as u8); self.buf >>= 8; self.cnt = self.cnt.saturating_sub(8); } }
}

#[inline] fn load3(data: &[u8], pos: usize) -> u32 {
    if pos + 4 <= data.len() { u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap()) & 0x00FF_FFFF }
    else { (data[pos] as u32) | ((data[pos + 1] as u32) << 8) | ((data[pos + 2] as u32) << 16) }
}
#[inline] fn hash3(v: u32) -> usize { (v.wrapping_mul(0x1E35_A7BD) >> 17) as usize }
#[inline] fn match_len(a: &[u8], b: &[u8]) -> usize {
    let (max_l, mut l) = (a.len().min(b.len()), 3usize);
    while l + 8 <= max_l {
        let diff = u64::from_le_bytes(a[l..l + 8].try_into().unwrap()) ^ u64::from_le_bytes(b[l..l + 8].try_into().unwrap());
        if diff != 0 { return l + (diff.trailing_zeros() >> 3) as usize; }
        l += 8;
    }
    while l < max_l && a[l] == b[l] { l += 1; }
    l
}

struct GzipScratch { head: Box<[u32; WINDOW]>, prev: Box<[u32; WINDOW]>, out: Vec<u8>, base: u32 }

impl GzipScratch {
    fn new() -> Box<Self> {
        let z = || vec![0u32; WINDOW].into_boxed_slice().try_into().unwrap();
        Box::new(Self { head: z(), prev: z(), out: Vec::new(), base: 1 })
    }

    /// Zero-dependency RFC 1952 gzip encoder using RFC 1951 LZ77 + fixed Huffman DEFLATE.
    fn compress_into(&mut self, input: &[u8]) {
        const MAX_EPOCH_INPUT: usize = (u32::MAX / 2) as usize;
        let n = input.len();
        let (base, after_base) = (n < MAX_EPOCH_INPUT).then(|| self.base.checked_add((n as u32).saturating_add(1))).flatten()
            .map_or_else(|| { self.head.fill(0); self.prev.fill(0); (1u32, if n >= MAX_EPOCH_INPUT { u32::MAX } else { 2 + n as u32 }) }, |nb| (self.base, nb));
        self.base = after_base;
        self.out.clear();
        let want_cap = n / 2 + 32;
        if self.out.capacity() < want_cap { self.out.reserve(want_cap); }
        self.out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);

        let ((head, prev), mut bw) = ((&mut *self.head, &mut *self.prev), BitWriter { out: &mut self.out, buf: 0, cnt: 0 });
        bw.write_bits(0b011, 3); // BFINAL=1, BTYPE=01 (fixed Huffman)

        let (hash_limit, mut i) = (n.min((u32::MAX - 1) as usize).saturating_sub(2), 0usize);
        while i < n {
            let (mut best_len, mut best_dist) = (2usize, 0usize);
            if i < hash_limit {
                let (cur3, max_l, min_cand) = (load3(input, i), (n - i).min(MAX_MATCH), base + i.saturating_sub(WINDOW) as u32);
                let h = hash3(cur3);
                let (mut cur_end, mut cand, mut steps) = (input[i + 2], head[h], 0usize);
                while cand >= min_cand && steps < MAX_CHAIN {
                    let c = (cand - base) as usize;
                    if c >= i { break; }
                    if input[c + best_len] == cur_end && (u32::from_le_bytes(input[c..c + 4].try_into().unwrap()) & 0x00FF_FFFF) == cur3 {
                        let l = match_len(&input[c..c + max_l], &input[i..i + max_l]);
                        if l > best_len { (best_len, best_dist) = (l, i - c); if l == max_l { break; } cur_end = input[i + l]; }
                    }
                    let next = prev[c & (WINDOW - 1)];
                    if next >= cand { break; }
                    cand = next; steps += 1;
                }
                prev[i & (WINDOW - 1)] = head[h]; head[h] = base + i as u32;
            }
            if best_len >= 3 {
                let ((lcode, lbits), d) = (LEN_LUT[best_len], best_dist - 1);
                let (dbase, rev5, dbits) = DIST_INFO[DIST_CODE_LUT[if d < 256 { d } else { 256 + (d >> 7) }] as usize];
                let dcode = (rev5 as u32) | (((best_dist as u32) - (dbase as u32)) << 5);
                bw.write_bits((lcode as u32) | (dcode << lbits), lbits + 5 + dbits);
                for j in (i + 1)..(i + best_len).min(hash_limit) {
                    let hj = hash3(load3(input, j)); prev[j & (WINDOW - 1)] = head[hj]; head[hj] = base + j as u32;
                }
                i += best_len;
            } else { let (code, bits) = LITLEN_LUT[input[i] as usize]; bw.write_bits(code as u32, bits); i += 1; }
        }
        let (eob_code, eob_bits) = LITLEN_LUT[256];
        bw.write_bits(eob_code as u32, eob_bits); bw.flush_pad();
        self.out.extend_from_slice(&crc32(input).to_le_bytes());
        self.out.extend_from_slice(&(n as u32).to_le_bytes());
    }
}

thread_local! { static SCRATCH: RefCell<Option<Box<GzipScratch>>> = const { RefCell::new(None) }; }

fn gzip_compress<R>(input: &[u8], f: impl FnOnce(&[u8]) -> R) -> R {
    SCRATCH.with(|cell| {
        let mut slot = cell.borrow_mut();
        let sc = slot.get_or_insert_with(GzipScratch::new);
        sc.compress_into(input);
        let res = f(&sc.out);
        if sc.out.capacity() > 131_072 { sc.out = Vec::new(); }
        res
    })
}

ffi_export! {
    qed_server_gzip_compress(data_obj: *mut LeanObj) => qed_lean_io_mk_ok(gzip_compress(ba_slice(data_obj), |gz| mk_ba(gz)));
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{io::Write, process::{Command, Stdio}};

    fn gunzip(gz: &[u8]) -> Vec<u8> {
        let mut child = Command::new("gzip").arg("-dc").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("spawn gzip -dc");
        let (mut stdin, payload) = (child.stdin.take().unwrap(), gz.to_vec());
        let w = std::thread::spawn(move || { let _ = stdin.write_all(&payload); });
        let out = child.wait_with_output().expect("wait gzip -dc"); w.join().unwrap();
        assert!(out.status.success(), "gzip -dc failed: {}", String::from_utf8_lossy(&out.stderr)); out.stdout
    }
    fn mk_repetitive_40k(rows: u32, m: u32) -> Vec<u8> {
        (0..rows).flat_map(|i| format!("<div class=\"row\" data-id=\"{i}\">item-{}-payload</div>\n", i % m).into_bytes()).collect()
    }

    #[test]
    fn crc32_vectors_and_alignments() {
        let crc_ref = |d: &[u8]| !d.iter().fold(!0u32, |mut c, &b| { c ^= b as u32; for _ in 0..8 { c = (c >> 1) ^ (0xEDB8_8320 & (c & 1).wrapping_neg()); } c });
        assert_eq!((crc32(b""), crc32(b"123456789")), (0, 0xCBF4_3926));
        let buf: Vec<u8> = (0..64u8).map(|i| i.wrapping_mul(37).wrapping_add(13)).collect();
        for s in 0..8 { for l in 0..=33 { assert_eq!(crc32(&buf[s..s + l]), crc_ref(&buf[s..s + l]), "s={s}, l={l}"); } }
    }

    #[test]
    fn gzip_roundtrip_table() {
        let mut rng = 0x9E37_79B9_7F4A_7C15u64;
        let rnd16k: Vec<u8> = (0..16384).map(|_| { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; (rng >> 24) as u8 }).collect();
        for (name, input) in [
            ("empty", Vec::new()), ("1B", vec![b'z']), ("3B", b"abc".to_vec()), ("258B_max_match", vec![b'A'; 258]),
            ("40KiB_window_wrap", mk_repetitive_40k(700, 53)), ("16KiB_random", rnd16k), ("8KiB_repetitive", b"hello-qed-gzip-runtime!".repeat(360)),
        ] { assert_eq!(gunzip(&gzip_compress(&input, |b| b.to_vec())), input, "case `{name}`"); }
    }

    #[test]
    fn gzip_base_epoch_wrap_equivalence() {
        let (payload, mut fresh, mut dirty) = (mk_repetitive_40k(750, 41), GzipScratch::new(), GzipScratch::new());
        fresh.compress_into(&payload);
        dirty.compress_into(&b"seed-different-data-for-hash-tables-1234567890".repeat(900));
        dirty.base = u32::MAX - 10; dirty.compress_into(&payload);
        assert_eq!(dirty.out, fresh.out, "epoch wrap must match fresh scratch byte-for-byte");
        let small = b"{\"status\":\"ok\",\"items\":[1,2,3,4,5,1,2,3,4,5]}";
        fresh.compress_into(small);
        dirty.base = u32::MAX - (small.len() as u32 + 1); dirty.compress_into(small);
        assert_eq!((&dirty.out, dirty.base), (&fresh.out, u32::MAX));
        dirty.compress_into(small); assert_eq!(dirty.out, fresh.out);
    }
}
