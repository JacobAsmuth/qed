use crate::lean_ffi::*;

const LEN_BASES: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
    35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258,
];
const LEN_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
    3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];

const DIST_BASES: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
    257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DIST_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
    7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13,
];

fn crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in data {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

#[inline]
fn reverse_bits(mut v: u32, n: u8) -> u32 {
    let mut out = 0u32;
    for _ in 0..n {
        out = (out << 1) | (v & 1);
        v >>= 1;
    }
    out
}

struct BitWriter {
    out: Vec<u8>,
    bit_buf: u64,
    bit_cnt: u8,
}

impl BitWriter {
    fn with_capacity(cap: usize) -> Self {
        Self { out: Vec::with_capacity(cap), bit_buf: 0, bit_cnt: 0 }
    }

    #[inline]
    fn write_bits(&mut self, val: u32, n: u8) {
        self.bit_buf |= (val as u64) << self.bit_cnt;
        self.bit_cnt += n;
        while self.bit_cnt >= 8 {
            self.out.push((self.bit_buf & 0xFF) as u8);
            self.bit_buf >>= 8;
            self.bit_cnt -= 8;
        }
    }

    #[inline]
    fn write_huff_litlen(&mut self, sym: u16) {
        let (code, bits) = if sym <= 143 {
            (0x30u32 + sym as u32, 8u8)
        } else if sym <= 255 {
            (0x190u32 + (sym as u32 - 144), 9u8)
        } else if sym <= 279 {
            (sym as u32 - 256, 7u8)
        } else {
            (0xC0u32 + (sym as u32 - 280), 8u8)
        };
        self.write_bits(reverse_bits(code, bits), bits);
    }

    #[inline]
    fn write_huff_dist(&mut self, code: u8) {
        self.write_bits(reverse_bits(code as u32, 5), 5);
    }

    fn flush_pad(&mut self) {
        if self.bit_cnt > 0 {
            self.out.push((self.bit_buf & 0xFF) as u8);
            self.bit_buf = 0;
            self.bit_cnt = 0;
        }
    }
}

#[inline]
fn lookup_base(bases: &[u16], extra: &[u8], val: u16) -> (usize, u32, u8) {
    let idx = bases.partition_point(|&b| b <= val) - 1;
    (idx, (val - bases[idx]) as u32, extra[idx])
}

#[inline]
fn encode_len(len: usize) -> (u16, u32, u8) {
    let (idx, extra, bits) = lookup_base(&LEN_BASES, &LEN_EXTRA, len as u16);
    (257 + idx as u16, extra, bits)
}

#[inline]
fn encode_dist(dist: usize) -> (u8, u32, u8) {
    let (idx, extra, bits) = lookup_base(&DIST_BASES, &DIST_EXTRA, dist as u16);
    (idx as u8, extra, bits)
}

#[inline]
fn hash3(data: &[u8], pos: usize) -> usize {
    let v = (data[pos] as usize)
        | ((data[pos + 1] as usize) << 8)
        | ((data[pos + 2] as usize) << 16);
    ((v.wrapping_mul(0x1E35_A7BD)) >> 17) & 0x7FFF
}

/// Zero-dependency RFC 1952 gzip encoder using RFC 1951 LZ77 + fixed Huffman DEFLATE.
pub fn gzip_compress(input: &[u8]) -> Vec<u8> {
    let mut bw = BitWriter::with_capacity(input.len() / 2 + 32);
    // RFC 1952 10-byte gzip header (DEFLATE, no flags, mtime=0, xfl=0, os=unknown)
    bw.out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);

    // Single final fixed-Huffman DEFLATE block: BFINAL=1 (1 bit), BTYPE=01 (2 bits)
    bw.write_bits(1, 1);
    bw.write_bits(1, 2);

    const HASH_SIZE: usize = 32768;
    const WINDOW: usize = 32768;
    const MAX_MATCH: usize = 258;
    const MAX_CHAIN: usize = 16;

    let mut head = vec![u32::MAX; HASH_SIZE];
    let mut prev = vec![u32::MAX; input.len().min(WINDOW)];
    let n = input.len();
    let mut i = 0usize;

    while i < n {
        let mut best_len = 0usize;
        let mut best_dist = 0usize;

        if i + 3 <= n {
            let h = hash3(input, i);
            let mut cand = head[h];
            let mut steps = 0usize;
            while cand != u32::MAX && steps < MAX_CHAIN {
                let c = cand as usize;
                let dist = i - c;
                if dist == 0 || dist > WINDOW {
                    break;
                }
                if input[c] == input[i] && input[c + 1] == input[i + 1] && input[c + 2] == input[i + 2] {
                    let max_l = (n - i).min(MAX_MATCH);
                    let mut l = 3usize;
                    while l < max_l && input[c + l] == input[i + l] {
                        l += 1;
                    }
                    if l > best_len {
                        best_len = l;
                        best_dist = dist;
                        if l == MAX_MATCH {
                            break;
                        }
                    }
                }
                cand = prev[c & (WINDOW - 1)];
                steps += 1;
            }
            if !prev.is_empty() {
                prev[i & (WINDOW - 1)] = head[h];
            }
            head[h] = i as u32;
        }

        if best_len >= 3 {
            let (lsym, lextra, lbits) = encode_len(best_len);
            bw.write_huff_litlen(lsym);
            if lbits > 0 {
                bw.write_bits(lextra, lbits);
            }
            let (dsym, dextra, dbits) = encode_dist(best_dist);
            bw.write_huff_dist(dsym);
            if dbits > 0 {
                bw.write_bits(dextra, dbits);
            }
            // Insert intermediate positions into hash chain for better ratio
            let end = (i + best_len).min(n.saturating_sub(2));
            let mut j = i + 1;
            while j < end {
                let hj = hash3(input, j);
                if !prev.is_empty() {
                    prev[j & (WINDOW - 1)] = head[hj];
                }
                head[hj] = j as u32;
                j += 1;
            }
            i += best_len;
        } else {
            bw.write_huff_litlen(input[i] as u16);
            i += 1;
        }
    }

    // End-of-block symbol (256)
    bw.write_huff_litlen(256);
    bw.flush_pad();

    // RFC 1952 8-byte trailer: CRC32 + ISIZE (mod 2^32), little-endian
    let crc = crc32(input);
    bw.out.extend_from_slice(&crc.to_le_bytes());
    bw.out.extend_from_slice(&(n as u32).to_le_bytes());
    bw.out
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_gzip_compress(data_obj: *mut LeanObj) -> *mut LeanObj {
    let data = ba_slice(data_obj);
    let gz = gzip_compress(data);
    qed_lean_io_mk_ok(mk_ba(&gz))
}
