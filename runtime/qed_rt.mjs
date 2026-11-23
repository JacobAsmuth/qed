export const tag = (o) => (typeof o === 'object' && o !== null) ? o.t : o;
export const PUnit = 0, ioVal = (r) => r.f[0], mkOk = (v) => ({ t: 0, f: [v] });
const _TC = { __tc: null }, isRc = (x) => x !== null && typeof x === 'object' && x.r !== undefined;
export const tc = (a) => (_TC.__tc = a, _TC), pap = (fn, arity, args) => ({ fn, arity, args });
export function app(clo, extra) {
  const a = clo.args.length ? clo.args.concat(extra) : extra, n = clo.arity;
  return a.length < n ? { fn: clo.fn, arity: n, args: a } : a.length === n ? clo.fn(...a) : app(clo.fn(...a.slice(0, n)), a.slice(n));
}
// Freeze module-global arrays (`v.r = Infinity`) so copy-on-write mutators never mutate shared constants.
export function memo(f) { let v, done = false; return () => { if (!done) { v = f(); done = true; if (isRc(v)) v.r = Infinity; } return v; }; }

// BigInt arithmetic (monomorphic BigInt ICs)
const B = BigInt, biAdd = (a, b) => a + b, biMul = (a, b) => a * b;
const biEq = (a, b) => a === b ? 1 : 0, biLe = (a, b) => a <= b ? 1 : 0, biLt = (a, b) => a < b ? 1 : 0;
export const Int_sub = (a, b) => a - b, Int_neg = (a) => -a, Int_ofNat = (n) => n, Int_negSucc = (n) => -(n + 1n), Int_natAbs = (a) => a < 0n ? -a : a;
export const Int_emod = (a, b) => { if (b === 0n) return a; const r = a % b; return r < 0n ? r + Int_natAbs(b) : r; };
export const Int_ediv = (a, b) => b === 0n ? 0n : (a - Int_emod(a, b)) / b;
export const Nat_sub = (a, b) => a > b ? a - b : 0n, Nat_div = (a, b) => b === 0n ? 0n : a / b, Nat_mod = (a, b) => b === 0n ? a : a % b;
export const Nat_pow = (a, b) => a ** b, Nat_land = (a, b) => a & b, Nat_lor = (a, b) => a | b, Nat_shiftRight = (a, b) => a >> b;

// Fixed-width integers (monomorphic Number ICs for <=32-bit / USize; BigInt for UInt64)
const nEq = (a, b) => a === b ? 1 : 0, nLe = (a, b) => a <= b ? 1 : 0, nLt = (a, b) => a < b ? 1 : 0, nToNat = (a) => B(a), mask8 = (a) => a & 0xFF;
const u8 = (n) => Number(n & 0xFFn), u32ToNat = (a) => B(a >>> 0), uSize = (n) => Number(n & 0x1FFFFFFFFFFFFFn);
export const UInt8_toUInt32 = (a) => a >>> 0, UInt8_land = (a, b) => a & b, UInt8_lor = (a, b) => a | b;
export const UInt8_shiftLeft = (a, b) => (a << (b & 7)) & 0xFF, UInt8_shiftRight = (a, b) => (a & 0xFF) >>> (b & 7);
export const UInt16_ofNat = (n) => Number(n & 0xFFFFn), UInt16_toNat = (a) => B(a & 0xFFFF), UInt16_add = (a, b) => (a + b) & 0xFFFF;
export const UInt16_mul = (a, b) => Math.imul(a, b) & 0xFFFF, UInt16_shiftLeft = (a, b) => (a << (b & 15)) & 0xFFFF, UInt16_shiftRight = (a, b) => (a & 0xFFFF) >>> (b & 15);
export const UInt32_ofNat = (n) => Number(n & 0xFFFFFFFFn), UInt32_ofBitVec = (bv) => Number(B(bv) & 0xFFFFFFFFn);
export const UInt32_add = (a, b) => (a + b) >>> 0, UInt32_sub = (a, b) => (a - b) >>> 0, UInt32_mul = (a, b) => Math.imul(a, b) >>> 0;
export const UInt32_shiftLeft = (a, b) => (a << (b & 31)) >>> 0, UInt32_shiftRight = (a, b) => (a >>> (b & 31)) >>> 0;
const M64 = (1n << 64n) - 1n, u64 = (x) => B(x) & M64;
export const UInt64_add = (a, b) => (B(a) + B(b)) & M64, UInt64_sub = (a, b) => (B(a) - B(b)) & M64, UInt64_mul = (a, b) => (B(a) * B(b)) & M64;
export const UInt64_land = (a, b) => (B(a) & B(b)) & M64, UInt64_lor = (a, b) => (B(a) | B(b)) & M64, UInt64_xor = (a, b) => (B(a) ^ B(b)) & M64;
export const UInt64_shiftLeft = (a, b) => (B(a) << (B(b) & 63n)) & M64, UInt64_shiftRight = (a, b) => (B(a) >> (B(b) & 63n)) & M64;
export const UInt64_decEq = (a, b) => u64(a) === u64(b) ? 1 : 0, UInt64_decLe = (a, b) => u64(a) <= u64(b) ? 1 : 0, UInt64_decLt = (a, b) => u64(a) < u64(b) ? 1 : 0;
export const UInt64_toUSize = (a) => Number(B(a) & 0x1FFFFFFFFFFFFFn), USize_add = (a, b) => a + b, USize_sub = (a, b) => a - b;
export const USize_land = (a, b) => (a <= 0x7FFFFFFF && b <= 0x7FFFFFFF) ? ((a & b) >>> 0) : Number(B(a) & B(b)), USize_repr = (a) => String(a);
export const System_Platform_getNumBits = () => 64n, Char_ofNatAux = (n, _h) => Number(n);

// Lists, refcounting, reference stamps & COW Arrays
const NIL = 0, cons = (h, t) => ({ t: 1, f: [h, t] });
const listToArray = (l) => { const a = []; while (typeof l === 'object' && l !== null) { a.push(l.f[0]); l = l.f[1]; } return a; };
const arrayToList = (a) => { let l = NIL; for (let i = a.length - 1; i >= 0; i--) l = cons(a[i], l); return l; };
const own = (a) => (a.r = 1, a), owned = (a) => a.r === 1, mutArr = (a) => owned(a) ? (a.__m = undefined, a) : own(a.slice());
export const inc = (x, n = 1) => { if (isRc(x)) x.r += Number(n); }, dec = (x, n = 1) => { if (isRc(x)) x.r -= Number(n); };
export const isShared = (x) => (isRc(x) && x.r <= 1) ? 0 : 1;
let __markCtr = 0; // Primitives get a fresh stamp each call so scalar rows safely fall back to recompute.
export const refMark = (...a) => { const o = a[a.length - 1]; return (o !== null && typeof o === 'object') ? (o.__m ?? (o.__m = ++__markCtr)) : ++__markCtr; };
export const Array_mkEmpty = (_cap) => own([]), Array_replicate = (n, x) => { const k = Number(n); inc(x, k); return own(new Array(k).fill(x)); };
export const Array_mk = (l) => own(listToArray(l)), Array_size = (a) => B(a.length), Array_usize = (a) => a.length;
export const Array_uget = (a, i) => { const x = a[i]; inc(x); return x; }, Array_getInternal = (a, i) => Array_uget(a, Number(i));
export const Array_getInternalBorrowed = (a, i) => a[Number(i)];
export const Array_getx33Internal = (_inst, a, i) => Array_uget(a, Number(i)), Array_getx33InternalBorrowed = (_inst, a, i) => a[Number(i)];
export const Array_push = (a, x) => owned(a) ? (a.__m = undefined, a.push(x), a) : own([...a, x]);
export const Array_pop = (a) => owned(a) ? (a.__m = undefined, a.pop(), a) : own(a.slice(0, a.length - 1));
export const Array_uset = (a, i, x) => { const b = mutArr(a); b[i] = x; return b; }, Array_set = (a, i, x) => Array_uset(a, Number(i), x);
export const Array_swap = (a, i, j) => { const b = mutArr(a), x = Number(i), y = Number(j), t = b[x]; b[x] = b[y]; b[y] = t; return b; };
export const Array_markLinear = (a) => a, Array_propagateMark = (_a, b) => b;

// Strings & UTF-8 cache
const ENC = new TextEncoder(), DEC = new TextDecoder(), DEC_FATAL = new TextDecoder('utf-8', { fatal: true });
const STR_CACHE_MAX = 4096, _strCache = new Map();
let _lastStr = null, _lastInfo = null, _evictScheduled = false;
function getStrInfo(s) {
  if (s === _lastStr) return _lastInfo;
  const cacheable = s.length <= STR_CACHE_MAX, hit = cacheable ? _strCache.get(s) : undefined;
  if (hit !== undefined) return (_lastStr = s, _lastInfo = hit);
  let ascii = true;
  for (let i = 0; i < s.length; i++) if (s.charCodeAt(i) >= 0x80) { ascii = false; break; }
  const bytes = ascii ? null : ENC.encode(s), info = { ascii, bytes, len: ascii ? s.length : bytes.length };
  if (cacheable) { if (_strCache.size >= STR_CACHE_MAX) _strCache.clear(); _strCache.set(s, info); }
  else if (!_evictScheduled) { _evictScheduled = true; queueMicrotask(() => { _evictScheduled = false; if (_lastStr?.length > STR_CACHE_MAX) _lastStr = _lastInfo = null; }); }
  return (_lastStr = s, _lastInfo = info);
}
const utf8Len = (b0) => b0 < 0x80 ? 1 : b0 < 0xE0 ? 2 : b0 < 0xF0 ? 3 : 4;
const strByte = (s, info, i) => info.ascii ? s.charCodeAt(i) : info.bytes[i];
export const String_append = (a, b) => a + b, String_utf8ByteSize = (s) => B(getStrInfo(s).len), String_push = (s, c) => s + String.fromCodePoint(c);
export const String_decEq = (a, b) => a === b ? 1 : 0, String_Internal_isPrefixOf = (p, s) => s.startsWith(p) ? 1 : 0;
export const String_Internal_any = (s, f) => { for (const ch of s) if (app(f, [ch.codePointAt(0)])) return 1; return 0; };
export const String_length = (s) => {
  let n = s.length;
  for (let i = 0; i < s.length; i++) if ((s.charCodeAt(i) & 0xFC00) === 0xD800 && i + 1 < s.length && (s.charCodeAt(i + 1) & 0xFC00) === 0xDC00) { n--; i++; }
  return B(n);
};
export const String_decidableLT = (a, b) => {
  for (let i = 0, j = 0; i < a.length && j < b.length; ) {
    const x = a.codePointAt(i), y = b.codePointAt(j);
    if (x !== y) return x < y ? 1 : 0;
    i += x > 0xFFFF ? 2 : 1; j += y > 0xFFFF ? 2 : 1;
  }
  return a.length < b.length ? 1 : 0;
};
export const String_get = (s, pos) => {
  const p = Number(pos), info = getStrInfo(s);
  if (p >= info.len) return 0;
  if (info.ascii) return s.charCodeAt(p);
  const b = info.bytes, b0 = b[p], n = utf8Len(b0);
  let cp = n === 1 ? b0 : b0 & (0x7F >> n);
  for (let i = 1; i < n; i++) cp = (cp << 6) | (b[p + i] & 0x3F);
  return cp;
};
export const String_next = (s, pos) => { const p = Number(pos), info = getStrInfo(s); return B(p + (p >= info.len || info.ascii ? 1 : utf8Len(info.bytes[p]))); };
export const String_prev = (s, pos) => {
  const p = Number(pos), info = getStrInfo(s);
  if (p <= 0 || !info.len) return 0n;
  let i = Math.min(p, info.len) - 1;
  if (!info.ascii) while (i > 0 && (info.bytes[i] & 0xC0) === 0x80) i--;
  return B(i);
};
export const String_atEnd = (s, pos) => Number(pos) >= getStrInfo(s).len ? 1 : 0;
export const String_extract = (s, b, e) => {
  const bo = Number(b), eo = Number(e), info = bo < eo ? getStrInfo(s) : null;
  return !info ? '' : info.ascii ? s.slice(bo, eo) : (bo === 0 && eo >= info.len) ? s : DEC.decode(info.bytes.subarray(bo, eo));
};
export const String_mk = (l) => { let s = ''; while (typeof l === 'object' && l !== null) { s += String.fromCodePoint(l.f[0]); l = l.f[1]; } return s; };
export const String_data = (s) => { const a = []; for (const ch of s) a.push(ch.codePointAt(0)); return arrayToList(a); };
export const String_hash = (s) => {
  let h1 = 0x811c9dc5, h2 = 0x01000193;
  for (let i = 0; i < s.length; i++) { const c = s.charCodeAt(i); h1 = Math.imul(h1 ^ c, 0x01000193); h2 = Math.imul(h2 ^ (c + i), 0x85ebca6b); }
  return (B(h2 >>> 0) << 32n) | B(h1 >>> 0);
};
export const String_toUTF8 = (s) => ENC.encode(s), String_ofByteArray = (ba, _h) => DEC.decode(ba);
export const String_getUTF8Byte = (s, p) => strByte(s, getStrInfo(s), Number(p));
export const String_Slice_Pattern_Internal_memcmpStr = (lhs, rhs, lstart, rstart, len) => {
  const ls = Number(lstart), rs = Number(rstart), n = Number(len);
  if (n <= 0) return 1;
  const li = getStrInfo(lhs), ri = getStrInfo(rhs);
  if (ls + n > li.len || rs + n > ri.len) return 0;
  if (li.ascii && ri.ascii) return lhs.slice(ls, ls + n) === rhs.slice(rs, rs + n) ? 1 : 0;
  for (let i = 0; i < n; i++) if (strByte(lhs, li, ls + i) !== strByte(rhs, ri, rs + i)) return 0;
  return 1;
};

// ByteArrays & Floats
const mkBytes = (cap, used) => { const ab = new ArrayBuffer(cap); ab.__used = used; return (ab.__view = new Uint8Array(ab)); };
const ensureBytes = (ba, end, cap, ok) => {
  const ab = ba.buffer;
  if (ok && ba.byteOffset === 0 && ab.__used === ba.length && end <= ab.byteLength) { ab.__used = end; return ab.__view ||= new Uint8Array(ab); }
  const u = mkBytes(cap, end); u.set(ba); return u;
};
export const ByteArray_validateUTF8 = (ba) => { try { DEC_FATAL.decode(ba); return 1; } catch { return 0; } };
export const ByteArray_emptyWithCapacity = (c) => mkBytes(Math.max(16, Number(c)), 0).subarray(0, 0);
export const ByteArray_mk = (arr) => { const u = mkBytes(Math.max(16, arr.length), arr.length); for (let i = 0; i < arr.length; i++) u[i] = Number(arr[i]); return u.subarray(0, arr.length); };
export const ByteArray_data = (ba) => own(Array.from(ba)), ByteArray_size = (ba) => B(ba.length), ByteArray_usize = (ba) => ba.length;
export const ByteArray_get = (ba, i) => ba[Number(i)], ByteArray_getx33 = (ba, i) => ba[Number(i)] ?? 0;
export const ByteArray_decEq = (a, b) => { if (a === b) return 1; if (a.length !== b.length) return 0; for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return 0; return 1; };
export const ByteArray_push = (ba, b) => { const n = ba.length, u = ensureBytes(ba, n + 1, Math.max(16, (n + 1) * 2), true); u[n] = Number(b); return u.subarray(0, n + 1); };
export const ByteArray_copySlice = (src, so, dst, dso, len, exact) => {
  const s = Math.min(Number(so), src.length), d = Number(dso), n = Math.min(Number(len), src.length - s);
  if (n <= 0 && d <= dst.length) return dst;
  const end = Math.max(dst.length, d + n), u = ensureBytes(dst, end, exact ? end : Math.max(16, dst.length * 2, end), d >= dst.length);
  if (n > 0) u.set(src.subarray(s, s + n), d);
  return u.subarray(0, end);
};
const _f64 = new DataView(new ArrayBuffer(8));
export const Float_toBits = (f) => Number.isNaN(f) ? 0x7ff8000000000000n : (_f64.setFloat64(0, f, true), _f64.getBigUint64(0, true));
export const Float_ofBits = (b) => (_f64.setBigUint64(0, B(b) & M64, true), _f64.getFloat64(0, true));

// ST Refs, IO Streams & Panic
export const ST_Prim_mkRef = (a, _w) => ({ v: a }), ST_Prim_Ref_get = (r, _w) => r.v, ST_Prim_Ref_set = (r, a, _w) => (r.v = a, PUnit), ST_Prim_Ref_swap = (r, a, _w) => { const prev = r.v; r.v = a; return prev; };
const mkStream = (log) => {
  const w = (s) => { const t = String(s).replace(/\n$/, ''); if (t) log(t); };
  return { t: 0, s: {}, u: {}, f: [pap(() => mkOk(PUnit), 1, []), pap(() => mkOk(new Uint8Array(0)), 2, []),
    pap((ba) => (w(DEC.decode(ba)), mkOk(PUnit)), 2, []), pap(() => mkOk(''), 1, []), pap((s) => (w(s), mkOk(PUnit)), 2, []), pap(() => 0, 1, [])] };
};
export const IO_getStdout = (_w) => mkStream((t) => console.log(t)), IO_getStderr = (_w) => mkStream((t) => console.error(t));
export function panicCore(msg) { throw new Error('Lean panic: ' + (typeof msg === 'string' ? msg : '')); }

// DOM backend bridge & aliases
let DOM = null;
export function registerDom(backend) { DOM = backend; }
const d = (k) => (...a) => { if (!DOM || typeof DOM[k] !== 'function') throw new Error('DOM extern called with no backend: ' + k); return DOM[k](...a); };
export const
  Qed_Dom_appRoot = d('appRoot'), Qed_Dom_appState = d('appState'), Qed_Dom_appendChild = d('appendChild'), Qed_Dom_bindSignal = d('bindSignal'), Qed_Dom_bindSignalAttr = d('bindSignalAttr'),
  Qed_Dom_getSigSlot = d('getSigSlot'), Qed_Dom_setSigSlot = d('setSigSlot'), Qed_Dom_compileRowTmpl = d('compileRowTmpl'), Qed_Dom_mountTmplRow = d('mountTmplRow'), Qed_Dom_mountTmplRows = d('mountTmplRows'),
  Qed_Dom_patchTmplRow = d('patchTmplRow'), Qed_Dom_hydrateTmplRow = d('hydrateTmplRow'), Qed_Dom_childAt = d('childAt'), Qed_Dom_childCount = d('childCount'), Qed_Dom_childNamespace = d('childNamespace'),
  Qed_Dom_clearHandlers = d('clearHandlers'), Qed_Dom_createElement = d('createElement'), Qed_Dom_createFragment = d('createFragment'), Qed_Dom_createText = d('createText'), Qed_Dom_currentPath = d('currentPath'),
  Qed_Dom_effect = d('effect'), Qed_Dom_effectResult = d('effectResult'), Qed_Dom_fetchStream = d('fetchStream'), Qed_Dom_getAttribute = d('getAttribute'), Qed_Dom_httpSend = d('httpSend'),
  Qed_Dom_httpSendBytes = d('httpSendBytes'), Qed_Dom_insertBefore = d('insertBefore'), Qed_Dom_insertBeforeRef = d('insertBeforeRef'), Qed_Dom_removeNode = d('removeNode'), Qed_Dom_clearChildren = d('clearChildren'),
  Qed_Dom_isConnected = d('isConnected'), Qed_Dom_mountRoot = d('mountRoot'), Qed_Dom_portSend = d('portSend'), Qed_Dom_pushPath = d('pushPath'), Qed_Dom_removeAttribute = d('removeAttribute'),
  Qed_Dom_removeChild = d('removeChild'), Qed_Dom_replaceChild = d('replaceChild'), Qed_Dom_setAttribute = d('setAttribute'), Qed_Dom_setChecked = d('setChecked'), Qed_Dom_retainAttributes = d('retainAttributes'),
  Qed_Dom_setText = d('setText'), Qed_Dom_setValue = d('setValue'), Qed_Dom_today = d('today'), Qed_Dom_wsOpen = d('wsOpen'), Qed_Dom_wsSendBytes = d('wsSendBytes'),
  Qed_Dom_wsSendText = d('wsSendText'), Qed_Dom_wsClose = d('wsClose');
export function assertExterns(required, ns) {
  const missing = required.filter((n) => typeof ns[n] !== 'function' && !(n in ns));
  if (missing.length) throw new Error('qed_rt: missing externs: ' + missing.join(', '));
}
export {
  biAdd as Int_add, biMul as Int_mul, biEq as Int_decEq, biLe as Int_decLe, biLt as Int_decLt, biAdd as Nat_add, biMul as Nat_mul, biEq as Nat_decEq, biLe as Nat_decLe, biLt as Nat_decLt, biLe as Nat_ble,
  u8 as UInt8_ofNat, u8 as UInt8_ofNatLT, nToNat as UInt8_toNat, mask8 as UInt8_toUInt16, nEq as UInt8_decEq, nLe as UInt8_decLe, nLt as UInt8_decLt, mask8 as UInt16_toUInt8,
  u32ToNat as UInt32_toNat, u32ToNat as UInt32_toUInt64, mask8 as UInt32_toUInt8, nEq as UInt32_decEq, nLe as UInt32_decLe, nLt as UInt32_decLt, u64 as UInt64_ofNat, u64 as UInt64_ofBitVec,
  u64 as UInt64_toNat, uSize as USize_ofNat, uSize as USize_ofNatLT, nToNat as USize_toNat, nEq as USize_decEq, nLt as USize_decLt, Array_mkEmpty as Array_emptyWithCapacity, arrayToList as Array_toList,
  Array_getInternalBorrowed as Array_ugetBorrowed, Array_set as Array_setx33, String_append as String_Internal_append, String_mk as String_ofList, String_data as String_toList,
  String_get as String_decodeChar, String_get as String_Pos_Raw_get, String_next as String_Pos_Raw_next, String_next as String_Pos_next, String_atEnd as String_Pos_Raw_atEnd,
  Array_markLinear as ByteArray_markLinear, Array_markLinear as String_markLinear, Array_markLinear as FloatArray_markLinear,
  Array_propagateMark as ByteArray_propagateMark, Array_propagateMark as String_propagateMark, Array_propagateMark as FloatArray_propagateMark,
  String_extract as String_Pos_Raw_extract, String_toUTF8 as String_toByteArray, ByteArray_get as ByteArray_uget, ByteArray_decEq as ByteArray_beq, ST_Prim_Ref_get as ST_Prim_Ref_take, ST_Prim_Ref_set as ST_Prim_Ref_put,
};
