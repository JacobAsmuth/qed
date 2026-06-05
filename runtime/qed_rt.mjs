// qed_rt.mjs — the hand-written runtime for Lean-IR-transpiled JavaScript.
//
// Mirrors the slice of `libleanrt` the Qed framework touches. Representation:
//   Int/Nat → BigInt   UInt8/16/32, USize, Bool/enum tags → Number   UInt64 → BigInt
//   String  → JS string (Pos = UTF-8 byte offset)   Array → JS Array   ByteArray → Uint8Array
//   nullary ctor → its tag (Number)   ctor w/ fields → {t, f:[…], s:{}, u:{}}
//   closure → {fn, arity, args}   IO world token → 0   PUnit/Unit → 0
//   IO action result → EStateM.Result.ok(v, world) = {t:0, f:[v, world], …}
//
// Anything an app needs that is absent here makes `assertExterns` throw at boot.

// ---- core: tags, closures, ctors, IO ----------------------------------------
export const tag = (o) => (typeof o === 'object' && o !== null) ? o.t : o;
export const ctor = (t, ...f) => ({ t, f, s: {}, u: {} });
export const box = (v) => v, unbox = (v) => v;

export function pap(fn, arity, args) { return { fn, arity, args }; }
export function app(clo, extra) {
  let args = clo.args.length ? clo.args.concat(extra) : extra;
  if (args.length < clo.arity) return { fn: clo.fn, arity: clo.arity, args };
  if (args.length === clo.arity) return clo.fn(...args);
  const head = clo.fn(...args.slice(0, clo.arity));
  return app(head, args.slice(clo.arity));   // over-application: result is itself a closure
}

const W = 0;                                  // the IO world token
export const PUnit = 0, Unit = 0;
export const ioVal = (r) => r.f[0];           // value out of an EStateM.Result.ok(v, w)
export const tc = (a) => ({ __tc: a });        // tail-self-call marker (trampoline; see Js.Backend)
// A module global: computed once, then SHARED by every reference — so it is persistent. Freeze
// any array it yields (refcount → ∞) so a mutator always copies it instead of mutating the one
// shared instance in place (mirrors Lean marking top-level constants persistent). `inc`/`dec`
// leave ∞ unchanged, so it stays frozen for the program's life.
export function memo(f) { let v, done = false; return () => { if (!done) { v = f(); done = true; if (v !== null && typeof v === 'object' && v.r !== undefined) v.r = Infinity; } return v; }; }
// v4.30 erased the IO RealWorld token: an IO result is a single-field `EST.Out` carrying just
// the value/error (no world). The monad wraps `pure`/return in `EST.Out.ok`; a fallible IO
// extern returns one of these, a BaseIO extern returns its value directly (see ST.Prim below).
export const mkOk  = (v) => ({ t: 0, f: [v], s: {}, u: {} });   // EST.Out.ok
export const mkErr = (e) => ({ t: 1, f: [e], s: {}, u: {} });   // EST.Out.error

// ---- Int (BigInt) -----------------------------------------------------------
export const Int_add = (a, b) => a + b;
export const Int_sub = (a, b) => a - b;
export const Int_mul = (a, b) => a * b;
export const Int_neg = (a) => -a;
export const Int_ofNat = (n) => n;
export const Int_natAbs = (a) => a < 0n ? -a : a;
const iabs = (b) => b < 0n ? -b : b;
export const Int_emod = (a, b) => { if (b === 0n) return a; let r = a % b; return r < 0n ? r + iabs(b) : r; };
export const Int_ediv = (a, b) => { if (b === 0n) return 0n; return (a - Int_emod(a, b)) / b; };
export const Int_decEq = (a, b) => a === b ? 1 : 0;
export const Int_decLe = (a, b) => a <= b ? 1 : 0;
export const Int_decLt = (a, b) => a < b ? 1 : 0;

// ---- Nat (BigInt, ≥ 0) ------------------------------------------------------
export const Nat_add = (a, b) => a + b;
export const Nat_sub = (a, b) => a > b ? a - b : 0n;
export const Nat_mul = (a, b) => a * b;
export const Nat_div = (a, b) => b === 0n ? 0n : a / b;
export const Nat_mod = (a, b) => b === 0n ? a : a % b;
export const Nat_pow = (a, b) => a ** b;
export const Nat_decEq = (a, b) => a === b ? 1 : 0;
export const Nat_decLe = (a, b) => a <= b ? 1 : 0;
export const Nat_decLt = (a, b) => a < b ? 1 : 0;
export const Nat_land = (a, b) => a & b;
export const Nat_lor  = (a, b) => a | b;

// ---- fixed-width integers ---------------------------------------------------
const M32 = 0xFFFFFFFF, M64 = (1n << 64n) - 1n;
export const UInt8_ofNat = (n) => Number(n & 0xFFn);
export const UInt8_toNat = (a) => BigInt(a);
export const UInt8_land = (a, b) => a & b;
export const UInt8_lor  = (a, b) => a | b;
export const UInt8_shiftLeft  = (a, b) => (a << b) & 0xFF;
export const UInt8_shiftRight = (a, b) => a >> b;
export const UInt32_mk = (n) => Number(n) >>> 0;
export const UInt32_ofNat = (n) => Number(n & 0xFFFFFFFFn);
export const UInt32_ofNatCore = (n) => Number(n & 0xFFFFFFFFn);
export const UInt32_toNat = (a) => BigInt(a >>> 0);
export const UInt32_add = (a, b) => (a + b) >>> 0;
export const UInt32_decEq = (a, b) => a === b ? 1 : 0;
export const UInt32_decLe = (a, b) => a <= b ? 1 : 0;
export const UInt64_ofNat = (n) => BigInt(n) & M64;
export const UInt64_toNat = (a) => BigInt(a) & M64;
export const UInt64_xor = (a, b) => (BigInt(a) ^ BigInt(b)) & M64;
export const UInt64_shiftRight = (a, b) => (BigInt(a) >> BigInt(b)) & M64;
export const UInt64_toUSize = (a) => Number(BigInt(a) & 0x1FFFFFFFFFFFFFn);
export const USize_ofNat = (n) => Number(n & 0x1FFFFFFFFFFFFFn);
export const USize_ofNatCore = (n) => Number(n & 0x1FFFFFFFFFFFFFn);
export const USize_add = (a, b) => a + b;
export const USize_sub = (a, b) => a - b;
export const USize_land = (a, b) => Number(BigInt(a) & BigInt(b));
export const USize_decEq = (a, b) => a === b ? 1 : 0;
export const USize_decLt = (a, b) => a < b ? 1 : 0;
export const USize_repr = (a) => String(a);
export const System_Platform_getNumBits = () => 64n;

// ---- Char -------------------------------------------------------------------
export const Char_ofNatAux = (n, _h) => Number(n);

// ---- list <-> array helpers (List.nil = 0, List.cons = {t:1,f:[h,t]}) -------
const NIL = 0;
const cons = (h, t) => ({ t: 1, f: [h, t], s: {}, u: {} });
export function listToArray(l) { const a = []; while (typeof l === 'object' && l !== null) { a.push(l.f[0]); l = l.f[1]; } return a; }
export function arrayToList(a) { let l = NIL; for (let i = a.length - 1; i >= 0; i--) l = cons(a[i], l); return l; }

// ---- Refcounting --------------------------------------------------------------
// The GC reclaims memory, but a refcount still lets an array mutator tell a uniquely-owned
// array (mutate in place — O(1)) from a shared one (copy — O(n)) — recovering Lean's in-place
// array updates. Only arrays carry a count (`a.r`); on ctors/closures/scalars `inc`/`dec` are a
// no-op and `isShared` is conservatively `true`. The transpiler emits `inc`/`dec` from the IR's
// RC ops, so a count tracks live references exactly as native Lean does. An UNtagged array (no
// `.r`) is treated as shared — the safe default — so anything that bypasses tagging still copies.
export const inc = (x, n = 1) => { if (x !== null && typeof x === 'object' && x.r !== undefined) x.r += Number(n); };
export const dec = (x, n = 1) => { if (x !== null && typeof x === 'object' && x.r !== undefined) x.r -= Number(n); };
export const isShared = (x) => (x !== null && typeof x === 'object' && x.r !== undefined && x.r <= 1) ? 0 : 1;
const own = (a) => { a.r = 1; return a; };          // a freshly-owned array
const owned = (a) => a.r === 1;                      // uniquely owned ⇒ safe to mutate in place

// A per-object identity stamp (≥ 1), for the driver's O(changed) list update: an unchanged row
// is the SAME object across renders (Lean returns it untouched), so equal marks ⇒ skip it with
// no field read. Objects get a stable lazy stamp; a primitive (a scalar-valued row) gets a fresh
// mark every call so it never matches — a safe fall back to recompute. Mirrors `Qed.refMark`,
// whose pure body is `0` (≠ any real mark), so the native model never skips. Last arg = the value.
let __markCtr = 0;
export const refMark = (...a) => { const o = a[a.length - 1]; return (o !== null && typeof o === 'object') ? (o.__m ?? (o.__m = ++__markCtr)) : ++__markCtr; };

// ---- Array (JS Array + refcount; in place when owned, copy when shared) --------
export const Array_mkEmpty = (_cap) => own([]);
export const Array_mkArray = (n, x) => { const k = Number(n); inc(x, k); return own(new Array(k).fill(x)); };
export const Array_mk = (l) => own(listToArray(l));
export const Array_toList = (a) => arrayToList(a);
export const Array_size = (a) => BigInt(a.length);
export const Array_usize = (a) => a.length;
export const Array_get = (a, i) => { const x = a[Number(i)]; inc(x); return x; };
export const Array_uget = (a, i) => { const x = a[i]; inc(x); return x; };
export const Array_push = (a, x) => owned(a) ? (a.push(x), a) : own([...a, x]);
export const Array_pop = (a) => owned(a) ? (a.pop(), a) : own(a.slice(0, a.length - 1));
export const Array_uset = (a, i, x) => { const b = owned(a) ? a : own(a.slice()); b[i] = x; return b; };
export const Array_swap = (a, i, j) => { const b = owned(a) ? a : own(a.slice()); const t = b[Number(i)]; b[Number(i)] = b[Number(j)]; b[Number(j)] = t; return b; };
export const Array_set = (a, i, x) => { const b = owned(a) ? a : own(a.slice()); b[Number(i)] = x; return b; };
export const Array_setx33 = (a, i, x) => { const b = owned(a) ? a : own(a.slice()); b[Number(i)] = x; return b; };  // set!

// ---- String (JS string; Pos = UTF-8 byte offset) ----------------------------
const ENC = new TextEncoder();
const u8len = (cp) => cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;   // UTF-8 length of a codepoint
export const String_append = (a, b) => a + b;
export const String_length = (s) => { let n = 0n; for (const _ of s) n++; return n; };
export const String_utf8ByteSize = (s) => BigInt(ENC.encode(s).length);
export const String_push = (s, c) => s + String.fromCodePoint(c);
export const String_decEq = (a, b) => a === b ? 1 : 0;
export const String_decLt = (a, b) => {
  const x = [...a], y = [...b];
  for (let i = 0; i < x.length && i < y.length; i++) {
    const cx = x[i].codePointAt(0), cy = y[i].codePointAt(0);
    if (cx !== cy) return cx < cy ? 1 : 0;
  }
  return x.length < y.length ? 1 : 0;
};
// codepoint at byte offset `pos`; returns [codepoint, utf8len, utf16len]
function atByte(s, pos) {
  let b = 0;
  for (const ch of s) {
    const cp = ch.codePointAt(0), l = u8len(cp);
    if (b === pos) return [cp, l, ch.length];
    b += l;
  }
  return [0, 1, 1];   // at/after end: '\0'
}
export const String_get = (s, pos) => atByte(s, Number(pos))[0];
export const String_next = (s, pos) => { const p = Number(pos); return BigInt(p + atByte(s, p)[1]); };
export const String_prev = (s, pos) => {
  const target = Number(pos); let b = 0, prev = 0;
  for (const ch of s) { const l = u8len(ch.codePointAt(0)); if (b >= target) break; prev = b; b += l; }
  return BigInt(prev);
};
export const String_atEnd = (s, pos) => Number(pos) >= ENC.encode(s).length ? 1 : 0;
export const String_extract = (s, b, e) => {
  const bo = Number(b), eo = Number(e); let out = '', off = 0;
  for (const ch of s) { const l = u8len(ch.codePointAt(0)); if (off >= eo) break; if (off >= bo) out += ch; off += l; }
  return out;
};
export const String_mk = (l) => { let s = ''; for (const c of listToArray(l)) s += String.fromCodePoint(c); return s; };
export const String_data = (s) => arrayToList([...s].map((ch) => ch.codePointAt(0)));
export const String_hash = (s) => { let h = 1469598103934665603n; for (let i = 0; i < s.length; i++) { h ^= BigInt(s.charCodeAt(i)); h = (h * 1099511628211n) & M64; } return h; };
export const String_toUTF8 = (s) => ENC.encode(s);
export const String_fromUTF8 = (ba, _h) => new TextDecoder().decode(ba);
export const String_validateUTF8 = (_ba) => 1;

// ---- ByteArray (Uint8Array; copy-on-write) ----------------------------------
export const ByteArray_mkEmpty = (_c) => new Uint8Array(0);
export const ByteArray_push = (ba, b) => { const r = new Uint8Array(ba.length + 1); r.set(ba); r[ba.length] = Number(b); return r; };
export const ByteArray_size = (ba) => BigInt(ba.length);
export const ByteArray_getx33 = (ba, i) => ba[Number(i)];   // get! → UInt8 (a Number)
export const ByteArray_copySlice = (src, so, dst, dso, len, _ex) => {
  // copySlice may grow the destination (it backs `ByteArray.append`), and a Uint8Array
  // is fixed-length, so allocate one large enough rather than writing past `dst`.
  const s = Number(so), d = Number(dso), n = Number(len);
  const r = new Uint8Array(Math.max(dst.length, d + n));
  r.set(dst);
  for (let i = 0; i < n; i++) r[d + i] = src[s + i];
  return r;
};

// ---- v4.30 stdlib externs (renames + the new String.Pos.Raw / UTF-8 byte API) ----
// Lean 4.30 backs `String` with a UTF-8 `ByteArray` and routes string ops through
// `String.Pos.Raw` (a byte offset). Our representation is unchanged (JS string, Pos = byte
// offset), so these reuse the same byte-offset helpers as the pre-4.30 `String.*` externs.
// (Erased proof args are stripped by the transpiler, so each arrives without them.)
export const Array_emptyWithCapacity = Array_mkEmpty;            // was Array.mkEmpty
export const Array_replicate = Array_mkArray;                    // was Array.mkArray
export const Array_getInternal = Array_get;                      // bounds proof erased
export const Array_getInternalBorrowed = (a, i) => a[Number(i)]; // borrowed: no inc
export const Array_ugetBorrowed = (a, i) => a[Number(i)];        // borrowed: no inc
// `Array.get!Internal : [Inhabited α] → Array α → Nat → α` — the instance is a real runtime arg.
export const Array_getx33Internal = (_inst, a, i) => { const x = a[Number(i)]; inc(x); return x; };
export const Array_getx33InternalBorrowed = (_inst, a, i) => a[Number(i)];
export const Nat_ble = (a, b) => a <= b ? 1 : 0;
export const String_decidableLT = String_decLt;                  // was String.decLt
export const Nat_shiftRight = (a, b) => a >> b;
export const UInt8_decEq = (a, b) => a === b ? 1 : 0;
export const UInt32_ofBitVec = (bv) => Number(BigInt(bv) & 0xFFFFFFFFn);
export const USize_ofNatLT = (n) => Number(n & 0x1FFFFFFFFFFFFFn);
export const String_ofList = String_mk;                          // was String.mk
export const String_toList = String_data;                        // was String.data
export const String_ofByteArray = (ba) => new TextDecoder().decode(ba);
export const String_Internal_append = (a, b) => a + b;
export const String_Pos_Raw_get = String_get;
export const String_Pos_Raw_next = String_next;
export const String_Pos_Raw_atEnd = String_atEnd;
export const String_Pos_Raw_extract = String_extract;
export const String_Pos_next = String_next;
export const String_decodeChar = (s, i) => atByte(s, Number(i))[0];
export const String_getUTF8Byte = (s, p) => ENC.encode(s)[Number(p)];
export const ByteArray_emptyWithCapacity = (_c) => new Uint8Array(0);
export const ByteArray_validateUTF8 = (ba) => { try { new TextDecoder('utf-8', { fatal: true }).decode(ba); return 1; } catch { return 0; } };

// ---- mutable refs + IO plumbing (EStateM.Result.ok protocol) ----------------
// BaseIO externs return their VALUE directly (the world is erased; no `EST.Out` wrapper).
export const ST_Prim_mkRef   = (a, _w) => ({ v: a });            // BaseIO (IO.Ref α) → the ref
export const ST_Prim_Ref_get = (r, _w) => r.v;                   // BaseIO α → the value
export const ST_Prim_Ref_set = (r, a, _w) => { r.v = a; return PUnit; };
export const ST_Prim_Ref_take = (r, _w) => r.v;
// stdout/stderr as an IO.FS.Stream {flush, read, write, getLine, putStr, isTty} (field order
// per `IO.FS.Stream`); each method is a pap'd closure taking its args + the erased world and
// returning an `EST.Out.ok` (isTty is BaseIO Bool → returns the bool directly).
const mkStream = (writeFn) => ctor(0,
  pap((_w) => mkOk(PUnit), 1, []),
  pap((_n, _w) => mkOk(new Uint8Array(0)), 2, []),
  pap((ba, _w) => (writeFn(new TextDecoder().decode(ba)), mkOk(PUnit)), 2, []),
  pap((_w) => mkOk(''), 1, []),
  pap((s, _w) => (writeFn(s), mkOk(PUnit)), 2, []),
  pap((_w) => 0, 1, []));
export const IO_getStdout = (_w) => mkStream((s) => { const t = String(s).replace(/\n$/, ''); if (t) console.log(t); });
export const IO_getStderr = (_w) => mkStream((s) => { const t = String(s).replace(/\n$/, ''); if (t) console.error(t); });
export function panicCore(msg) { throw new Error('Lean panic: ' + (typeof msg === 'string' ? msg : '')); }

// ---- DOM externs: delegate to a host-registered backend ---------------------
let DOM = null;
export function registerDom(backend) { DOM = backend; }
const domCall = (name) => (...args) => {
  if (!DOM || typeof DOM[name] !== 'function') throw new Error('DOM extern called with no backend: ' + name);
  return DOM[name](...args);
};
export const Qed_Dom_appRoot = domCall('appRoot');
export const Qed_Dom_appState = domCall('appState');
export const Qed_Dom_appendChild = domCall('appendChild');
export const Qed_Dom_bindSignal = domCall('bindSignal');
export const Qed_Dom_bindSignalAttr = domCall('bindSignalAttr');
export const Qed_Dom_childAt = domCall('childAt');
export const Qed_Dom_childCount = domCall('childCount');
export const Qed_Dom_childNamespace = domCall('childNamespace');
export const Qed_Dom_clearHandlers = domCall('clearHandlers');
export const Qed_Dom_createElement = domCall('createElement');
export const Qed_Dom_createText = domCall('createText');
export const Qed_Dom_currentPath = domCall('currentPath');
export const Qed_Dom_effect = domCall('effect');
export const Qed_Dom_effectResult = domCall('effectResult');
export const Qed_Dom_fetchStream = domCall('fetchStream');
export const Qed_Dom_getAttribute = domCall('getAttribute');
export const Qed_Dom_httpSend = domCall('httpSend');
export const Qed_Dom_insertBefore = domCall('insertBefore');
export const Qed_Dom_isConnected = domCall('isConnected');
export const Qed_Dom_mountRoot = domCall('mountRoot');
export const Qed_Dom_portSend = domCall('portSend');
export const Qed_Dom_pushPath = domCall('pushPath');
export const Qed_Dom_removeAttribute = domCall('removeAttribute');
export const Qed_Dom_removeChild = domCall('removeChild');
export const Qed_Dom_replaceChild = domCall('replaceChild');
export const Qed_Dom_setAttribute = domCall('setAttribute');
export const Qed_Dom_setChecked = domCall('setChecked');
export const Qed_Dom_setText = domCall('setText');
export const Qed_Dom_setValue = domCall('setValue');
export const Qed_Dom_today = domCall('today');

// ---- boot check -------------------------------------------------------------
// Pass the transpiled module's `__externs` and its imported runtime namespace.
export function assertExterns(required, ns) {
  const missing = required.filter((n) => typeof ns[n] !== 'function' && !(n in ns));
  if (missing.length) throw new Error('qed_rt: missing externs: ' + missing.join(', '));
}
