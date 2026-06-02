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
export function memo(f) { let v, done = false; return () => { if (!done) { v = f(); done = true; } return v; }; } // a module global: computed once, shared
export const mkOk  = (v, w = W) => ({ t: 0, f: [v, w], s: {}, u: {} });   // EStateM.Result.ok
export const mkErr = (e, w = W) => ({ t: 1, f: [e, w], s: {}, u: {} });   // EStateM.Result.error

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

// ---- Array (JS Array; copy-on-write for safety) -----------------------------
export const Array_mkEmpty = (_cap) => [];
export const Array_mkArray = (n, x) => new Array(Number(n)).fill(x);
export const Array_mk = (l) => listToArray(l);
export const Array_toList = (a) => arrayToList(a);
export const Array_size = (a) => BigInt(a.length);
export const Array_usize = (a) => a.length;
export const Array_get = (a, i) => a[Number(i)];
export const Array_uget = (a, i) => a[i];
export const Array_push = (a, x) => { const b = a.slice(); b.push(x); return b; };
export const Array_pop = (a) => a.slice(0, a.length - 1);
export const Array_set = (a, i, x) => { const b = a.slice(); b[Number(i)] = x; return b; };
export const Array_setx33 = (a, i, x) => { const b = a.slice(); b[Number(i)] = x; return b; };  // set!
export const Array_uset = (a, i, x) => { const b = a.slice(); b[i] = x; return b; };
export const Array_swap = (a, i, j) => { const b = a.slice(); const t = b[Number(i)]; b[Number(i)] = b[Number(j)]; b[Number(j)] = t; return b; };

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
export const ByteArray_getx33 = (ba, i) => BigInt(ba[Number(i)]);   // get!
export const ByteArray_copySlice = (src, so, dst, dso, len, _ex) => {
  const r = dst.slice(); const s = Number(so), d = Number(dso), n = Number(len);
  for (let i = 0; i < n; i++) r[d + i] = src[s + i]; return r;
};

// ---- mutable refs + IO plumbing (EStateM.Result.ok protocol) ----------------
export const ST_Prim_mkRef = (a, w) => mkOk({ v: a }, w);
export const ST_Prim_Ref_get = (r, w) => mkOk(r.v, w);
export const ST_Prim_Ref_set = (r, a, w) => { r.v = a; return mkOk(PUnit, w); };
export const ST_Prim_Ref_take = (r, w) => mkOk(r.v, w);
export const IO_getStderr = (w) => mkOk({ stderr: true }, w);
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
