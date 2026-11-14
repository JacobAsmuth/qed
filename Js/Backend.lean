-- Runtime representation (matches `qed_rt.mjs`; recheck on Lean bumps, see `docs/upgrading-lean.md`):
-- Int/Nat/UInt64 → BigInt; UInt8/16/32/USize/Bool/nullary-ctor → Number; String → JS string (UTF-8 byte Pos);
-- Array → JS Array with refcount `.r`; ctor w/ fields → `{t, f, s, u}`; closure → `{fn, arity, args}`;
-- BaseIO returns raw values, EIO/IO wraps in single-field `EST.Out` (`{t:0|1, f:[v]}`).
import Lean
open Lean IR

namespace Js

def mangle (n : Name) : String := Id.run do
  let mut s := ""
  for c in n.toString.toList do
    if c.isAlphanum then s := s.push c
    else if c == '.' || c == '_' then s := s.push '_'
    else s := s ++ s!"x{c.toNat}"
  return s

partial def callees : FnBody → Array Name → Array Name
  | b, acc =>
    match b with
    | .vdecl _ _ e b' =>
      let acc := match e with | .fap c _ => acc.push c | .pap c _ => acc.push c | _ => acc
      callees b' acc
    | .jdecl _ _ v b' => callees b' (callees v acc)
    | .case _ _ _ alts => alts.foldl (fun acc alt => callees alt.body acc) acc
    | _ => if b.isTerminal then acc else callees b.body acc

partial def reach (env : Environment) : List Name → Array Name → Array Name
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.push n
      match findEnvDecl env n with
      | some (.fdecl (body := b) ..) =>
          let extra := (callees b #[]).toList ++ (getInitFnNameFor? env n).toList
          reach env (rest ++ extra) seen
      | _ => reach env rest seen

structure Ctx where
  env        : Environment
  names      : Std.HashMap Name String
  externs    : Std.HashMap Name Decl
  min        : Bool := false
  selfFn     : Option Name := none
  selfParams : Array Param := #[]
  directLoop : Bool := false
  nonArr     : Std.HashSet Nat := {}
  projSrc    : Std.HashMap Nat Nat := {}
  inlineJps  : Std.HashMap Nat (Array Param) := {}

def Ctx.js (c : Ctx) (n : Name) : String :=
  match c.names.get? n with
  | some s => s
  | none   => "$." ++ mangle n

def Ctx.ind (c : Ctx) (d : Nat) : String := if c.min then "" else String.ofList (List.replicate (2 * d) ' ')

def v (x : VarId) : String := s!"x{x.idx}"
def jp (j : JoinPointId) : String := s!"j{j.idx}"

def emitArg : Arg → String
  | .var x  => v x
  | .erased => "0"

def ctorVal (i : CtorInfo) (ys : Array Arg) : String :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then toString i.cidx
  else
    let fs := String.intercalate ", " (ys.toList.map emitArg)
    let s := if i.ssize == 0 then "" else ", s: {}"
    let u := if i.usize == 0 then "" else ", u: {}"
    s!"\{t: {i.cidx}, f: [{fs}]{s}{u}}"

def soff (n offset : Nat) : String := s!"\"{n}_{offset}\""

def jsStr (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r"
      | '\t' => "\\t"
      | c =>
        if c.toNat < 32 then
          let h := Nat.toDigits 16 c.toNat
          "\\x" ++ String.ofList (if h.length == 1 then '0' :: h else h)
        else String.singleton c)
  "\"" ++ escaped ++ "\""

def emitApp (c : Ctx) (f : Name) (ys : Array Arg) : String :=
  -- `Qed.refMark`'s pure Lean body is conservative `0`; substitute the runtime identity stamp here.
  if f == `Qed.refMark then
    s!"$.refMark({String.intercalate ", " (ys.toList.filterMap fun | .var x => some (v x) | .erased => none)})"
  else
  let argStrs : List String :=
    match findEnvDecl c.env f with
    | some (.extern (xs := ps) ..) =>
        ys.toList.zipIdx.filterMap fun (a, i) =>
          if i < ps.size && ps[i]!.ty.isErased then none else some (emitArg a)
    | _ => ys.toList.map emitArg
  s!"{c.js f}({String.intercalate ", " argStrs})"

def emitExpr (c : Ctx) (ty : IRType) : IR.Expr → String
  | .ctor i ys      => ctorVal i ys
  | .reset ..       => "0"
  | .reuse _ i _ ys => ctorVal i ys
  | .proj i x       => s!"{v x}.f[{i}]"
  | .uproj i x      => s!"{v x}.u[{i}]"
  | .sproj n off x  => s!"{v x}.s[{soff n off}]"
  | .fap f ys       => emitApp c f ys
  | .pap f ys       =>
      let arity := (findEnvDecl c.env f).map (·.params.size) |>.getD ys.size
      s!"$.pap({c.js f}, {arity}, [{String.intercalate ", " (ys.toList.map emitArg)}])"
  | .ap x ys        => s!"$.app({v x}, [{String.intercalate ", " (ys.toList.map emitArg)}])"
  | .box _ x        => v x
  | .unbox x        => v x
  | .lit (.num n)   => if ty.isObj || ty == .uint64 then s!"{n}n" else s!"{n}"
  | .lit (.str s)   => jsStr s
  | .isShared x     => s!"$.isShared({v x})"

partial def skipRC : FnBody → FnBody
  | .inc _ _ _ _ b => skipRC b
  | .dec _ _ _ _ b => skipRC b
  | .del _ b       => skipRC b
  | b              => b

def retsVar (z : VarId) (cont : FnBody) : Bool :=
  match skipRC cont with
  | .ret (.var w) => w == z
  | _             => false

partial def hasSelfTail (self : Name) : FnBody → Bool
  | .vdecl z _ (.fap f _) cont => (f == self && retsVar z cont) || hasSelfTail self cont
  | .vdecl _ _ _ b    => hasSelfTail self b
  | .jdecl _ _ v b    => hasSelfTail self v || hasSelfTail self b
  | .case _ _ _ alts  => alts.any (fun a => hasSelfTail self a.body)
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b => hasSelfTail self b
  | .sset _ _ _ _ _ b => hasSelfTail self b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasSelfTail self b
  | _ => false

partial def hasJmpTo (target : JoinPointId) : FnBody → Bool
  | .jmp j _          => j == target
  | .vdecl _ _ _ b | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b
  | .sset _ _ _ _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasJmpTo target b
  | .jdecl _ _ v b    => hasJmpTo target v || hasJmpTo target b
  | .case _ _ _ alts  => alts.any (fun a => hasJmpTo target a.body)
  | .ret _ | .unreachable => false

-- Non-recursive join points lower to labeled blocks (`jN: { ... }`), so `continue` inside them
-- still targets the enclosing `while (true)` loop; only recursive closure join points need `$.tc`.
partial def hasJpSelfTail (self : Name) (inClosureJp : Bool := false) : FnBody → Bool
  | .vdecl z _ (.fap f _) cont => (inClosureJp && f == self && retsVar z cont) || hasJpSelfTail self inClosureJp cont
  | .vdecl _ _ _ b    => hasJpSelfTail self inClosureJp b
  | .jdecl j _ v b    =>
      let recJp := hasJmpTo j v
      hasJpSelfTail self (inClosureJp || recJp) v || hasJpSelfTail self inClosureJp b
  | .case _ _ _ alts  => alts.any (fun a => hasJpSelfTail self inClosureJp a.body)
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b => hasJpSelfTail self inClosureJp b
  | .sset _ _ _ _ _ b => hasJpSelfTail self inClosureJp b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasJpSelfTail self inClosureJp b
  | _ => false

partial def collectNonArr (acc : Std.HashSet Nat) : FnBody → Std.HashSet Nat
  | .vdecl x _ e b =>
      let acc := match e with
        | .ctor .. | .reuse .. | .pap .. | .lit .. | .box .. | .unbox .. | .isShared .. => acc.insert x.idx
        | .proj _ p | .uproj _ p | .sproj _ _ p => acc.insert p.idx
        | _ => acc
      collectNonArr acc b
  | .jdecl _ _ v b => collectNonArr (collectNonArr acc v) b
  | .case _ x _ alts => alts.foldl (fun acc alt => collectNonArr acc alt.body) (acc.insert x.idx)
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => collectNonArr acc b
  | _ => acc

partial def hasDecOf (p : Nat) : FnBody → Bool
  | .dec y _ _ _ b => p == y.idx || hasDecOf p b
  | .del y b       => p == y.idx || hasDecOf p b
  | .inc _ _ _ _ b => hasDecOf p b
  | .vdecl _ _ (.proj ..) b | .vdecl _ _ (.uproj ..) b | .vdecl _ _ (.sproj ..) b => hasDecOf p b
  | _              => false

partial def collectProjSrc (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) : FnBody → Std.HashMap Nat Nat
  | .vdecl x _ (.fap ..) b | .vdecl x _ (.ap ..) b => collectProjSrc (calls.insert x.idx) acc b
  | .vdecl x _ (.proj _ p) b =>
      collectProjSrc calls (if calls.contains p.idx then acc.insert x.idx p.idx else acc) b
  | .vdecl _ _ _ b => collectProjSrc calls acc b
  | .jdecl _ _ v b => collectProjSrc calls (collectProjSrc calls acc v) b
  | .case _ _ _ alts => alts.foldl (fun acc alt => collectProjSrc calls acc alt.body) acc
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => collectProjSrc calls acc b
  | _ => acc

partial def emitBody (c : Ctx) (d : Nat) : FnBody → String
  | .vdecl x ty e b   =>
      match e with
      | .fap f args =>
          if c.selfFn == some f && retsVar x b then
            if c.directLoop then
              if args.isEmpty then s!"{c.ind d}continue;\n"
              else
                let ps := c.selfParams.toList.map (v ·.x)
                let as := args.toList.map emitArg
                let tmps := String.intercalate ", " (as.zipIdx.map fun (a, i) => s!"_t{i} = {a}")
                let assigns := String.intercalate " " (ps.zipIdx.map fun (p, i) => s!"{p} = _t{i};")
                s!"{c.ind d}\{ let {tmps}; {assigns} continue; }\n"
            else
              s!"{c.ind d}return $.tc([{String.intercalate ", " (args.toList.map emitArg)}]);\n"
          else s!"{c.ind d}let {v x} = {emitExpr c ty e};\n" ++ emitBody c d b
      | _ => s!"{c.ind d}let {v x} = {emitExpr c ty e};\n" ++ emitBody c d b
  | .jdecl j xs val b =>
      if !hasJmpTo j val then
        let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
        let decls := if xs.isEmpty then ""
          else s!"{c.ind d}let {String.intercalate ", " (xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}")};\n"
        let binds := if xs.isEmpty then ""
          else s!"{c.ind d}let {String.intercalate ", " (xs.toList.zipIdx.map fun (p, i) => s!"{v p.x} = _{jp j}_{i}")};\n"
        decls ++ s!"{c.ind d}{jp j}: \{\n" ++ emitBody c' (d+1) b ++ s!"{c.ind d}}\n" ++ binds ++ emitBody c d val
      else
        let ps := String.intercalate ", " (xs.toList.map (v ·.x))
        s!"{c.ind d}const {jp j} = ({ps}) => " ++ "{\n" ++ emitBody c (d+1) val ++ s!"{c.ind d}" ++ "};\n"
          ++ emitBody c d b
  | .set x i y b      => s!"{c.ind d}{v x}.f[{i}] = {emitArg y};\n" ++ emitBody c d b
  | .setTag x cidx b  => s!"{c.ind d}{v x}.t = {cidx};\n" ++ emitBody c d b
  | .uset x i y b     => s!"{c.ind d}{v x}.u[{i}] = {v y};\n" ++ emitBody c d b
  | .sset x n off y _ b => s!"{c.ind d}{v x}.s[{soff n off}] = {v y};\n" ++ emitBody c d b
  -- Only `Array`s carry `.r`. When `x = p.f[i]` is `inc`ed right before `p` is dropped (`hasDecOf`),
  -- 1 reference transfers from `p` to `x` (`n - 1`) since constructor `dec` does not cascade in JS.
  | .inc x n _ _ b    =>
      let n' := match c.projSrc.get? x.idx with
        | some p => if hasDecOf p b then n - 1 else n
        | none   => n
      (if n' == 0 || c.nonArr.contains x.idx then "" else s!"{c.ind d}$.inc({v x}, {n'});\n") ++ emitBody c d b
  | .dec x n _ _ b    => (if c.nonArr.contains x.idx then "" else s!"{c.ind d}$.dec({v x}, {n});\n") ++ emitBody c d b
  | .del x b          => (if c.nonArr.contains x.idx then "" else s!"{c.ind d}$.dec({v x}, 1);\n") ++ emitBody c d b
  | .ret a            => s!"{c.ind d}return {emitArg a};\n"
  | .jmp j ys         =>
      match c.inlineJps.get? j.idx with
      | some _ =>
          let assigns := String.intercalate " " (ys.toList.zipIdx.map fun (a, i) => s!"_{jp j}_{i} = {emitArg a};")
          let pfx := if assigns.isEmpty then "" else assigns ++ " "
          s!"{c.ind d}{pfx}break {jp j};\n"
      | none =>
          s!"{c.ind d}return {jp j}({String.intercalate ", " (ys.toList.map emitArg)});\n"
  | .unreachable      => s!"{c.ind d}throw new Error('unreachable');\n"
  | .case _ x xType alts =>
      let scrut := if xType.isObj then s!"$.tag({v x})" else v x
      let arms := alts.toList.map fun alt =>
        match alt with
        | .ctor info b => s!"{c.ind (d+1)}case {info.cidx}: " ++ "{\n" ++ emitBody c (d+2) b ++ s!"{c.ind (d+1)}" ++ "}\n"
        | .default b   => s!"{c.ind (d+1)}default: " ++ "{\n" ++ emitBody c (d+2) b ++ s!"{c.ind (d+1)}" ++ "}\n"
      s!"{c.ind d}switch ({scrut}) " ++ "{\n" ++ String.join arms ++ s!"{c.ind d}" ++ "}\n"

def emitDecl (c0 : Ctx) : Decl → String
  | .fdecl f xs _ body _ =>
      let c := { c0 with nonArr := collectNonArr {} body, projSrc := collectProjSrc {} {} body }
      if xs.isEmpty then
        match getInitFnNameFor? c.env f with
        | some initFn =>
            s!"const {c.js f} = $.memo(() => $.ioVal({c.js initFn}(0)));\n"
        | none =>
            s!"const {c.js f} = $.memo(() => " ++ "{\n" ++ emitBody c 1 body ++ "});\n"
      else
        let ps := String.intercalate ", " (xs.toList.map (v ·.x))
        let note := if c.min then "" else s!"/* {f} */ "
        if hasSelfTail f body then
          if !hasJpSelfTail f false body then
            let c' := { c with selfFn := some f, selfParams := xs, directLoop := true }
            let bodyStr := emitBody c' 2 body
            s!"function {c.js f}({ps}) " ++ note ++ "{\n" ++
              s!"{c.ind 1}while (true) " ++ "{\n" ++ bodyStr ++ s!"{c.ind 1}" ++ "}\n}\n"
          else
            let c' := { c with selfFn := some f, selfParams := xs }
            let bodyStr := emitBody c' 2 body
            let reasn := s!"[{String.intercalate ", " (xs.toList.map (v ·.x))}] = __r.__tc;"
            s!"function {c.js f}({ps}) " ++ note ++ "{\n" ++
              s!"{c.ind 1}const __step = () => " ++ "{\n" ++ bodyStr ++ s!"{c.ind 1}" ++ "};\n" ++
              s!"{c.ind 1}while (true) " ++ "{\n" ++
              s!"{c.ind 2}const __r = __step();\n" ++
              s!"{c.ind 2}if (__r !== null && typeof __r === \"object\" && __r.__tc !== undefined) " ++
                "{ " ++ reasn ++ " continue; }\n" ++
              s!"{c.ind 2}return __r;\n" ++
              s!"{c.ind 1}" ++ "}\n}\n"
        else
          s!"function {c.js f}({ps}) " ++ note ++ "{\n" ++ emitBody c 1 body ++ "}\n"
  | .extern .. => ""

def emitProgram (env : Environment) (entries : List (Name × String)) (min : Bool := false) : Except String String := do
  let roots := entries.map (·.1)
  let names := reach env roots #[]
  let mut nm : Std.HashMap Name String := {}
  let mut externs : Std.HashMap Name Decl := {}
  let mut counter := 0
  let entryMap : Std.HashMap Name String := entries.foldl (fun m e => m.insert e.1 e.2) {}
  for n in names do
    match findEnvDecl env n with
    | some (.fdecl ..) =>
        match entryMap.get? n with
        | some s => nm := nm.insert n s
        | none   => nm := nm.insert n s!"_g{counter}"; counter := counter + 1
    | some d@(.extern ..) => externs := externs.insert n d
    | none => throw s!"no IR for `{n}` (not compiled?)"
  let c : Ctx := { env, names := nm, externs, min }
  let mut out := if min then "" else "// GENERATED by Js.Backend (Lean-IR → JS). Do not edit.\n"
  out := out ++ "import * as $ from './qed_rt.mjs';\n"
  for n in names do
    match findEnvDecl env n with
    | some d@(.fdecl ..) => out := out ++ emitDecl c d
    | _ => pure ()
  let exportList := entries.map fun (n, s) => if n.toString == s then s else s!"{c.js n} as {s}"
  out := out ++ "\nexport { " ++ String.intercalate ", " exportList ++ " };\n"
  let externNames := (externs.toList.map (mangle ·.1)).toArray.qsort (· < ·)
  out := out ++ "export const __externs = [" ++
    String.intercalate ", " (externNames.toList.map (s!"\"{·}\"")) ++ "];\n"
  return out

end Js
