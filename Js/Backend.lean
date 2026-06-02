/-
  Js.Backend — a faithful Lean-IR → JavaScript transpiler (build-time tool).

  It reads the *compiled* `Lean.IR.Decl` for an app's entry points — the same IR the
  C backend consumes — and emits JavaScript, mirroring `Lean.IR.EmitC` minus the
  manual memory model. Because JS is garbage-collected, the whole reference-counting /
  boxing layer collapses: `inc`/`dec`/`del` are dropped, `box`/`unbox` are identities,
  `isShared` is conservatively `true` (so `reset`/`reuse` always allocate fresh and we
  never mutate possibly-shared data), and the IO monad — which the compiler materializes
  as `EStateM.Result.ok value world` ctors threading a world token — transpiles with the
  ordinary ctor/proj/case machinery, so even the driver is just data.

  Runtime representation (matches `qed_rt.mjs`):
    • Int / Nat        → BigInt
    • UInt8/16/32, USize, Bool-as-u8, enum tags → Number
    • UInt64           → BigInt
    • String           → JS string (Pos = byte offset, handled in the runtime)
    • Array            → JS Array
    • nullary ctor     → the number `cidx`            (lean_box(cidx))
    • ctor with fields → {t: cidx, f:[objFields], s:{}, u:{}}
    • closure          → {fn, arity, args}             ($.pap / $.app)
    • IO world token   → 0 (threaded, never inspected)

  Anything the emitter cannot lower, or an extern with no JS implementation, makes the
  build FAIL LOUDLY — it never emits a silently-wrong program.
-/
import Lean
open Lean IR

namespace Js

/-- A JS-safe identifier fragment for an extern/global name. -/
def mangle (n : Name) : String := Id.run do
  let mut s := ""
  for c in n.toString.data do
    if c.isAlphanum then s := s.push c
    else if c == '.' || c == '_' then s := s.push '_'
    else s := s ++ s!"x{c.toNat}"
  return s

/-! ## Reachability -/

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
      | some (.fdecl (body := b) ..) => reach env (rest ++ (callees b #[]).toList) seen
      | _ => reach env rest seen

/-! ## Names -/

structure Ctx where
  env     : Environment
  /-- decl name → JS identifier (internal fdecls get `_gN`; entries keep a stable name). -/
  names   : Std.HashMap Name String
  /-- externs the program references (must be provided by the runtime). -/
  externs : Std.HashMap Name Decl

def Ctx.js (c : Ctx) (n : Name) : String :=
  match c.names.get? n with
  | some s => s
  | none   => "$." ++ mangle n   -- an extern: a member of the runtime namespace `$`

/-! ## Expression / body emission -/

def v (x : VarId) : String := s!"x{x.idx}"
def jp (j : JoinPointId) : String := s!"j{j.idx}"

def emitArg : Arg → String
  | .var x      => v x
  | .irrelevant => "0"   -- irrelevant value; never inspected

/-- A constructor value: nullary → its tag number; otherwise a tagged record. -/
def ctorVal (i : CtorInfo) (ys : Array Arg) : String :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then toString i.cidx
  else
    let fs := String.intercalate ", " (ys.toList.map emitArg)
    "{t: " ++ toString i.cidx ++ ", f: [" ++ fs ++ "], s: {}, u: {}}"

/-- Byte-offset key for a packed scalar field (mirrors EmitC `emitOffset`). -/
def soff (n offset : Nat) : String := s!"\"{n}_{offset}\""

def jsStr (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r"
      | '\t' => "\\t"
      | c =>
        if c.toNat < 32 then
          let h := Nat.toDigits 16 c.toNat
          "\\x" ++ String.mk (if h.length == 1 then '0' :: h else h)
        else String.singleton c)
  "\"" ++ escaped ++ "\""

/-- Emit a full application, stripping irrelevant args for externs (as EmitC does). -/
def emitApp (c : Ctx) (f : Name) (ys : Array Arg) : String :=
  let argStrs : List String :=
    match findEnvDecl c.env f with
    | some (.extern (xs := ps) ..) =>
        ys.toList.enum.filterMap fun (i, a) =>
          if i < ps.size && ps[i]!.ty.isIrrelevant then none else some (emitArg a)
    | _ => ys.toList.map emitArg
  s!"{c.js f}({String.intercalate ", " argStrs})"

def emitExpr (c : Ctx) (ty : IRType) : IR.Expr → String
  | .ctor i ys      => ctorVal i ys
  | .reset ..       => "0"                       -- conservative: not exclusive
  | .reuse _ i _ ys => ctorVal i ys              -- always fresh; following set/sset mutate it
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
  | .isShared _     => "1"                        -- conservative: assume shared (Bool.true as u8)

def ind (d : Nat) : String := String.mk (List.replicate (2 * d) ' ')

partial def emitBody (c : Ctx) (d : Nat) : FnBody → String
  | .vdecl x ty e b   => s!"{ind d}let {v x} = {emitExpr c ty e};\n" ++ emitBody c d b
  | .jdecl j xs val b =>
      let ps := String.intercalate ", " (xs.toList.map (v ·.x))
      s!"{ind d}const {jp j} = ({ps}) => " ++ "{\n" ++ emitBody c (d+1) val ++ s!"{ind d}" ++ "};\n"
        ++ emitBody c d b
  | .set x i y b      => s!"{ind d}{v x}.f[{i}] = {emitArg y};\n" ++ emitBody c d b
  | .setTag x cidx b  => s!"{ind d}{v x}.t = {cidx};\n" ++ emitBody c d b
  | .uset x i y b     => s!"{ind d}{v x}.u[{i}] = {v y};\n" ++ emitBody c d b
  | .sset x n off y _ b => s!"{ind d}{v x}.s[{soff n off}] = {v y};\n" ++ emitBody c d b
  | .inc _ _ _ _ b    => emitBody c d b
  | .dec _ _ _ _ b    => emitBody c d b
  | .del _ b          => emitBody c d b
  | .mdata _ b        => emitBody c d b
  | .ret a            => s!"{ind d}return {emitArg a};\n"
  | .jmp j ys         => s!"{ind d}return {jp j}({String.intercalate ", " (ys.toList.map emitArg)});\n"
  | .unreachable      => s!"{ind d}throw new Error('unreachable');\n"
  | .case _ x xType alts =>
      let scrut := if xType.isObj then s!"$.tag({v x})" else v x
      let arms := alts.toList.map fun alt =>
        match alt with
        | .ctor info b => s!"{ind (d+1)}case {info.cidx}: " ++ "{\n" ++ emitBody c (d+2) b ++ s!"{ind (d+1)}" ++ "}\n"
        | .default b   => s!"{ind (d+1)}default: " ++ "{\n" ++ emitBody c (d+2) b ++ s!"{ind (d+1)}" ++ "}\n"
      s!"{ind d}switch ({scrut}) " ++ "{\n" ++ String.join arms ++ s!"{ind d}" ++ "}\n"

def emitDecl (c : Ctx) : Decl → String
  | .fdecl f xs _ body _ =>
      let ps := String.intercalate ", " (xs.toList.map (v ·.x))
      s!"function {c.js f}({ps}) " ++ s!"/* {f} */ " ++ "{\n" ++ emitBody c 1 body ++ "}\n"
  | .extern .. => ""

/-! ## Program assembly -/

/-- Build the JS module. `entries` maps a decl name to the stable JS name to export it as. -/
def emitProgram (env : Environment) (entries : List (Name × String)) : Except String String := do
  let roots := entries.map (·.1)
  let names := reach env roots #[]
  -- Assign identifiers.
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
  let c : Ctx := { env, names := nm, externs }
  -- Emit.
  let mut out := "// GENERATED by Js.Backend (Lean-IR → JS). Do not edit.\n"
  out := out ++ "import * as $ from './qed_rt.mjs';\n\n"
  for n in names do
    match findEnvDecl env n with
    | some d@(.fdecl ..) => out := out ++ emitDecl c d
    | _ => pure ()
  -- Exports + a manifest of required externs (so the runtime can be checked).
  let exportList := entries.map fun (n, s) => if n.toString == s then s else s!"{c.js n} as {s}"
  out := out ++ "\nexport { " ++ String.intercalate ", " exportList ++ " };\n"
  let externNames := (externs.toList.map (mangle ·.1)).toArray.qsort (· < ·)
  out := out ++ "export const __externs = [" ++
    String.intercalate ", " (externNames.toList.map (s!"\"{·}\"")) ++ "];\n"
  return out

end Js
