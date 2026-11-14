-- Runtime representation (matches `qed_rt.mjs`; recheck on Lean bumps, see `docs/upgrading-lean.md`):
-- Int/Nat/UInt64 → BigInt; UInt8/16/32/USize/Bool/nullary-ctor → Number; String → JS string (UTF-8 byte Pos);
-- Array → JS Array with refcount `.r`; ctor w/ fields → `{t, f, s, u}`; closure → `{fn, arity, args}`;
-- BaseIO returns raw values, EIO/IO wraps in single-field `EST.Out` (`{t:0|1, f:[v]}`).
import Lean
import Js.VerifyEnv
open Lean IR

namespace Js

def mangle (n : Name) : String := Id.run do
  let mut s := ""
  for c in n.toString.toList do
    if c.isAlphanum then s := s.push c
    else if c == '.' || c == '_' then s := s.push '_'
    else s := s ++ s!"x{c.toNat}"
  return s

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

def indStr (min : Bool) (d : Nat) : String :=
  if min then "" else String.ofList (List.replicate (2 * d) ' ')

/-! ## Typed JavaScript Target AST (`JsExpr`, `JsStmt`, `JsDecl`) -/

inductive JsExpr where
  | var       (name : String)
  | numLit    (n : Nat)
  | bigIntLit (n : Nat)
  | strLit    (s : String)
  | arrLit    (elems : List JsExpr)
  | ctorObj   (cidx : Nat) (fields : List JsExpr) (hasS : Bool) (hasU : Bool)
  | fieldProj (obj : JsExpr) (idx : Nat)
  | uProj     (obj : JsExpr) (idx : Nat)
  | sProj     (obj : JsExpr) (n offset : Nat)
  | call      (fn : String) (args : List JsExpr)
  | pap       (fn : String) (arity : Nat) (args : List JsExpr)
  | app       (fn : JsExpr) (args : List JsExpr)
  | tc        (args : List JsExpr)

mutual
def JsExpr.render : JsExpr → String
  | .var name         => name
  | .numLit n         => toString n
  | .bigIntLit n      => s!"{n}n"
  | .strLit s         => jsStr s
  | .arrLit elems     => s!"[{JsExpr.renderList elems}]"
  | .ctorObj cidx fields hasS hasU =>
      let s := if hasS then ", s: {}" else ""
      let u := if hasU then ", u: {}" else ""
      s!"\{t: {cidx}, f: [{JsExpr.renderList fields}]{s}{u}}"
  | .fieldProj obj i  => s!"{obj.render}.f[{i}]"
  | .uProj obj i      => s!"{obj.render}.u[{i}]"
  | .sProj obj n off  => s!"{obj.render}.s[{soff n off}]"
  | .call fn args     => s!"{fn}({JsExpr.renderList args})"
  | .pap fn ar args   => s!"$.pap({fn}, {ar}, [{JsExpr.renderList args}])"
  | .app fn args      => s!"$.app({fn.render}, [{JsExpr.renderList args}])"
  | .tc args          => s!"$.tc([{JsExpr.renderList args}])"

def JsExpr.renderList : List JsExpr → String
  | []      => ""
  | [e]     => e.render
  | e :: es => e.render ++ ", " ++ JsExpr.renderList es
end

mutual
inductive JsStmt where
  | letVar           (name : String) (val : JsExpr)
  | letDecls         (names : List String)
  | letBinds         (binds : List (String × JsExpr))
  | labeledBlock     (label : String) (body : List JsStmt)
  | constArrow       (name : String) (params : List String) (body : List JsStmt)
  | setField         (x : String) (idx : Nat) (val : JsExpr)
  | setTag           (x : String) (cidx : Nat)
  | setU             (x : String) (idx : Nat) (val : JsExpr)
  | setS             (x : String) (n offset : Nat) (val : JsExpr)
  | incRef           (x : String) (n : Nat)
  | decRef           (x : String) (n : Nat)
  | ret              (val : JsExpr)
  | tailContinue     (params : List String) (args : List JsExpr)
  | breakLabel       (assigns : List (String × JsExpr)) (label : String)
  | throwUnreachable
  | switchStmt       (scrut : JsExpr) (arms : List JsSwitchArm)

inductive JsSwitchArm where
  | caseArm    (cidx : Nat) (body : List JsStmt)
  | defaultArm (body : List JsStmt)
end

mutual
def JsStmt.render (min : Bool) (d : Nat) : JsStmt → String
  | .letVar x val =>
      s!"{indStr min d}let {x} = {val.render};\n"
  | .letDecls names =>
      if names.isEmpty then ""
      else s!"{indStr min d}let {String.intercalate ", " names};\n"
  | .letBinds binds =>
      if binds.isEmpty then ""
      else s!"{indStr min d}let {String.intercalate ", " (binds.map fun (k, e) => s!"{k} = {e.render}")};\n"
  | .labeledBlock lbl body =>
      s!"{indStr min d}{lbl}: \{\n" ++ JsStmt.renderList min (d + 1) body ++ s!"{indStr min d}}\n"
  | .constArrow name params body =>
      s!"{indStr min d}const {name} = ({String.intercalate ", " params}) => \{\n" ++
        JsStmt.renderList min (d + 1) body ++ s!"{indStr min d}};\n"
  | .setField x i val =>
      s!"{indStr min d}{x}.f[{i}] = {val.render};\n"
  | .setTag x cidx =>
      s!"{indStr min d}{x}.t = {cidx};\n"
  | .setU x i val =>
      s!"{indStr min d}{x}.u[{i}] = {val.render};\n"
  | .setS x n off val =>
      s!"{indStr min d}{x}.s[{soff n off}] = {val.render};\n"
  | .incRef x n =>
      s!"{indStr min d}$.inc({x}, {n});\n"
  | .decRef x n =>
      s!"{indStr min d}$.dec({x}, {n});\n"
  | .ret val =>
      s!"{indStr min d}return {val.render};\n"
  | .tailContinue params args =>
      if args.isEmpty then s!"{indStr min d}continue;\n"
      else
        let tmps := String.intercalate ", " (args.zipIdx.map fun (a, i) => s!"_t{i} = {a.render}")
        let assigns := String.intercalate " " (params.zipIdx.map fun (p, i) => s!"{p} = _t{i};")
        s!"{indStr min d}\{ let {tmps}; {assigns} continue; }\n"
  | .breakLabel assigns lbl =>
      let assignStr := String.intercalate " " (assigns.map fun (lhs, rhs) => s!"{lhs} = {rhs.render};")
      let pfx := if assignStr.isEmpty then "" else assignStr ++ " "
      s!"{indStr min d}{pfx}break {lbl};\n"
  | .throwUnreachable =>
      s!"{indStr min d}throw new Error('unreachable');\n"
  | .switchStmt scrut arms =>
      s!"{indStr min d}switch ({scrut.render}) \{\n" ++
        JsSwitchArm.renderList min (d + 1) arms ++ s!"{indStr min d}}\n"

def JsStmt.renderList (min : Bool) (d : Nat) : List JsStmt → String
  | []      => ""
  | s :: ss => s.render min d ++ JsStmt.renderList min d ss

def JsSwitchArm.render (min : Bool) (d : Nat) : JsSwitchArm → String
  | .caseArm cidx body =>
      s!"{indStr min d}case {cidx}: \{\n" ++ JsStmt.renderList min (d + 1) body ++ s!"{indStr min d}}\n"
  | .defaultArm body =>
      s!"{indStr min d}default: \{\n" ++ JsStmt.renderList min (d + 1) body ++ s!"{indStr min d}}\n"

def JsSwitchArm.renderList (min : Bool) (d : Nat) : List JsSwitchArm → String
  | []      => ""
  | a :: as => a.render min d ++ JsSwitchArm.renderList min d as
end

inductive JsDecl where
  | memoInit     (name : String) (initFn : String)
  | memoThunk    (name : String) (body : List JsStmt)
  | fnPlain      (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnDirectLoop (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnTrampoline (name : String) (origName : Name) (params : List String) (body : List JsStmt)

private def fnHeader (min : Bool) (name : String) (orig : Name) (params : List String) : String :=
  let ps := String.intercalate ", " params
  let note := if min then "" else s!"/* {orig} */ "
  s!"function {name}({ps}) {note}\{\n"

def JsDecl.render (min : Bool) : JsDecl → String
  | .memoInit name initFn =>
      s!"const {name} = $.memo(() => $.ioVal({initFn}(0)));\n"
  | .memoThunk name body =>
      s!"const {name} = $.memo(() => \{\n" ++ JsStmt.renderList min 1 body ++ "});\n"
  | .fnPlain name orig params body =>
      fnHeader min name orig params ++ JsStmt.renderList min 1 body ++ "}\n"
  | .fnDirectLoop name orig params body =>
      fnHeader min name orig params ++
        s!"{indStr min 1}while (true) \{\n" ++ JsStmt.renderList min 2 body ++ s!"{indStr min 1}}\n}\n"
  | .fnTrampoline name orig params body =>
      let ps := String.intercalate ", " params
      let reasn := s!"[{ps}] = __r.__tc;"
      fnHeader min name orig params ++
        s!"{indStr min 1}const __step = () => \{\n" ++ JsStmt.renderList min 2 body ++ s!"{indStr min 1}};\n" ++
        s!"{indStr min 1}while (true) \{\n" ++
        s!"{indStr min 2}const __r = __step();\n" ++
        s!"{indStr min 2}if (__r !== null && typeof __r === \"object\" && __r.__tc !== undefined) \{ {reasn} continue; }\n" ++
        s!"{indStr min 2}return __r;\n" ++
        s!"{indStr min 1}}\n}\n"

/-! ## Total IR Analysis & Reachability Passes -/

mutual
def callees : FnBody → Array Name → Array Name
  | .vdecl _ _ e b, acc =>
      let acc := match e with | .fap c _ => acc.push c | .pap c _ => acc.push c | _ => acc
      callees b acc
  | .jdecl _ _ v b, acc => callees b (callees v acc)
  | .case _ _ _ alts, acc => calleesAlts alts.toList acc
  | .set _ _ _ b, acc | .setTag _ _ b, acc | .uset _ _ _ b, acc
  | .sset _ _ _ _ _ b, acc | .inc _ _ _ _ b, acc | .dec _ _ _ _ b, acc
  | .del _ b, acc => callees b acc
  | .ret _, acc | .jmp _ _, acc | .unreachable, acc => acc

def calleesAlts : List Alt → Array Name → Array Name
  | [], acc => acc
  | .ctor _ b :: rest, acc | .default b :: rest, acc => calleesAlts rest (callees b acc)
end

def reachAux (env : Environment) : Nat → List Name → Array Name → Std.HashSet Name → Array Name
  | 0, _, seen, _ => seen
  | _ + 1, [], seen, _ => seen
  | fuel + 1, n :: rest, seen, visited =>
      if visited.contains n then
        reachAux env fuel rest seen visited
      else
        let seen := seen.push n
        let visited := visited.insert n
        match findEnvDecl env n with
        | some (.fdecl (body := b) ..) =>
            let extra := (callees b #[]).toList ++ (getInitFnNameFor? env n).toList
            reachAux env fuel (rest ++ extra) seen visited
        | _ =>
            reachAux env fuel rest seen visited

def reach (env : Environment) (roots : List Name) (seen : Array Name := #[]) : Array Name :=
  let initVisited := seen.foldl (fun s n => s.insert n) ({} : Std.HashSet Name)
  reachAux env 1000000 roots seen initVisited

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

def v (x : VarId) : String := s!"x{x.idx}"
def jp (j : JoinPointId) : String := s!"j{j.idx}"

def lowerArg : Arg → JsExpr
  | .var x  => .var (v x)
  | .erased => .numLit 0

def lowerCtor (i : CtorInfo) (ys : Array Arg) : JsExpr :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then
    .numLit i.cidx
  else
    .ctorObj i.cidx (ys.toList.map lowerArg) (i.ssize != 0) (i.usize != 0)

def lowerApp (c : Ctx) (f : Name) (ys : Array Arg) : JsExpr :=
  -- `Qed.refMark`'s pure Lean body is conservative `0`; substitute the runtime identity stamp here.
  if f == `Qed.refMark then
    .call "$.refMark" (ys.toList.filterMap fun | .var x => some (.var (v x)) | .erased => none)
  else
    let argExprs : List JsExpr :=
      match findEnvDecl c.env f with
      | some (.extern (xs := ps) ..) =>
          ys.toList.zipIdx.filterMap fun (a, i) =>
            if i < ps.size && ps[i]!.ty.isErased then none else some (lowerArg a)
      | _ => ys.toList.map lowerArg
    .call (c.js f) argExprs

def lowerExpr (c : Ctx) (ty : IRType) : IR.Expr → JsExpr
  | .ctor i ys      => lowerCtor i ys
  | .reset ..       => .numLit 0
  | .reuse _ i _ ys => lowerCtor i ys
  | .proj i x       => .fieldProj (.var (v x)) i
  | .uproj i x      => .uProj (.var (v x)) i
  | .sproj n off x  => .sProj (.var (v x)) n off
  | .fap f ys       => lowerApp c f ys
  | .pap f ys       =>
      let arity := (findEnvDecl c.env f).map (·.params.size) |>.getD ys.size
      .pap (c.js f) arity (ys.toList.map lowerArg)
  | .ap x ys        => .app (.var (v x)) (ys.toList.map lowerArg)
  | .box _ x        => .var (v x)
  | .unbox x        => .var (v x)
  | .lit (.num n)   => if ty.isObj || ty == .uint64 then .bigIntLit n else .numLit n
  | .lit (.str s)   => .strLit s
  | .isShared x     => .call "$.isShared" [.var (v x)]

def skipRC : FnBody → FnBody
  | .inc _ _ _ _ b => skipRC b
  | .dec _ _ _ _ b => skipRC b
  | .del _ b       => skipRC b
  | b              => b

def retsVar (z : VarId) (cont : FnBody) : Bool :=
  match skipRC cont with
  | .ret (.var w) => w == z
  | _             => false

mutual
def hasJmpTo (target : JoinPointId) : FnBody → Bool
  | .jmp j _          => j == target
  | .vdecl _ _ _ b | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b
  | .sset _ _ _ _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasJmpTo target b
  | .jdecl _ _ v b    => hasJmpTo target v || hasJmpTo target b
  | .case _ _ _ alts  => hasJmpToAlts target alts.toList
  | .ret _ | .unreachable => false

def hasJmpToAlts (target : JoinPointId) : List Alt → Bool
  | [] => false
  | .ctor _ b :: rest | .default b :: rest => hasJmpTo target b || hasJmpToAlts target rest
end

-- Non-recursive join points lower to labeled blocks (`jN: { ... }`), so `continue` inside them
-- still targets the enclosing `while (true)` loop; only recursive closure join points (`onlyRecJp = true`)
-- require falling back to `$.tc`.
mutual
def hasSelfTailAux (self : Name) (onlyRecJp active : Bool) : FnBody → Bool
  | .vdecl z _ (.fap f _) cont => (active && f == self && retsVar z cont) || hasSelfTailAux self onlyRecJp active cont
  | .vdecl _ _ _ b    => hasSelfTailAux self onlyRecJp active b
  | .jdecl j _ v b    =>
      let activeV := if onlyRecJp then active || hasJmpTo j v else active
      hasSelfTailAux self onlyRecJp activeV v || hasSelfTailAux self onlyRecJp active b
  | .case _ _ _ alts  => hasSelfTailAltsAux self onlyRecJp active alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b => hasSelfTailAux self onlyRecJp active b
  | .sset _ _ _ _ _ b => hasSelfTailAux self onlyRecJp active b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasSelfTailAux self onlyRecJp active b
  | .ret _ | .jmp _ _ | .unreachable => false

def hasSelfTailAltsAux (self : Name) (onlyRecJp active : Bool) : List Alt → Bool
  | [] => false
  | .ctor _ b :: rest | .default b :: rest =>
      hasSelfTailAux self onlyRecJp active b || hasSelfTailAltsAux self onlyRecJp active rest
end

def hasSelfTail (self : Name) (b : FnBody) : Bool := hasSelfTailAux self false true b
def hasJpSelfTail (self : Name) (b : FnBody) : Bool := hasSelfTailAux self true false b

mutual
def collectNonArr (acc : Std.HashSet Nat) : FnBody → Std.HashSet Nat
  | .vdecl x _ e b =>
      let acc := match e with
        | .ctor .. | .reuse .. | .pap .. | .lit .. | .box .. | .unbox .. | .isShared .. => acc.insert x.idx
        | .proj _ p | .uproj _ p | .sproj _ _ p => acc.insert p.idx
        | _ => acc
      collectNonArr acc b
  | .jdecl _ _ v b => collectNonArr (collectNonArr acc v) b
  | .case _ x _ alts => collectNonArrAlts (acc.insert x.idx) alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => collectNonArr acc b
  | .ret _ | .jmp _ _ | .unreachable => acc

def collectNonArrAlts (acc : Std.HashSet Nat) : List Alt → Std.HashSet Nat
  | [] => acc
  | .ctor _ b :: rest | .default b :: rest => collectNonArrAlts (collectNonArr acc b) rest
end

def hasDecOf (p : Nat) : FnBody → Bool
  | .dec y _ _ _ b => p == y.idx || hasDecOf p b
  | .del y b       => p == y.idx || hasDecOf p b
  | .inc _ _ _ _ b => hasDecOf p b
  | .vdecl _ _ (.proj ..) b | .vdecl _ _ (.uproj ..) b | .vdecl _ _ (.sproj ..) b => hasDecOf p b
  | _              => false

mutual
def collectProjSrc (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) : FnBody → Std.HashMap Nat Nat
  | .vdecl x _ (.fap ..) b | .vdecl x _ (.ap ..) b => collectProjSrc (calls.insert x.idx) acc b
  | .vdecl x _ (.proj _ p) b =>
      collectProjSrc calls (if calls.contains p.idx then acc.insert x.idx p.idx else acc) b
  | .vdecl _ _ _ b => collectProjSrc calls acc b
  | .jdecl _ _ v b => collectProjSrc calls (collectProjSrc calls acc v) b
  | .case _ _ _ alts => collectProjSrcAlts calls acc alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => collectProjSrc calls acc b
  | .ret _ | .jmp _ _ | .unreachable => acc

def collectProjSrcAlts (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) :
    List Alt → Std.HashMap Nat Nat
  | [] => acc
  | .ctor _ b :: rest | .default b :: rest =>
      collectProjSrcAlts calls (collectProjSrc calls acc b) rest
end

/-! ## Lowering `Lean.IR` into Typed JS Statements & Declarations -/

mutual
def lowerBody (c : Ctx) : FnBody → List JsStmt
  | .vdecl x ty e b =>
      match e with
      | .fap f args =>
          if c.selfFn == some f && retsVar x b then
            if c.directLoop then
              [.tailContinue (c.selfParams.toList.map (v ·.x)) (args.toList.map lowerArg)]
            else
              [.ret (.tc (args.toList.map lowerArg))]
          else
            .letVar (v x) (lowerExpr c ty e) :: lowerBody c b
      | _ => .letVar (v x) (lowerExpr c ty e) :: lowerBody c b
  | .jdecl j xs val b =>
      if !hasJmpTo j val then
        let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
        let declNames := xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}"
        let bindPairs := xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}")
        let pre := if xs.isEmpty then [] else [JsStmt.letDecls declNames]
        let post := if xs.isEmpty then [] else [JsStmt.letBinds bindPairs]
        pre ++ [.labeledBlock (jp j) (lowerBody c' b)] ++ post ++ lowerBody c val
      else
        let ps := xs.toList.map (v ·.x)
        .constArrow (jp j) ps (lowerBody c val) :: lowerBody c b
  | .set x i y b        => .setField (v x) i (lowerArg y) :: lowerBody c b
  | .setTag x cidx b    => .setTag (v x) cidx :: lowerBody c b
  | .uset x i y b       => .setU (v x) i (.var (v y)) :: lowerBody c b
  | .sset x n off y _ b => .setS (v x) n off (.var (v y)) :: lowerBody c b
  -- Only `Array`s carry `.r`. When `x = p.f[i]` is `inc`ed right before `p` is dropped (`hasDecOf`),
  -- 1 reference transfers from `p` to `x` (`n - 1`) since constructor `dec` does not cascade in JS.
  | .inc x n _ _ b =>
      let n' := match c.projSrc.get? x.idx with
        | some p => if hasDecOf p b then n - 1 else n
        | none   => n
      if n' == 0 || c.nonArr.contains x.idx then lowerBody c b
      else .incRef (v x) n' :: lowerBody c b
  | .dec x n _ _ b =>
      if c.nonArr.contains x.idx then lowerBody c b
      else .decRef (v x) n :: lowerBody c b
  | .del x b =>
      if c.nonArr.contains x.idx then lowerBody c b
      else .decRef (v x) 1 :: lowerBody c b
  | .ret a =>
      [.ret (lowerArg a)]
  | .jmp j ys =>
      match c.inlineJps.get? j.idx with
      | some _ =>
          let assigns := ys.toList.zipIdx.map fun (a, i) => (s!"_{jp j}_{i}", lowerArg a)
          [.breakLabel assigns (jp j)]
      | none =>
          [.ret (.call (jp j) (ys.toList.map lowerArg))]
  | .unreachable =>
      [.throwUnreachable]
  | .case _ x xType alts =>
      let scrut := if xType.isObj then .call "$.tag" [.var (v x)] else .var (v x)
      [.switchStmt scrut (lowerAlts c alts.toList)]

def lowerAlts (c : Ctx) : List Alt → List JsSwitchArm
  | [] => []
  | .ctor info b :: rest => .caseArm info.cidx (lowerBody c b) :: lowerAlts c rest
  | .default b :: rest   => .defaultArm (lowerBody c b) :: lowerAlts c rest
end

def lowerDecl (c0 : Ctx) : Decl → Option JsDecl
  | .fdecl f xs _ body _ =>
      let c := { c0 with nonArr := collectNonArr {} body, projSrc := collectProjSrc {} {} body }
      if xs.isEmpty then
        match getInitFnNameFor? c.env f with
        | some initFn => some (.memoInit (c.js f) (c.js initFn))
        | none        => some (.memoThunk (c.js f) (lowerBody c body))
      else
        let ps := xs.toList.map (v ·.x)
        if hasSelfTail f body then
          if !hasJpSelfTail f body then
            let c' := { c with selfFn := some f, selfParams := xs, directLoop := true }
            some (.fnDirectLoop (c.js f) f ps (lowerBody c' body))
          else
            let c' := { c with selfFn := some f, selfParams := xs }
            some (.fnTrampoline (c.js f) f ps (lowerBody c' body))
        else
          some (.fnPlain (c.js f) f ps (lowerBody c body))
  | .extern .. => none

def emitDecl (c0 : Ctx) (d : Decl) : String :=
  match lowerDecl c0 d with
  | some jd => jd.render c0.min
  | none    => ""

def emitProgram (env : Environment) (entries : List (Name × String)) (min : Bool := false) : Except String String := do
  let roots := entries.map (·.1)
  let names := reach env roots #[]
  verifyReachable env names
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
  let externNames := (externs.toList.map (mangle ·.1)).mergeSort (· < ·)
  out := out ++ "export const __externs = [" ++
    String.intercalate ", " (externNames.map (s!"\"{·}\"")) ++ "];\n"
  return out

end Js
