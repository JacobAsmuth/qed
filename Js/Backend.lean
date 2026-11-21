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

private def joinChunksAux (xs : Array String) (lo hi : Nat) : String :=
  if _ : lo ≥ hi then ""
  else if _ : lo + 1 == hi then xs[lo]!
  else if _ : lo + 2 == hi then xs[lo]! ++ xs[lo + 1]!
  else
    let mid := (lo + hi) / 2
    joinChunksAux xs lo mid ++ joinChunksAux xs mid hi
termination_by hi - lo
decreasing_by all_goals (simp_all; omega)

private def joinChunks (xs : Array String) : String :=
  joinChunksAux xs 0 xs.size

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
def JsExpr.renderMin (min : Bool) : JsExpr → String
  | .var name         => name
  | .numLit n         => toString n
  | .bigIntLit n      => s!"{n}n"
  | .strLit s         => jsStr s
  | .arrLit elems     => s!"[{joinChunks (JsExpr.renderListMinAux min #[] elems)}]"
  | .ctorObj cidx fields hasS hasU =>
      let sep := if min then "" else " "
      let s := if hasS then s!",{sep}s:{sep}" ++ "{}" else ""
      let u := if hasU then s!",{sep}u:{sep}" ++ "{}" else ""
      s!"\{t:{sep}{cidx},{sep}f:{sep}[{joinChunks (JsExpr.renderListMinAux min #[] fields)}]{s}{u}}"
  | .fieldProj obj i  => s!"{obj.renderMin min}.f[{i}]"
  | .uProj obj i      => s!"{obj.renderMin min}.u[{i}]"
  | .sProj obj n off  => s!"{obj.renderMin min}.s[{soff n off}]"
  | .call fn args     => s!"{fn}({joinChunks (JsExpr.renderListMinAux min #[] args)})"
  | .pap fn ar args   =>
      let sep := if min then "," else ", "
      s!"$.pap({fn}{sep}{ar}{sep}[{joinChunks (JsExpr.renderListMinAux min #[] args)}])"
  | .app fn args      =>
      let sep := if min then "," else ", "
      s!"$.app({fn.renderMin min}{sep}[{joinChunks (JsExpr.renderListMinAux min #[] args)}])"
  | .tc args          => s!"$.tc([{joinChunks (JsExpr.renderListMinAux min #[] args)}])"

def JsExpr.renderListMinAux (min : Bool) (acc : Array String) : List JsExpr → Array String
  | []      => acc
  | [e]     => acc.push (e.renderMin min)
  | e :: es => JsExpr.renderListMinAux min ((acc.push (e.renderMin min)).push (if min then "," else ", ")) es
end

def JsExpr.render (e : JsExpr) : String :=
  e.renderMin false

def JsExpr.renderList (es : List JsExpr) : String :=
  joinChunks (JsExpr.renderListMinAux false #[] es)

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
      if min then s!"let {x}={val.renderMin true};"
      else s!"{indStr false d}let {x} = {val.renderMin false};\n"
  | .letDecls names =>
      if names.isEmpty then ""
      else if min then s!"let {String.intercalate "," names};"
      else s!"{indStr false d}let {String.intercalate ", " names};\n"
  | .letBinds binds =>
      if binds.isEmpty then ""
      else if min then s!"let {String.intercalate "," (binds.map fun (k, e) => s!"{k}={e.renderMin true}")};"
      else s!"{indStr false d}let {String.intercalate ", " (binds.map fun (k, e) => s!"{k} = {e.renderMin false}")};\n"
  | .labeledBlock lbl body =>
      if min then s!"{lbl}:\{" ++ joinChunks (JsStmt.renderListAux true (d + 1) #[] body) ++ "}"
      else s!"{indStr false d}{lbl}: \{\n" ++ joinChunks (JsStmt.renderListAux false (d + 1) #[] body) ++ s!"{indStr false d}}\n"
  | .constArrow name params body =>
      if min then
        s!"const {name}=({String.intercalate "," params})=>\{" ++
          joinChunks (JsStmt.renderListAux true (d + 1) #[] body) ++ "};"
      else
        s!"{indStr false d}const {name} = ({String.intercalate ", " params}) => \{\n" ++
          joinChunks (JsStmt.renderListAux false (d + 1) #[] body) ++ s!"{indStr false d}};\n"
  | .setField x i val =>
      if min then s!"{x}.f[{i}]={val.renderMin true};"
      else s!"{indStr false d}{x}.f[{i}] = {val.renderMin false};\n"
  | .setTag x cidx =>
      if min then s!"{x}.t={cidx};"
      else s!"{indStr false d}{x}.t = {cidx};\n"
  | .setU x i val =>
      if min then s!"{x}.u[{i}]={val.renderMin true};"
      else s!"{indStr false d}{x}.u[{i}] = {val.renderMin false};\n"
  | .setS x n off val =>
      if min then s!"{x}.s[{soff n off}]={val.renderMin true};"
      else s!"{indStr false d}{x}.s[{soff n off}] = {val.renderMin false};\n"
  | .incRef x n =>
      if min then s!"$.inc({x},{n});"
      else s!"{indStr false d}$.inc({x}, {n});\n"
  | .decRef x n =>
      if min then s!"$.dec({x},{n});"
      else s!"{indStr false d}$.dec({x}, {n});\n"
  | .ret val =>
      if min then s!"return {val.renderMin true};"
      else s!"{indStr false d}return {val.renderMin false};\n"
  | .tailContinue params args =>
      if args.isEmpty then
        if min then "continue;" else s!"{indStr false d}continue;\n"
      else if min then
        match params, args with
        | [p], [a] => s!"\{{p}={a.renderMin true};continue;}"
        | _, _ =>
            let tmps := String.intercalate "," (args.zipIdx.map fun (a, i) => s!"_{i}={a.renderMin true}")
            let assigns := String.intercalate "" (params.zipIdx.map fun (p, i) => s!"{p}=_{i};")
            s!"\{let {tmps};{assigns}continue;}"
      else
        let tmps := String.intercalate ", " (args.zipIdx.map fun (a, i) => s!"_t{i} = {a.renderMin false}")
        let assigns := String.intercalate " " (params.zipIdx.map fun (p, i) => s!"{p} = _t{i};")
        s!"{indStr false d}\{ let {tmps}; {assigns} continue; }\n"
  | .breakLabel assigns lbl =>
      if min then
        let assignStr := String.intercalate "" (assigns.map fun (lhs, rhs) => s!"{lhs}={rhs.renderMin true};")
        s!"{assignStr}break {lbl};"
      else
        let assignStr := String.intercalate " " (assigns.map fun (lhs, rhs) => s!"{lhs} = {rhs.renderMin false};")
        let pfx := if assignStr.isEmpty then "" else assignStr ++ " "
        s!"{indStr false d}{pfx}break {lbl};\n"
  | .throwUnreachable =>
      if min then "throw new Error('unreachable');"
      else s!"{indStr false d}throw new Error('unreachable');\n"
  | .switchStmt scrut arms =>
      if min then
        s!"switch({scrut.renderMin true})\{" ++
          joinChunks (JsSwitchArm.renderListAux true (d + 1) #[] arms) ++ "}"
      else
        s!"{indStr false d}switch ({scrut.renderMin false}) \{\n" ++
          joinChunks (JsSwitchArm.renderListAux false (d + 1) #[] arms) ++ s!"{indStr false d}}\n"

def JsStmt.renderListAux (min : Bool) (d : Nat) (acc : Array String) : List JsStmt → Array String
  | []      => acc
  | s :: ss => JsStmt.renderListAux min d (acc.push (s.render min d)) ss

def JsSwitchArm.render (min : Bool) (d : Nat) : JsSwitchArm → String
  | .caseArm cidx body =>
      if min then s!"case {cidx}:\{" ++ joinChunks (JsStmt.renderListAux true (d + 1) #[] body) ++ "}"
      else s!"{indStr false d}case {cidx}: \{\n" ++ joinChunks (JsStmt.renderListAux false (d + 1) #[] body) ++ s!"{indStr false d}}\n"
  | .defaultArm body =>
      if min then "default:{" ++ joinChunks (JsStmt.renderListAux true (d + 1) #[] body) ++ "}"
      else s!"{indStr false d}default: \{\n" ++ joinChunks (JsStmt.renderListAux false (d + 1) #[] body) ++ s!"{indStr false d}}\n"

def JsSwitchArm.renderListAux (min : Bool) (d : Nat) (acc : Array String) : List JsSwitchArm → Array String
  | []      => acc
  | a :: as => JsSwitchArm.renderListAux min d (acc.push (a.render min d)) as
end

def JsStmt.renderList (min : Bool) (d : Nat) (ss : List JsStmt) : String :=
  joinChunks (JsStmt.renderListAux min d #[] ss)

def JsSwitchArm.renderList (min : Bool) (d : Nat) (as : List JsSwitchArm) : String :=
  joinChunks (JsSwitchArm.renderListAux min d #[] as)

inductive JsDecl where
  | memoInit     (name : String) (initFn : String)
  | memoThunk    (name : String) (body : List JsStmt)
  | fnPlain      (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnDirectLoop (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnTrampoline (name : String) (origName : Name) (params : List String) (body : List JsStmt)

private def fnHeader (min : Bool) (name : String) (orig : Name) (params : List String) : String :=
  if min then
    s!"function {name}({String.intercalate "," params})\{"
  else
    let ps := String.intercalate ", " params
    s!"function {name}({ps}) /* {orig} */ \{\n"

def JsDecl.render (min : Bool) : JsDecl → String
  | .memoInit name initFn =>
      if min then s!"const {name}=$.memo(()=>$.ioVal({initFn}(0)));\n"
      else s!"const {name} = $.memo(() => $.ioVal({initFn}(0)));\n"
  | .memoThunk name body =>
      if min then s!"const {name}=$.memo(()=>\{" ++ JsStmt.renderList true 1 body ++ "});\n"
      else s!"const {name} = $.memo(() => \{\n" ++ JsStmt.renderList false 1 body ++ "});\n"
  | .fnPlain name orig params body =>
      fnHeader min name orig params ++ JsStmt.renderList min 1 body ++ "}\n"
  | .fnDirectLoop name orig params body =>
      if min then
        fnHeader true name orig params ++ "while(1){" ++ JsStmt.renderList true 2 body ++ "}}\n"
      else
        fnHeader false name orig params ++
          s!"{indStr false 1}while (true) \{\n" ++ JsStmt.renderList false 2 body ++ s!"{indStr false 1}}\n}\n"
  | .fnTrampoline name orig params body =>
      if min then
        let ps := String.intercalate "," params
        fnHeader true name orig params ++
          "const _s=()=>{" ++ JsStmt.renderList true 2 body ++ "};" ++
          s!"while(1)\{const _r=_s();if(_r!==null&&typeof _r===\"object\"&&_r.__tc!==void 0)\{[{ps}]=_r.__tc;continue;}return _r;}}\n"
      else
        let ps := String.intercalate ", " params
        let reasn := s!"[{ps}] = __r.__tc;"
        fnHeader false name orig params ++
          s!"{indStr false 1}const __step = () => \{\n" ++ JsStmt.renderList false 2 body ++ s!"{indStr false 1}};\n" ++
          s!"{indStr false 1}while (true) \{\n" ++
          s!"{indStr false 2}const __r = __step();\n" ++
          s!"{indStr false 2}if (__r !== null && typeof __r === \"object\" && __r.__tc !== undefined) \{ {reasn} continue; }\n" ++
          s!"{indStr false 2}return __r;\n" ++
          s!"{indStr false 1}}\n}\n"

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

def reachAux (env : Environment) :
    Nat → List Name → Array Name → Std.HashSet Name → Except String (Array Name)
  | _, [], seen, _ => .ok seen
  | 0, n :: _, _, _ => .error s!"JS reachability gate: exceeded fuel limit while inspecting `{n}`"
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

def reach (env : Environment) (roots : List Name) (seen : Array Name := #[]) :
    Except String (Array Name) :=
  let initVisited := seen.foldl (fun s n => s.insert n) ({} : Std.HashSet Name)
  reachAux env 1000000 roots seen initVisited

structure Ctx where
  env        : Environment
  names      : Std.HashMap Name String
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
  | .vdecl z _ e cont =>
      (match e with | .fap f _ => active && f == self && retsVar z cont | _ => false) ||
      hasSelfTailAux self onlyRecJp active cont
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
  | .vdecl _ _ e b => match e with
      | .proj .. | .uproj .. | .sproj .. => hasDecOf p b
      | _ => false
  | _              => false

mutual
def collectProjSrc (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) : FnBody → Std.HashMap Nat Nat
  | .vdecl x _ e b => match e with
      | .fap .. | .ap .. => collectProjSrc (calls.insert x.idx) acc b
      | .proj _ p =>
          collectProjSrc calls (if calls.contains p.idx then acc.insert x.idx p.idx else acc) b
      | _ => collectProjSrc calls acc b
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

/-! ## Deterministic Identifier Minification (`--min`) -/

private def identFirstChars : Array Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList.toArray

private def identRestChars : Array Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toList.toArray

private def encodeIdentRest : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let c := identRestChars[n % 62]!
      if n < 62 then c :: acc
      else encodeIdentRest fuel (n / 62 - 1) (c :: acc)

/-- Bijective base-52/62 short JS identifier (`a`..`z`, `A`..`Z`, `aa`..).
    Never starts with `_` or `$`, so it cannot collide with runtime `$` or internal `_`-prefixed temporaries. -/
def shortIdentAt (idx : Nat) : String :=
  if idx < 52 then
    String.singleton identFirstChars[idx]!
  else
    let n := idx - 52
    let first := identFirstChars[n % 52]!
    let rest := encodeIdentRest (n + 1) (n / 52) []
    String.ofList (first :: rest)

def jsMinReservedSet : Std.HashSet String :=
  let words : List String := [
    "do", "if", "in", "for", "let", "new", "try", "var", "case", "else", "enum", "eval",
    "null", "this", "true", "void", "with", "await", "break", "catch", "class", "const",
    "false", "super", "throw", "while", "yield", "delete", "export", "import", "public",
    "return", "static", "switch", "typeof", "default", "extends", "finally", "package",
    "private", "arguments", "continue", "debugger", "function", "protected", "implements",
    "instanceof", "interface", "Error", "Object", "Array", "BigInt", "String", "Number",
    "Boolean", "Symbol", "Math", "JSON", "Promise", "Map", "Set", "Uint8Array",
    "undefined", "NaN", "Infinity", "globalThis", "window", "document",
    "$", "__step", "__r", "__externs"
  ]
  words.foldl (fun s w => s.insert w) {}

private def nextShortIdentAux (avoid : Std.HashSet String) : Nat → Nat → String × Nat
  | 0, idx => (shortIdentAt idx, idx + 1)
  | fuel + 1, idx =>
      let cand := shortIdentAt idx
      if avoid.contains cand then nextShortIdentAux avoid fuel (idx + 1)
      else (cand, idx + 1)

def nextShortIdent (avoid : Std.HashSet String) (idx : Nat) : String × Nat :=
  nextShortIdentAux avoid (avoid.size + 64) idx

mutual
private def collectLocalArrowsStmt (acc : Std.HashSet String) : JsStmt → Std.HashSet String
  | .constArrow name _ body => collectLocalArrowsStmts (acc.insert name) body
  | .labeledBlock _ body    => collectLocalArrowsStmts acc body
  | .switchStmt _ arms      => collectLocalArrowsArms acc arms
  | _                       => acc

private def collectLocalArrowsStmts (acc : Std.HashSet String) : List JsStmt → Std.HashSet String
  | []      => acc
  | s :: ss => collectLocalArrowsStmts (collectLocalArrowsStmt acc s) ss

private def collectLocalArrowsArms (acc : Std.HashSet String) : List JsSwitchArm → Std.HashSet String
  | []                     => acc
  | .caseArm _ b :: rest   => collectLocalArrowsArms (collectLocalArrowsStmts acc b) rest
  | .defaultArm b :: rest  => collectLocalArrowsArms (collectLocalArrowsStmts acc b) rest
end

mutual
private def collectGlobalsExpr (localArrows : Std.HashSet String) (acc : Std.HashSet String) :
    JsExpr → Std.HashSet String
  | .call fn args =>
      let acc' := if !fn.startsWith "$." && !localArrows.contains fn then acc.insert fn else acc
      collectGlobalsExprs localArrows acc' args
  | .pap fn _ args =>
      let acc' := if !fn.startsWith "$." then acc.insert fn else acc
      collectGlobalsExprs localArrows acc' args
  | .arrLit elems      => collectGlobalsExprs localArrows acc elems
  | .ctorObj _ fs _ _  => collectGlobalsExprs localArrows acc fs
  | .fieldProj o _     => collectGlobalsExpr localArrows acc o
  | .uProj o _         => collectGlobalsExpr localArrows acc o
  | .sProj o _ _       => collectGlobalsExpr localArrows acc o
  | .app fn args       => collectGlobalsExprs localArrows (collectGlobalsExpr localArrows acc fn) args
  | .tc args           => collectGlobalsExprs localArrows acc args
  | _                  => acc

private def collectGlobalsExprs (localArrows : Std.HashSet String) (acc : Std.HashSet String) :
    List JsExpr → Std.HashSet String
  | []      => acc
  | e :: es => collectGlobalsExprs localArrows (collectGlobalsExpr localArrows acc e) es
end

mutual
private def collectGlobalsStmt (localArrows : Std.HashSet String) (acc : Std.HashSet String) :
    JsStmt → Std.HashSet String
  | .letVar _ val          => collectGlobalsExpr localArrows acc val
  | .letBinds binds        => collectGlobalsExprs localArrows acc (binds.map Prod.snd)
  | .labeledBlock _ body   => collectGlobalsStmts localArrows acc body
  | .constArrow _ _ body   => collectGlobalsStmts localArrows acc body
  | .setField _ _ val      => collectGlobalsExpr localArrows acc val
  | .setU _ _ val          => collectGlobalsExpr localArrows acc val
  | .setS _ _ _ val        => collectGlobalsExpr localArrows acc val
  | .ret val               => collectGlobalsExpr localArrows acc val
  | .tailContinue _ args   => collectGlobalsExprs localArrows acc args
  | .breakLabel assigns _  => collectGlobalsExprs localArrows acc (assigns.map Prod.snd)
  | .switchStmt scrut arms => collectGlobalsArms localArrows (collectGlobalsExpr localArrows acc scrut) arms
  | _                      => acc

private def collectGlobalsStmts (localArrows : Std.HashSet String) (acc : Std.HashSet String) :
    List JsStmt → Std.HashSet String
  | []      => acc
  | s :: ss => collectGlobalsStmts localArrows (collectGlobalsStmt localArrows acc s) ss

private def collectGlobalsArms (localArrows : Std.HashSet String) (acc : Std.HashSet String) :
    List JsSwitchArm → Std.HashSet String
  | []                    => acc
  | .caseArm _ b :: rest  => collectGlobalsArms localArrows (collectGlobalsStmts localArrows acc b) rest
  | .defaultArm b :: rest => collectGlobalsArms localArrows (collectGlobalsStmts localArrows acc b) rest
end

private structure MinSt where
  avoid       : Std.HashSet String
  localArrows : Std.HashSet String
  varMap      : Std.HashMap String String := {}
  varIdx      : Nat := 0
  lblMap      : Std.HashMap String String := {}
  lblIdx      : Nat := 0

private def MinSt.mapVar (st : MinSt) (name : String) : String × MinSt :=
  match st.varMap.get? name with
  | some s => (s, st)
  | none   =>
      let (s, idx') := nextShortIdent st.avoid st.varIdx
      (s, { st with varMap := st.varMap.insert name s, varIdx := idx' })

private def MinSt.mapVars (st : MinSt) : List String → List String × MinSt
  | [] => ([], st)
  | x :: xs =>
      let (x', st1) := st.mapVar x
      let (xs', st2) := st1.mapVars xs
      (x' :: xs', st2)

private def MinSt.mapLbl (st : MinSt) (lbl : String) : String × MinSt :=
  match st.lblMap.get? lbl with
  | some s => (s, st)
  | none   =>
      let (s, idx') := nextShortIdent jsMinReservedSet st.lblIdx
      (s, { st with lblMap := st.lblMap.insert lbl s, lblIdx := idx' })

mutual
private def renameExpr (st : MinSt) : JsExpr → JsExpr × MinSt
  | .var name =>
      let (n', st') := st.mapVar name
      (.var n', st')
  | .numLit n      => (.numLit n, st)
  | .bigIntLit n   => (.bigIntLit n, st)
  | .strLit s      => (.strLit s, st)
  | .arrLit elems  =>
      let (es', st') := renameExprs st elems
      (.arrLit es', st')
  | .ctorObj cidx fs hasS hasU =>
      let (fs', st') := renameExprs st fs
      (.ctorObj cidx fs' hasS hasU, st')
  | .fieldProj o i =>
      let (o', st') := renameExpr st o
      (.fieldProj o' i, st')
  | .uProj o i =>
      let (o', st') := renameExpr st o
      (.uProj o' i, st')
  | .sProj o n off =>
      let (o', st') := renameExpr st o
      (.sProj o' n off, st')
  | .call fn args =>
      let (fn', st1) := if st.localArrows.contains fn then st.mapVar fn else (fn, st)
      let (args', st2) := renameExprs st1 args
      (.call fn' args', st2)
  | .pap fn ar args =>
      let (args', st') := renameExprs st args
      (.pap fn ar args', st')
  | .app fn args =>
      let (fn', st1) := renameExpr st fn
      let (args', st2) := renameExprs st1 args
      (.app fn' args', st2)
  | .tc args =>
      let (args', st') := renameExprs st args
      (.tc args', st')

private def renameExprs (st : MinSt) : List JsExpr → List JsExpr × MinSt
  | [] => ([], st)
  | e :: es =>
      let (e', st1) := renameExpr st e
      let (es', st2) := renameExprs st1 es
      (e' :: es', st2)
end

private def renamePairs (st : MinSt) : List (String × JsExpr) → List (String × JsExpr) × MinSt
  | [] => ([], st)
  | (k, e) :: rest =>
      let (k', st1) := st.mapVar k
      let (e', st2) := renameExpr st1 e
      let (rest', st3) := renamePairs st2 rest
      ((k', e') :: rest', st3)

mutual
private def renameStmt (st : MinSt) : JsStmt → JsStmt × MinSt
  | .letVar x val =>
      let (val', st1) := renameExpr st val
      let (x', st2) := st1.mapVar x
      (.letVar x' val', st2)
  | .letDecls names =>
      let (ns', st') := st.mapVars names
      (.letDecls ns', st')
  | .letBinds binds =>
      let (bs', st') := renamePairs st binds
      (.letBinds bs', st')
  | .labeledBlock lbl body =>
      let (lbl', st1) := st.mapLbl lbl
      let (body', st2) := renameStmts st1 body
      (.labeledBlock lbl' body', st2)
  | .constArrow name params body =>
      let (name', st1) := st.mapVar name
      let (ps', st2) := st1.mapVars params
      let (body', st3) := renameStmts st2 body
      (.constArrow name' ps' body', st3)
  | .setField x i val =>
      let (x', st1) := st.mapVar x
      let (val', st2) := renameExpr st1 val
      (.setField x' i val', st2)
  | .setTag x cidx =>
      let (x', st1) := st.mapVar x
      (.setTag x' cidx, st1)
  | .setU x i val =>
      let (x', st1) := st.mapVar x
      let (val', st2) := renameExpr st1 val
      (.setU x' i val', st2)
  | .setS x n off val =>
      let (x', st1) := st.mapVar x
      let (val', st2) := renameExpr st1 val
      (.setS x' n off val', st2)
  | .incRef x n =>
      let (x', st1) := st.mapVar x
      (.incRef x' n, st1)
  | .decRef x n =>
      let (x', st1) := st.mapVar x
      (.decRef x' n, st1)
  | .ret val =>
      let (val', st1) := renameExpr st val
      (.ret val', st1)
  | .tailContinue params args =>
      let (args', st1) := renameExprs st args
      let (ps', st2) := st1.mapVars params
      (.tailContinue ps' args', st2)
  | .breakLabel assigns lbl =>
      let (as', st1) := renamePairs st assigns
      let (lbl', st2) := st1.mapLbl lbl
      (.breakLabel as' lbl', st2)
  | .throwUnreachable => (.throwUnreachable, st)
  | .switchStmt scrut arms =>
      let (scrut', st1) := renameExpr st scrut
      let (arms', st2) := renameArms st1 arms
      (.switchStmt scrut' arms', st2)

private def renameStmts (st : MinSt) : List JsStmt → List JsStmt × MinSt
  | [] => ([], st)
  | s :: ss =>
      let (s', st1) := renameStmt st s
      let (ss', st2) := renameStmts st1 ss
      (s' :: ss', st2)

private def renameArms (st : MinSt) : List JsSwitchArm → List JsSwitchArm × MinSt
  | [] => ([], st)
  | .caseArm cidx b :: rest =>
      let (b', st1) := renameStmts st b
      let (rest', st2) := renameArms st1 rest
      (.caseArm cidx b' :: rest', st2)
  | .defaultArm b :: rest =>
      let (b', st1) := renameStmts st b
      let (rest', st2) := renameArms st1 rest
      (.defaultArm b' :: rest', st2)
end

/-- Deterministically alpha-renames all local variables, parameters, join-point arrow bindings,
    inline join-point slots, and block labels in a lowered `JsDecl` to short base-52/62 names,
    avoiding all JS reserved words, `$`, and any global function names referenced by the body. -/
def minifyDecl : JsDecl → JsDecl
  | d@(.memoInit ..) => d
  | .memoThunk name body =>
      let localArrows := collectLocalArrowsStmts {} body
      let avoid := collectGlobalsStmts localArrows (jsMinReservedSet.insert name) body
      let (body', _) := renameStmts { avoid, localArrows } body
      .memoThunk name body'
  | .fnPlain name orig params body =>
      let localArrows := collectLocalArrowsStmts {} body
      let avoid := collectGlobalsStmts localArrows (jsMinReservedSet.insert name) body
      let (ps', st1) := ({ avoid, localArrows } : MinSt).mapVars params
      let (body', _) := renameStmts st1 body
      .fnPlain name orig ps' body'
  | .fnDirectLoop name orig params body =>
      let localArrows := collectLocalArrowsStmts {} body
      let avoid := collectGlobalsStmts localArrows (jsMinReservedSet.insert name) body
      let (ps', st1) := ({ avoid, localArrows } : MinSt).mapVars params
      let (body', _) := renameStmts st1 body
      .fnDirectLoop name orig ps' body'
  | .fnTrampoline name orig params body =>
      let localArrows := collectLocalArrowsStmts {} body
      let avoid := collectGlobalsStmts localArrows (jsMinReservedSet.insert name) body
      let (ps', st1) := ({ avoid, localArrows } : MinSt).mapVars params
      let (body', _) := renameStmts st1 body
      .fnTrampoline name orig ps' body'

def emitDecl (c0 : Ctx) (d : Decl) : String :=
  match lowerDecl c0 d with
  | some jd => (if c0.min then minifyDecl jd else jd).render c0.min
  | none    => ""

/-! ## Source Map v3 (`.mjs.map`) VLQ Encoder & Generator -/

private def vlqChars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def encodeVlqNatAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc.reverse
  | fuel + 1, u, acc =>
      let digit := u &&& 31
      let rest := u >>> 5
      let encoded := if rest > 0 then digit ||| 32 else digit
      let ch := vlqChars[encoded]!
      if rest == 0 then (ch :: acc).reverse
      else encodeVlqNatAux fuel rest (ch :: acc)

/-- Base64-VLQ encode a signed integer according to the Source Map v3 specification. -/
def encodeVlqInt (v : Int) : String :=
  let u : Nat := if v < 0 then (((-v).toNat) <<< 1) + 1 else (v.toNat) <<< 1
  String.ofList (encodeVlqNatAux 64 u [])

private def vlqCharVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 'A'.toNat ≤ n && n ≤ 'Z'.toNat then some (n - 'A'.toNat)
  else if 'a'.toNat ≤ n && n ≤ 'z'.toNat then some (n - 'a'.toNat + 26)
  else if '0'.toNat ≤ n && n ≤ '9'.toNat then some (n - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

private def decodeVlqAux : List Char → Nat → Nat → Option (Int × List Char)
  | [], _, _ => none
  | c :: cs, shift, acc =>
      match vlqCharVal c with
      | none => none
      | some d =>
          let acc' := acc ||| ((d &&& 31) <<< shift)
          if (d &&& 32) != 0 then
            decodeVlqAux cs (shift + 5) acc'
          else
            let neg := (acc' &&& 1) == 1
            let mag := acc' >>> 1
            let val : Int := if neg then -(Int.ofNat mag) else Int.ofNat mag
            some (val, cs)

/-- Decode a single Base64-VLQ signed integer from a character list (used for round-trip verification). -/
def decodeVlqInt (s : String) : Option Int :=
  match decodeVlqAux s.toList 0 0 with
  | some (v, []) => some v
  | _            => none

private def findDeclRangeAux (env : Environment) : Nat → Name → Option DeclarationRanges
  | 0, _ => none
  | fuel + 1, n =>
      match Lean.declRangeExt.find? env n with
      | some r => some r
      | none =>
          match n with
          | .str p _ => findDeclRangeAux env fuel p
          | .num p _ => findDeclRangeAux env fuel p
          | .anonymous => none

/-- Look up `(sourceFile, origLine0, origCol0, origName)` for a Lean declaration in `env`. -/
def findDeclSourceLoc (env : Environment) (n : Name) : Option (String × Nat × Nat × String) :=
  let modName := definingModule env n
  if modName.isAnonymous then none
  else
    let sourceFile := (modName.toString.replace "." "/") ++ ".lean"
    let (origLine, origCol) := match findDeclRangeAux env 8 n with
      | some r => (if r.range.pos.line > 0 then r.range.pos.line - 1 else 0, r.range.pos.column)
      | none   => (0, 0)
    some (sourceFile, origLine, origCol, n.toString)

private structure DeclMapSpan where
  startLine  : Nat
  lineCount  : Nat
  nameCol    : Nat
  sourceFile : String
  origLine   : Nat
  origCol    : Nat
  origName   : String

private def countNewlines (s : String) : Nat :=
  s.foldl (init := 0) fun acc c => if c == '\n' then acc + 1 else acc

private def declNameColOffset : JsDecl → Nat
  | .memoInit .. | .memoThunk .. => 6  -- after "const "
  | .fnPlain .. | .fnDirectLoop .. | .fnTrampoline .. => 9  -- after "function "

/-- Render a valid Source Map v3 JSON string for `fileName` given per-declaration line spans. -/
private def buildSourceMapV3 (fileName : String) (totalLines : Nat) (spans : Array DeclMapSpan) : String := Id.run do
  let mut sources : Array String := #[]
  let mut sourceIdx : Std.HashMap String Nat := {}
  let mut names : Array String := #[]
  let mut nameIdx : Std.HashMap String Nat := {}
  -- Per-line mapping info: `(srcIdx, origLine, origCol, optNameIdx, optNameCol)`
  let mut lineMap : Std.HashMap Nat (Nat × Nat × Nat × Option Nat × Nat) := {}
  for sp in spans do
    let sIdx ← match sourceIdx.get? sp.sourceFile with
      | some i => pure i
      | none   =>
          let i := sources.size
          sources := sources.push sp.sourceFile
          sourceIdx := sourceIdx.insert sp.sourceFile i
          pure i
    let nIdx ← match nameIdx.get? sp.origName with
      | some i => pure i
      | none   =>
          let i := names.size
          names := names.push sp.origName
          nameIdx := nameIdx.insert sp.origName i
          pure i
    lineMap := lineMap.insert sp.startLine (sIdx, sp.origLine, sp.origCol, some nIdx, sp.nameCol)
    if sp.lineCount > 1 then
      for off in [1:sp.lineCount] do
        lineMap := lineMap.insert (sp.startLine + off) (sIdx, sp.origLine, sp.origCol, none, 0)

  let mut prevSrc : Int := 0
  let mut prevOrigLine : Int := 0
  let mut prevOrigCol : Int := 0
  let mut prevName : Int := 0
  let mut mapChunks : Array String := #[]
  for lineIdx in [0:totalLines] do
    if lineIdx > 0 then
      mapChunks := mapChunks.push ";"
    if let some (sIdx, oLine, oCol, nIdx?, nameCol) := lineMap.get? lineIdx then
      let sI := Int.ofNat sIdx
      let lI := Int.ofNat oLine
      let cI := Int.ofNat oCol
      -- Segment 1 at generated column 0
      let seg1 :=
        encodeVlqInt 0 ++
        encodeVlqInt (sI - prevSrc) ++
        encodeVlqInt (lI - prevOrigLine) ++
        encodeVlqInt (cI - prevOrigCol) ++
        match nIdx? with
        | some ni => encodeVlqInt (Int.ofNat ni - prevName)
        | none    => ""
      prevSrc := sI
      prevOrigLine := lI
      prevOrigCol := cI
      if let some ni := nIdx? then
        prevName := Int.ofNat ni
      mapChunks := mapChunks.push seg1
      -- Segment 2 at function/const identifier column on declaration header lines
      if nameCol > 0 then
        let seg2 :=
          "," ++
          encodeVlqInt (Int.ofNat nameCol) ++
          encodeVlqInt 0 ++
          encodeVlqInt 0 ++
          encodeVlqInt 0 ++
          match nIdx? with
          | some _ => encodeVlqInt 0
          | none   => ""
        mapChunks := mapChunks.push seg2

  let sourcesJson := String.intercalate "," (sources.toList.map jsStr)
  let namesJson := String.intercalate "," (names.toList.map jsStr)
  let mappingsStr := joinChunks mapChunks
  return s!"\{\"version\":3,\"file\":{jsStr fileName},\"sources\":[{sourcesJson}],\"names\":[{namesJson}],\"mappings\":{jsStr mappingsStr}}\n"

def collectProgramExterns (env : Environment) (roots : List Name) :
    Except String (Array Name × List String) := do
  let names ← reach env roots #[]
  verifyReachable env names
  verifyNoServerLeakInClient env names
  let mut externSet : Std.HashSet String := {}
  for n in names do
    match findEnvDecl env n with
    | some (.fdecl ..) => pure ()
    | some (.extern ..) => externSet := externSet.insert (mangle n)
    | none => throw s!"no IR for `{n}` (not compiled?)"
  let externNames := externSet.toList.mergeSort (· < ·)
  return (names, externNames)

private def assignTopLevelNames (env : Environment) (names : Array Name)
    (entries : List (Name × String)) (min : Bool) : Std.HashMap Name String := Id.run do
  let entryMap : Std.HashMap Name String := entries.foldl (fun m e => m.insert e.1 e.2) {}
  let mut nm : Std.HashMap Name String := {}
  if !min then
    let mut counter := 0
    for n in names do
      match findEnvDecl env n with
      | some (.fdecl ..) =>
          match entryMap.get? n with
          | some s => nm := nm.insert n s
          | none   => nm := nm.insert n s!"_g{counter}"; counter := counter + 1
      | _ => pure ()
    return nm

  -- In `--min` mode, assign deterministic short base-52/62 names to internal declarations,
  -- prioritizing the most-referenced declarations for 1-character names while preserving exports.
  let mut avoid : Std.HashSet String := jsMinReservedSet
  for (_, s) in entries do
    avoid := avoid.insert s
  let mut refCounts : Std.HashMap Name Nat := {}
  for n in names do
    match findEnvDecl env n with
    | some (.fdecl (body := b) ..) =>
        for callee in callees b #[] do
          refCounts := refCounts.insert callee ((refCounts.getD callee 0) + 1)
        if let some initFn := getInitFnNameFor? env n then
          refCounts := refCounts.insert initFn ((refCounts.getD initFn 0) + 1)
    | _ => pure ()
  let mut internals : Array (Nat × Nat × Name) := #[]
  let mut orderIdx := 0
  for n in names do
    match findEnvDecl env n with
    | some (.fdecl ..) =>
        match entryMap.get? n with
        | some s => nm := nm.insert n s
        | none   =>
            internals := internals.push (refCounts.getD n 0, orderIdx, n)
            orderIdx := orderIdx + 1
    | _ => pure ()
  let sorted := internals.qsort fun a b =>
    a.1 > b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let mut idIdx := 0
  for (_, _, n) in sorted do
    let (shortName, nextIdx) := nextShortIdent avoid idIdx
    nm := nm.insert n shortName
    avoid := avoid.insert shortName
    idIdx := nextIdx
  return nm

def emitProgramWithSourceMap (env : Environment) (entries : List (Name × String))
    (min : Bool := false) (fileName : String := "app.mjs") (sourceMapUrl? : Option String := none) :
    Except String (String × String × List String) := do
  let roots := entries.map (·.1)
  let (names, externNames) ← collectProgramExterns env roots
  let nm := assignTopLevelNames env names entries min
  let c : Ctx := { env, names := nm, min }
  let hdr := if min then "" else "// GENERATED by Js.Backend (Lean-IR → JS). Do not edit.\n"
  let imp := "import * as $ from './qed_rt.mjs';\n"
  let mut chunks : Array String := #[hdr, imp]
  let mut curLine : Nat := countNewlines hdr + countNewlines imp
  let mut spans : Array DeclMapSpan := #[]
  let wantMap := sourceMapUrl?.isSome || !fileName.isEmpty
  for n in names do
    match findEnvDecl env n with
    | some d@(.fdecl ..) =>
        match lowerDecl c d with
        | some jd0 =>
            let jd := if min then minifyDecl jd0 else jd0
            let s := jd.render min
            if !s.isEmpty then
              let nLines := countNewlines s
              if wantMap then
                if let some (srcFile, oLine, oCol, oName) := findDeclSourceLoc env n then
                  spans := spans.push {
                    startLine := curLine
                    lineCount := nLines
                    nameCol := declNameColOffset jd
                    sourceFile := srcFile
                    origLine := oLine
                    origCol := oCol
                    origName := oName
                  }
              chunks := chunks.push s
              curLine := curLine + nLines
        | none => pure ()
    | _ => pure ()
  let exportList := entries.map fun (n, s) =>
    let loc := c.js n
    if loc == s then s else s!"{loc} as {s}"
  let exportChunk :=
    if min then "export{" ++ String.intercalate "," exportList ++ "};\n"
    else "\nexport { " ++ String.intercalate ", " exportList ++ " };\n"
  let externsChunk :=
    if min then "export const __externs=[" ++ String.intercalate "," (externNames.map (s!"\"{·}\"")) ++ "];\n"
    else "export const __externs = [" ++ String.intercalate ", " (externNames.map (s!"\"{·}\"")) ++ "];\n"
  chunks := chunks.push exportChunk
  chunks := chunks.push externsChunk
  curLine := curLine + countNewlines exportChunk + countNewlines externsChunk
  if let some mapUrl := sourceMapUrl? then
    let mapComment := s!"//# sourceMappingURL={mapUrl}\n"
    chunks := chunks.push mapComment
    curLine := curLine + 1
  let sourceMap := buildSourceMapV3 fileName curLine spans
  return (joinChunks chunks, sourceMap, externNames)

def emitProgramWithExterns (env : Environment) (entries : List (Name × String)) (min : Bool := false) :
    Except String (String × List String) := do
  let (js, _, externNames) ← emitProgramWithSourceMap env entries min "" none
  return (js, externNames)

private def skipLine : List Char → List Char
  | [] => []
  | '\n' :: t => t
  | _ :: t => skipLine t

private def skipBlock : List Char → List Char
  | [] => []
  | '*' :: '/' :: t => t
  | _ :: t => skipBlock t

private def skipQuoted (q : Char) : List Char → List Char
  | [] => []
  | '\\' :: _ :: t => skipQuoted q t
  | c :: t => if c == q then t else skipQuoted q t

private def takeJsIdent (acc : String) : List Char → String × List Char
  | c :: cs => if c.isAlphanum || c == '_' || c == '$' then takeJsIdent (acc.push c) cs else (acc, c :: cs)
  | [] => (acc, [])

private def nextRtToken : Nat → List Char → Option (String ⊕ Char) × List Char
  | 0, _ | _ + 1, [] => (none, [])
  | fuel + 1, c :: cs =>
      if c.isWhitespace then nextRtToken fuel cs
      else if c == '/' then
        match cs with
        | '/' :: t => nextRtToken fuel (skipLine t)
        | '*' :: t => nextRtToken fuel (skipBlock t)
        | _        => (some (.inr c), cs)
      else if c == '"' || c == '\'' || c == '`' then nextRtToken fuel (skipQuoted c cs)
      else if c.isAlpha || c == '_' || c == '$' then
        let (id, rest) := takeJsIdent (String.singleton c) cs
        (some (.inl id), rest)
      else (some (.inr c), cs)

private inductive ExportMode where
  | none | afterExport | afterAsync | afterFn
  | inVar (expectName : Bool)
  | inBrace (expectName : Bool) (pending : Option String)

private def stepBraceDepth (d : Nat) : String ⊕ Char → Nat
  | .inr '(' | .inr '[' | .inr '{' => d + 1
  | .inr ')' | .inr ']' | .inr '}' => d - 1
  | _ => d

private def walkRtExports (fuel depth : Nat) (mode : ExportMode)
    (cs : List Char) (acc : Std.HashSet String) : Std.HashSet String :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      match nextRtToken (fuel + 1) cs with
      | (none, _) => acc
      | (some tok, rest) =>
          let addOpt (a : Std.HashSet String) : Option String → Std.HashSet String
            | some s => a.insert s
            | none   => a
          match mode with
          | .none =>
              if depth == 0 && tok == .inl "export" then walkRtExports fuel 0 .afterExport rest acc
              else walkRtExports fuel (stepBraceDepth depth tok) .none rest acc
          | .afterExport =>
              match tok with
              | .inl "function" => walkRtExports fuel 0 .afterFn rest acc
              | .inl "async"    => walkRtExports fuel 0 .afterAsync rest acc
              | .inl "const" | .inl "let" | .inl "var" => walkRtExports fuel 0 (.inVar true) rest acc
              | .inr '{'        => walkRtExports fuel 1 (.inBrace true none) rest acc
              | _               => walkRtExports fuel (stepBraceDepth depth tok) .none rest acc
          | .afterAsync =>
              match tok with
              | .inl "function" => walkRtExports fuel 0 .afterFn rest acc
              | _               => walkRtExports fuel (stepBraceDepth depth tok) .none rest acc
          | .afterFn =>
              match tok with
              | .inl name => walkRtExports fuel 0 .none rest (acc.insert name)
              | _         => walkRtExports fuel (stepBraceDepth depth tok) .none rest acc
          | .inVar expectName =>
              if depth == 0 then
                match tok with
                | .inr ';' => walkRtExports fuel 0 .none rest acc
                | .inr ',' => walkRtExports fuel 0 (.inVar true) rest acc
                | .inl "export" =>
                    if expectName then walkRtExports fuel 0 (.inVar false) rest (acc.insert "export")
                    else walkRtExports fuel 0 .afterExport rest acc
                | .inl name =>
                    walkRtExports fuel 0 (.inVar false) rest (if expectName then acc.insert name else acc)
                | _ => walkRtExports fuel (stepBraceDepth 0 tok) (.inVar expectName) rest acc
              else
                walkRtExports fuel (stepBraceDepth depth tok) (.inVar expectName) rest acc
          | .inBrace expectName pending =>
              match tok with
              | .inr '}' => walkRtExports fuel 0 .none rest (addOpt acc pending)
              | .inr ',' => walkRtExports fuel depth (.inBrace true none) rest (addOpt acc pending)
              | .inl "as" => walkRtExports fuel depth (.inBrace true none) rest acc
              | .inl name =>
                  if expectName then walkRtExports fuel depth (.inBrace false (some name)) rest acc
                  else walkRtExports fuel depth (.inBrace false pending) rest acc
              | _ => walkRtExports fuel depth (.inBrace expectName pending) rest acc

/-- Parse named ESM exports (`export const`, `export function`, `export { ... }`) from a JS runtime module. -/
def rtExports (rtSrc : String) : Std.HashSet String :=
  let cs := rtSrc.toList
  walkRtExports (cs.length + 1) 0 .none cs {}

/-- Verify that every extern name in `externNames` is present in `avail` (parsed from `runtime/qed_rt.mjs`). -/
def checkRtExterns (avail : Std.HashSet String) (externNames : List String) : Except String Unit := do
  let missing := externNames.filter (!avail.contains ·)
  if !missing.isEmpty then
    throw s!"qed_rt: missing externs: {String.intercalate ", " missing}"

end Js
