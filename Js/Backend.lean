-- Runtime representation (matches `qed_rt.mjs`; recheck on Lean bumps, see `docs/upgrading-lean.md`):
-- Int/Nat/UInt64 → BigInt; UInt8/16/32/USize/Bool/nullary-ctor → Number; String → JS string (UTF-8 byte Pos);
-- Array → JS Array with refcount `.r`; ctor w/ fields → `{t, f, s, u}`; closure → `{fn, arity, args}`;
-- BaseIO returns raw values, EIO/IO wraps in single-field `EST.Out` (`{t:0|1, f:[v]}`).
import Lean
import Js.VerifyEnv
open Lean IR

namespace Js

def mangle (n : Name) : String :=
  n.toString.foldl (init := "") fun s c =>
    if c.isAlphanum then s.push c
    else if c == '.' || c == '_' then s.push '_'
    else s ++ s!"x{c.toNat}"

def soff (n offset : Nat) : String := s!"\"{n}_{offset}\""

def jsStrChar (c : Char) : String :=
  match c with
  | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
  | c =>
    if c.toNat < 32 then
      let h := Nat.toDigits 16 c.toNat
      "\\x" ++ String.ofList (if h.length == 1 then '0' :: h else h)
    else String.singleton c

def jsStr (s : String) : String :=
  "\"" ++ s.foldl (init := "") (fun acc c => acc ++ jsStrChar c) ++ "\""

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

private def fmtTokens (min : Bool) : String × String × String × String :=
  if min then ("", "", ",", "=") else (" ", "\n", ", ", " = ")

mutual
def JsExpr.renderMin (min : Bool) : JsExpr → String
  | .var name         => name
  | .numLit n         => toString n
  | .bigIntLit n      => s!"{n}n"
  | .strLit s         => jsStr s
  | .arrLit elems     => s!"[{JsExpr.renderListMin min elems}]"
  | .ctorObj cidx fields hasS hasU =>
      let sp := if min then "" else " "
      let s := if hasS then s!",{sp}s:{sp}" ++ "{}" else ""
      let u := if hasU then s!",{sp}u:{sp}" ++ "{}" else ""
      s!"\{t:{sp}{cidx},{sp}f:{sp}[{JsExpr.renderListMin min fields}]{s}{u}}"
  | .fieldProj obj i  => s!"{obj.renderMin min}.f[{i}]"
  | .uProj obj i      => s!"{obj.renderMin min}.u[{i}]"
  | .sProj obj n off  => s!"{obj.renderMin min}.s[{soff n off}]"
  | .call fn args     => s!"{fn}({JsExpr.renderListMin min args})"
  | .pap fn ar args   =>
      let sep := if min then "," else ", "
      s!"$.pap({fn}{sep}{ar}{sep}[{JsExpr.renderListMin min args}])"
  | .app fn args      =>
      let sep := if min then "," else ", "
      s!"$.app({fn.renderMin min}{sep}[{JsExpr.renderListMin min args}])"
  | .tc args          => s!"$.tc([{JsExpr.renderListMin min args}])"

def JsExpr.renderListMin (min : Bool) (es : List JsExpr) : String :=
  go #[] es
where
  go (acc : Array String) : List JsExpr → String
    | []      => joinChunks acc
    | [e]     => joinChunks (acc.push (e.renderMin min))
    | e :: es => go ((acc.push (e.renderMin min)).push (if min then "," else ", ")) es
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
def JsStmt.render (min : Bool) (d : Nat) (s : JsStmt) : String :=
  let ind := indStr min d
  let (sp, nl, sep, eq) := fmtTokens min
  match s with
  | .letVar x val => s!"{ind}let {x}{eq}{val.renderMin min};{nl}"
  | .letDecls names =>
      if names.isEmpty then "" else s!"{ind}let {String.intercalate sep names};{nl}"
  | .letBinds binds =>
      if binds.isEmpty then ""
      else s!"{ind}let {String.intercalate sep (binds.map fun (k, e) => s!"{k}{eq}{e.renderMin min}")};{nl}"
  | .labeledBlock lbl body =>
      s!"{ind}{lbl}:{sp}\{{nl}{JsStmt.renderListAux min (d + 1) #[] body}{ind}}{nl}"
  | .constArrow name params body =>
      s!"{ind}const {name}{eq}({String.intercalate sep params}){sp}=>{sp}\{{nl}{JsStmt.renderListAux min (d + 1) #[] body}{ind}};{nl}"
  | .setField x i val => s!"{ind}{x}.f[{i}]{eq}{val.renderMin min};{nl}"
  | .setTag x cidx => s!"{ind}{x}.t{eq}{cidx};{nl}"
  | .setU x i val => s!"{ind}{x}.u[{i}]{eq}{val.renderMin min};{nl}"
  | .setS x n off val => s!"{ind}{x}.s[{soff n off}]{eq}{val.renderMin min};{nl}"
  | .incRef x n => s!"{ind}$.inc({x}{sep}{n});{nl}"
  | .decRef x n => s!"{ind}$.dec({x}{sep}{n});{nl}"
  | .ret val => s!"{ind}return {val.renderMin min};{nl}"
  | .tailContinue params args =>
      if args.isEmpty then s!"{ind}continue;{nl}"
      else match min, params, args with
      | true, [p], [a] => s!"\{{p}={a.renderMin true};continue;}"
      | _, _, _ =>
          let tp := if min then "_" else "_t"
          let tmps := String.intercalate sep (args.zipIdx.map fun (a, i) => s!"{tp}{i}{eq}{a.renderMin min}")
          let assigns := String.intercalate sp (params.zipIdx.map fun (p, i) => s!"{p}{eq}{tp}{i};")
          s!"{ind}\{{sp}let {tmps};{sp}{assigns}{sp}continue;{sp}}{nl}"
  | .breakLabel assigns lbl =>
      let assignStr := String.intercalate sp (assigns.map fun (lhs, rhs) => s!"{lhs}{eq}{rhs.renderMin min};")
      let pfx := if assignStr.isEmpty then "" else assignStr ++ sp
      s!"{ind}{pfx}break {lbl};{nl}"
  | .throwUnreachable => s!"{ind}throw new Error('unreachable');{nl}"
  | .switchStmt scrut arms =>
      s!"{ind}switch{sp}({scrut.renderMin min}){sp}\{{nl}{JsSwitchArm.renderListAux min (d + 1) #[] arms}{ind}}{nl}"

def JsStmt.renderListAux (min : Bool) (d : Nat) (acc : Array String) : List JsStmt → String
  | []      => joinChunks acc
  | s :: ss => JsStmt.renderListAux min d (acc.push (s.render min d)) ss

def JsSwitchArm.render (min : Bool) (d : Nat) : JsSwitchArm → String
  | .caseArm cidx body =>
      let (sp, nl, _, _) := fmtTokens min; let ind := indStr min d
      s!"{ind}case {cidx}:{sp}\{{nl}{JsStmt.renderListAux min (d + 1) #[] body}{ind}}{nl}"
  | .defaultArm body =>
      let (sp, nl, _, _) := fmtTokens min; let ind := indStr min d
      s!"{ind}default:{sp}\{{nl}{JsStmt.renderListAux min (d + 1) #[] body}{ind}}{nl}"

def JsSwitchArm.renderListAux (min : Bool) (d : Nat) (acc : Array String) : List JsSwitchArm → String
  | []      => joinChunks acc
  | a :: as => JsSwitchArm.renderListAux min d (acc.push (a.render min d)) as
end

def JsStmt.renderList (min : Bool) (d : Nat) (ss : List JsStmt) : String :=
  JsStmt.renderListAux min d #[] ss

inductive JsDecl where
  | memoInit     (name : String) (initFn : String)
  | memoThunk    (name : String) (body : List JsStmt)
  | fnPlain      (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnDirectLoop (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnTrampoline (name : String) (origName : Name) (params : List String) (body : List JsStmt)

private def fnHeader (min : Bool) (name : String) (orig : Name) (params : List String) : String :=
  if min then s!"function {name}({String.intercalate "," params})\{"
  else s!"function {name}({String.intercalate ", " params}) /* {orig} */ \{\n"

def JsDecl.render (min : Bool) (d : JsDecl) : String :=
  let (sp, nl, sep, eq) := fmtTokens min
  match d with
  | .memoInit name initFn =>
      s!"const {name}{eq}$.memo((){sp}=>{sp}$.ioVal({initFn}(0)));\n"
  | .memoThunk name body =>
      s!"const {name}{eq}$.memo((){sp}=>{sp}\{{nl}{JsStmt.renderList min 1 body}});\n"
  | .fnPlain name orig params body =>
      fnHeader min name orig params ++ JsStmt.renderList min 1 body ++ "}\n"
  | .fnDirectLoop name orig params body =>
      let w := if min then "while(1){" else s!"{indStr false 1}while (true) \{\n"
      fnHeader min name orig params ++ w ++ JsStmt.renderList min 2 body ++ s!"{indStr min 1}}{nl}}\n"
  | .fnTrampoline name orig params body =>
      let ps := String.intercalate sep params
      let (ind1, ind2) := (indStr min 1, indStr min 2)
      let (sf, rv, und, wt) := if min then ("_s", "_r", "void 0", "while(1){") else ("__step", "__r", "undefined", "while (true) {\n")
      fnHeader min name orig params ++
        s!"{ind1}const {sf}{eq}(){sp}=>{sp}\{{nl}{JsStmt.renderList min 2 body}{ind1}};{nl}" ++
        s!"{ind1}{wt}{ind2}const {rv}{eq}{sf}();{nl}" ++
        s!"{ind2}if{sp}({rv}{sp}!=={sp}null{sp}&&{sp}typeof {rv}{sp}==={sp}\"object\"{sp}&&{sp}{rv}.__tc{sp}!=={sp}{und}){sp}\{{sp}[{ps}]{eq}{rv}.__tc;{sp}continue;{sp}}{nl}" ++
        s!"{ind2}return {rv};{nl}{ind1}}{nl}}\n"

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

private def identChars : Array Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toList.toArray

private def encodeIdentRest : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let c := identChars[n % 62]!
      if n < 62 then c :: acc
      else encodeIdentRest fuel (n / 62 - 1) (c :: acc)

/-- Bijective base-52/62 short JS identifier (`a`..`z`, `A`..`Z`, `aa`..).
    Never starts with `_` or `$`, so it cannot collide with runtime `$` or internal `_`-prefixed temporaries. -/
def shortIdentAt (idx : Nat) : String :=
  if idx < 52 then String.singleton identChars[idx]!
  else
    let n := idx - 52
    String.ofList (identChars[n % 52]! :: encodeIdentRest (n + 1) (n / 52) [])

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

private structure MinScan where
  localArrows : Std.HashSet String := {}
  called      : Std.HashSet String := {}
  avoid       : Std.HashSet String

mutual
private def scanMinExpr (acc : MinScan) : JsExpr → MinScan
  | .call fn args =>
      let acc := if !fn.startsWith "$." then { acc with called := acc.called.insert fn } else acc
      scanMinExprs acc args
  | .pap fn _ args =>
      let acc := if !fn.startsWith "$." then { acc with avoid := acc.avoid.insert fn } else acc
      scanMinExprs acc args
  | .arrLit elems | .ctorObj _ elems _ _ | .tc elems => scanMinExprs acc elems
  | .fieldProj o _ | .uProj o _ | .sProj o _ _ => scanMinExpr acc o
  | .app fn args => scanMinExprs (scanMinExpr acc fn) args
  | _ => acc

private def scanMinExprs (acc : MinScan) : List JsExpr → MinScan
  | []      => acc
  | e :: es => scanMinExprs (scanMinExpr acc e) es
end

mutual
private def scanMinStmt (acc : MinScan) : JsStmt → MinScan
  | .letVar _ val | .setField _ _ val | .setU _ _ val | .setS _ _ _ val | .ret val => scanMinExpr acc val
  | .letBinds binds | .breakLabel binds _ => scanMinExprs acc (binds.map Prod.snd)
  | .labeledBlock _ body => scanMinStmts acc body
  | .constArrow name _ body => scanMinStmts { acc with localArrows := acc.localArrows.insert name } body
  | .tailContinue _ args => scanMinExprs acc args
  | .switchStmt scrut arms => scanMinArms (scanMinExpr acc scrut) arms
  | _ => acc

private def scanMinStmts (acc : MinScan) : List JsStmt → MinScan
  | []      => acc
  | s :: ss => scanMinStmts (scanMinStmt acc s) ss

private def scanMinArms (acc : MinScan) : List JsSwitchArm → MinScan
  | [] => acc
  | .caseArm _ b :: rest | .defaultArm b :: rest => scanMinArms (scanMinStmts acc b) rest
end

private structure MinSt where
  avoid       : Std.HashSet String
  localArrows : Std.HashSet String
  varMap      : Std.HashMap String String := {}
  varIdx      : Nat := 0
  lblMap      : Std.HashMap String String := {}
  lblIdx      : Nat := 0

private abbrev MinM := StateM MinSt

private def internShort (avoid : Std.HashSet String) (m : Std.HashMap String String) (idx : Nat) (k : String) :
    String × Std.HashMap String String × Nat :=
  match m.get? k with
  | some s => (s, m, idx)
  | none   => let (s, idx') := nextShortIdent avoid idx; (s, m.insert k s, idx')

private def mapVarM (name : String) : MinM String := modifyGet fun st =>
  let (s, m, i) := internShort st.avoid st.varMap st.varIdx name
  (s, { st with varMap := m, varIdx := i })

private def mapLblM (lbl : String) : MinM String := modifyGet fun st =>
  let (s, m, i) := internShort jsMinReservedSet st.lblMap st.lblIdx lbl
  (s, { st with lblMap := m, lblIdx := i })

mutual
private def renameExpr : JsExpr → MinM JsExpr
  | .var name => return .var (← mapVarM name)
  | .arrLit elems => return .arrLit (← renameExprs elems)
  | .ctorObj cidx fs hasS hasU => return .ctorObj cidx (← renameExprs fs) hasS hasU
  | .fieldProj o i => return .fieldProj (← renameExpr o) i
  | .uProj o i => return .uProj (← renameExpr o) i
  | .sProj o n off => return .sProj (← renameExpr o) n off
  | .call fn args => do
      let fn' ← if (← get).localArrows.contains fn then mapVarM fn else pure fn
      return .call fn' (← renameExprs args)
  | .pap fn ar args => return .pap fn ar (← renameExprs args)
  | .app fn args => return .app (← renameExpr fn) (← renameExprs args)
  | .tc args => return .tc (← renameExprs args)
  | e => return e

private def renameExprs : List JsExpr → MinM (List JsExpr)
  | [] => return []
  | e :: es => return (← renameExpr e) :: (← renameExprs es)
end

private def renamePairs (ps : List (String × JsExpr)) : MinM (List (String × JsExpr)) :=
  ps.mapM fun (k, e) => return (← mapVarM k, ← renameExpr e)

mutual
private def renameStmt : JsStmt → MinM JsStmt
  | .letVar x val => do
      let val' ← renameExpr val
      return .letVar (← mapVarM x) val'
  | .letDecls names => return .letDecls (← names.mapM mapVarM)
  | .letBinds binds => return .letBinds (← renamePairs binds)
  | .labeledBlock lbl body => return .labeledBlock (← mapLblM lbl) (← renameStmts body)
  | .constArrow name params body =>
      return .constArrow (← mapVarM name) (← params.mapM mapVarM) (← renameStmts body)
  | .setField x i val => return .setField (← mapVarM x) i (← renameExpr val)
  | .setTag x cidx => return .setTag (← mapVarM x) cidx
  | .setU x i val => return .setU (← mapVarM x) i (← renameExpr val)
  | .setS x n off val => return .setS (← mapVarM x) n off (← renameExpr val)
  | .incRef x n => return .incRef (← mapVarM x) n
  | .decRef x n => return .decRef (← mapVarM x) n
  | .ret val => return .ret (← renameExpr val)
  | .tailContinue params args => do
      let args' ← renameExprs args
      return .tailContinue (← params.mapM mapVarM) args'
  | .breakLabel assigns lbl => return .breakLabel (← renamePairs assigns) (← mapLblM lbl)
  | .throwUnreachable => return .throwUnreachable
  | .switchStmt scrut arms => return .switchStmt (← renameExpr scrut) (← renameArms arms)

private def renameStmts : List JsStmt → MinM (List JsStmt)
  | [] => return []
  | s :: ss => return (← renameStmt s) :: (← renameStmts ss)

private def renameArms : List JsSwitchArm → MinM (List JsSwitchArm)
  | [] => return []
  | .caseArm cidx b :: rest => return .caseArm cidx (← renameStmts b) :: (← renameArms rest)
  | .defaultArm b :: rest => return .defaultArm (← renameStmts b) :: (← renameArms rest)
end

private def minifyFnBody (name : String) (params : List String) (body : List JsStmt) :
    List String × List JsStmt :=
  let sc := scanMinStmts { avoid := jsMinReservedSet.insert name } body
  let avoid := sc.called.fold (fun a fn => if sc.localArrows.contains fn then a else a.insert fn) sc.avoid
  ((do return (← params.mapM mapVarM, ← renameStmts body)).run { avoid, localArrows := sc.localArrows }).1

/-- Deterministically alpha-renames all local variables, parameters, join-point arrow bindings,
    inline join-point slots, and block labels in a lowered `JsDecl` to short base-52/62 names,
    avoiding all JS reserved words, `$`, and any global function names referenced by the body. -/
def minifyDecl : JsDecl → JsDecl
  | d@(.memoInit ..) => d
  | .memoThunk name body => .memoThunk name (minifyFnBody name [] body).2
  | .fnPlain name orig params body => let (ps, b) := minifyFnBody name params body; .fnPlain name orig ps b
  | .fnDirectLoop name orig params body => let (ps, b) := minifyFnBody name params body; .fnDirectLoop name orig ps b
  | .fnTrampoline name orig params body => let (ps, b) := minifyFnBody name params body; .fnTrampoline name orig ps b

/-! ## Source Map v3 (`.mjs.map`) VLQ Encoder & Generator -/

private def vlqChars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def encodeVlqNatAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc.reverse
  | fuel + 1, u, acc =>
      let rest := u >>> 5
      let ch := vlqChars[if rest > 0 then (u &&& 31) ||| 32 else u &&& 31]!
      if rest == 0 then (ch :: acc).reverse else encodeVlqNatAux fuel rest (ch :: acc)

/-- Base64-VLQ encode a signed integer according to the Source Map v3 specification. -/
def encodeVlqInt (v : Int) : String :=
  let u : Nat := if v < 0 then (((-v).toNat) <<< 1) + 1 else (v.toNat) <<< 1
  String.ofList (encodeVlqNatAux 64 u [])

/-- Decode a single Base64-VLQ signed integer from a character list (used for round-trip verification). -/
def decodeVlqInt (s : String) : Option Int := Id.run do
  let mut shift := 0
  let mut acc := 0
  let mut done := false
  for c in s.toList do
    if done then return none
    let some d := vlqChars.idxOf? c | return none
    acc := acc ||| ((d &&& 31) <<< shift)
    if (d &&& 32) != 0 then shift := shift + 5 else done := true
  if !done then return none
  return some (if (acc &&& 1) == 1 then -(Int.ofNat (acc >>> 1)) else Int.ofNat (acc >>> 1))

/-- Look up `(sourceFile, origLine0, origCol0, origName)` for a Lean declaration in `env`. -/
def findDeclSourceLoc (env : Environment) (n : Name) : Option (String × Nat × Nat × String) := Id.run do
  let modName := definingModule env n
  if modName.isAnonymous then return none
  let mut cur := n
  let mut range? : Option DeclarationRanges := none
  for _ in [0:8] do
    if let some r := Lean.declRangeExt.find? env cur then range? := some r; break
    match cur with
    | .str p _ | .num p _ => cur := p
    | .anonymous => break
  let (origLine, origCol) := match range? with
    | some r => (r.range.pos.line - 1, r.range.pos.column)
    | none   => (0, 0)
  return some ((modName.toString.replace "." "/") ++ ".lean", origLine, origCol, n.toString)

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

private def internIdx (arr : Array String) (idx : Std.HashMap String Nat) (s : String) :
    Nat × Array String × Std.HashMap String Nat :=
  match idx.get? s with
  | some i => (i, arr, idx)
  | none   => let i := arr.size; (i, arr.push s, idx.insert s i)

/-- Render a valid Source Map v3 JSON string for `fileName` given per-declaration line spans. -/
private def buildSourceMapV3 (fileName : String) (totalLines : Nat) (spans : Array DeclMapSpan) : String := Id.run do
  let mut sources : Array String := #[]
  let mut sourceIdx : Std.HashMap String Nat := {}
  let mut names : Array String := #[]
  let mut nameIdx : Std.HashMap String Nat := {}
  -- Per-line mapping info: `(srcIdx, origLine, origCol, optNameIdx, optNameCol)`
  let mut lineMap : Std.HashMap Nat (Nat × Nat × Nat × Option Nat × Nat) := {}
  for sp in spans do
    let (sIdx, sources', sourceIdx') := internIdx sources sourceIdx sp.sourceFile
    sources := sources'; sourceIdx := sourceIdx'
    let (nIdx, names', nameIdx') := internIdx names nameIdx sp.origName
    names := names'; nameIdx := nameIdx'
    lineMap := lineMap.insert sp.startLine (sIdx, sp.origLine, sp.origCol, some nIdx, sp.nameCol)
    for off in [1:sp.lineCount] do
      lineMap := lineMap.insert (sp.startLine + off) (sIdx, sp.origLine, sp.origCol, none, 0)

  let mut prevSrc : Int := 0
  let mut prevOrigLine : Int := 0
  let mut prevOrigCol : Int := 0
  let mut prevName : Int := 0
  let mut mapChunks : Array String := #[]
  for lineIdx in [0:totalLines] do
    if lineIdx > 0 then mapChunks := mapChunks.push ";"
    if let some (sIdx, oLine, oCol, nIdx?, nameCol) := lineMap.get? lineIdx then
      let (sI, lI, cI) := (Int.ofNat sIdx, Int.ofNat oLine, Int.ofNat oCol)
      let nameVlq := match nIdx? with | some ni => encodeVlqInt (Int.ofNat ni - prevName) | none => ""
      mapChunks := mapChunks.push ("A" ++ encodeVlqInt (sI - prevSrc) ++ encodeVlqInt (lI - prevOrigLine) ++ encodeVlqInt (cI - prevOrigCol) ++ nameVlq)
      prevSrc := sI; prevOrigLine := lI; prevOrigCol := cI
      if let some ni := nIdx? then prevName := Int.ofNat ni
      if nameCol > 0 then
        mapChunks := mapChunks.push ("," ++ encodeVlqInt (Int.ofNat nameCol) ++ if nIdx?.isSome then "AAAA" else "AAA")

  let sourcesJson := String.intercalate "," (sources.toList.map jsStr)
  let namesJson := String.intercalate "," (names.toList.map jsStr)
  return s!"\{\"version\":3,\"file\":{jsStr fileName},\"sources\":[{sourcesJson}],\"names\":[{namesJson}],\"mappings\":{jsStr (joinChunks mapChunks)}}\n"

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
  let mut internals : Array Name := #[]
  for n in names do
    if let some (.fdecl ..) := findEnvDecl env n then
      match entryMap.get? n with
      | some s => nm := nm.insert n s
      | none   => internals := internals.push n
  if !min then
    for h : i in [:internals.size] do
      nm := nm.insert internals[i] s!"_g{i}"
    return nm
  -- In `--min` mode, assign deterministic short base-52/62 names to internal declarations,
  -- prioritizing the most-referenced declarations for 1-character names while preserving exports.
  let mut avoid : Std.HashSet String := entries.foldl (fun s (_, n) => s.insert n) jsMinReservedSet
  let mut refCounts : Std.HashMap Name Nat := {}
  for n in names do
    if let some (.fdecl (body := b) ..) := findEnvDecl env n then
      for callee in callees b #[] do
        refCounts := refCounts.insert callee ((refCounts.getD callee 0) + 1)
      if let some initFn := getInitFnNameFor? env n then
        refCounts := refCounts.insert initFn ((refCounts.getD initFn 0) + 1)
  let ranked := internals.mapIdx fun i n => (refCounts.getD n 0, i, n)
  let sorted := ranked.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
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
    if let some d@(.fdecl ..) := findEnvDecl env n then
      if let some jd0 := lowerDecl c d then
        let jd := if min then minifyDecl jd0 else jd0
        let s := jd.render min
        if !s.isEmpty then
          let lineCount := countNewlines s
          if wantMap then
            if let some (sourceFile, origLine, origCol, origName) := findDeclSourceLoc env n then
              spans := spans.push { startLine := curLine, lineCount, nameCol := declNameColOffset jd, sourceFile, origLine, origCol, origName }
          chunks := chunks.push s
          curLine := curLine + lineCount
  let exportList := entries.map fun (n, s) =>
    let loc := c.js n
    if loc == s then s else s!"{loc} as {s}"
  let (_, _, sep, eq) := fmtTokens min
  let exportChunk :=
    if min then s!"export\{{String.intercalate sep exportList}};\n"
    else s!"\nexport \{ {String.intercalate sep exportList} };\n"
  let externsChunk := s!"export const __externs{eq}[{String.intercalate sep (externNames.map (s!"\"{·}\""))}];\n"
  chunks := chunks.push exportChunk |>.push externsChunk
  curLine := curLine + countNewlines exportChunk + countNewlines externsChunk
  if let some mapUrl := sourceMapUrl? then
    chunks := chunks.push s!"//# sourceMappingURL={mapUrl}\n"
    curLine := curLine + 1
  let sourceMap := if wantMap then buildSourceMapV3 fileName curLine spans else ""
  return (joinChunks chunks, sourceMap, externNames)

private def isJsIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

private def stepDepth (d : Nat) (t : String) : Nat :=
  if t == "(" || t == "[" || t == "{" then d + 1
  else if t == ")" || t == "]" || t == "}" then d - 1
  else d

/-- Parse named ESM exports (`export const`, `export function`, `export { ... }`) from a JS runtime module. -/
def rtExports (rtSrc : String) : Std.HashSet String := Id.run do
  let cs := rtSrc.toList.toArray
  let n := cs.size
  let mut toks : Array String := #[]
  let mut i := 0
  for _ in [0:n] do
    if i ≥ n then break
    let c := cs[i]!
    if c.isWhitespace then i := i + 1
    else if c == '/' && i + 1 < n && (cs[i + 1]! == '/' || cs[i + 1]! == '*') then
      let line := cs[i + 1]! == '/'
      i := i + 2
      for _ in [i:n] do
        if i ≥ n then break
        if line then
          let d := cs[i]! == '\n'; i := i + 1
          if d then break
        else if cs[i]! == '*' && i + 1 < n && cs[i + 1]! == '/' then
          i := i + 2; break
        else i := i + 1
    else if c == '"' || c == '\'' || c == '`' then
      let q := c; i := i + 1
      for _ in [i:n] do
        if i ≥ n then break
        if cs[i]! == '\\' then i := i + 2
        else
          let d := cs[i]! == q; i := i + 1
          if d then break
    else if isJsIdentStart c then
      let start := i; i := i + 1
      for _ in [i:n] do
        if i < n && (isJsIdentStart cs[i]! || cs[i]!.isDigit) then i := i + 1 else break
      toks := toks.push (String.ofList (cs.extract start i).toList)
    else
      toks := toks.push (String.singleton c); i := i + 1
  let mut acc : Std.HashSet String := {}
  let mut depth := 0
  let mut k := 0
  for _ in [0:toks.size] do
    if k ≥ toks.size then break
    let t := toks[k]!
    if depth == 0 && t == "export" && k + 1 < toks.size then
      let k1 := if toks[k + 1]! == "async" && k + 2 < toks.size && toks[k + 2]! == "function" then k + 2 else k + 1
      match toks[k1]! with
      | "function" =>
          if k1 + 1 < toks.size then acc := acc.insert toks[k1 + 1]!
          k := k1 + 2
      | "const" | "let" | "var" =>
          k := k1 + 1
          let mut expect := true
          for _ in [k:toks.size] do
            if k ≥ toks.size then break
            let tk := toks[k]!
            if depth == 0 && (tk == ";" || (tk == "export" && !expect)) then
              if tk == ";" then k := k + 1
              break
            if depth == 0 && tk == "," then expect := true
            else if depth == 0 && expect && isJsIdentStart tk.front then
              acc := acc.insert tk; expect := false
            else depth := stepDepth depth tk
            k := k + 1
      | "{" =>
          k := k1 + 1
          let mut pending : Option String := none
          for _ in [k:toks.size] do
            if k ≥ toks.size then break
            let tk := toks[k]!; k := k + 1
            if tk == "}" then
              if let some s := pending then acc := acc.insert s
              break
            else if tk == "," then
              if let some s := pending then acc := acc.insert s
              pending := none
            else if tk == "as" then pending := none
            else if pending.isNone && isJsIdentStart tk.front then pending := some tk
      | _ => k := k + 1
    else
      depth := stepDepth depth t
      k := k + 1
  return acc

/-- Verify that every extern name in `externNames` is present in `avail` (parsed from `runtime/qed_rt.mjs`). -/
def checkRtExterns (avail : Std.HashSet String) (externNames : List String) : Except String Unit := do
  let missing := externNames.filter (!avail.contains ·)
  if !missing.isEmpty then
    throw s!"qed_rt: missing externs: {String.intercalate ", " missing}"

end Js
