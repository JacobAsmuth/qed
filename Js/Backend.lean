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
  | c => if c.toNat < 32 then let h := Nat.toDigits 16 c.toNat; "\\x" ++ String.ofList (if h.length == 1 then '0' :: h else h)
         else String.singleton c

def jsStr (s : String) : String := "\"" ++ s.foldl (init := "") (fun acc c => acc ++ jsStrChar c) ++ "\""
def indStr (min : Bool) (d : Nat) : String := if min then "" else String.ofList (List.replicate (2 * d) ' ')

/-! ## Typed JavaScript Target AST (`JsExpr`, `JsStmt`, `JsDecl`) -/

inductive JsExpr where
  | var (name : String) | numLit (n : Nat) | bigIntLit (n : Nat) | strLit (s : String) | arrLit (elems : List JsExpr)
  | ctorObj (cidx : Nat) (fields : List JsExpr) (hasS hasU : Bool)
  | fieldProj (obj : JsExpr) (idx : Nat) | uProj (obj : JsExpr) (idx : Nat) | sProj (obj : JsExpr) (n offset : Nat)
  | call (fn : String) (args : List JsExpr) | pap (fn : String) (arity : Nat) (args : List JsExpr)
  | app (fn : JsExpr) (args : List JsExpr) | tc (args : List JsExpr)

@[inline] private def fmtTokens (min : Bool) : String × String × String × String :=
  if min then ("", "", ",", "=") else (" ", "\n", ", ", " = ")

mutual
def JsExpr.renderMin (min : Bool) : JsExpr → String
  | .var name => name | .numLit n => toString n | .bigIntLit n => s!"{n}n" | .strLit s => jsStr s
  | .arrLit elems => s!"[{renderExprs min elems}]"
  | .ctorObj cidx fields hasS hasU =>
      let (sp, _, _, _) := fmtTokens min
      s!"\{t:{sp}{cidx},{sp}f:{sp}[{renderExprs min fields}]{if hasS then s!",{sp}s:{sp}" ++ "{}" else ""}{if hasU then s!",{sp}u:{sp}" ++ "{}" else ""}}"
  | .fieldProj obj i => s!"{obj.renderMin min}.f[{i}]" | .uProj obj i => s!"{obj.renderMin min}.u[{i}]"
  | .sProj obj n off => s!"{obj.renderMin min}.s[{soff n off}]"
  | .call fn args => s!"{fn}({renderExprs min args})"
  | .pap fn ar args => let (_, _, sep, _) := fmtTokens min; s!"$.pap({fn}{sep}{ar}{sep}[{renderExprs min args}])"
  | .app fn args => let (_, _, sep, _) := fmtTokens min; s!"$.app({fn.renderMin min}{sep}[{renderExprs min args}])"
  | .tc args => s!"$.tc([{renderExprs min args}])"

private def renderExprs (min : Bool) : List JsExpr → String
  | [] => "" | [e] => e.renderMin min | e :: es => e.renderMin min ++ (if min then "," else ", ") ++ renderExprs min es
end

mutual
inductive JsStmt where
  | letVar (name : String) (val : JsExpr) | letDecls (names : List String) | letBinds (binds : List (String × JsExpr))
  | labeledBlock (label : String) (body : List JsStmt) | constArrow (name : String) (params : List String) (body : List JsStmt)
  | setField (x : String) (idx : Nat) (val : JsExpr) | setTag (x : String) (cidx : Nat)
  | setU (x : String) (idx : Nat) (val : JsExpr) | setS (x : String) (n offset : Nat) (val : JsExpr)
  | incRef (x : String) (n : Nat) | decRef (x : String) (n : Nat) | ret (val : JsExpr)
  | tailContinue (params : List String) (args : List JsExpr) | breakLabel (assigns : List (String × JsExpr)) (label : String)
  | throwUnreachable | switchStmt (scrut : JsExpr) (arms : List JsSwitchArm)

inductive JsSwitchArm where
  | caseArm (cidx : Nat) (body : List JsStmt) | defaultArm (body : List JsStmt)
end

private def renderBlock (min : Bool) (d : Nat) (hdr body : String) : String :=
  let (sp, nl, _, _) := fmtTokens min; let ind := indStr min d; s!"{ind}{hdr}{sp}\{{nl}{body}{ind}}{nl}"

mutual
def JsStmt.render (min : Bool) (d : Nat) (s : JsStmt) : String :=
  let ind := indStr min d; let (sp, nl, sep, eq) := fmtTokens min
  match s with
  | .letVar x val => s!"{ind}let {x}{eq}{val.renderMin min};{nl}"
  | .letDecls names => if names.isEmpty then "" else s!"{ind}let {String.intercalate sep names};{nl}"
  | .letBinds binds => if binds.isEmpty then "" else s!"{ind}let {String.intercalate sep (binds.map fun (k, e) => s!"{k}{eq}{e.renderMin min}")};{nl}"
  | .labeledBlock lbl body => renderBlock min d s!"{lbl}:" (JsStmt.renderList min (d + 1) body)
  | .constArrow name params body => s!"{ind}const {name}{eq}({String.intercalate sep params}){sp}=>{sp}\{{nl}{JsStmt.renderList min (d + 1) body}{ind}};{nl}"
  | .setField x i val => s!"{ind}{x}.f[{i}]{eq}{val.renderMin min};{nl}" | .setTag x cidx => s!"{ind}{x}.t{eq}{cidx};{nl}"
  | .setU x i val => s!"{ind}{x}.u[{i}]{eq}{val.renderMin min};{nl}" | .setS x n off val => s!"{ind}{x}.s[{soff n off}]{eq}{val.renderMin min};{nl}"
  | .incRef x n => s!"{ind}$.inc({x}{sep}{n});{nl}" | .decRef x n => s!"{ind}$.dec({x}{sep}{n});{nl}"
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
      let a := String.intercalate sp (assigns.map fun (lhs, rhs) => s!"{lhs}{eq}{rhs.renderMin min};")
      s!"{ind}{if a.isEmpty then "" else a ++ sp}break {lbl};{nl}"
  | .throwUnreachable => s!"{ind}throw new Error('unreachable');{nl}"
  | .switchStmt scrut arms => renderBlock min d s!"switch{sp}({scrut.renderMin min})" (renderArms min (d + 1) arms)
def JsStmt.renderList (min : Bool) (d : Nat) : List JsStmt → String | [] => "" | s :: ss => s.render min d ++ JsStmt.renderList min d ss
private def renderArms (min : Bool) (d : Nat) : List JsSwitchArm → String
  | [] => "" | .caseArm c b :: rs => renderBlock min d s!"case {c}:" (JsStmt.renderList min (d + 1) b) ++ renderArms min d rs
  | .defaultArm b :: rs => renderBlock min d "default:" (JsStmt.renderList min (d + 1) b) ++ renderArms min d rs
end

inductive JsDecl where
  | memoInit (name initFn : String) | memoThunk (name : String) (body : List JsStmt)
  | fnPlain (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnDirectLoop (name : String) (origName : Name) (params : List String) (body : List JsStmt)
  | fnTrampoline (name : String) (origName : Name) (params : List String) (body : List JsStmt)

private def fnHeader (min : Bool) (name : String) (orig : Name) (params : List String) : String :=
  if min then s!"function {name}({String.intercalate "," params})\{" else s!"function {name}({String.intercalate ", " params}) /* {orig} */ \{\n"

def JsDecl.render (min : Bool) (d : JsDecl) : String :=
  let (sp, nl, sep, eq) := fmtTokens min; let (ind1, ind2) := (indStr min 1, indStr min 2)
  let wt := if min then "while(1){" else s!"{ind1}while (true) \{\n"
  match d with
  | .memoInit name initFn => s!"const {name}{eq}$.memo((){sp}=>{sp}$.ioVal({initFn}(0)));\n"
  | .memoThunk name body => s!"const {name}{eq}$.memo((){sp}=>{sp}\{{nl}{JsStmt.renderList min 1 body}});\n"
  | .fnPlain name orig params body => fnHeader min name orig params ++ JsStmt.renderList min 1 body ++ "}\n"
  | .fnDirectLoop name orig params body => fnHeader min name orig params ++ wt ++ JsStmt.renderList min 2 body ++ s!"{ind1}}{nl}}\n"
  | .fnTrampoline name orig params body =>
      let (sf, rv, und) := if min then ("_s", "_r", "void 0") else ("__step", "__r", "undefined")
      fnHeader min name orig params ++ s!"{ind1}const {sf}{eq}(){sp}=>{sp}\{{nl}{JsStmt.renderList min 2 body}{ind1}};{nl}{wt}{ind2}const {rv}{eq}{sf}();{nl}" ++
        s!"{ind2}if{sp}({rv}{sp}!=={sp}null{sp}&&{sp}typeof {rv}{sp}==={sp}\"object\"{sp}&&{sp}{rv}.__tc{sp}!=={sp}{und}){sp}\{{sp}[{String.intercalate sep params}]{eq}{rv}.__tc;{sp}continue;{sp}}{nl}" ++
        s!"{ind2}return {rv};{nl}{ind1}}{nl}}\n"

/-! ## Total IR Analysis & Reachability Passes -/

def reachAux (env : Environment) : Nat → List Name → Array Name → Std.HashSet Name → Except String (Array Name)
  | _, [], seen, _ => .ok seen
  | 0, n :: _, _, _ => .error s!"JS reachability gate: exceeded fuel limit while inspecting `{n}`"
  | fuel + 1, n :: rest, seen, visited =>
      if visited.contains n then reachAux env fuel rest seen visited
      else
        let seen := seen.push n; let visited := visited.insert n
        match findEnvDecl env n with
        | some (.fdecl (body := b) ..) =>
            let extra := (callees b #[]).toList ++ (getInitFnNameFor? env n).toList
            reachAux env fuel (rest ++ extra) seen visited
        | _ => reachAux env fuel rest seen visited

def reach (env : Environment) (roots : List Name) (seen : Array Name := #[]) : Except String (Array Name) :=
  reachAux env 1000000 roots seen (seen.foldl (fun s n => s.insert n) ({} : Std.HashSet Name))

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

def Ctx.js (c : Ctx) (n : Name) : String := match c.names.get? n with | some s => s | none => "$." ++ mangle n
def v (x : VarId) : String := s!"x{x.idx}"
def jp (j : JoinPointId) : String := s!"j{j.idx}"
def lowerArg : Arg → JsExpr | .var x => .var (v x) | .erased => .numLit 0

def lowerCtor (i : CtorInfo) (ys : Array Arg) : JsExpr :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then .numLit i.cidx
  else .ctorObj i.cidx (ys.toList.map lowerArg) (i.ssize != 0) (i.usize != 0)

def lowerApp (c : Ctx) (f : Name) (ys : Array Arg) : JsExpr :=
  if f == `Qed.refMark then
    .call "$.refMark" (ys.toList.filterMap fun | .var x => some (.var (v x)) | .erased => none)
  else
    let argExprs : List JsExpr := match findEnvDecl c.env f with
      | some (.extern (xs := ps) ..) =>
          ys.toList.zipIdx.filterMap fun (a, i) => if i < ps.size && ps[i]!.ty.isErased then none else some (lowerArg a)
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
  | .pap f ys       => .pap (c.js f) ((findEnvDecl c.env f).map (·.params.size) |>.getD ys.size) (ys.toList.map lowerArg)
  | .ap x ys        => .app (.var (v x)) (ys.toList.map lowerArg)
  | .box _ x        => .var (v x)
  | .unbox x        => .var (v x)
  | .lit (.num n)   => if ty.isObj || ty == .uint64 then .bigIntLit n else .numLit n
  | .lit (.str s)   => .strLit s
  | .isShared x     => .call "$.isShared" [.var (v x)]

def skipRC : FnBody → FnBody
  | .inc _ _ _ _ b => skipRC b | .dec _ _ _ _ b => skipRC b | .del _ b => skipRC b | b => b

def retsVar (z : VarId) (cont : FnBody) : Bool := match skipRC cont with | .ret (.var w) => w == z | _ => false

mutual
def hasJmpTo (target : JoinPointId) : FnBody → Bool
  | .jmp j _ => j == target
  | .vdecl _ _ _ b | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b
  | .sset _ _ _ _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasJmpTo target b
  | .jdecl _ _ v b => hasJmpTo target v || hasJmpTo target b
  | .case _ _ _ alts => hasJmpToAlts target alts.toList
  | .ret _ | .unreachable => false

def hasJmpToAlts (target : JoinPointId) : List Alt → Bool
  | [] => false | .ctor _ b :: rest | .default b :: rest => hasJmpTo target b || hasJmpToAlts target rest
end

mutual
def hasSelfTailAux (self : Name) (onlyRecJp active : Bool) : FnBody → Bool
  | .vdecl z _ e cont =>
      (match e with | .fap f _ => active && f == self && retsVar z cont | _ => false) ||
      hasSelfTailAux self onlyRecJp active cont
  | .jdecl j _ v b =>
      let activeV := if onlyRecJp then active || hasJmpTo j v else active
      hasSelfTailAux self onlyRecJp activeV v || hasSelfTailAux self onlyRecJp active b
  | .case _ _ _ alts => hasSelfTailAltsAux self onlyRecJp active alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => hasSelfTailAux self onlyRecJp active b
  | .ret _ | .jmp _ _ | .unreachable => false

def hasSelfTailAltsAux (self : Name) (onlyRecJp active : Bool) : List Alt → Bool
  | [] => false
  | .ctor _ b :: rest | .default b :: rest => hasSelfTailAux self onlyRecJp active b || hasSelfTailAltsAux self onlyRecJp active rest
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
  | [] => acc | .ctor _ b :: rest | .default b :: rest => collectNonArrAlts (collectNonArr acc b) rest
end

def hasDecOf (p : Nat) : FnBody → Bool
  | .dec y _ _ _ b => p == y.idx || hasDecOf p b
  | .del y b => p == y.idx || hasDecOf p b
  | .inc _ _ _ _ b => hasDecOf p b
  | .vdecl _ _ e b => match e with | .proj .. | .uproj .. | .sproj .. => hasDecOf p b | _ => false
  | _ => false

mutual
def collectProjSrc (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) : FnBody → Std.HashMap Nat Nat
  | .vdecl x _ e b => match e with
      | .fap .. | .ap .. => collectProjSrc (calls.insert x.idx) acc b
      | .proj _ p => collectProjSrc calls (if calls.contains p.idx then acc.insert x.idx p.idx else acc) b
      | _ => collectProjSrc calls acc b
  | .jdecl _ _ v b => collectProjSrc calls (collectProjSrc calls acc v) b
  | .case _ _ _ alts => collectProjSrcAlts calls acc alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => collectProjSrc calls acc b
  | .ret _ | .jmp _ _ | .unreachable => acc

def collectProjSrcAlts (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) : List Alt → Std.HashMap Nat Nat
  | [] => acc | .ctor _ b :: rest | .default b :: rest => collectProjSrcAlts calls (collectProjSrc calls acc b) rest
end

/-! ## Lowering `Lean.IR` into Typed JS Statements & Declarations -/

mutual
def lowerBody (c : Ctx) : FnBody → List JsStmt
  | .vdecl x ty e b => match e with
      | .fap f args =>
          if c.selfFn == some f && retsVar x b then
            if c.directLoop then [.tailContinue (c.selfParams.toList.map (v ·.x)) (args.toList.map lowerArg)]
            else [.ret (.tc (args.toList.map lowerArg))]
          else .letVar (v x) (lowerExpr c ty e) :: lowerBody c b
      | _ => .letVar (v x) (lowerExpr c ty e) :: lowerBody c b
  | .jdecl j xs val b =>
      if !hasJmpTo j val then
        let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
        let pre := if xs.isEmpty then [] else [JsStmt.letDecls (xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}")]
        let post := if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]
        pre ++ [.labeledBlock (jp j) (lowerBody c' b)] ++ post ++ lowerBody c val
      else .constArrow (jp j) (xs.toList.map (v ·.x)) (lowerBody c val) :: lowerBody c b
  | .set x i y b        => .setField (v x) i (lowerArg y) :: lowerBody c b
  | .setTag x cidx b    => .setTag (v x) cidx :: lowerBody c b
  | .uset x i y b       => .setU (v x) i (.var (v y)) :: lowerBody c b
  | .sset x n off y _ b => .setS (v x) n off (.var (v y)) :: lowerBody c b
  | .inc x n _ _ b =>
      let n' := match c.projSrc.get? x.idx with | some p => if hasDecOf p b then n - 1 else n | none => n
      if n' == 0 || c.nonArr.contains x.idx then lowerBody c b else .incRef (v x) n' :: lowerBody c b
  | .dec x n _ _ b => if c.nonArr.contains x.idx then lowerBody c b else .decRef (v x) n :: lowerBody c b
  | .del x b => if c.nonArr.contains x.idx then lowerBody c b else .decRef (v x) 1 :: lowerBody c b
  | .ret a => [.ret (lowerArg a)]
  | .jmp j ys => match c.inlineJps.get? j.idx with
      | some _ => [.breakLabel (ys.toList.zipIdx.map fun (a, i) => (s!"_{jp j}_{i}", lowerArg a)) (jp j)]
      | none   => [.ret (.call (jp j) (ys.toList.map lowerArg))]
  | .unreachable => [.throwUnreachable]
  | .case _ x xType alts =>
      [.switchStmt (if xType.isObj then .call "$.tag" [.var (v x)] else .var (v x)) (lowerAlts c alts.toList)]

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
            some (.fnDirectLoop (c.js f) f ps (lowerBody { c with selfFn := some f, selfParams := xs, directLoop := true } body))
          else
            some (.fnTrampoline (c.js f) f ps (lowerBody { c with selfFn := some f, selfParams := xs } body))
        else some (.fnPlain (c.js f) f ps (lowerBody c body))
  | .extern .. => none

/-! ## Deterministic Identifier Minification (`--min`) -/

private def identChars : Array Char := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toList.toArray

private def encodeIdentRest : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc => let c := identChars[n % 62]!; if n < 62 then c :: acc else encodeIdentRest fuel (n / 62 - 1) (c :: acc)

def shortIdentAt (idx : Nat) : String :=
  if idx < 52 then String.singleton identChars[idx]!
  else let n := idx - 52; String.ofList (identChars[n % 52]! :: encodeIdentRest (n + 1) (n / 52) [])

def jsMinReservedSet : Std.HashSet String :=
  ("do if in for let new try var case else enum eval null this true void with await break catch class const " ++
   "false super throw while yield delete export import public return static switch typeof default extends finally " ++
   "package private arguments continue debugger function protected implements instanceof interface Error Object " ++
   "Array BigInt String Number Boolean Symbol Math JSON Promise Map Set Uint8Array undefined NaN Infinity " ++
   "globalThis window document $ __step __r __externs").splitOn " " |>.foldl (·.insert ·) {}

private def nextShortIdentAux (avoid : Std.HashSet String) : Nat → Nat → String × Nat
  | 0, idx => (shortIdentAt idx, idx + 1)
  | fuel + 1, idx => let cand := shortIdentAt idx; if avoid.contains cand then nextShortIdentAux avoid fuel (idx + 1) else (cand, idx + 1)
def nextShortIdent (avoid : Std.HashSet String) (idx : Nat) : String × Nat := nextShortIdentAux avoid (avoid.size + 64) idx

private structure MinScan where
  localArrows : Std.HashSet String := {}
  called      : Std.HashSet String := {}
  avoid       : Std.HashSet String
mutual
private def scanMinExpr (acc : MinScan) : JsExpr → MinScan
  | .call fn args => scanMinExprs (if !fn.startsWith "$." then { acc with called := acc.called.insert fn } else acc) args
  | .pap fn _ args => scanMinExprs (if !fn.startsWith "$." then { acc with avoid := acc.avoid.insert fn } else acc) args
  | .arrLit es | .ctorObj _ es _ _ | .tc es => scanMinExprs acc es | .fieldProj o _ | .uProj o _ | .sProj o _ _ => scanMinExpr acc o
  | .app fn args => scanMinExprs (scanMinExpr acc fn) args | _ => acc
private def scanMinExprs (acc : MinScan) : List JsExpr → MinScan | [] => acc | e :: es => scanMinExprs (scanMinExpr acc e) es
end
mutual
private def scanMinStmt (acc : MinScan) : JsStmt → MinScan
  | .letVar _ v | .setField _ _ v | .setU _ _ v | .setS _ _ _ v | .ret v => scanMinExpr acc v
  | .letBinds bs | .breakLabel bs _ => bs.foldl (fun a (_, e) => scanMinExpr a e) acc
  | .labeledBlock _ body => scanMinStmts acc body
  | .constArrow name _ body => scanMinStmts { acc with localArrows := acc.localArrows.insert name } body
  | .tailContinue _ args => scanMinExprs acc args | .switchStmt scrut arms => scanMinArms (scanMinExpr acc scrut) arms | _ => acc
private def scanMinStmts (acc : MinScan) : List JsStmt → MinScan | [] => acc | s :: ss => scanMinStmts (scanMinStmt acc s) ss
private def scanMinArms (acc : MinScan) : List JsSwitchArm → MinScan | [] => acc | .caseArm _ b :: rs | .defaultArm b :: rs => scanMinArms (scanMinStmts acc b) rs
end

private structure MinSt where
  avoid : Std.HashSet String
  localArrows : Std.HashSet String
  vars : Std.HashMap String String × Nat := ({}, 0)
  lbls : Std.HashMap String String × Nat := ({}, 0)
private abbrev MinM := StateM MinSt
@[noinline] private def internShort (avoid : Std.HashSet String) (p : Std.HashMap String String × Nat) (k : String) : String × (Std.HashMap String String × Nat) :=
  match p.1.get? k with | some s => (s, p) | none => let (s, i') := nextShortIdent avoid p.2; (s, p.1.insert k s, i')
@[noinline] private def mapVarM (name : String) : MinM String := modifyGet fun st => let (s, v) := internShort st.avoid st.vars name; (s, { st with vars := v })
@[noinline] private def mapVarsM (ns : List String) : MinM (List String) := ns.mapM mapVarM
@[noinline] private def mapLblM (lbl : String) : MinM String := modifyGet fun st => let (s, l) := internShort jsMinReservedSet st.lbls lbl; (s, { st with lbls := l })
mutual
@[noinline] private def renameExpr : JsExpr → MinM JsExpr
  | .var name => return .var (← mapVarM name) | .arrLit es => return .arrLit (← renameExprs es)
  | .ctorObj c fs hs hu => return .ctorObj c (← renameExprs fs) hs hu
  | .fieldProj o i => return .fieldProj (← renameExpr o) i | .uProj o i => return .uProj (← renameExpr o) i | .sProj o n off => return .sProj (← renameExpr o) n off
  | .call fn args => do let fn' ← (if (← get).localArrows.contains fn then mapVarM fn else pure fn); return .call fn' (← renameExprs args)
  | .pap fn ar args => return .pap fn ar (← renameExprs args) | .app fn args => return .app (← renameExpr fn) (← renameExprs args)
  | .tc args => return .tc (← renameExprs args) | e => return e
@[noinline] private def renameExprs : List JsExpr → MinM (List JsExpr) | [] => return [] | e :: es => return (← renameExpr e) :: (← renameExprs es)
end
@[noinline] private def renamePairs (ps : List (String × JsExpr)) : MinM (List (String × JsExpr)) := ps.mapM fun (k, e) => return (← mapVarM k, ← renameExpr e)
mutual
@[noinline] private def renameStmt : JsStmt → MinM JsStmt
  | .letVar x v => do let v' ← renameExpr v; return .letVar (← mapVarM x) v'
  | .letDecls ns => return .letDecls (← mapVarsM ns) | .letBinds bs => return .letBinds (← renamePairs bs)
  | .labeledBlock l b => return .labeledBlock (← mapLblM l) (← renameStmts b)
  | .constArrow n ps b => return .constArrow (← mapVarM n) (← mapVarsM ps) (← renameStmts b)
  | .setField x i v => return .setField (← mapVarM x) i (← renameExpr v) | .setTag x c => return .setTag (← mapVarM x) c
  | .setU x i v => return .setU (← mapVarM x) i (← renameExpr v) | .setS x n o v => return .setS (← mapVarM x) n o (← renameExpr v)
  | .incRef x n => return .incRef (← mapVarM x) n | .decRef x n => return .decRef (← mapVarM x) n | .ret v => return .ret (← renameExpr v)
  | .tailContinue ps as => do let as' ← renameExprs as; return .tailContinue (← mapVarsM ps) as'
  | .breakLabel bs l => return .breakLabel (← renamePairs bs) (← mapLblM l) | .throwUnreachable => return .throwUnreachable
  | .switchStmt scr arms => return .switchStmt (← renameExpr scr) (← renameArms arms)
@[noinline] private def renameStmts : List JsStmt → MinM (List JsStmt) | [] => return [] | s :: ss => return (← renameStmt s) :: (← renameStmts ss)
@[noinline] private def renameArms : List JsSwitchArm → MinM (List JsSwitchArm)
  | [] => return [] | .caseArm c b :: rs => return .caseArm c (← renameStmts b) :: (← renameArms rs) | .defaultArm b :: rs => return .defaultArm (← renameStmts b) :: (← renameArms rs)
end
@[noinline] private def minifyFnBody (name : String) (params : List String) (body : List JsStmt) : List String × List JsStmt :=
  let sc := scanMinStmts { avoid := jsMinReservedSet.insert name } body
  let avoid := sc.called.fold (fun a fn => if sc.localArrows.contains fn then a else a.insert fn) sc.avoid
  ((do return (← mapVarsM params, ← renameStmts body)).run { avoid, localArrows := sc.localArrows }).1
def minifyDecl : JsDecl → JsDecl
  | d@(.memoInit ..) => d | .memoThunk n b => .memoThunk n (minifyFnBody n [] b).2
  | .fnPlain n o ps b => let (ps, b) := minifyFnBody n ps b; .fnPlain n o ps b
  | .fnDirectLoop n o ps b => let (ps, b) := minifyFnBody n ps b; .fnDirectLoop n o ps b
  | .fnTrampoline n o ps b => let (ps, b) := minifyFnBody n ps b; .fnTrampoline n o ps b

/-! ## Source Map v3 (`.mjs.map`) VLQ Encoder & Generator -/

private def vlqChars : Array Char := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
private def encodeVlqNatAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc.reverse
  | fuel + 1, u, acc =>
      let rest := u >>> 5; let ch := vlqChars[if rest > 0 then (u &&& 31) ||| 32 else u &&& 31]!
      if rest == 0 then (ch :: acc).reverse else encodeVlqNatAux fuel rest (ch :: acc)
def encodeVlqInt (v : Int) : String := String.ofList (encodeVlqNatAux 64 (if v < 0 then (((-v).toNat) <<< 1) + 1 else v.toNat <<< 1) [])
private def decodeVlqAux (shift acc : Nat) : List Char → Option Int
  | [] => none
  | c :: rest => (vlqChars.idxOf? c).bind fun d =>
      let acc := acc ||| ((d &&& 31) <<< shift)
      if (d &&& 32) != 0 then decodeVlqAux (shift + 5) acc rest
      else if rest.isEmpty then some (if (acc &&& 1) == 1 then -(Int.ofNat (acc >>> 1)) else Int.ofNat (acc >>> 1)) else none
def decodeVlqInt (s : String) : Option Int := decodeVlqAux 0 0 s.toList

private def findRangeAux (env : Environment) : Nat → Name → Option DeclarationRanges
  | 0, _ | _, .anonymous => none
  | f + 1, cur => (Lean.declRangeExt.find? env cur).orElse fun _ => match cur with | .str p _ | .num p _ => findRangeAux env f p | .anonymous => none
def findDeclSourceLoc (env : Environment) (n : Name) : Option (String × Nat × Nat × String) :=
  let modName := definingModule env n
  if modName.isAnonymous then none
  else let (oLine, oCol) := (findRangeAux env 8 n).elim (0, 0) fun r => (r.range.pos.line - 1, r.range.pos.column)
       some ((modName.toString.replace "." "/") ++ ".lean", oLine, oCol, n.toString)
private def countNewlines (s : String) : Nat := s.foldl (init := 0) fun acc c => if c == '\n' then acc + 1 else acc
private def internIdx (p : Array String × Std.HashMap String Nat) (s : String) : Nat × Array String × Std.HashMap String Nat :=
  match p.2.get? s with | some i => (i, p) | none => let i := p.1.size; (i, p.1.push s, p.2.insert s i)

def collectProgramExterns (env : Environment) (roots : List Name) : Except String (Array Name × List String) := do
  let names ← reach env roots #[]
  verifyReachable env names roots; verifyNoServerLeakInClient env names; verifyNoServerLeakInClientExprs env roots names
  let externSet ← names.foldlM (init := ({} : Std.HashSet String)) fun s n => match findEnvDecl env n with
    | some (.fdecl ..) => pure s | some (.extern ..) => pure (s.insert (mangle n)) | none => throw s!"no IR for `{n}` (not compiled?)"
  return (names, externSet.toList.mergeSort (· < ·))

private def assignTopLevelNames (env : Environment) (names : Array Name) (entries : List (Name × String)) (min : Bool) : Std.HashMap Name String :=
  let entryMap := entries.foldl (fun (m : Std.HashMap Name String) e => m.insert e.1 e.2) {}
  let (nm0, internals) := names.foldl (init := ({}, #[])) fun (nm, ints) n =>
    match findEnvDecl env n with
    | some (.fdecl ..) => match entryMap.get? n with | some s => (nm.insert n s, ints) | none => (nm, ints.push n)
    | _ => (nm, ints)
  if !min then (internals.foldl (init := (nm0, 0)) fun (m, i) n => (m.insert n s!"_g{i}", i + 1)).1
  else
    let inc (rc : Std.HashMap Name Nat) (k : Name) := rc.insert k (rc.getD k 0 + 1)
    let refCounts := names.foldl (init := ({} : Std.HashMap Name Nat)) fun rc n =>
      match findEnvDecl env n with
      | some (.fdecl (body := b) ..) => (getInitFnNameFor? env n).elim ((callees b #[]).foldl inc rc) (inc ((callees b #[]).foldl inc rc))
      | _ => rc
    let sorted := (internals.mapIdx fun i n => (refCounts.getD n 0, i, n)).qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
    let avoid0 := entries.foldl (fun s (_, n) => s.insert n) jsMinReservedSet
    (sorted.foldl (init := (nm0, avoid0, 0)) fun (nm, avoid, idIdx) (_, _, n) =>
      let (s, idx') := nextShortIdent avoid idIdx; (nm.insert n s, avoid.insert s, idx')).1

private structure EmitSt where
  jsOut : String
  mappings : String
  srcs : Array String × Std.HashMap String Nat := (#[], {})
  nms : Array String × Std.HashMap String Nat := (#[], {})
  prev : Int × Int × Int × Int := (0, 0, 0, 0)

@[noinline] private def emitOneDecl (env : Environment) (c : Ctx) (min wantMap : Bool) (st : EmitSt) (n : Name) : EmitSt :=
  match findEnvDecl env n with
  | some d@(.fdecl ..) => match lowerDecl c d with
    | none => st
    | some jd0 =>
        let jd := if min then minifyDecl jd0 else jd0; let s := jd.render min
        if s.isEmpty then st else if !wantMap then { st with jsOut := st.jsOut ++ s }
        else
          let lc := countNewlines s
          match findDeclSourceLoc env n with
          | some (srcFile, oLine, oCol, oName) =>
              let (sIdx, srcs) := internIdx st.srcs srcFile; let (nIdx, nms) := internIdx st.nms oName
              let (sI, lI, cI, nI) := (Int.ofNat sIdx, Int.ofNat oLine, Int.ofNat oCol, Int.ofNat nIdx); let (pS, pL, pC, pN) := st.prev
              let seg := ";A" ++ encodeVlqInt (sI - pS) ++ encodeVlqInt (lI - pL) ++ encodeVlqInt (cI - pC) ++
                encodeVlqInt (nI - pN) ++ "," ++ encodeVlqInt (match jd with | .memoInit .. | .memoThunk .. => 6 | _ => 9) ++ "AAAA"
              { jsOut := st.jsOut ++ s, srcs, nms, prev := (sI, lI, cI, nI), mappings := st.mappings ++ seg ++ String.join (List.replicate (lc - 1) ";AAAA") }
          | none => { st with jsOut := st.jsOut ++ s, mappings := st.mappings ++ String.ofList (List.replicate lc ';') }
  | _ => st

def emitProgramWithSourceMap (env : Environment) (entries : List (Name × String)) (min : Bool := false) (fileName : String := "app.mjs") (sourceMapUrl? : Option String := none) : Except String (String × String × List String) := do
  let (names, externNames) ← collectProgramExterns env (entries.map (·.1))
  let c : Ctx := { env, names := assignTopLevelNames env names entries min, min }
  let hdr := (if min then "" else "// GENERATED by Js.Backend (Lean-IR → JS). Do not edit.\n") ++ "import * as $ from './qed_rt.mjs';\n"
  let wantMap := sourceMapUrl?.isSome || !fileName.isEmpty
  let st := names.foldl (emitOneDecl env c min wantMap) { jsOut := hdr, mappings := if wantMap then String.ofList (List.replicate (countNewlines hdr - 1) ';') else "" }
  let (_, _, sep, eq) := fmtTokens min
  let exportList := entries.map fun (n, s) => let loc := c.js n; if loc == s then s else s!"{loc} as {s}"
  let tail := (if min then s!"export\{{String.intercalate sep exportList}};\n" else s!"\nexport \{ {String.intercalate sep exportList} };\n") ++
    s!"export const __externs{eq}[{String.intercalate sep (externNames.map (s!"\"{·}\""))}];\n" ++ (sourceMapUrl?.elim "" (s!"//# sourceMappingURL={·}\n"))
  let jArr (xs : Array String) := String.intercalate "," (xs.toList.map jsStr)
  let sourceMap := if !wantMap then "" else
    s!"\{\"version\":3,\"file\":{jsStr fileName},\"sources\":[{jArr st.srcs.1}],\"names\":[{jArr st.nms.1}],\"mappings\":{jsStr (st.mappings ++ String.ofList (List.replicate (countNewlines tail) ';'))}}\n"
  return (st.jsOut ++ tail, sourceMap, externNames)

private def isJsIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
private def isJsIdentChar (c : Char) : Bool := isJsIdentStart c || c.isDigit
private def stepDepth (d : Nat) (t : String) : Nat := if t == "(" || t == "[" || t == "{" then d + 1 else if t == ")" || t == "]" || t == "}" then d - 1 else d
private def skipBlockComment : List Char → List Char | '*' :: '/' :: r => r | _ :: r => skipBlockComment r | [] => []
private def skipJsStr (q : Char) : List Char → List Char | '\\' :: _ :: r => skipJsStr q r | c :: r => if c == q then r else skipJsStr q r | [] => []
private def scanJsToks : Nat → List Char → List String → List String
  | 0, _, acc | _, [], acc => acc.reverse
  | f + 1, c :: cs, acc =>
      if c.isWhitespace then scanJsToks f cs acc
      else match c, cs with
      | '/', '/' :: r => scanJsToks f (r.dropWhile (· != '\n')) acc | '/', '*' :: r => scanJsToks f (skipBlockComment r) acc
      | '"', r | '\'', r | '`', r => scanJsToks f (skipJsStr c r) acc
      | _, _ => if isJsIdentStart c then scanJsToks f (cs.dropWhile isJsIdentChar) (String.ofList (c :: cs.takeWhile isJsIdentChar) :: acc) else scanJsToks f cs (String.singleton c :: acc)
private def collectExports : Nat → UInt8 → Nat → Bool → Option String → Std.HashSet String → List String → Std.HashSet String
  | 0, _, _, _, _, acc, _ | _, _, _, _, _, acc, [] => acc
  | f + 1, mode, depth, expect, pend, acc, t :: ts =>
      if mode == 0 then
        if depth == 0 && t == "export" then match ts with
          | "async" :: "function" :: name :: r | "function" :: name :: r => collectExports f 0 0 true none (acc.insert name) r
          | "const" :: r | "let" :: r | "var" :: r => collectExports f 1 0 true none acc r
          | "{" :: r => collectExports f 2 0 true none acc r | _ => collectExports f 0 0 true none acc ts
        else collectExports f 0 (stepDepth depth t) true none acc ts
      else if mode == 1 then
        if depth == 0 && (t == ";" || (t == "export" && !expect)) then collectExports f 0 0 true none acc (if t == ";" then ts else t :: ts)
        else if depth == 0 && t == "," then collectExports f 1 0 true none acc ts
        else if depth == 0 && expect && isJsIdentStart t.front then collectExports f 1 0 false none (acc.insert t) ts
        else collectExports f 1 (stepDepth depth t) expect none acc ts
      else if t == "}" || t == "," then collectExports f (if t == "}" then 0 else 2) 0 true none (pend.elim acc acc.insert) ts
      else if t == "as" then collectExports f 2 0 true none acc ts
      else collectExports f 2 0 true (if pend.isNone && isJsIdentStart t.front then some t else pend) acc ts

/-- Parse named ESM exports (`export const/let/var/function/{...}`) from a JS runtime module. -/
def rtExports (rtSrc : String) : Std.HashSet String :=
  let cs := rtSrc.toList; let toks := scanJsToks cs.length cs []; collectExports toks.length 0 0 true none {} toks

def checkRtExterns (avail : Std.HashSet String) (externNames : List String) : Except String Unit := do
  let missing := externNames.filter (!avail.contains ·)
  if !missing.isEmpty then throw s!"qed_rt: missing externs: {String.intercalate ", " missing}"

end Js
