import Qed.View.Core
import Lean

namespace Qed

open Lean in
private partial def viewMentions (m : Name) : Syntax → Bool
  | .ident _ _ n _ => m.isPrefixOf n
  | .node _ _ args => args.any (viewMentions m)
  | _              => false

private def lastStr? : Lean.Name → Option String
  | .str _ s => some s
  | _        => none

private def kApp      : Lean.Name := `Lean.Parser.Term.app
private def kParen    : Lean.Name := `Lean.Parser.Term.paren
private def kFun      : Lean.Name := `Lean.Parser.Term.fun
private def kBasicFun : Lean.Name := `Lean.Parser.Term.basicFun
private def kMatch    : Lean.Name := `Lean.Parser.Term.match
private def kList     : Lean.Name := `«term[_]»

private def dropLastComp : Lean.Name → Lean.Name
  | .str p _   => p
  | .num p _   => p
  | .anonymous => .anonymous

private def stringAttrName? : String → Option String
  | "cls"         => some "class"
  | "value"       => some "value"
  | "placeholder" => some "placeholder"
  | "style"       => some "style"
  | "href"        => some "href"
  | "src"         => some "src"
  | "action"      => some "action"
  | "alt"         => some "alt"
  | "title"       => some "title"
  | "type'"       => some "type"
  | "name"        => some "name"
  | _             => none

private def eventPrime? : String → Option String
  | "onClick" => some "onClick'"
  | "onInput" => some "onInput'"
  | "onCheck" => some "onCheck'"
  | _         => none

open Lean in
private def asApp? (stx : Syntax) : Option (Syntax × Array Syntax) :=
  if stx.getKind == kApp && stx.getArgs.size == 2 then
    some (stx.getArgs[0]!, stx.getArgs[1]!.getArgs)
  else none

open Lean in
private def unparen (stx : Syntax) : Syntax :=
  if stx.getKind == kParen && stx.getArgs.size == 3 then stx.getArgs[1]! else stx

open Lean in
private def asElementApp? (stx : Syntax) : Option (String × Array Syntax) :=
  match asApp? (unparen stx) with
  | some (fn, args) =>
      match fn with
      | .ident _ _ n _ =>
          if lastStr? n.eraseMacroScopes == some "el" && 0 < args.size then
            args[0]!.isStrLit?.map fun tag => (tag, args.extract 1 args.size)
          else none
      | _ => none
  | none => none

open Lean in
private def asProj? (stx : Syntax) (field : Name) : Option Syntax :=
  let s := unparen stx
  if s.getKind == `Lean.Parser.Term.proj && s.getArgs.size == 3
      && s.getArgs[2]!.getId.eraseMacroScopes == field
  then some s.getArgs[0]! else none

open Lean in
private def unwrapForEachItems (recv : Syntax) : Syntax × Bool :=
  let r := unparen recv
  match asApp? r with
  | some (.ident _ _ rn _, #[xs]) =>
      if rn.eraseMacroScopes == ``Qed.ForEachItems.toList then (unparen xs, true) else (r, false)
  | _ => (r, false)

open Lean in
private def asMap? (stx : Syntax) : Option (Syntax × Syntax × Bool) :=
  let stx := (asProj? stx `toList).getD stx
  match asApp? (unparen stx) with
  | some (.ident _ _ n _, #[recv, fnArg]) =>
      if n.eraseMacroScopes == ``Qed.mapList then
        let (xs, isFE) := unwrapForEachItems recv
        some (xs, unparen fnArg, isFE)
      else none
  | some (fn, #[fnArg]) =>
      match fn with
      | .ident _ _ n _ =>
          if lastStr? n.eraseMacroScopes == some "map" then
            some (mkIdentFrom fn (dropLastComp n.eraseMacroScopes), unparen fnArg, false)
          else none
      | _ =>
          (asProj? fn `map).map fun recv =>
            let (xs, isFE) := unwrapForEachItems recv
            (xs, unparen fnArg, isFE)
  | _ => none

open Lean in
private def asFun? (stx : Syntax) : Option (Syntax × Syntax) :=
  let s := unparen stx
  if s.getKind == kFun && s.getArgs.size ≥ 2 then
    let basic := s.getArgs[1]!
    if basic.getKind == kBasicFun && basic.getArgs.size ≥ 4 then
      let binders := basic.getArgs[0]!.getArgs
      if binders.size == 1 then some (binders[0]!, basic.getArgs[3]!) else none
    else none
  else none

open Lean in
private def keyArg? (e : Syntax) : Option Syntax :=
  match asApp? e with
  | some (fn, args) =>
      match fn with
      | .ident _ _ n _ =>
          if lastStr? n.eraseMacroScopes == some "key" && args.size == 1 then some args[0]! else none
      | _ => none
  | none => none

open Lean in
private def extractKey (attrsList : Syntax) : MacroM (Option (Term × Term)) := do
  if attrsList.getKind != kList || attrsList.getArgs.size != 3 then return none
  let mut keyV : Option Syntax := none
  let mut kept : Array Term := #[]
  for e in attrsList.getArgs[1]!.getSepArgs do
    match keyArg? e with
    | some v => keyV := some v
    | none   => kept := kept.push ⟨e⟩
  match keyV with
  | some v => return some (⟨v⟩, ← `([$kept,*]))
  | none   => return none

open Lean in
private def viewMentionsAny (m : Name) (fields : Array Ident) (stx : Syntax) : Bool :=
  viewMentions m stx || fields.any (fun f => viewMentions f.getId stx)

open Lean in
private def wrapFieldLets (m : Ident) (fields : Array Ident) (body : Term) : MacroM Term := do
  let mut out := body
  for f in fields.reverse do
    if viewMentions f.getId out.raw then
      out ← `(let $f:ident := $m.$f:ident; $out)
  return out

open Lean in
private def mkModelFn (m : Ident) (fields : Array Ident) (body : Term) : MacroM Term := do
  `(fun $m => $(← wrapFieldLets m fields body))

open Lean in
private def stripFieldLets (fv : Expr) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, .letE n ty val body nonDep =>
      if val.containsFVar fv.fvarId! then stripFieldLets fv fuel (body.instantiate1 val)
      else .letE n ty val body nonDep
  | _, e => e

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
elab "qedInternalChild% " "fun " mb:ident " => " body:term : term <= expectedType => do
  match_expr (← instantiateMVars expectedType) with
  | Qed.View σ msg =>
      if (← instantiateMVars σ).isMVar then tryPostpone
      withLocalDeclD mb.getId σ fun fv => do
        let b   ← elabTerm body none
        let bTy ← whnf (← instantiateMVars (← inferType b))
        if bTy.isConstOf ``String then
          mkAppOptM ``Qed.View.dyn #[σ, msg, ← mkLambdaFVars #[fv] b]
        else if bTy.isAppOfArity ``Qed.View 2 then
          ensureHasType expectedType b
        else if !bTy.hasMVar && !bTy.isAppOfArity ``Qed.Html 1 && !bTy.isAppOfArity ``Option 1 &&
                (← whnf (← inferType bTy)) == .sort (Level.succ .zero) &&
                (← trySynthInstance (mkApp (mkConst ``ToString [Level.zero]) bTy)) matches .some _ then
          let s ← mkAppM ``toString #[b]
          mkAppOptM ``Qed.View.dyn #[σ, msg, ← mkLambdaFVars #[fv] s]
        else
          let b' ← instantiateMVars (← ensureHasType (← mkAppM ``Qed.Html #[msg]) b)
          let bCore := stripFieldLets fv 64 b'
          if bCore.isAppOfArity ``Qed.View.render 4 then
            let v   := bCore.getArg! 2
            let arg := bCore.getArg! 3
            if !v.containsFVar fv.fvarId! then
              if arg == fv then return v
              else return (← mkAppM ``Qed.View.mapScope #[← mkLambdaFVars #[fv] arg, v])
          if bCore.isAppOfArity ``Qed.lazy 5 then
            let α    := bCore.getArg! 0
            let inst := bCore.getArg! 2
            let f    := bCore.getArg! 3
            let a    := bCore.getArg! 4
            if f.containsFVar fv.fvarId! || inst.containsFVar fv.fvarId! || α.containsFVar fv.fvarId! then
              logErrorAt body "Qed.lazy function must not capture state directly; pass all state dependencies through the `[LawfulKey]` argument so memoization stays sound"
              return (← mkAppOptM ``Qed.View.text #[σ, msg, mkStrLit ""])
            return (← mkAppOptM ``Qed.V.memo #[α, σ, msg, inst, f, ← mkLambdaFVars #[fv] a])
          mkAppOptM ``Qed.View.dynNode #[σ, msg, ← mkLambdaFVars #[fv] b']
  | _ => throwError "qedInternalChild% expects a `View` expected type"

open Lean in
mutual
  partial def viewLift (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax := do
    let liftIf (c t e : Term) (h? : Option Ident) : MacroM Syntax := do
      let t' : Term := ⟨← viewLift m fields t⟩
      let e' : Term := ⟨← viewLift m fields e⟩
      let mkIte (a b : Term) := match h? with | some h => `(if $h:ident : $c then $a else $b) | none => `(if $c then $a else $b)
      if viewMentionsAny m.getId fields c then
        return (← `(Qed.V.ifElse $(← mkModelFn m fields (← mkIte (← `(true)) (← `(false)))) $t' $e'))
      else return (← mkIte t' e')
    match stx with
    | `(text $e:term) =>
        if viewMentionsAny m.getId fields e then
          return (← `(Qed.V.dyn $(← mkModelFn m fields (← `(toString $e)))))
        else return (← `(Qed.V.text (toString $e)))
    | `(if $c:term then $t:term else $e:term) => liftIf c t e none
    | `(if $h:ident : $c:term then $t:term else $e:term) =>
        if !viewMentionsAny h.getId #[] t && !viewMentionsAny h.getId #[] e then liftIf c t e (some h)
        else catchAll m fields stx
    | _ =>
        if stx.isStrLit?.isSome then return stx
        if stx.getKind == kMatch && viewMentionsAny m.getId fields stx then
          return (← `(Qed.V.dynNode $(← mkModelFn m fields ⟨stx⟩)))
        if let some out ← tryForEach m fields stx then return out
        if let some out ← tryElement m fields stx then return out
        catchAll m fields stx

  partial def tryElement (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, args) := asElementApp? stx | return none
    if args.size > 2 then return none
    let empty : Term ← `([])
    let attrsO ← if args.size ≥ 1 then liftAttrList m fields args[0]! else pure (some empty)
    let kidsO  ← if args.size ≥ 2 then liftKidList  m fields args[1]! else pure (some empty)
    match attrsO, kidsO with
    | some attrsL, some kidsL =>
        let tagL : Term := ⟨Syntax.mkStrLit tag⟩
        return some (← `(Qed.V.el $tagL $attrsL $kidsL))
    | _, _ => return none

  partial def liftAttrList (m : Ident) (fields : Array Ident) (lst : Syntax) : MacroM (Option Term) := do
    if lst.getKind != kList || lst.getArgs.size != 3 then return none
    let lifted ← lst.getArgs[1]!.getSepArgs.mapM fun a => do
      let aT : Term := ⟨a⟩
      match ← tryAttr m fields a with
      | some a' => pure (⟨a'⟩ : Term)
      | none    =>
          if viewMentionsAny m.getId fields a then `(Qed.VAttr.bind $(← mkModelFn m fields aT))
          -- Explicit `.stat` rather than coercion because `σ` may still be an unresolved metavar.
          else `(Qed.VAttr.stat $aT)
    return some (← `([$lifted,*]))

  partial def liftKidList (m : Ident) (fields : Array Ident) (lst : Syntax) : MacroM (Option Term) := do
    if lst.getKind != kList || lst.getArgs.size != 3 then return none
    let lifted ← lst.getArgs[1]!.getSepArgs.mapM fun k => do pure (⟨← viewLift m fields k⟩ : Term)
    return some (← `([$lifted,*]))

  partial def catchAll (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax := do
    let e : Term := ⟨stx⟩
    if viewMentionsAny m.getId fields stx then
      return (← `(qedInternalChild% fun $m => $(← wrapFieldLets m fields e)))
    else return (← `(Qed.V.static $e))

  partial def tryAttr (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (fn, args) := asApp? stx | return none
    match fn with
    | .ident _ _ n _ =>
        let hn := (lastStr? n.eraseMacroScopes).getD ""
        if let some an := stringAttrName? hn then
          if args.size == 1 && viewMentionsAny m.getId fields args[0]! then
            let nm : Term := ⟨Syntax.mkStrLit an⟩
            let rawV : Term := ⟨args[0]!⟩
            let v : Term ← if hn == "href" || hn == "src" || hn == "action" then `(Qed.ToHref.toHref $rawV)
                           else if hn == "value" then `(toString $rawV)
                           else pure rawV
            return some (← `(Qed.V.dynAttr $nm $(← mkModelFn m fields v)))
        if hn == "attr" && args.size == 2 && viewMentionsAny m.getId fields args[1]! then
          let k : Term := ⟨args[0]!⟩
          let v : Term := ⟨args[1]!⟩
          return some (← `(Qed.V.dynAttr $k $(← mkModelFn m fields (← `(toString $v)))))
        if let some pn := eventPrime? hn then
          if args.size == 1 && viewMentionsAny m.getId fields args[0]! then
            let primed := mkIdent ((`Qed.V).append (Name.mkSimple pn))
            return some (← `($primed $(← mkModelFn m fields ⟨args[0]!⟩)))
        return none
    | _ => return none

  partial def tryForEach (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, pargs) := asElementApp? stx | return none
    if pargs.size != 2 then return none
    let some (xs, funArg, isForEachItems) := asMap? pargs[1]! | return none
    let some (binder, body) := asFun? funArg | return none
    let binderId : Ident := ⟨binder⟩
    let attrsL : Term ← (match ← liftAttrList m fields pargs[0]! with | some a => pure a | none => pure ⟨pargs[0]!⟩)
    let xsT    : Term := ⟨xs⟩
    let xsArrT : Term ← if isForEachItems then `(Qed.ForEachItems.toArray $xsT) else pure xsT
    let tagL   : Term := ⟨Syntax.mkStrLit tag⟩
    let outerFields := fields.filter (fun f => f.getId != binderId.getId)
    let usesOuter := viewMentions m.getId body || outerFields.any (fun f => viewMentions f.getId body)
    let rowEl? := asElementApp? body
    let keyOpt ← (match rowEl? with
                  | some (_, bargs) => if bargs.size ≥ 1 then extractKey bargs[0]! else pure none
                  | none            => pure none)
    match usesOuter, keyOpt, rowEl? with
    | false, some (keyV, newAttrs), some (rowTag, bargs) =>
        let rowTagL : Term := ⟨Syntax.mkStrLit rowTag⟩
        let rowKids : Term ← if bargs.size ≥ 2 then pure ⟨bargs[1]!⟩ else `([])
        let body' ← `(Qed.el $rowTagL $newAttrs $rowKids)
        let rowL : Term := ⟨← viewLift binderId #[] body'⟩
        let pos   := (stx.getPos?.map (·.byteIdx)).getD 0
        let prefT : Term := ⟨Syntax.mkStrLit (toString pos ++ "@")⟩
        return some (← `(Qed.V.forEach $tagL $(← mkModelFn m fields xsArrT) (fun $binderId => toString $keyV) $rowL (attrs := $attrsL) (sigPrefix := $prefT)))
    | _, _, _ =>
        let rowL : Term := ⟨← viewLift binderId #[] body⟩
        let rowsTerm ← if isForEachItems then
          `((Qed.ForEachItems.toList $xsT).map (fun $binderId => Qed.View.render $rowL $binderId))
        else
          `((($xsT).map (fun $binderId => Qed.View.render $rowL $binderId)).toList)
        let dynFn ← mkModelFn m fields (← `(Qed.Html.element $tagL (($attrsL).map (Qed.VAttr.eval $m)) $rowsTerm))
        return some (← `(Qed.V.dynNode $dynFn))
end

namespace Internal
open Lean in
def liftViewWithFields (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax :=
  viewLift m fields stx
end Internal

end Qed
