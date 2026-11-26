import Qed.View.Core
import Lean

namespace Qed
section ViewLift
open Lean

private partial def viewMentions (m : Name) : Syntax → Bool
  | .ident _ _ n _ => m.isPrefixOf n | .node _ _ args => args.any (viewMentions m) | _ => false

private def stringAttrName? : String → Option String
  | "cls" => some "class" | "type'" => some "type"
  | s => if s == "value" || s == "placeholder" || s == "style" || s == "href" || s == "src" || s == "action" || s == "alt" || s == "title" || s == "name" then some s else none

private def isNode (s : Syntax) (k : Name) (n : Nat) : Bool := s.getKind == k && s.getArgs.size == n
private def unparen (s : Syntax) : Syntax := if isNode s `Lean.Parser.Term.paren 3 then s.getArgs[1]! else s
private def asApp? (s : Syntax) : Option (Syntax × Array Syntax) := if isNode s `Lean.Parser.Term.app 2 then some (s.getArgs[0]!, s.getArgs[1]!.getArgs) else none
private def asListElems? (s : Syntax) : Option (Array Syntax) := if isNode s `«term[_]» 3 then some s.getArgs[1]!.getSepArgs else none

private def asIdentApp? (s : Syntax) : Option (String × Array Syntax) :=
  match asApp? s with
  | some (.ident _ _ n _, args) => match n.eraseMacroScopes with | .str _ k => some (k, args) | _ => none
  | _ => none

private def asElementApp? (s : Syntax) : Option (String × Array Syntax) :=
  match asIdentApp? (unparen s) with
  | some ("el", args) => if 0 < args.size then args[0]!.isStrLit?.map (·, args.extract 1 args.size) else none | _ => none

private def asProj? (s : Syntax) (field : Name) : Option Syntax :=
  let s := unparen s; if isNode s `Lean.Parser.Term.proj 3 && s.getArgs[2]!.getId.eraseMacroScopes == field then some s.getArgs[0]! else none

private def unwrapForEachItems (recv : Syntax) : Syntax × Bool :=
  let r := unparen recv
  match asApp? r with
  | some (.ident _ _ rn _, #[xs]) => if rn.eraseMacroScopes == ``Qed.ForEachItems.toList then (unparen xs, true) else (r, false) | _ => (r, false)

private def asMap? (stx : Syntax) : Option (Syntax × Syntax × Bool) :=
  match asApp? (unparen ((asProj? stx `toList).getD stx)) with
  | some (.ident _ _ n _, #[recv, fnArg]) => if n.eraseMacroScopes == ``Qed.mapList then let (xs, fe) := unwrapForEachItems recv; some (xs, unparen fnArg, fe) else none
  | some (fn@(.ident _ _ n _), #[fnArg]) => match n.eraseMacroScopes with | .str p "map" => some (mkIdentFrom fn p, unparen fnArg, false) | _ => none
  | some (fn, #[fnArg]) => (asProj? fn `map).map fun recv => let (xs, fe) := unwrapForEachItems recv; (xs, unparen fnArg, fe)
  | _ => none

private def asFun? (s : Syntax) : Option (Syntax × Syntax) :=
  let s := unparen s
  if s.getKind == `Lean.Parser.Term.fun && s.getArgs.size ≥ 2 then
    let b := s.getArgs[1]!
    if b.getKind == `Lean.Parser.Term.basicFun && b.getArgs.size ≥ 4 && b.getArgs[0]!.getArgs.size == 1 then some (b.getArgs[0]!.getArgs[0]!, b.getArgs[3]!) else none
  else none

private def extractKey (attrsList : Syntax) : MacroM (Option (Term × Term)) := do
  let some elems := asListElems? attrsList | return none
  let (keyV, kept) := elems.foldl (init := (none, (#[] : Array Term))) fun (kv, acc) e =>
    match asIdentApp? e with | some ("key", #[v]) => (some v, acc) | _ => (kv, acc.push ⟨e⟩)
  match keyV with | some v => return some (⟨v⟩, ← `([$kept,*])) | none => return none

private def viewMentionsAny (m : Name) (fields : Array Ident) (s : Syntax) : Bool := viewMentions m s || fields.any (viewMentions ·.getId s)
private def wrapFieldLets (m : Ident) (fields : Array Ident) (body : Term) : MacroM Term :=
  fields.foldrM (init := body) fun f out => if viewMentions f.getId out.raw then `(let $f:ident := $m.$f:ident; $out) else pure out
private def mkModelFn (m : Ident) (fields : Array Ident) (body : Term) : MacroM Term := do `(fun $m => $(← wrapFieldLets m fields body))

private def stripFieldLets (fv : Expr) : Nat → Expr → Expr
  | fuel + 1, .letE n ty val body nonDep => if val.containsFVar fv.fvarId! then stripFieldLets fv fuel (body.instantiate1 val) else .letE n ty val body nonDep
  | _, e => e

open Lean.Elab Lean.Elab.Term Lean.Meta in
elab "qedInternalChild% " "fun " mb:ident " => " body:term : term <= expectedType => do
  match_expr (← instantiateMVars expectedType) with
  | Qed.View σ msg =>
      if (← instantiateMVars σ).isMVar then tryPostpone
      withLocalDeclD mb.getId σ fun fv => do
        let b ← elabTerm body none; let bTy ← whnf (← instantiateMVars (← inferType b))
        if bTy.isConstOf ``String then mkAppOptM ``Qed.View.dyn #[σ, msg, ← mkLambdaFVars #[fv] b]
        else if bTy.isAppOfArity ``Qed.View 2 then ensureHasType expectedType b
        else
          let isToStr ← if !bTy.hasMVar && !bTy.isAppOfArity ``Qed.Html 1 && !bTy.isAppOfArity ``Option 1 then
            if (← whnf (← inferType bTy)) == .sort (Level.succ .zero) then
              pure ((← trySynthInstance (mkApp (mkConst ``ToString [Level.zero]) bTy)) matches .some _)
            else pure false
          else pure false
          if isToStr then mkAppOptM ``Qed.View.dyn #[σ, msg, ← mkLambdaFVars #[fv] (← mkAppM ``toString #[b])]
          else
            let b' ← instantiateMVars (← ensureHasType (← mkAppM ``Qed.Html #[msg]) b); let bCore := stripFieldLets fv 64 b'
            if bCore.isAppOfArity ``Qed.View.render 4 then
              let v := bCore.getArg! 2; let arg := bCore.getArg! 3
              if !v.containsFVar fv.fvarId! then
                if arg == fv then return v else return (← mkAppM ``Qed.View.mapScope #[← mkLambdaFVars #[fv] arg, v])
            if bCore.isAppOfArity ``Qed.lazy 5 then
              let (α, inst, f, a) := (bCore.getArg! 0, bCore.getArg! 2, bCore.getArg! 3, bCore.getArg! 4)
              if f.containsFVar fv.fvarId! || inst.containsFVar fv.fvarId! || α.containsFVar fv.fvarId! then
                logErrorAt body "Qed.lazy function must not capture state directly; pass all state dependencies through the `[LawfulKey]` argument so memoization stays sound"
                return ← mkAppOptM ``Qed.View.text #[σ, msg, mkStrLit ""]
              return ← mkAppOptM ``Qed.V.memo #[α, σ, msg, inst, f, ← mkLambdaFVars #[fv] a]
            mkAppOptM ``Qed.View.dynNode #[σ, msg, ← mkLambdaFVars #[fv] b']
  | _ => throwError "qedInternalChild% expects a `View` expected type"

private def catchAll (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax := do
  if viewMentionsAny m.getId fields stx then return (← `(qedInternalChild% fun $m => $(← wrapFieldLets m fields ⟨stx⟩)))
  else return (← `(Qed.V.static $(⟨stx⟩)))

private def tryAttr (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
  let some (hn, args) := asIdentApp? stx | return none
  if let some an := stringAttrName? hn then
    if args.size == 1 && viewMentionsAny m.getId fields args[0]! then
      let rawV : Term := ⟨args[0]!⟩
      let v : Term ← if hn == "href" || hn == "src" || hn == "action" then `(Qed.ToHref.toHref $rawV) else if hn == "value" then `(toString $rawV) else pure rawV
      return some (← `(Qed.V.dynAttr $(⟨Syntax.mkStrLit an⟩) $(← mkModelFn m fields v)))
  if hn == "attr" && args.size == 2 && viewMentionsAny m.getId fields args[1]! then
    return some (← `(Qed.V.dynAttr $(⟨args[0]!⟩) $(← mkModelFn m fields (← `(toString $(⟨args[1]!⟩))))))
  if ["onClick", "onInput", "onCheck"].contains hn && args.size == 1 && viewMentionsAny m.getId fields args[0]! then
    return some (← `($(mkIdent ((`Qed.V).append (Name.mkSimple (hn ++ "'")))) $(← mkModelFn m fields ⟨args[0]!⟩)))
  return none

private def liftAttrList (m : Ident) (fields : Array Ident) (lst : Syntax) : MacroM (Option Term) := do
  let some elems := asListElems? lst | return none
  let lifted ← elems.mapM fun a => do
    match ← tryAttr m fields a with
    | some a' => pure (⟨a'⟩ : Term)
    | none => if viewMentionsAny m.getId fields a then `(Qed.VAttr.bind $(← mkModelFn m fields ⟨a⟩)) else `(Qed.VAttr.stat $(⟨a⟩))
  return some (← `([$lifted,*]))

mutual
  partial def viewLift (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax := withRef stx do
    let liftIf (c t e : Term) (h? : Option Ident) : MacroM Syntax := do
      let t' : Term := ⟨← viewLift m fields t⟩; let e' : Term := ⟨← viewLift m fields e⟩
      let mkIte (a b : Term) := match h? with | some h => `(if $h:ident : $c then $a else $b) | none => `(if $c then $a else $b)
      if viewMentionsAny m.getId fields c then return (← `(Qed.V.ifElse $(← mkModelFn m fields (← mkIte (← `(true)) (← `(false)))) $t' $e'))
      else return (← mkIte t' e')
    match stx with
    | `(text $e:term) => if viewMentionsAny m.getId fields e then return (← `(Qed.V.dyn $(← mkModelFn m fields (← `(toString $e))))) else return (← `(Qed.V.text (toString $e)))
    | `(if $c:term then $t:term else $e:term) => liftIf c t e none
    | `(if $h:ident : $c:term then $t:term else $e:term) => if !viewMentionsAny h.getId #[] t && !viewMentionsAny h.getId #[] e then liftIf c t e (some h) else catchAll m fields stx
    | _ =>
        if stx.isStrLit?.isSome then return stx
        if stx.getKind == `Lean.Parser.Term.match && viewMentionsAny m.getId fields stx then return (← `(Qed.V.dynNode $(← mkModelFn m fields ⟨stx⟩)))
        if let some out ← tryForEach m fields stx then return out
        if let some out ← tryElement m fields stx then return out
        catchAll m fields stx

  partial def tryElement (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, args) := asElementApp? stx | return none
    if args.size > 2 then return none
    let empty : Term ← `([])
    let some attrsL ← (if args.size ≥ 1 then liftAttrList m fields args[0]! else pure (some empty)) | return none
    let some kidsL ← (if args.size ≥ 2 then
      match asListElems? args[1]! with | some elems => do let ks ← elems.mapM (fun k => do pure (⟨← viewLift m fields k⟩ : Term)); pure (some (← `([$ks,*]))) | none => pure none
      else pure (some empty)) | return none
    return some (← `(Qed.V.el $(⟨Syntax.mkStrLit tag⟩) $attrsL $kidsL))

  partial def tryForEach (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, pargs) := asElementApp? stx | return none
    if pargs.size != 2 then return none
    let some (xs, funArg, isFE) := asMap? pargs[1]! | return none
    let some (binder, body) := asFun? funArg | return none
    let binderId : Ident := ⟨binder⟩; let attrsL : Term := (← liftAttrList m fields pargs[0]!).getD ⟨pargs[0]!⟩
    let xsT : Term := ⟨xs⟩; let tagL : Term := ⟨Syntax.mkStrLit tag⟩
    let usesOuter := viewMentions m.getId body || (fields.filter (·.getId != binderId.getId)).any (viewMentions ·.getId body)
    let rowEl? := asElementApp? body
    let keyOpt ← match rowEl? with | some (_, bargs) => if bargs.size ≥ 1 then extractKey bargs[0]! else pure none | none => pure none
    match usesOuter, keyOpt, rowEl? with
    | false, some (keyV, newAttrs), some (rowTag, bargs) =>
        let rowKids : Term ← if bargs.size ≥ 2 then pure ⟨bargs[1]!⟩ else `([])
        let rowL : Term := ⟨← viewLift binderId #[] (← `(Qed.el $(⟨Syntax.mkStrLit rowTag⟩) $newAttrs $rowKids))⟩
        let xsArrT : Term ← if isFE then `(Qed.ForEachItems.toArray $xsT) else pure xsT
        let prefT : Term := ⟨Syntax.mkStrLit (toString ((stx.getPos?.map (·.byteIdx)).getD 0) ++ "@")⟩
        return some (← `(Qed.V.forEach $tagL $(← mkModelFn m fields xsArrT) (fun $binderId => toString $keyV) $rowL (attrs := $attrsL) (sigPrefix := $prefT)))
    | _, _, _ =>
        let rowL : Term := ⟨← viewLift binderId #[] body⟩
        let rowsTerm ← if isFE then `((Qed.ForEachItems.toList $xsT).map (fun $binderId => Qed.View.render $rowL $binderId))
                       else `((($xsT).map (fun $binderId => Qed.View.render $rowL $binderId)).toList)
        return some (← `(Qed.V.dynNode $(← mkModelFn m fields (← `(Qed.Html.element $tagL (($attrsL).map (Qed.VAttr.eval $m)) $rowsTerm)))))
end

namespace Internal
def liftViewWithFields (m : Ident) (fields : Array Ident) (stx : Syntax) : MacroM Syntax := viewLift m fields stx
end Internal

end ViewLift
end Qed
