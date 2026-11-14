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

private def htmlTags : List String :=
  ["div", "span", "p", "h1", "h2", "h3", "h4", "h5", "h6", "ul", "ol", "li", "a", "nav",
   "header", "footer", "section", "article", "button", "label", "table", "thead", "tbody",
   "tfoot", "tr", "td", "th", "strong", "em", "select", "option", "input", "textarea",
   "img", "br", "hr", "small", "pre", "code", "b", "i", "main", "aside", "figure",
   "figcaption", "blockquote", "ol", "fieldset", "legend", "datalist", "progress", "meter"]

private def elementTag? (n : Lean.Name) : Option String :=
  match lastStr? n.eraseMacroScopes with
  | some "formEl" => some "form"
  | some s        => if htmlTags.contains s then some s else none
  | none          => none

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
          if lastStr? n.eraseMacroScopes == some "el" then
            if 0 < args.size then
              match args[0]!.isStrLit? with
              | some tag => some (tag, args.extract 1 args.size)
              | none     => none
            else none
          else
            match elementTag? n with
            | some tag => some (tag, args)
            | none     => none
      | _ => none
  | none => none

open Lean in
private def asMap? (stx : Syntax) : Option (Syntax × Syntax) :=
  let stx :=
    let s := unparen stx
    if s.getKind == `Lean.Parser.Term.proj && s.getArgs.size == 3
        && s.getArgs[2]!.getId.eraseMacroScopes == `toList
    then s.getArgs[0]! else stx
  match asApp? (unparen stx) with
  | some (fn, args) =>
      if args.size == 1 then
        match fn with
        | .ident _ _ n _ =>
             if lastStr? n.eraseMacroScopes == some "map" then
              some (mkIdentFrom fn (dropLastComp n.eraseMacroScopes), unparen args[0]!)
            else none
        | _ => none
      else none
  | none => none

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

open Lean Lean.Elab Lean.Elab.Term Lean.Meta in
elab "child% " "fun " mb:ident " => " body:term : term <= expectedType => do
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
          if b'.isAppOfArity ``Qed.View.render 4 then
            let v   := b'.getArg! 2
            let arg := b'.getArg! 3
            if !v.containsFVar fv.fvarId! then
              if arg == fv then return v
              else return (← mkAppM ``Qed.View.mapScope #[← mkLambdaFVars #[fv] arg, v])
          if b'.isAppOfArity ``Qed.lazy 5 then
            let α    := b'.getArg! 0
            let inst := b'.getArg! 2
            let f    := b'.getArg! 3
            let a    := b'.getArg! 4
            if f.containsFVar fv.fvarId! || inst.containsFVar fv.fvarId! || α.containsFVar fv.fvarId! then
              throwErrorAt body "Qed.lazy function must not capture model variable `{mb.getId}` directly; pass all model dependencies through the `[LawfulKey]` argument so memoization stays sound"
            return (← mkAppOptM ``Qed.V.memo #[α, σ, msg, inst, f, ← mkLambdaFVars #[fv] a])
          mkAppOptM ``Qed.View.dynNode #[σ, msg, ← mkLambdaFVars #[fv] b']
  | _ => throwError "child% expects a `View` expected type"

open Lean in
mutual
  partial def viewLift (m : Ident) (stx : Syntax) : MacroM Syntax := do
    match stx with
    | `(text $e:term) =>
        if viewMentions m.getId e then return (← `(Qed.V.dyn (fun $m => toString $e)))
        else return (← `(Qed.V.text (toString $e)))
    | `(if $c:term then $t:term else $e:term) =>
        let t' : Term := ⟨← viewLift m t⟩
        let e' : Term := ⟨← viewLift m e⟩
        if viewMentions m.getId c then
          return (← `(Qed.V.ifElse (fun $m => if $c then true else false) $t' $e'))
        else
          return (← `(if $c then $t' else $e'))
    | _ =>
        if stx.isStrLit?.isSome then return stx
        if stx.getKind == kMatch && viewMentions m.getId stx then
          let raw : Term := ⟨stx⟩
          return (← `(Qed.V.dynNode (fun $m => $raw)))
        if let some out ← tryForEach m stx then return out
        if let some out ← tryElement m stx then return out
        catchAll m stx

  partial def tryElement (m : Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, args) := asElementApp? stx | return none
    if args.size > 2 then return none
    let empty : Term ← `([])
    let attrsO ← if args.size ≥ 1 then liftAttrList m args[0]! else pure (some empty)
    let kidsO  ← if args.size ≥ 2 then liftKidList  m args[1]! else pure (some empty)
    match attrsO, kidsO with
    | some attrsL, some kidsL =>
        let tagL : Term := ⟨Syntax.mkStrLit tag⟩
        return some (← `(Qed.V.el $tagL $attrsL $kidsL))
    | _, _ => return none

  partial def liftAttrList (m : Ident) (lst : Syntax) : MacroM (Option Term) := do
    if lst.getKind != kList || lst.getArgs.size != 3 then return none
    let lifted ← lst.getArgs[1]!.getSepArgs.mapM fun a => do
      let aT : Term := ⟨a⟩
      match ← tryAttr m a with
      | some a' => pure (⟨a'⟩ : Term)
      | none    =>
          if viewMentions m.getId a then `(Qed.VAttr.bind (fun $m => $aT))
          -- Explicit `.stat` rather than coercion because `σ` may still be an unresolved metavar.
          else `(Qed.VAttr.stat $aT)
    return some (← `([$lifted,*]))

  partial def liftKidList (m : Ident) (lst : Syntax) : MacroM (Option Term) := do
    if lst.getKind != kList || lst.getArgs.size != 3 then return none
    let lifted ← lst.getArgs[1]!.getSepArgs.mapM fun k => do pure (⟨← viewLift m k⟩ : Term)
    return some (← `([$lifted,*]))

  partial def catchAll (m : Ident) (stx : Syntax) : MacroM Syntax := do
    let e : Term := ⟨stx⟩
    if viewMentions m.getId stx then return (← `(child% fun $m => $e))
    else return (← `(Qed.V.static $e))

  partial def tryAttr (m : Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (fn, args) := asApp? stx | return none
    match fn with
    | .ident _ _ n _ =>
        let hn := (lastStr? n.eraseMacroScopes).getD ""
        if let some an := stringAttrName? hn then
          if args.size == 1 && viewMentions m.getId args[0]! then
            let nm : Term := ⟨Syntax.mkStrLit an⟩
            let rawV : Term := ⟨args[0]!⟩
            let v : Term ← if hn == "href" || hn == "src" || hn == "action" then `(Qed.ToHref.toHref $rawV)
                           else if hn == "value" then `(toString $rawV)
                           else pure rawV
            return some (← `(Qed.V.dynAttr $nm (fun $m => $v)))
        if hn == "attr" && args.size == 2 && viewMentions m.getId args[1]! then
          let k : Term := ⟨args[0]!⟩
          let v : Term := ⟨args[1]!⟩
          return some (← `(Qed.V.dynAttr $k (fun $m => toString $v)))
        if let some pn := eventPrime? hn then
          if args.size == 1 && viewMentions m.getId args[0]! then
            let primed := mkIdent ((`Qed.V).append (Name.mkSimple pn))
            let v : Term := ⟨args[0]!⟩
            return some (← `($primed (fun $m => $v)))
        return none
    | _ => return none

  partial def tryForEach (m : Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (tag, pargs) := asElementApp? stx | return none
    if pargs.size != 2 then return none
    let some (xs, funArg) := asMap? pargs[1]! | return none
    let some (binder, body) := asFun? funArg | return none
    let binderId : Ident := ⟨binder⟩
    let attrsL : Term ← (match ← liftAttrList m pargs[0]! with | some a => pure a | none => pure ⟨pargs[0]!⟩)
    let xsT    : Term := ⟨xs⟩
    let tagL   : Term := ⟨Syntax.mkStrLit tag⟩
    let rowEl? := asElementApp? body
    let keyOpt ← (match rowEl? with
                  | some (_, bargs) => if bargs.size ≥ 1 then extractKey bargs[0]! else pure none
                  | none            => pure none)
    match keyOpt, rowEl? with
    | some (keyV, newAttrs), some (rowTag, bargs) =>
        let rowTagL : Term := ⟨Syntax.mkStrLit rowTag⟩
        let rowKids : Term ← if bargs.size ≥ 2 then pure ⟨bargs[1]!⟩ else `([])
        let body' ← `(Qed.el $rowTagL $newAttrs $rowKids)
        let rowL : Term := ⟨← viewLift binderId body'⟩
        let pos   := (stx.getPos?.map (·.byteIdx)).getD 0
        let prefT : Term := ⟨Syntax.mkStrLit (toString pos ++ "@")⟩
        return some (← `(Qed.V.forEach $tagL (fun $m => $xsT) (fun $binderId => toString $keyV) $rowL (attrs := $attrsL) (sigPrefix := $prefT)))
    | _, _ =>
        let rowL : Term := ⟨← viewLift binderId body⟩
        return some (← `(Qed.V.dynNode (fun $m =>
          Qed.Html.element $tagL (($attrsL).map (Qed.VAttr.eval $m))
            (($xsT).map (fun $binderId => Qed.View.render $rowL $binderId)).toList)))
end

open Lean in
macro "view% " "fun " m:ident " => " body:term : term => do
  return ⟨← viewLift m body⟩

end Qed
