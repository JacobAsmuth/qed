import Qed.Component.Syntax
import Qed.Schema.Registry
import Qed.Runtime.LocalCore

namespace Qed
section CompElab
open Lean Elab Command Term

/-! ## JSX `<Component …>…</Component>` Term Elaborator (`elabQedCompTerm`) -/

private def checkParentNesting (ref : Syntax) (pPath compLabel childTag : String) : TermElabM Unit := do
  if let some (ptag, pctx) := Qed.Jsx.ctxOfPath pPath then
    if (stepHtmlCtx pctx childTag).isNone then
      let what := if compLabel == childTag then s!"<{childTag}>" else s!"<{compLabel}> (root <{childTag}>)"
      throwErrorAt ref s!"invalid HTML5 nesting: {what} is not allowed inside <{ptag}> (browsers rewrite this tree during HTML parsing, causing hydration mismatch)"

private def throwNoChildren (stx : Syntax) (tag : String) : TermElabM Unit :=
  throwErrorAt stx s!"<{tag}> does not render `\{children}` in its `view:`; write it self-closing (`<{tag} …/>`) or render `\{children}` in `{tag}`"

private def checkInlineComp (stx : Syntax) (pPath tag : String) (hasKids : Bool) (info : ComponentInfo) : TermElabM Unit := do
  if let some rtag := info.rootTag? then checkParentNesting stx pPath tag rtag
  if hasKids && !info.hasChildren then throwNoChildren stx tag

private def finishWithKey (expectedType? : Option Expr) (key? : Option Term) (call : Term) : TermElabM Expr := do
  elabTerm (← match key? with | some k => `(Qed.withKey (toString $k) $call) | none => pure call) expectedType?

private def mkPropsRec (pairs : Array (Ident × Term)) (ty : Term) : TermElabM Term := do
  let (fids, vals) := (pairs.map (·.1), pairs.map (·.2)); `( ({ $[$fids:ident := $vals],* } : $ty) )

private def elabSchemaFormTag (stx : Syntax) (expectedType? : Option Expr)
    (tag pPath : String) (cName : Name) (propNodes : Array Syntax) (hasKids : Bool) : TermElabM (Option Expr) := do
  let some sInfo ← lookupSchemaForm? cName | return none
  if hasKids then throwErrorAt stx s!"<{tag}> takes no children; write it self-closing (<{tag} …/>)"
  checkParentNesting stx pPath tag "div"
  let (ctxProps, specials) := splitCompProps propNodes ["key", "bind", "onSubmit", "reset"]
  if let some (resetRef, _) := specials["reset"]? then throwErrorAt resetRef s!"<{tag}>: `reset` is only supported inside a `component` view"
  let some (_, b) := specials["bind"]? | throwErrorAt stx s!"<{tag}> requires `bind=\{draft}` when used outside a `component` view"
  let some (_, submitVal) := specials["onSubmit"]? | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
  let ctxArgs ← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps
  let callT ← Qed.Lang.mkAppTerms ⟨mkIdentFrom stx sInfo.formViewName⟩ (ctxArgs ++ #[← `(($b).1), ← `(($b).2), submitVal])
  some <$> finishWithKey expectedType? (specials["key"]?.map (·.2)) callT

private def partitionBindProps (props : Array (Syntax × String × Term)) (evSigs : Array CompEventSig) (bindAsEvent : Bool) :
    TermElabM (Array (Ident × Term) × Array OutArm) := do
  let mut dataPairs : Array (Ident × Term) := #[]; let mut evArms : Array OutArm := #[]
  for (ref, nm, v) in props do
    if let some (bStr, v1, v2) ← liftMacroM (unpackBindProp nm v) then
      let bNm := Name.mkSimple bStr; let setNm := bindSetName bNm
      dataPairs := dataPairs.push (mkIdentFrom ref bNm, v1)
      if bindAsEvent then evArms := evArms.push (.mk setNm 1 v2)
      else dataPairs := dataPairs.push (mkIdentFrom ref setNm, v2)
    else if let some sig := evSigs.find? (·.name.toString == nm) then
      evArms := evArms.push (.mk sig.name sig.arity v)
    else dataPairs := dataPairs.push (mkIdentFrom ref (Name.mkSimple nm), v)
  return (dataPairs, evArms)

private def elabPureCompTag (stx : Syntax) (expectedType? : Option Expr) (info : ComponentInfo)
    (cId : Name → Term) (pPath tag : String) (propNodes : Array Syntax) (kidsT : Term) (hasKids : Bool) : TermElabM Expr := do
  checkInlineComp stx pPath tag hasKids info
  let (otherProps, specials) := splitCompProps propNodes ["key"]
  let (pairs0, _) ← partitionBindProps otherProps #[] false
  let pairs := if hasKids then pairs0.push (mkIdentFrom stx `children, kidsT) else pairs0
  let callT ← if info.hasProps then `($(cId `view) $(← mkPropsRec pairs (← `($(cId `Props) _)))) else `($(cId `view))
  finishWithKey expectedType? (specials["key"]?.map (·.2)) callT

private def elabHoistedCompTag (stx : Syntax) (expectedType? : Option Expr) (info? : Option ComponentInfo)
    (tag pPath : String) (hasKids : Bool) (cId : Name → Term) (props : Array (Syntax × String × Term))
    (kidsT hPair : Term) (key? : Option Term) : TermElabM Expr := do
  let some info := info? | throwErrorAt stx s!"internal: missing ComponentInfo for hoisted <{tag}>"
  checkInlineComp stx pPath tag hasKids info
  let mut dataPairs : Array (Ident × Term) := #[]; let mut slotArgs : Array (TSyntax ``Lean.Parser.Term.argument) := #[]
  for (ref, nm, v) in props do
    let id := mkIdentFrom ref (Name.mkSimple nm)
    if info.slotNames.contains id.getId then slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($id:ident := $v)))
    else dataPairs := dataPairs.push (id, v)
  if hasKids then slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($(mkIdentFrom stx `children):ident := $kidsT)))
  let (wrapA, subSA) := (← `(Lean.Parser.Term.argument| ($hPair).1), ← `(Lean.Parser.Term.argument| ($hPair).2))
  let baseArgs ← if info.hasProps then pure #[← `(Lean.Parser.Term.argument| $(← mkPropsRec dataPairs (cId `Props)):term), wrapA, subSA] else pure #[wrapA, subSA]
  finishWithKey expectedType? key? ⟨Syntax.node .none ``Lean.Parser.Term.app #[(cId `_qed_render).raw, Syntax.node .none nullKind ((baseArgs ++ slotArgs).map (·.raw))]⟩

private def elabStatefulCompTag (stx : Syntax) (expectedType? : Option Expr) (info? : Option ComponentInfo)
    (baseName : Name) (cId : Name → Term) (tag pPath : String) (posNum : Nat)
    (props : Array (Syntax × String × Term)) (key? state? initial? onMsg? : Option Term) : TermElabM Expr := do
  let (dataPairs, evArms) ← partitionBindProps props (info?.map (·.events) |>.getD #[]) true
  let propValues ← mkPropsRec dataPairs (cId `Props)
  if let some st := state? then
    if initial?.isSome then throwErrorAt stx s!"<{tag}>: `initial` seeds local state and cannot be combined with parent-owned `state=\{...}`"
    if !evArms.isEmpty then
      let evNames := String.intercalate ", " (evArms.toList.map fun a => s!"`{a.ctor}`")
      throwErrorAt stx s!"<{tag} state=…>: a parent-owned component routes every event through `onMsg` (cannot also pass event props {evNames})"
    let some route := onMsg?
      | throwErrorAt stx s!"<{tag} state=…> requires `onMsg=\{...}`: pass the parent message constructor `(k : String) (msg : {tag}.Msg)` (or declare `collection <field> : {tag}` so Qed wires `onMsg` automatically)"
    let resT ← match key? with
      | some k => `(Qed.withKey (toString $k) ($(cId `_qed_renderTag) $propValues $route $st (toString $k)))
      | none   => `($(cId `_qed_renderTag) $propValues $route $st)
    return ← elabTerm resT expectedType?
  if onMsg?.isSome then throwErrorAt stx s!"<{tag}>: `onMsg` routes a parent-owned row; pass `state=\{...}` alongside `onMsg`, or remove `onMsg` and pass named event props"
  if info?.any (!·.hasLocalDef) then
    throwErrorAt stx s!"<{tag}> uses effects, `Html` props, `children`, or non-JSON props and cannot be mounted dynamically via `LocalDef`; mount `<{tag} …/>` directly inside a parent `component` view so Qed hoists its state"
  checkParentNesting stx pPath "div" "div"
  let keyT : Term ← match key? with | some k => `(toString $k) | none => pure ⟨Syntax.mkStrLit s!"@{posNum}"⟩
  let mountBase : Term ← if evArms.isEmpty then `($(cId `_qed_mount) $keyT) else do
    let outVar := mkIdent `_out
    let mTerm ← liftMacroM <| mkOutMatchTerm baseName ((info?.map fun i => i.events.size + i.bindNames.size).getD 999) evArms outVar
    `($(cId `_qed_mountWithOpt) $keyT (fun $outVar:ident => $mTerm))
  let mountBase ← match initial? with | none => pure mountBase | some seed => `(Qed.Attr.localInit $mountBase ($seed : $(cId `State)))
  elabTerm (← `(Qed.el "div" [Qed.key $keyT, Qed.Attr.localProps $mountBase $propValues] [])) expectedType?

@[term_elab Qed.Jsx.qedCompTerm] def elabQedCompTerm : TermElab := fun stx expectedType? => do
  let (tag, pPath, posNum) := ((⟨stx.getArg 1⟩ : TSyntax `str).getString, (⟨stx.getArg 2⟩ : TSyntax `str).getString, (⟨stx.getArg 3⟩ : TSyntax `num).getNat)
  let (propNodes, kidsT) := ((stx.getArg 5).getSepArgs, (⟨stx.getArg 7⟩ : Term))
  let hasKids := !(kidsT.raw.getKind == `«term[_]» && (kidsT.raw.getArg 1).getArgs.isEmpty)
  let cName := tag.toName; let info? ← lookupComponent? cName
  let baseName := info?.map (·.fullName) |>.getD cName
  let cId (sub : Name) : Term := ⟨mkIdentFrom stx (baseName ++ sub)⟩
  if info?.isNone && tag.endsWith ".Form" then
    if let some res ← elabSchemaFormTag stx expectedType? tag pPath cName propNodes hasKids then return res
    throwErrorAt stx s!"unknown schema form `<{tag}>`; check that `schema {String.ofList (tag.toList.take (tag.length - 5))}:` is defined and imported"
  if info?.isNone then
    if ← isFailedComponent cName then return ← elabTerm (← `(Qed.Html.empty)) expectedType?
    let env ← getEnv
    unless env.contains (baseName ++ `_qed_mount) || env.contains (baseName ++ `_qed_renderTag) do
      throwErrorAt stx s!"unknown component `<{tag}>`; check the spelling or import the module defining `component {tag}:`{if !tag.contains '.' then s!" (HTML elements must be lowercase, e.g. `<{tag.toLower}>`)" else ""}"
  if let some info := info? then
    if info.kind == .pureView then return ← elabPureCompTag stx expectedType? info cId pPath tag propNodes kidsT hasKids
  let (props, specials) := splitCompProps propNodes ["key", "state", "initial", "onMsg", "_hoist"]
  let sp (k : String) := specials[k]?.map (·.2)
  if let some hPair := sp "_hoist" then return ← elabHoistedCompTag stx expectedType? info? tag pPath hasKids cId props kidsT hPair (sp "key")
  if hasKids then throwNoChildren stx tag
  elabStatefulCompTag stx expectedType? info? baseName cId tag pPath posNum props (sp "key") (sp "state") (sp "initial") (sp "onMsg")

end CompElab
end Qed
