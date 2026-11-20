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

private def checkInlineComp (stx : Syntax) (pPath tag : String) (hasKids : Bool) (info : ComponentInfo) :
    TermElabM Unit := do
  if let some rtag := info.rootTag? then checkParentNesting stx pPath tag rtag
  if hasKids && !info.hasChildren then
    throwErrorAt stx s!"<{tag}> does not render `\{children}` in its `view:`; write `<{tag} …/>` or render `\{children}` in `{tag}`"

private def finishWithKey (expectedType? : Option Expr) (key? : Option Term) (call : Term) : TermElabM Expr := do
  elabTerm (← match key? with | some k => `(Qed.withKey (toString $k) $call) | none => pure call) expectedType?

private def elabSchemaFormTag (stx : Syntax) (expectedType? : Option Expr)
    (tag pPath : String) (cName : Name) (propNodes : Array Syntax) (hasKids : Bool) :
    TermElabM (Option Expr) := do
  let some sInfo ← lookupSchemaForm? cName | return none
  if hasKids then
    throwErrorAt stx s!"<{tag}> takes no children; write it self-closing (<{tag} …/>)"
  checkParentNesting stx pPath tag "div"
  let mut key?    : Option Term := none
  let mut bind?   : Option Term := none
  let mut submit? : Option Term := none
  let mut ctxProps : Array (Syntax × String × Term) := #[]
  for p in propNodes do
    let nm := (⟨(p.getArg 0)⟩ : TSyntax `str).getString
    let v : Term := ⟨(p.getArg 2)⟩
    if nm == "key" then key? := some v
    else if nm == "bind" then bind? := some v
    else if nm == "onSubmit" then submit? := some v
    else if nm == "reset" then
      throwErrorAt (p.getArg 0) s!"<{tag}>: `reset` is only supported inside a `component` view"
    else
      ctxProps := ctxProps.push ((p.getArg 0), nm, v)
  let some b := bind?
    | throwErrorAt stx s!"<{tag}> requires `bind=\{draft}` when used outside a `component` view"
  let dVal ← `(($b).1)
  let onEditVal ← `(($b).2)
  let some submitVal := submit?
    | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
  let ctxArgs ← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps
  let mut callT : Term := ⟨mkIdentFrom stx sInfo.formViewName⟩
  for ca in ctxArgs do
    callT ← `($callT $ca)
  callT ← `($callT $dVal $onEditVal $submitVal)
  some <$> finishWithKey expectedType? key? callT

private def elabPureCompTag (stx : Syntax) (expectedType? : Option Expr) (info : ComponentInfo)
    (cId : Name → Term) (pPath tag : String) (propNodes : Array Syntax) (kidsT : Term) (hasKids : Bool) :
    TermElabM Expr := do
  checkInlineComp stx pPath tag hasKids info
  let mut key? : Option Term := none
  let mut fids : Array Ident := #[]
  let mut vals : Array Term  := #[]
  for p in propNodes do
    let nm := (⟨(p.getArg 0)⟩ : TSyntax `str).getString
    let v : Term := ⟨(p.getArg 2)⟩
    if nm == "key" then key? := some v
    else if nm.startsWith "bind:" then
      let bStr := (nm.drop 5).toString
      fids := fids.push (mkIdentFrom (p.getArg 0) (Name.mkSimple bStr))
      vals := vals.push (← `(($v).1))
      fids := fids.push (mkIdentFrom (p.getArg 0) (Name.mkSimple s!"set_{bStr}"))
      vals := vals.push (← `(($v).2))
    else
      fids := fids.push (mkIdentFrom (p.getArg 0) (Name.mkSimple nm))
      vals := vals.push v
  if hasKids then fids := fids.push (mkIdentFrom stx `children); vals := vals.push kidsT
  let callT ← if info.hasProps then
    `($(cId `view) ({ $[$fids:ident := $vals],* } : $(cId `Props) _))
  else `($(cId `view))
  finishWithKey expectedType? key? callT

private def elabHoistedCompTag (stx : Syntax) (expectedType? : Option Expr) (info? : Option ComponentInfo)
    (tag pPath : String) (hasKids : Bool) (cId : Name → Term) (props : Array (Syntax × String × Term))
    (kidsT hPair : Term) (key? : Option Term) : TermElabM Expr := do
  let some info := info? | throwErrorAt stx s!"internal: missing ComponentInfo for hoisted <{tag}>"
  checkInlineComp stx pPath tag hasKids info
  let mut dataFids : Array Ident := #[]
  let mut dataVals : Array Term  := #[]
  let mut slotArgs : Array (TSyntax ``Lean.Parser.Term.argument) := #[]
  for (ref, nm, v) in props do
    let id := mkIdentFrom ref (Name.mkSimple nm)
    if info.slotNames.contains id.getId then
      slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($id:ident := $v)))
    else
      dataFids := dataFids.push id; dataVals := dataVals.push v
  if hasKids then
    slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($(mkIdentFrom stx `children):ident := $kidsT)))
  let wrapA ← `(Lean.Parser.Term.argument| ($hPair).1)
  let subSA ← `(Lean.Parser.Term.argument| ($hPair).2)
  let baseArgs ← if info.hasProps then
    let propRec ← `(({ $[$dataFids:ident := $dataVals],* } : $(cId `Props)))
    pure #[← `(Lean.Parser.Term.argument| $propRec:term), wrapA, subSA]
  else pure #[wrapA, subSA]
  let renderCall : Term := ⟨Syntax.node .none ``Lean.Parser.Term.app
    #[(cId `_qed_render).raw, Syntax.node .none nullKind ((baseArgs ++ slotArgs).map (·.raw))]⟩
  finishWithKey expectedType? key? renderCall

private def elabStatefulCompTag (stx : Syntax) (expectedType? : Option Expr) (info? : Option ComponentInfo)
    (baseName : Name) (cId : Name → Term) (tag pPath : String) (posNum : Nat)
    (props : Array (Syntax × String × Term)) (key? state? initial? onMsg? : Option Term) :
    TermElabM Expr := do
  let evSigs := match info? with | some i => i.events | none => #[]
  let mut dataProps : Array (Syntax × String × Term) := #[]
  let mut evArms    : Array OutArm := #[]
  for (ref, nm, v) in props do
    if nm.startsWith "bind:" then
      let bStr := (nm.drop 5).toString
      dataProps := dataProps.push (ref, bStr, ← `(($v).1))
      evArms := evArms.push { ctor := Name.mkSimple s!"set_{bStr}", arity := 1, handler := ← `(($v).2) }
    else if let some sig := evSigs.find? (·.name.toString == nm) then
      evArms := evArms.push { ctor := sig.name, arity := sig.arity, handler := v }
    else
      dataProps := dataProps.push (ref, nm, v)

  let fids := dataProps.map fun (ref, n, _) => mkIdentFrom ref (Name.mkSimple n)
  let vals := dataProps.map (·.2.2)
  let propValues ← `(({ $[$fids:ident := $vals],* } : $(cId `Props)))

  if let some st := state? then
    if initial?.isSome then
      throwErrorAt stx s!"<{tag}>: `initial` seeds local state and cannot be combined with parent-owned `state=\{...}`"
    if !evArms.isEmpty then
      let evNames := String.intercalate ", " (evArms.toList.map fun a => s!"`{a.ctor}`")
      throwErrorAt stx s!"<{tag} state=…>: a parent-owned component routes every event through `onMsg` (cannot also pass event props {evNames})"
    let some route := onMsg?
      | throwErrorAt stx s!"<{tag} state=…> requires `onMsg=\{...}`: pass the parent message constructor `(k : String) (msg : {tag}.Msg)` (or declare `collection <field> : {tag}` so Qed wires `onMsg` automatically)"
    let resT ← match key? with
      | some k => `(Qed.withKey (toString $k) ($(cId `_qed_renderTag) $propValues $route $st (toString $k)))
      | none   => `($(cId `_qed_renderTag) $propValues $route $st)
    return ← elabTerm resT expectedType?

  if onMsg?.isSome then
    throwErrorAt stx s!"<{tag}>: `onMsg` routes a parent-owned row; pass `state=\{...}` alongside `onMsg`, or remove `onMsg` and pass named event props"
  if let some info := info? then
    if !info.hasLocalDef then
      throwErrorAt stx s!"<{tag}> uses effects, `Html` props, `children`, or non-JSON props and cannot be mounted dynamically via `LocalDef`; mount `<{tag} …/>` directly inside a parent `component` view so Qed hoists its state"
  checkParentNesting stx pPath "div" "div"
  let keyT : Term ← match key? with | some k => `(toString $k) | none => pure ⟨Syntax.mkStrLit s!"@{posNum}"⟩
  let mountBase : Term ←
    if !evArms.isEmpty then
      let outVar := mkIdent `_out
      let totalOutCtors := (info?.map fun i => i.events.size + i.bindNames.size).getD 999
      let mTerm ← liftMacroM <| mkOutMatchTerm baseName totalOutCtors evArms outVar
      `($(cId `_qed_mountWithOpt) $keyT (fun $outVar:ident => $mTerm))
    else
      `($(cId `_qed_mount) $keyT)
  let mountBase ← match initial? with
    | none      => pure mountBase
    | some seed => `(Qed.Attr.localInit $mountBase ($seed : $(cId `State)))
  let mountT ← `(Qed.Attr.localProps $mountBase $propValues)
  elabTerm (← `(Qed.el "div" [Qed.key $keyT, $mountT] [])) expectedType?

@[term_elab Qed.Jsx.qedCompTerm] def elabQedCompTerm : TermElab := fun stx expectedType? => do
  let tag := (⟨(stx.getArg 1)⟩ : TSyntax `str).getString
  let pPath := (⟨(stx.getArg 2)⟩ : TSyntax `str).getString
  let posNum := (⟨(stx.getArg 3)⟩ : TSyntax `num).getNat
  let propNodes := (stx.getArg 5).getSepArgs
  let kidsT : Term := ⟨(stx.getArg 7)⟩
  let hasKids := !(kidsT.raw.getKind == `«term[_]» && (kidsT.raw.getArg 1).getArgs.isEmpty)
  let cName := (tag.splitOn ".").foldl Name.str Name.anonymous
  let info? ← lookupComponent? cName
  let baseName := match info? with | some info => info.fullName | none => cName
  let cId (sub : Name) : Term := ⟨mkIdentFrom stx (baseName ++ sub)⟩

  if info?.isNone && tag.endsWith ".Form" then
    if let some res ← elabSchemaFormTag stx expectedType? tag pPath cName propNodes hasKids then
      return res
    let schemaNm := String.ofList (tag.toList.take (tag.length - 5))
    throwErrorAt stx s!"unknown schema form `<{tag}>`; check that `schema {schemaNm}:` is defined and imported"

  if info?.isNone then
    let env ← getEnv
    unless env.contains (baseName ++ `_qed_mount) || env.contains (baseName ++ `_qed_renderTag) do
      let lowerHint := if !tag.contains '.' then s!" (HTML elements must be lowercase, e.g. `<{tag.toLower}>`)" else ""
      throwErrorAt stx s!"unknown component `<{tag}>`; check the spelling or import the module defining `component {tag}:`{lowerHint}"

  if let some info := info? then
    if info.kind == .pureView then
      return ← elabPureCompTag stx expectedType? info cId pPath tag propNodes kidsT hasKids

  let mut props    : Array (Syntax × String × Term) := #[]
  let mut key?     : Option Term := none
  let mut state?   : Option Term := none
  let mut initial? : Option Term := none
  let mut onMsg?   : Option Term := none
  let mut hoist?   : Option Term := none
  for p in propNodes do
    let nm := (⟨(p.getArg 0)⟩ : TSyntax `str).getString
    let v : Term := ⟨(p.getArg 2)⟩
    match nm with
    | "key"     => key?     := some v
    | "state"   => state?   := some v
    | "initial" => initial? := some v
    | "onMsg"   => onMsg?   := some v
    | "_hoist"  => hoist?   := some v
    | _         => props    := props.push ((p.getArg 0), nm, v)

  if let some hPair := hoist? then
    return ← elabHoistedCompTag stx expectedType? info? tag pPath hasKids cId props kidsT hPair key?

  if hasKids then
    throwErrorAt stx s!"<{tag}> does not render `\{children}` in its `view:`; write it self-closing (`<{tag} …/>`) or render `\{children}` in `{tag}`"

  elabStatefulCompTag stx expectedType? info? baseName cId tag pPath posNum props key? state? initial? onMsg?

end CompElab
end Qed
