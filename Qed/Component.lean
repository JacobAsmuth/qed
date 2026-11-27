import Qed.Collection
import Qed.Component.Codegen
import Qed.Component.AwaitLift
import Qed.Component.Speculative
import Qed.Component.Invariants
import Qed.Speculative.Core
import Qed.Speculative.Proofs
import Qed.View
import Qed.Runtime
import Qed.Resource
import Qed.Socket

namespace Qed
section CompElab
open Lean Elab Command Term Qed.Lang

/-! ## Component Command Elaborator (`elabComponentCmd`) -/

private def elabCmds (cs : Array CmdStx) : CommandElabM Unit :=
  Lang.foldlCmd cs () fun _ c => elabCommand c

@[noinline] private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  Lang.foldlCmd spec.mutFns () fun _ f =>
    throwErrorAt f.id s!"`fn {f.id.getId}` has no `-> ReturnType` and mutates component state, but `{spec.t.getId}` has no `state`/`event`/`bind`; add `-> Type` for a pure helper or declare `state`"
  let msgV := mkIdent `msg
  let baseBinders ← Lang.mapCmd spec.props mkStructBinder
  let propFieldTys ← Lang.mapCmd spec.props fun pr => do
    let ty ← match pr.ty?, pr.def? with | some t, _ => pure t | none, some d => Lang.runPQ `(type_of% $d) | none, none => throwErrorAt pr.id s!"`prop {pr.id.getId}` needs a type or default"
    return (pr.id.getId, ty)
  let bindTys ← Lang.mapCmd spec.binds resolveBindTy
  let extraBinders ← Lang.mapCmd (spec.binds.zip bindTys) fun (bd, bTy) =>
    return (← mkStructBinder { bd with ty? := some bTy }, bd.id, bTy)
  let pureFieldTys := propFieldTys ++ (spec.binds.zip bindTys).map fun (bd, bTy) => (bd.id.getId, bTy)
  let (propsCmd, viewBinders, needsProps) ← Lang.runPQ do
    let b1 ← Lang.foldlPQ spec.slots baseBinders fun pb sl => return pb.push (← `(Lean.Parser.Command.structExplicitBinder| ($(sl.id) : Html $msgV := $(← sl.def?.getDM `(Qed.Html.empty)))))
    let b2 ← Lang.foldlPQ extraBinders b1 fun pb (b1', bId, bTy) => return pb.push b1' |>.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdentFrom bId (bindSetName bId.getId)) : $bTy → $msgV)))
    let b3 ← Lang.foldlPQ spec.events b2 fun pb ev => do
      let evTy ← Lang.foldrPQ ev.params (⟨msgV.raw⟩ : Term) fun (_, pTy) acc => `($pTy → $acc)
      return pb.push (← `(Lean.Parser.Command.structExplicitBinder| ($(ev.id) : $evTy)))
    let pBinders ← if spec.hasChildren then do pure (b3.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent `children) : List (Html $msgV) := [])))) else pure b3
    let needsProps := !pBinders.isEmpty
    let vbs ← if needsProps then do pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $(spec.propsId) $msgV))] else do pure #[← `(bracketedBinder| {$msgV : Type})]
    return (← `(command| structure $(spec.propsId) ($msgV : Type) where $[$pBinders:structExplicitBinder]*), vbs, needsProps)
  elabCommand propsCmd
  if !spec.pureFns.isEmpty then
    let rwCtx ← mkRewriteCtx spec true (allowHoist := false)
    let rwPureFns ← Lang.mapCmd spec.pureFns fun f => do pure { f with stmts := ← Lang.mapCmd f.stmts (rewriteIn rwCtx false) }
    elabCmds (← mkPureCompFnCmds { spec with fns := rwPureFns } pureFieldTys)
  Lang.elabPureCmd do
    let propReadNames := spec.propNames ++ spec.slots.map (·.id.getId) ++ spec.binds.map (·.id.getId) ++ spec.events.map (·.id.getId) ++ (if spec.hasChildren then #[`children] else #[])
    let viewBody ← Lang.foldrPQ propReadNames body' fun g acc => if mentionsIdent acc.raw g then let gId := mkIdent g; `(let $gId:ident := (p.$gId:ident); $acc) else pure acc
    `(command| $[$(spec.doc?):docComment]? @[inline] def $(spec.viewId) $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody)
  Lang.foldlCmd spec.invariants () fun _ invStx => do
    if invStx.getKind == ``compForEachInvClause || invStx.getKind == ``compExampleClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` and `example` apply to stateful components"
    if (invStx.getArg 5).getNumArgs > 0 then throwErrorAt (invStx.getArg 5) "per-action `prove:` applies to stateful components, not pure `view` components"
    let invId := resolveInvIdent invStx spec.t.getId; let rawClauses := (invStx.getArg 2).getSepArgs
    let (vPred, predStr) ← mkViewPredAndStr invStx rawClauses (← Lang.mapCmd rawClauses (lowerCompExpr .val)) "empty view invariant"
    let pf? : Option Term := if (invStx.getArg 6).getNumArgs == 2 then some ⟨(invStx.getArg 6).getArg 1⟩ else none
    elabIsolatedTheorem (← Lang.runPQ do
      let vCall ← if needsProps then `($(spec.viewId) p) else `(($(spec.viewId) : Html $msgV))
      let rhs ← pf?.getDM `(by let _qed_hv := fun (_ : Unit) => $vCall; suffices ∀ u, ($vPred) (_qed_hv u) = true from this (); qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
      `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let ty ← Term.elabType tyTerm
    if (← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _ then return (← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _
    else return false

private def canSynthDecidablePred (stateId : Ident) (pred : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let pVal ← Term.elabTermEnsuringType pred (← Term.elabType (← runPureQuot `($stateId → Prop)))
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← Meta.trySynthInstance (← Meta.mkAppM ``DecidablePred #[pVal])) matches .some _

@[noinline] private def mkCompLocalDefCmdsPure (spec : ComponentSpec) (idLit : StrLit) : PureQuotM (Array CmdStx) := do
  let regRhs ← match spec.hasProps, spec.outTy?.isNone with
    | true,  true  => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) (fun p s m => ($(spec.updateId) p s m, (none : Option Bool))))
    | true,  false => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, true  => `(LocalDef.ofSimple $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, false => `(LocalDef.of $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
  let regDoc? := if spec.hasProps then none else spec.doc?
  let cmds : Array CmdStx := #[
    ← `(command| $[$regDoc?:docComment]? def $(spec.id `reg) : LocalDef := $regRhs),
    ← `(command| $[$(spec.doc?):docComment]? def $(spec.id `_qed_mount) {msg : Type} (key : String) : Attr msg := localMount $idLit key)]
  match spec.outTy? with
  | some o => return cmds.push (← `(command| def $(spec.id `_qed_mountWithOpt) {msg : Type} (key : String) (onOut : $o → Option msg) : Attr msg := localMountWith $idLit key onOut))
  | none   => return cmds

@[noinline] private def mkHoistedKeyAndPropsFnsPure (spec : ComponentSpec) (h : HoistedSub) : PureQuotM (Term × Term) := do
  let keyFn ← if h.hasLifecycle then
      let kId := mkIdent (subKeyDefName spec.t.getId h)
      if spec.hasProps then `(fun pm => match _getProps pm with | Option.none => "" | Option.some p => let pk := _getKey pm; if pk.isEmpty then "" else let hk := $kId p (_getState pm); if hk.isEmpty then "" else pk ++ "|" ++ hk)
      else `(fun pm => let pk := _getKey pm; if pk.isEmpty then "" else let hk := $kId (_getState pm); if hk.isEmpty then "" else pk ++ "|" ++ hk)
    else `(_getKey)
  let propsFn ← if h.info.hasProps then
      if h.hasLifecycle then
        let pId := mkIdent (subPropsDefName spec.t.getId h)
        if spec.hasProps then `(fun pm => (_getProps pm).bind fun p => $pId p (_getState pm)) else `(fun pm => $pId (_getState pm))
      else
        let propsT ← mkHoistedPropsTermPure h; let recT ← bindMentionedFieldsPure spec (mentionsIdent propsT.raw) propsT
        if spec.hasProps then `(fun pm => (_getProps pm).map fun p => let s := _getState pm; $recT) else `(fun pm => let s := _getState pm; Option.some $recT)
    else `(fun _ => Option.some ({} : $(mkIdent (h.info.fullName ++ `Props))))
  return (keyFn, propsFn)

@[noinline] private def mkCompLifecycleCmdsPure (spec : ComponentSpec) (isTopMount : Bool) (liftName topName : Name)
    (itemTy : Term) (hasSlotPfx : Bool) (hasChild : ComponentInfo → Bool) (ownTerms : Array Term) : PureQuotM (Array CmdStx) := do
  let hoistedParts ← Lang.foldlPQ spec.hoisted #[] fun parts h => do
    if !hasChild h.info then return parts
    let (hkFn, hpFn) ← mkHoistedKeyAndPropsFnsPure spec h; let subF := h.fieldId
    let baseArgs : Array Term := #[hkFn, hpFn, ← `(fun pm => (_getState pm).$subF:ident),
      ← `(fun cs pm => _setState { _getState pm with $subF:ident := cs } pm), ← `(_wrapMsg ∘ $(spec.msgCtor h.ctorName))]
    let callArgs ← if hasSlotPfx then do pure (#[← `(_slotPfx ++ $(Syntax.mkStrLit s!"{subF.getId}."))] ++ baseArgs) else pure baseArgs
    return parts.push (← mkAppTermsPure (mkIdent (h.info.fullName ++ liftName)) callArgs)
  let base : Array Term ← if ownTerms.isEmpty then pure #[] else do pure #[← `([$[$ownTerms],*])]
  let allParts := base ++ hoistedParts
  let listExpr ← if allParts.isEmpty then `([]) else Lang.foldlPQ (allParts.extract 1 allParts.size) allParts[0]! fun acc x => `($acc ++ $x)
  let slotBinders ← if hasSlotPfx then do pure #[← `(bracketedBinder| (_slotPfx : String))] else pure #[]
  let cmds : Array CmdStx := #[← `(command|
    set_option linter.unusedVariables false in
    def $(spec.id liftName) {PModel PMsg : Type} $[$slotBinders:bracketedBinder]* (_getKey : PModel → String) (_getProps : PModel → Option $(spec.propsId))
        (_getState : PModel → $(spec.stateId)) (_setState : $(spec.stateId) → PModel → PModel) (_wrapMsg : $(spec.msgId) → PMsg) : List ($itemTy PModel PMsg) := $listExpr)]
  if !isTopMount then return cmds
  let pfxArgs : Array Term ← if hasSlotPfx then do pure #[← `("")] else pure #[]
  let topArgs := pfxArgs ++ #[← `(fun _ => "1"), ← `(fun _ => Option.some ({} : $(spec.propsId))), ← `(id), ← `(fun s _ => s), ← `(id)]
  return cmds.push (← `(command| def $(spec.id topName) : List ($itemTy $(spec.stateId) $(spec.msgId)) := $(← mkAppTermsPure (spec.id liftName) topArgs)))

@[noinline] private def mkCompQueriesAndSubsCmds (spec : ComponentSpec) (isTopMount : Bool) : CommandElabM (Array CmdStx) := do
  Lang.foldlCmd spec.subscriptions () fun _ sub =>
    if sub.hasMsgEnsured && sub.chInfo.ensPredConst.isNone then throwErrorAt sub.chanRef "internal: missing channel `ensures` predicate in `subscribe`" else pure ()
  let recTerms ← Lang.mapCmd spec.subscriptions fun sub => liftMacroM sub.reconnect.toSyntaxTerm
  Lang.runPQ do
    let c0 : Array CmdStx ← if !spec.hasAnyQueries then pure #[] else do
      let ownTerms ← Lang.mapPQ spec.queries fun q => do
        let reqTupleTy ← buildProdTypePure (q.rpc.mInfo.paramTypeConsts.map fun n => (mkIdent n : Term))
        let pCall ← appWithPropsPure spec (mkIdent (queryParamsFnName spec.t.getId q)) #[← `(s)]
        let fCall ← appWithPropsPure spec (mkIdent (queryFetchFnName spec.t.getId q)) #[← `(s), ← `(_qk)]
        let qCore ← `(Qed.Resource.rpcQuery (Req := $reqTupleTy) (params? := fun (s : $(spec.stateId)) => $pCall)
            (fetch := fun (s : $(spec.stateId)) _ _qk => $fCall) (got := $(spec.msgCtor q.ctorName))
            (get := fun (s : $(spec.stateId)) => s.$(q.id):ident) (set := fun c (s : $(spec.stateId)) => { s with $(q.id):ident := c }))
        `(Qed.Query.liftWithProps _getKey _getProps _getState _setState _wrapMsg (fun (p : $(spec.propsId)) => $qCore))
      mkCompLifecycleCmdsPure spec isTopMount `liftQueries `queries (← `(Query)) false (·.hasQueries) ownTerms
    if !spec.hasAnySubscriptions then return c0
    let ownTerms ← Lang.mapPQ (spec.subscriptions.zip recTerms) fun (sub, recTerm) => do
      let (slotLit, msgCtor, slotId) := (Syntax.mkStrLit sub.id.getId.toString, spec.msgCtor (sub.ctor "Msg"), mkIdent `_subSlot)
      let openBody ← mkSubBranchesPure spec sub (← `(none)) true fun qaIds => do
        let onMsgCb ← match sub.hasMsgEnsured, sub.chInfo.ensPredConst with
          | true, some ensConst =>
              let weId := mkIdent `_we; let (ensApp, exPrf) ← mkEnsuredExistentialWrapPure ensConst qaIds weId
              `(fun ($weId : Qed.Ensured $(mkIdentFrom sub.chanRef sub.chInfo.eventTypeConst) ($ensApp)) => $msgCtor _wk ⟨($weId:ident).val, $exPrf⟩)
          | _, _ => `($msgCtor _wk)
        let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
        `(some $(← withRef sub.chanRef `(qedCheckChanSub% $(mkIdentFrom sub.chanRef sub.chInfo.fullName):ident [$[$qaTerms:term],*] $slotId:ident ($recTerm, $(spec.msgCtor (sub.ctor "Join")) _wk, $onMsgCb, $(spec.msgCtor (sub.ctor "Status")) _wk))))
      let keyFnId := mkIdent (subKeyFnName spec.t.getId sub)
      let childKeyFn ← if spec.hasProps then `(fun (p : $(spec.propsId)) (s : $(spec.stateId)) => $keyFnId p s) else `(fun (_ : $(spec.propsId)) (s : $(spec.stateId)) => $keyFnId s)
      `(Qed.Subscription.liftWithProps _getKey _getProps _getState _setState _wrapMsg (_slotPfx ++ $slotLit) $childKeyFn
          (fun ($slotId:ident : String) (p : $(spec.propsId)) _wk (s : $(spec.stateId)) => $openBody)
          (fun ($slotId:ident : String) => $(mkIdentFrom sub.chanRef sub.chInfo.unsubHelperConst) $slotId)
          (fun (s : $(spec.stateId)) => { s with $(sub.id):ident := Qed.SocketStatus.disconnected }))
    return c0 ++ (← mkCompLifecycleCmdsPure spec isTopMount `liftSubscriptions `subscriptions (← `(Qed.Subscription)) true (·.hasSubscriptions) ownTerms)

private def mkSpecStepPfPure (sVar mVar : Ident) : List Ident → Term → PureQuotM Term
  | [], _ => `(trivial) | [id0], hTerm => `(($id0:ident).2 $sVar $mVar $hTerm)
  | lastId :: prevRev, hTerm => do `(And.intro $(← mkSpecStepPfPure sVar mVar prevRev (← `(($hTerm).1))) (($lastId:ident).2 $sVar $mVar ($hTerm).2))

private def mkSpecPropPairPure (spec : ComponentSpec) (suffix : String) (prop initPf stepFn : Term) : PureQuotM (Array CmdStx) := do
  let appIdent := spec.id `app
  return #[
    ← `(command| theorem $(spec.id (Name.mkSimple s!"specApp_init_{suffix}")) : $prop ($appIdent).init.1 := $initPf),
    ← `(command| theorem $(spec.id (Name.mkSimple s!"specApp_preserves_{suffix}")) (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) (msg : $(spec.msgId)) (h : $prop st) : $prop (($appIdent).update st msg).1 := $stepFn st msg h)]

@[noinline] private def mkRehydrateInvCmdsPure (spec : ComponentSpec) (specBaseApp? : Option Ident) (compInv? : Option Term) (hasDecInv : Bool) : PureQuotM (Array CmdStx) := do
  let some inv := compInv? | return #[]
  let appId := spec.id `app
  let (stTy, invWrap) ← match specBaseApp? with
    | some _ => pure (← `(Qed.SpecState $(spec.stateId) $(spec.msgId)), ← `(Qed.SpecEngine.SpecInv ($inv))) | none => pure ((spec.stateId : Term), inv)
  if hasDecInv then
    let pf ← if specBaseApp?.isSome then `(Qed.Internal.App.withSpeculative_rehydrate_sound _ _ (Qed.App.guardRehydrate_sound _ _ _) raw st')
             else `(Qed.App.guardRehydrate_sound _ _ _ raw st')
    return #[← `(command| theorem $(spec.id `rehydrate_inv) (raw : String) (st' : $stTy) : ($appId).rehydrate raw = some st' → ($invWrap) st' := $pf)]
  let pf ← match specBaseApp? with
    | some b => `(Qed.Internal.App.withSpeculative_dehydrate_inv _ _ (by dsimp only [$b:ident]; qedProveDehydrateInv))
    | none   => `(by dsimp only [$appId:ident]; qedProveDehydrateInv)
  return #[← `(command| theorem $(spec.id `dehydrate_inv) : ∀ st st', ($invWrap) st → ($appId).rehydrate (($appId).dehydrate st) = some st' → ($invWrap) st' := $pf)]

private def mkViewEqThmPure (thmId appId viewId stateId : Ident) : PureQuotM CmdStx :=
  `(command| theorem $thmId (s : $stateId) : Qed.Html.canonical (Qed.App.view $appId s) = Qed.Html.canonical ($viewId s) := by qedProveViewEquiv $appId $viewId)

@[noinline] private def mkSpecAppCmdsPure (spec : ComponentSpec) (finalApp : Term) (compInv? : Option Term)
    (hasDecInv : Bool) (stateInvEntries : Array (Term × Option Ident)) (initCmds : Array CmdStx) : PureQuotM (Array CmdStx × CmdStx) := do
  let (appId, baseId, clsId) := (spec.id `app, spec.id `_baseApp, spec.id `_specClassify)
  let c0 := initCmds ++ #[
    ← `(command| def $baseId : App $(spec.stateId) $(spec.msgId) := $finalApp),
    ← `(command| $[$(spec.doc?):docComment]? def $appId : App (Qed.SpecState $(spec.stateId) $(spec.msgId)) $(spec.msgId) := Qed.Internal.App.withSpeculative $clsId $baseId)]
    ++ (← mkSpecPropPairPure spec "coherent" (← `(Qed.SpecEngine.Coherent (fun s m => (($baseId).update s m).1)))
          (← `(Qed.Internal.App.withSpeculative_init_coherent $clsId $baseId)) (← `(Qed.Internal.App.withSpeculative_step_coherent $clsId $baseId)))
    ++ (← mkSpecPropPairPure spec "wellFormedIds" (← `(Qed.SpecEngine.WellFormedIds))
          (← `(Qed.Internal.App.withSpeculative_init_wellFormedIds $clsId $baseId)) (← `(Qed.Internal.App.withSpeculative_step_wellFormedIds $clsId $baseId)))
  let c1 ← if !spec.hasAnyQueries && !spec.hasAnySubscriptions then
      match compInv?, stateInvEntries.foldl (init := some #[]) fun acc (_, id?) => match acc, id? with | some arr, some id => some (arr.push id) | _, _ => none with
      | some inv, some invIds =>
          if invIds.isEmpty then pure c0 else do
            let initPf ← Lang.foldlPQ (invIds.extract 1 invIds.size) (← `(($(invIds[0]!):ident).1)) fun acc id => `(And.intro $acc ($id:ident).1)
            let (sV, mV, hV) := (mkIdent `_s, mkIdent `_m, mkIdent `_h)
            pure (c0 ++ (← mkSpecPropPairPure spec "inv" (← `(Qed.SpecEngine.SpecInv ($inv)))
              (← `(Qed.Internal.App.withSpeculative_init_inv $clsId $baseId $initPf))
              (← `(Qed.Internal.App.withSpeculative_step_inv $clsId $baseId (fun $sV $mV $hV => $(← mkSpecStepPfPure sV mV invIds.toList.reverse hV))))))
      | _, _ => pure c0
    else pure c0
  let baseViewEqId := spec.id `_base_app_view_eq
  let cmds := c1 ++ (← mkRehydrateInvCmdsPure spec (some baseId) compInv? hasDecInv) |>.push (← mkViewEqThmPure baseViewEqId baseId spec.viewId spec.stateId)
  return (cmds, ← `(command| theorem $(spec.id `app_view_eq) (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) :
      Qed.Html.canonical (Qed.App.view $appId st) = Qed.Html.canonical ($(spec.viewId) st.visible) := by
    simpa [Qed.Internal.App.withSpeculative_view, $appId:ident] using $baseViewEqId st.visible))

@[noinline] private def applyOneHeadDir (hmId stId : Ident) (acc : Term) (d : Syntax) : CommandElabM Term := do
  match d.getKind with
  | `Qed.compHeadTitle | `Qed.compHeadDescription =>
      let v ← lowerCompExpr .val (d.getArg 1); let fId := mkIdent <| if d.getKind == `Qed.compHeadTitle then `title else `description
      Lang.runPQ `(let $hmId:ident := { $hmId with $fId:ident := Option.some ($v : String) }; $acc)
  | `Qed.compHeadCanonical => let v ← lowerCompExpr .val (d.getArg 1); Lang.runPQ `(let $hmId:ident := { $hmId with canonical := Option.some (($v : Qed.HrefTarget).raw) }; $acc)
  | `Qed.compHeadMeta      => let (k, v) := (← lowerCompExpr .val (d.getArg 1), ← lowerCompExpr .val (d.getArg 3)); Lang.runPQ `(let $hmId:ident := { $hmId with metaTags := ($hmId).metaTags ++ [(($k : String), ($v : String))] }; $acc)
  | `Qed.compHeadStatus    => let v ← lowerCompExpr .val (d.getArg 1); Lang.runPQ `(let $stId:ident : Nat := $v; $acc)
  | `Qed.compHeadRedirect  =>
      let v ← lowerCompExpr .val (d.getArg 1)
      let stT ← if (d.getArg 2).getNumArgs == 4 then lowerCompExpr .val ((d.getArg 2).getArg 3) else Lang.runPQ `((302 : Nat))
      Lang.runPQ `(let $hmId:ident := { $hmId with redirect := Option.some (($v : Qed.HrefTarget).raw) }; let $stId:ident : Nat := $stT; $acc)
  | _ => throwErrorAt d "unexpected directive in `head:`"

@[noinline] private def mkCompHeadCmd? (spec : ComponentSpec) : CommandElabM (Option CmdStx) := do
  let some headStx := spec.headClause? | return none
  let (hmId, stId) := (mkIdent `_qed_hm, mkIdent `_qed_st)
  let (sharedDirs, caseItems) ← Lang.foldlCmd (headStx.getArg 2).getArgs (#[], #[]) fun (sd, ci) item =>
    if item.getKind == `Qed.compHeadCase then pure (sd, ci.push item)
    else if !ci.isEmpty then throwErrorAt item "shared `head:` directives must appear before `case` arms"
    else pure (sd.push item, ci)
  let pairT ← Lang.runPQ `(($hmId, $stId))
  let coreTail ← if caseItems.isEmpty then pure pairT else do
    let some rd := spec.route? | throwErrorAt caseItems[0]! s!"`case` inside `head:` requires a `route` declaration on `component {spec.t.getId}`"
    let altPairs ← Lang.mapCmd caseItems fun c =>
      return (← liftMacroM (lowerCasePatAlts (c.getArg 1)), ← Lang.foldlCmd (c.getArg 3).getArgs.reverse pairT (applyOneHeadDir hmId stId))
    Lang.runPQ do let alts ← Lang.mapPQ altPairs fun (ps, b) => mkMatchAltFromAlts ps b; `(match $(rd.field):ident with $[$alts:matchAlt]*)
  let applied ← Lang.foldlCmd sharedDirs.reverse coreTail (applyOneHeadDir hmId stId)
  return some (← Lang.runPQ do
    let fullBody ← `(let $hmId:ident : Qed.HeadMeta := {}; let $stId:ident : Nat := 200; $applied)
    `(command| set_option linter.unusedVariables false in def $(spec.id `headInfo) (s : $(spec.stateId)) : Qed.HeadMeta × Nat := $(← bindMentionedFieldsPure spec (mentionsIdent fullBody.raw) fullBody)))

@[noinline] private def wrapAppPipelinePure (spec : ComponentSpec) (templateTerm0 : Term) (hasStart : Bool)
    (thTerms : Array Term) (compInv? : Option Term) (hasDecInv : Bool) (stateInvEntries : Array (Term × Option Ident)) : PureQuotM (Array CmdStx × CmdStx) := do
  let startArg ← if hasStart then `($(spec.id `startCmd)) else `(Qed.Cmd.none)
  let (cmds, onPortArg) ← if spec.portIns.isEmpty then do pure (#[], ← `(Option.none)) else do
    let onPortId := spec.id `onPort
    let inTuples ← Lang.mapPQ spec.portIns fun p =>
      `(($(Syntax.mkStrLit p.id.getId.toString), fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $(spec.msgCtor p.id.getId)))
    pure (#[← `(command| def $onPortId : String → String → Option $(spec.msgId) := dispatchPorts #[$inTuples,*])], ← `(some $onPortId))
  let templateTerm ← Lang.foldrPQ spec.portOuts templateTerm0 fun po acc =>
    if mentionsIdent acc.raw po.id.getId then `(let $(mkIdent po.id.getId):ident := $(spec.id po.id.getId); $acc) else pure acc
  let appUpdate ← if spec.hasEffects then `($(spec.updateId)) else `(fun s m => ($(spec.updateId) s m, Qed.Cmd.none))
  let onSessionArg ← if spec.hasAnySession then `(some $(spec.msgCtor `_onSession)) else `(none)
  let mut appT ← if spec.route?.isSome then
      `(Qed.Internal.mkRoutedApp $(spec.initId) $appUpdate $templateTerm (onRoute := $(spec.msgCtor `_onRoute))
          (onSession := $onSessionArg) (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg))
    else `(Qed.Internal.mkApp $(spec.initId) $appUpdate $templateTerm (onSession := $onSessionArg)
          (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg))
  if !thTerms.isEmpty then appT ← `(Qed.Internal.App.withExtraStyles [$[$thTerms],*] $appT)
  if !spec.stylesheets.isEmpty then appT ← `(Qed.Internal.App.withStylesheets [$(spec.stylesheets.map Syntax.mkStrLit):str,*] $appT)
  appT ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $(spec.initId) $appT)
         else `(Qed.Internal.App.withDehydrate (Dehydrate.except $(spec.initId) [$[$spec.ephemeralFields:ident],*]) $appT)
  if spec.hasAnyQueries then appT ← `(Qed.Internal.App.withQueries $(spec.id `queries) $appT)
  if spec.hasAnySubscriptions then appT ← `(Qed.Internal.App.withSubscriptions $(spec.id `subscriptions) $appT)
  if spec.headClause?.isSome then let hId := spec.id `headInfo; appT ← `(Qed.App.withSsrStatus (fun _s => ($hId _s).2) (Qed.App.withHead (fun _s => ($hId _s).1) $appT))
  if let (some inv, true) := (compInv?, hasDecInv) then appT ← `(Qed.App.guardRehydrate ($inv) $appT)
  if spec.hasSpeculative then return ← mkSpecAppCmdsPure spec appT compInv? hasDecInv stateInvEntries cmds
  let appId := spec.id `app
  return (cmds.push (← `(command| $[$(spec.doc?):docComment]? def $appId : App $(spec.stateId) $(spec.msgId) := $appT)) ++
          (← mkRehydrateInvCmdsPure spec none compInv? hasDecInv), ← mkViewEqThmPure (spec.id `app_view_eq) appId spec.viewId spec.stateId)

@[noinline] private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool) (stateInvEntries : Array (Term × Option Ident)) : CommandElabM (Array CmdStx × CmdStx) := do
  let expandedBody ← liftMacroM <| Qed.Jsx.expandJsxIn body'.raw
  let templateTerm0 : Term := ⟨← liftMacroM <| Qed.Internal.liftViewWithFields (mkIdent `_qed_s) (spec.states.map (·.id)) expandedBody⟩
  let thTerms ← if spec.themes.isEmpty then pure #[] else do
    let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, (← getScope).openDecls)
    let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
    Lang.mapCmd spec.themes fun thId => do
      let some thInfo := Qed.StyleDsl.resolveInRegistry thReg env currNs openDecls thId.getId.toString | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
      return (mkIdentFrom thId thInfo.styleConst : Term)
  let stateInvPreds := stateInvEntries.map (·.1)
  let compInv? : Option Term ← if stateInvPreds.isEmpty then pure none else Lang.runPQ do
    if stateInvPreds.size == 1 then some <$> `(($(stateInvPreds[0]!) : $(spec.stateId) → Prop))
    else let sVar := mkIdent `_qed_s; some <$> `(fun ($sVar:ident : $(spec.stateId)) => $(← mkConjBody (← Lang.mapPQ stateInvPreds fun p => `(($p) $sVar))))
  let hasDecInv ← match compInv? with | some inv => canSynthDecidablePred spec.stateId inv | none => pure false
  Lang.runPQ (wrapAppPipelinePure spec templateTerm0 hasStart thTerms compInv? hasDecInv stateInvEntries)

@[noinline] private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) : CommandElabM (Array CmdStx × Bool × Bool) := do
  let (tId, outCtorSpecs) := (spec.t.getId, spec.events.map (fun ev => (ev.id.getId, ev.params)) ++ spec.binds.map (fun bd => (bindSetName bd.id.getId, #[(mkIdent `v, bd.ty)])))
  let canEmitCodecs ← if ← spec.props.allM (canSynthJson ``FromJsonField ·.ty) then spec.states.allM (canSynthJson ``FromJsonField ·.ty) else pure false
  let outJsonOk ← if spec.outTy?.isSome then outCtorSpecs.allM fun (_, ps) => ps.allM (canSynthJson ``FromJsonField ·.2) else pure true
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && !spec.hasAnySession && canEmitCodecs && outJsonOk
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart); let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  let cmds ← Lang.runPQ do
    let fs := spec.states.map (·.id); let mut cmds : Array CmdStx := #[]
    if spec.mountable then let dsT := spec.states.filterMap (·.def?); cmds := cmds.push (← `(command| def $(spec.initId) : $(spec.stateId) := { $[$fs:ident := $dsT],* }))
    if hasStart then
      let pBinders ← mkPropsBindersPure spec
      let subStarts ← Lang.mapPQ hoistedStarts fun h => do mkHoistedStartCmdExprPure spec h (← `(s)) none (← `(Qed.Cmd.none)) pure
      let mut startBody ← mkCmdBatchPure (starts' ++ subStarts)
      if spec.mountable then
        startBody ← bindMentionedFieldsPure spec (mentionsIdent startBody.raw) startBody
        if mentionsIdent startBody.raw `s then startBody ← `(let s := $(spec.initId); $startBody)
      cmds := cmds.push (← `(command| def $(spec.id `startCmd) $[$pBinders:bracketedBinder]* : Cmd $(spec.msgId) := $startBody))
    if canEmitCodecs then
      let mkJ (sNm : Name) (ds : Array FieldDecl) := Qed.mkStructJsonCmdsPure (mkIdent sNm) (ds.map fun d => { ident := d.id, wireKey := d.id.getId.toString, valTy := d.ty }) { emitNamedDefs := false }
      cmds := cmds ++ (← mkJ (tId ++ `Props) spec.props) ++ (← mkJ (tId ++ `State) spec.states)
    if spec.outTy?.isSome && outJsonOk then
      cmds := cmds ++ (← Qed.mkTaggedUnionJsonCmdsPure (mkIdent (tId ++ `Out))
        (outCtorSpecs.map fun (cName, ps) => { ctorName := cName, wireTag := cName.toString, fields := ps.zipIdx.map fun ((pId, pTy), i) => (pId, toString i, pTy) })
        { emitNamedDefs := false, unknownTagStatic? := some "unknown Out tag" })
    if hasLocalDef then cmds := cmds ++ (← mkCompLocalDefCmdsPure spec idLit)
    let own ← if hasLocalDef then `([$(spec.id `reg)]) else `(([] : List LocalDef))
    return cmds.push (← `(command| def $(spec.id `regs) : List LocalDef := LocalDef.dedupe ($own ++ qedInternalLocalRegistrations% $(spec.viewId))))
  return (cmds, hasStart, hasLocalDef)

private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k else k

@[noinline] private def elabStatefulComponentBody (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
  if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone && rawSpec.starts.isEmpty &&
      rawSpec.sessionField?.isNone && rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty &&
      rawSpec.queries.isEmpty && rawSpec.subscriptions.isEmpty && rawSpec.headClause?.isNone then
    let rCtx ← mkRewriteCtx rawSpec true (allowHoist := true)
    let body' ← lowerCompExpr .val (← rewriteIn rCtx false rawSpec.body)
    let acc ← rCtx.accum.get
    if acc.hoisted.isEmpty && acc.formDrafts.isEmpty && acc.resetForms.isEmpty then elabPureComponent rawSpec body'; return
  let rw ← collectSitesAndRewriteStateful rawSpec; let acc := rw.accum
  if let some rs0 := acc.specResolves[0]? then checkTopLevelMountable rawSpec rs0.callRef "speculative `predict`"
  let allUsedRpcs := acc.hoisted.foldl (fun a h => h.info.usedRpcs.foldl pushUnique a) acc.usedRpcs
  let ownChans := rawSpec.subscriptions.foldl (init := #[]) fun a sub => match sub.chInfo.kind with | .fullstack _ srvShort _ => pushUnique a (srvShort, sub.chInfo.channelName) | _ => a
  let allUsedChannels := acc.hoisted.foldl (fun a h => h.info.usedChannels.foldl pushUnique a) ownChans
  let eventNames := rawSpec.events.map (·.id.getId)
  let specWithRwFns := { rawSpec with fns := rw.fns, subscriptions := rw.subscriptions }
  let pureMut := specWithRwFns.pureMutFnNames
  let ownHasEffects := !rw.starts.isEmpty || !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty ||
    !rawSpec.queries.isEmpty || !rawSpec.subscriptions.isEmpty || !acc.specResolves.isEmpty ||
    acc.sites.any (fun s => s.stmts?.any (·.any (hasEffectStmt eventNames · pureMut))) ||
    rw.fns.any (fun f => f.isMut && f.stmts.any (hasEffectStmt eventNames · pureMut)) ||
    (rw.route?.any fun rd => rd.alts.any (hasEffectStmt eventNames · pureMut)) || acc.hoisted.any (·.info.hasEffects)
  let spec ← elabStructsAndResolveTypes { specWithRwFns with
    route? := rw.route?, hasEffects := ownHasEffects, usedRpcs := allUsedRpcs, usedChannels := allUsedChannels,
    specDispatches := acc.specDispatches, specNodes := acc.specNodes, specResolves := acc.specResolves
  } acc.hoisted acc.formDrafts acc.resetForms
  currentCompSessionRef.set spec.sessionField?
  let errsBefore ← getErrorCount
  if !spec.pureFns.isEmpty then elabCmds (← mkPureCompFnCmds spec ((spec.states ++ spec.props).map fun d => (d.id.getId, d.ty)))
  let msgAndUpd ← mkMsgAndUpdateCmds spec acc.sites
  Lang.elabPureCmds (mkViewCmdsPure spec rw.body msgAndUpd)
  if (← getErrorCount) > errsBefore then return
  let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec rw.starts (Syntax.mkStrLit compNs.toString)
  elabCmds mountCmds
  let isTopMount := spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids
  elabCmds (← mkCompQueriesAndSubsCmds spec isTopMount)
  if isTopMount then
    if let some c ← mkCompHeadCmd? spec then elabCommand c
    elabCmds (← mkSpecClassifyCmds spec)
  let stateInvEntries ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
  let activeInvEntries := if (← getErrorCount) == errsBefore then stateInvEntries else #[]
  if (← getErrorCount) == errsBefore then withOpenNs compNs (elabCompReachableAndWitnesses spec)
  verifyPendingRpcChecks spec (activeInvEntries.map (·.1))
  if isTopMount then
    if (← getErrorCount) == errsBefore then
      let (appCmds, eqCmd) ← mkCompAppCmds spec rw.body hasStart activeInvEntries
      elabCmds appCmds
      if (← getErrorCount) == errsBefore then elabCommand eqCmd
  let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
  Lang.elabPureCmds do Lang.mapPQ #[(`usedRpcs, allUsedRpcs), (`usedChannels, allUsedChannels)] fun (defName, pairs) => do
    let ts ← Lang.mapPQ pairs fun (a, b) => `((($(Syntax.mkStrLit a), $(Syntax.mkStrLit b)) : String × String))
    `(command| def $(spec.id defName) : List (String × String) := [$[$ts],*])
  let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
  modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
    hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects, hasStart, mountable := spec.mountable,
    hasLocalDef, hasQueries := spec.hasAnyQueries, hasSubscriptions := spec.hasAnySubscriptions,
    hasSession := spec.hasAnySession, usedRpcs := allUsedRpcs, usedChannels := allUsedChannels }

@[noinline, command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let (savedEnv, errsInit, priorTasks) := (← getEnv, ← getErrorCount, (← get).snapshotTasks.size)
  let compNs := (← getCurrNamespace) ++ (stx.getArg 2).getId
  pendingRpcChecks.set #[]; pendingPredictChecks.set #[]; currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    Lang.foldlCmd rawSpec.styles () fun _ stCl =>
      withOpenNs compNs do
        let sNameId : Ident := ⟨stCl.getArg 1⟩
        Qed.StyleDsl.elabStyleDef none (mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId))
          (Qed.StyleDsl.extractStyleExtends (stCl.getArg 2)) ((stCl.getArg 3).getNumArgs == 1)
          (stCl.getArg 6).getArgs (Qed.StyleDsl.extractOptChild (stCl.getArg 4))
    withOpenNs compNs (elabStatefulComponentBody compNs rawSpec); okRef.set true
  finally
    pendingRpcChecks.set #[]; pendingPredictChecks.set #[]; currentCompSessionRef.set none
    let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
    let ok ← okRef.get; let errsNow ← getErrorCount
    if !ok || errsNow > errsInit || newTasks.any (Qed.Diag.snapshotTreeHasErrors 64 ·.get) then
      setEnv (failedComponentRegistry.addEntry savedEnv compNs)

/-! ## JSX `<Component …>…</Component>` Term Elaborator (`elabQedCompTerm`) -/

private def checkParentNesting (ref : Syntax) (pPath compLabel childTag : String) : TermElabM Unit := do
  if let some (ptag, pctx) := Qed.Jsx.ctxOfPath pPath then
    if (stepHtmlCtx pctx childTag).isNone then
      let what := if compLabel == childTag then s!"<{childTag}>" else s!"<{compLabel}> (root <{childTag}>)"
      throwErrorAt ref s!"invalid HTML5 nesting: {what} is not allowed inside <{ptag}> (browsers rewrite this tree during HTML parsing, causing hydration mismatch)"

private def throwNoChildren (stx : Syntax) (tag : String) : TermElabM Unit :=
  throwErrorAt stx s!"<{tag}> does not render `\{children}` in its `view:`; write it self-closing (`<{tag} …/>`) or render `\{children}` in `{tag}`"

private def mkPropsRecPure (pairs : Array (Ident × Term)) (ty : Term) : PureQuotM Term :=
  let (fids, vals) := (pairs.map (·.1), pairs.map (·.2)); `( ({ $[$fids:ident := $vals],* } : $ty) )

@[noinline] private def elabInlineCompTag (stx : Syntax) (expectedType? : Option Expr) (info : ComponentInfo)
    (cId : Name → Term) (pPath tag : String) (props : Array (Syntax × String × Term)) (kidsT : Term)
    (hasKids : Bool) (key? hPair? : Option Term) : TermElabM Expr := do
  if let some rtag := info.rootTag? then checkParentNesting stx pPath tag rtag
  if hasKids && !info.hasChildren then throwNoChildren stx tag
  let callT ← runPureQuot do
    let core ← match hPair? with
      | none =>
          let (pairs0, _) ← partitionBindPropsPure props #[] false
          let pairs := if hasKids then pairs0.push (mkIdentFrom stx `children, kidsT) else pairs0
          if info.hasProps then `($(cId `view) $(← mkPropsRecPure pairs (← `($(cId `Props) _)))) else `($(cId `view))
      | some hPair =>
          let (dataPairs, slotArgs0) ← Lang.foldlPQ props (#[], #[]) fun (dp, sa) (ref, nm, v) => do
            let id := mkIdentFrom ref (Name.mkSimple nm)
            if info.slotNames.contains id.getId then return (dp, sa.push (← `(Lean.Parser.Term.argument| ($id:ident := $v))))
            else return (dp.push (id, v), sa)
          let slotArgs ← if hasKids then do pure (slotArgs0.push (← `(Lean.Parser.Term.argument| ($(mkIdentFrom stx `children):ident := $kidsT)))) else pure slotArgs0
          let (wrapA, subSA) := (← `(Lean.Parser.Term.argument| ($hPair).1), ← `(Lean.Parser.Term.argument| ($hPair).2))
          let baseArgs ← if info.hasProps then pure #[← `(Lean.Parser.Term.argument| $(← mkPropsRecPure dataPairs (cId `Props)):term), wrapA, subSA] else pure #[wrapA, subSA]
          pure (⟨Syntax.node .none ``Lean.Parser.Term.app #[(cId `_qed_render).raw, Syntax.node .none nullKind ((baseArgs ++ slotArgs).map (·.raw))]⟩ : Term)
    match key? with | some k => `(Qed.withKey (toString $k) $core) | none => pure core
  elabTerm callT expectedType?

@[noinline] private def elabStatefulCompTag (stx : Syntax) (expectedType? : Option Expr) (info? : Option ComponentInfo)
    (baseName : Name) (cId : Name → Term) (tag pPath : String) (posNum : Nat)
    (props : Array (Syntax × String × Term)) (key? state? initial? onMsg? : Option Term) : TermElabM Expr := do
  let (dataPairs, evArms) ← runPureQuot (partitionBindPropsPure props (info?.map (·.events) |>.getD #[]) true)
  if let some st := state? then
    if initial?.isSome then throwErrorAt stx s!"<{tag}>: `initial` seeds local state and cannot be combined with parent-owned `state=\{...}`"
    if !evArms.isEmpty then
      throwErrorAt stx s!"<{tag} state=…>: a parent-owned component routes every event through `onMsg` (cannot also pass event props {String.intercalate ", " (evArms.toList.map fun a => s!"`{a.ctor}`")})"
    let some route := onMsg?
      | throwErrorAt stx s!"<{tag} state=…> requires `onMsg=\{...}`: pass the parent message constructor `(k : String) (msg : {tag}.Msg)` (or declare `collection <field> : {tag}` so Qed wires `onMsg` automatically)"
    return ← elabTerm (← runPureQuot do
      let pv ← mkPropsRecPure dataPairs (cId `Props)
      match key? with | some k => `(Qed.withKey (toString $k) ($(cId `_qed_renderTag) $pv $route $st (toString $k))) | none => `($(cId `_qed_renderTag) $pv $route $st)) expectedType?
  if onMsg?.isSome then throwErrorAt stx s!"<{tag}>: `onMsg` routes a parent-owned row; pass `state=\{...}` alongside `onMsg`, or remove `onMsg` and pass named event props"
  if info?.any (!·.hasLocalDef) then
    throwErrorAt stx s!"<{tag}> uses effects, `Html` props, `children`, or non-JSON props and cannot be mounted dynamically via `LocalDef`; mount `<{tag} …/>` directly inside a parent `component` view so Qed hoists its state"
  checkParentNesting stx pPath "div" "div"
  elabTerm (← runPureQuot do
    let pv ← mkPropsRecPure dataPairs (cId `Props)
    let keyT : Term ← match key? with | some k => `(toString $k) | none => pure ⟨Syntax.mkStrLit s!"@{posNum}"⟩
    let mount0 ← if evArms.isEmpty then `($(cId `_qed_mount) $keyT) else do
      let outVar := mkIdent `_out
      let mTerm ← mkOutMatchTermPure baseName ((info?.map fun i => i.events.size + i.bindNames.size).getD 999) evArms outVar
      `($(cId `_qed_mountWithOpt) $keyT (fun $outVar:ident => $mTerm))
    let mountBase ← match initial? with | none => pure mount0 | some seed => `(Qed.Attr.localInit $mount0 ($seed : $(cId `State)))
    `(Qed.el "div" [Qed.key $keyT, Qed.Attr.localProps $mountBase $pv] [])) expectedType?

@[noinline, term_elab Qed.Jsx.qedCompTerm] def elabQedCompTerm : TermElab := fun stx expectedType? => do
  let (tag, pPath, posNum) := ((⟨stx.getArg 1⟩ : TSyntax `str).getString, (⟨stx.getArg 2⟩ : TSyntax `str).getString, (⟨stx.getArg 3⟩ : TSyntax `num).getNat)
  let (propNodes, kidsT) := ((stx.getArg 5).getSepArgs, (⟨stx.getArg 7⟩ : Term))
  let hasKids := !(kidsT.raw.getKind == `«term[_]» && (kidsT.raw.getArg 1).getArgs.isEmpty)
  let cName := tag.toName; let info? ← lookupComponent? cName
  let baseName := info?.map (·.fullName) |>.getD cName
  let cId (sub : Name) : Term := ⟨mkIdentFrom stx (baseName ++ sub)⟩
  if info?.isNone && tag.endsWith ".Form" then
    let some sInfo ← lookupSchemaForm? cName
      | throwErrorAt stx s!"unknown schema form `<{tag}>`; check that `schema {String.ofList (tag.toList.take (tag.length - 5))}:` is defined and imported"
    if hasKids then throwErrorAt stx s!"<{tag}> takes no children; write it self-closing (<{tag} …/>)"
    checkParentNesting stx pPath tag "div"
    let (ctxProps, specials) := splitCompProps propNodes ["key", "bind", "onSubmit", "reset"]
    if let some (resetRef, _) := specials["reset"]? then throwErrorAt resetRef s!"<{tag}>: `reset` is only supported inside a `component` view"
    let some (_, b) := specials["bind"]? | throwErrorAt stx s!"<{tag}> requires `bind=\{draft}` when used outside a `component` view"
    let some (_, submitVal) := specials["onSubmit"]? | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
    let ctxArgs ← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps
    return ← elabTerm (← runPureQuot do
      let callT ← mkAppTermsPure ⟨mkIdentFrom stx sInfo.formViewName⟩ (ctxArgs ++ #[← `(($b).1), ← `(($b).2), submitVal])
      match specials["key"]?.map (·.2) with | some k => `(Qed.withKey (toString $k) $callT) | none => pure callT) expectedType?
  if info?.isNone then
    if ← isFailedComponent cName then return ← elabTerm (← runPureQuot `(Qed.Html.empty)) expectedType?
    let env ← getEnv
    unless env.contains (baseName ++ `_qed_mount) || env.contains (baseName ++ `_qed_renderTag) do
      throwErrorAt stx s!"unknown component `<{tag}>`; check the spelling or import the module defining `component {tag}:`{if !tag.contains '.' then s!" (HTML elements must be lowercase, e.g. `<{tag.toLower}>`)" else ""}"
  if let some info := info? then
    if info.kind == .pureView then
      let (otherProps, specials) := splitCompProps propNodes ["key"]
      return ← elabInlineCompTag stx expectedType? info cId pPath tag otherProps kidsT hasKids (specials["key"]?.map (·.2)) none
  let (props, specials) := splitCompProps propNodes ["key", "state", "initial", "onMsg", "_hoist"]
  let sp (k : String) := specials[k]?.map (·.2)
  if let some hPair := sp "_hoist" then
    let some info := info? | throwErrorAt stx s!"internal: missing ComponentInfo for hoisted <{tag}>"
    return ← elabInlineCompTag stx expectedType? info cId pPath tag props kidsT hasKids (sp "key") (some hPair)
  if hasKids then throwNoChildren stx tag
  elabStatefulCompTag stx expectedType? info? baseName cId tag pPath posNum props (sp "key") (sp "state") (sp "initial") (sp "onMsg")

end CompElab
end Qed
