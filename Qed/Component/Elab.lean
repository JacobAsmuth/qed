import Qed.Component.Codegen
import Qed.Component.AwaitLift
import Qed.Component.Speculative
import Qed.Component.Invariants
import Qed.Component.RpcChecks
import Qed.Speculative
import Qed.View.Lift
import Qed.Runtime
import Qed.Resource
import Qed.Socket

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  let msgV := mkIdent `msg
  let mut pBinders ← spec.props.mapM mkStructBinder
  for sl in spec.slots do
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(sl.id) : Html $msgV := $(← sl.def?.getDM `(Qed.Html.empty)))))
  for bd in spec.binds do
    let bTy ← resolveBindTy bd
    pBinders := pBinders.push (← mkStructBinder { bd with ty? := some bTy })
      |>.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdentFrom bd.id (bindSetName bd.id.getId)) : $bTy → $msgV)))
  for ev in spec.events do
    let evTy ← ev.params.foldrM (init := (⟨msgV.raw⟩ : Term)) fun (_, pTy) acc => `($pTy → $acc)
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(ev.id) : $evTy)))
  if spec.hasChildren then
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent `children) : List (Html $msgV) := [])))
  elabCommand (← `(command| structure $(spec.propsId) ($msgV : Type) where $[$pBinders:structExplicitBinder]*))
  let propReadNames := spec.propNames ++ spec.slots.map (·.id.getId) ++ spec.binds.map (·.id.getId) ++
    spec.events.map (·.id.getId) ++ (if spec.hasChildren then #[`children] else #[])
  let viewBody ← propReadNames.reverse.foldlM (init := body') fun acc g =>
    if mentionsIdent acc.raw g then let gId := mkIdent g; `(let $gId:ident := (p.$gId:ident); $acc) else pure acc
  let needsProps := !pBinders.isEmpty
  let viewBinders : Array BinderStx ←
    if needsProps then pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $(spec.propsId) $msgV))] else pure #[← `(bracketedBinder| {$msgV : Type})]
  elabCommand (← `(command| $[$(spec.doc?):docComment]? @[inline] def $(spec.viewId) $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody))
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause || invStx.getKind == ``compExampleClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` and `example` apply to stateful components"
    let invId := resolveInvIdent invStx spec.t.getId; let rawClauses := (invStx.getArg 2).getSepArgs
    let (vPred, predStr) ← mkViewPredAndStr invStx rawClauses (← rawClauses.mapM (lowerCompExpr .val)) "empty view invariant"
    let vCall ← if needsProps then `($(spec.viewId) p) else `(($(spec.viewId) : Html $msgV))
    let pf? : Option Term := if (invStx.getArg 5).getNumArgs == 2 then some ⟨(invStx.getArg 5).getArg 1⟩ else none
    let rhs ← pf?.getDM `(by let _qed_hv := fun (_ : Unit) => $vCall; suffices ∀ u, ($vPred) (_qed_hv u) = true from this (); qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let ty ← Term.elabType tyTerm
    if (← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _ then
      return (← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _
    else return false

private def mkCompStructJsonCmds (sName : Name) (decls : Array FieldDecl) : CommandElabM (Array CmdStx) :=
  Qed.mkStructJsonCmds (mkIdent sName) (decls.map fun d => { ident := d.id, wireKey := d.id.getId.toString, valTy := d.ty }) { emitNamedDefs := false }

private def mkOutJsonCmds (tId : Name) (outCtorSpecs : Array (Name × Array (Ident × Term))) : CommandElabM (Array CmdStx) := do
  let outId := mkIdent (tId ++ `Out)
  let encAlts ← outCtorSpecs.mapM fun (cName, ps) => do
    let (cId, pTerms) := (mkIdent (tId ++ `Out ++ cName), (ps.map (⟨·.1.raw⟩) : Array Term))
    let pairs := #[← `(("t", Json.str $(Syntax.mkStrLit cName.toString)))] ++ (← ps.zipIdx.mapM fun ((pId, _), i) => `(($(Syntax.mkStrLit (toString i)), toJson $pId:ident)))
    `(Lean.Parser.Term.matchAltExpr| | $cId $pTerms* => Json.obj [$[$pairs],*])
  let decBody ← outCtorSpecs.reverse.foldlM (init := ← `(Except.error "unknown Out tag")) fun acc (cName, ps) => do
    let (cId, pIds) := (mkIdent (tId ++ `Out ++ cName), ps.map (·.1)); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let decSteps ← ps.zipIdx.mapM fun ((_, pTy), i) => `((FromJsonField.fromField j $(Syntax.mkStrLit (toString i)) : Except String $pTy))
    let okBr ← `(do
      $[let $pIds:ident ← $decSteps:term]*
      return ($cId $pTerms*))
    `(if tag == $(Syntax.mkStrLit cName.toString) then $okBr else $acc)
  pure #[
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instToJson)):ident : ToJson $outId := ⟨fun o => match o with $[$encAlts:matchAlt]*⟩),
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instFromJson)):ident : FromJson $outId := ⟨fun j => do let tag ← (FromJsonField.fromField j "t" : Except String String); $decBody:term⟩) ]

private def mkCompLocalDefCmds (spec : ComponentSpec) (idLit : StrLit) : CommandElabM (Array CmdStx) := do
  let regRhs ← match spec.hasProps, spec.outTy?.isNone with
    | true,  true  => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) (fun p s m => ($(spec.updateId) p s m, (none : Option Bool))))
    | true,  false => `(LocalDef.ofProps $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, true  => `(LocalDef.ofSimple $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
    | false, false => `(LocalDef.of $idLit $(spec.initId) $(spec.viewId) $(spec.updateId))
  let regDoc? := if spec.hasProps then none else spec.doc?
  let mut cmds : Array CmdStx := #[
    ← `(command| $[$regDoc?:docComment]? def $(spec.id `reg) : LocalDef := $regRhs),
    ← `(command| $[$(spec.doc?):docComment]? def $(spec.id `_qed_mount) {msg : Type} (key : String) : Attr msg := localMount $idLit key) ]
  if let some o := spec.outTy? then cmds := cmds.push (← `(command| def $(spec.id `_qed_mountWithOpt) {msg : Type} (key : String) (onOut : $o → Option msg) : Attr msg := localMountWith $idLit key onOut))
  return cmds

private def canSynthDecidablePred (stateId : Ident) (pred : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let pVal ← Term.elabTermEnsuringType pred (← Term.elabType (← `($stateId → Prop)))
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← Meta.trySynthInstance (← Meta.mkAppM ``DecidablePred #[pVal])) matches .some _

private def mkEnsuredExistentialWrap (ensConst : Name) (qaIds : Array Ident) (elemVar : Ident) : CommandElabM (Term × Term) := do
  return (← Qed.Lang.mkAppTerms (mkIdent ensConst) (qaIds.map (⟨·.raw⟩)),
          ← qaIds.foldrM (init := ← `(($elemVar:ident).ok)) fun qa acc => `(Exists.intro $qa $acc))

private def mkCompQueriesCmd? (spec : ComponentSpec) : CommandElabM (Option CmdStx) := do
  if spec.queries.isEmpty then return none
  let qTerms ← spec.queries.mapM fun q => do
    let rspec := q.rpc; let reqTupleTy ← Qed.Lang.buildProdType (rspec.mInfo.paramTypeConsts.map fun n => (mkIdent n : Term))
    let fetchBody ← mkRpcQueryBranches spec rspec fun qaIds => do
      let cbTerm : Term ← if !rspec.hasMsgEnsured then `(_qgot _qk) else do
        let some ensConst := rspec.mInfo.ensPredConst | throwErrorAt rspec.rpcRef "internal: missing server `ensures` predicate in `query`"
        let qeId := mkIdent `_qe; let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds qeId
        `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => _qgot _qk (_qr.map fun $qeId => ⟨($qeId:ident).val, $exPrf⟩))
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $(mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName):ident $(mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)):ident [$[$qaTerms:term],*] $cbTerm)))
    `(Qed.Resource.rpcQuery (Req := $reqTupleTy) (params? := fun (s : $(spec.stateId)) => $(← mkRpcQueryParamsBody spec rspec))
        (fetch := fun (s : $(spec.stateId)) _qgot _qk => $fetchBody) (got := $(spec.msgCtor q.ctorName))
        (get := fun (s : $(spec.stateId)) => s.$(q.id):ident) (set := fun c (s : $(spec.stateId)) => { s with $(q.id):ident := c }))
  return some (← `(command| set_option linter.unusedVariables false in def $(spec.id `queries) : List (Query $(spec.stateId) $(spec.msgId)) := [$[$qTerms],*]))

private def mkCompSubscriptionsCmd? (spec : ComponentSpec) : CommandElabM (Option CmdStx) := do
  if spec.subscriptions.isEmpty then return none
  let subTerms ← spec.subscriptions.mapM fun sub => do
    let (slotLit, msgCtor, recTerm) := (Syntax.mkStrLit sub.id.getId.toString, spec.msgCtor (sub.ctor "Msg"), ← liftMacroM <| sub.reconnect.toSyntaxTerm)
    let openBody ← mkSubBranches spec sub (← `(none)) true fun qaIds => do
      let onMsgCb ← if !sub.hasMsgEnsured then `($msgCtor _wk) else do
        let some ensConst := sub.chInfo.ensPredConst | throwErrorAt sub.chanRef "internal: missing channel `ensures` predicate in `subscribe`"
        let weId := mkIdent `_we; let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds weId
        `(fun ($weId : Qed.Ensured $(mkIdentFrom sub.chanRef sub.chInfo.eventTypeConst) ($ensApp)) => $msgCtor _wk ⟨($weId:ident).val, $exPrf⟩)
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      `(some $(← withRef sub.chanRef `(qedCheckChanSub% $(mkIdentFrom sub.chanRef sub.chInfo.fullName):ident [$[$qaTerms:term],*] $slotLit:str ($recTerm, $(spec.msgCtor (sub.ctor "Join")) _wk, $onMsgCb, $(spec.msgCtor (sub.ctor "Status")) _wk))))
    `(Qed.Subscription.mk $slotLit $(mkIdent (subKeyFnName spec.t.getId sub))
        (fun _wk (s : $(spec.stateId)) => $openBody) ($(mkIdentFrom sub.chanRef sub.chInfo.unsubHelperConst) $slotLit)
        (fun (s : $(spec.stateId)) => { s with $(sub.id):ident := Qed.SocketStatus.disconnected }))
  return some (← `(command| set_option linter.unusedVariables false in def $(spec.id `subscriptions) : List (Qed.Subscription $(spec.stateId) $(spec.msgId)) := [$[$subTerms],*]))

private def mkSpecStepPf (sVar mVar : Ident) : List Ident → Term → CommandElabM Term
  | [], _ => `(trivial) | [id0], hTerm => `(($id0:ident).2 $sVar $mVar $hTerm)
  | lastId :: prevRev, hTerm => do `(And.intro $(← mkSpecStepPf sVar mVar prevRev (← `(($hTerm).1))) (($lastId:ident).2 $sVar $mVar ($hTerm).2))

private def mkSpecPropPair (spec : ComponentSpec) (suffix : String) (prop initPf stepFn : Term) : CommandElabM (Array CmdStx) := do
  let appIdent := spec.id `app
  pure #[
    ← `(command| theorem $(spec.id (Name.mkSimple s!"specApp_init_{suffix}")) : $prop ($appIdent).init.1 := $initPf),
    ← `(command| theorem $(spec.id (Name.mkSimple s!"specApp_preserves_{suffix}")) (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) (msg : $(spec.msgId)) (h : $prop st) : $prop (($appIdent).update st msg).1 := $stepFn st msg h) ]

private def mkRehydrateInvCmds (spec : ComponentSpec) (specBaseApp? : Option Ident) (compInv? : Option Term) (hasDecInv : Bool) : CommandElabM (Array CmdStx) := do
  let some inv := compInv? | return #[]
  let appId := spec.id `app
  let (stTy, invWrap) ← match specBaseApp? with
    | some _ => pure (← `(Qed.SpecState $(spec.stateId) $(spec.msgId)), ← `(Qed.SpecEngine.SpecInv ($inv))) | none => pure ((spec.stateId : Term), inv)
  match specBaseApp?, hasDecInv with
  | some _, true  => pure #[← `(command| theorem $(spec.id `rehydrate_inv) (raw : String) (st' : $stTy) : ($appId).rehydrate raw = some st' → ($invWrap) st' := Qed.Internal.App.withSpeculative_rehydrate_sound _ _ (Qed.App.guardRehydrate_sound _ _ _) raw st')]
  | none,   true  => pure #[← `(command| theorem $(spec.id `rehydrate_inv) (raw : String) (st' : $stTy) : ($appId).rehydrate raw = some st' → ($invWrap) st' := Qed.App.guardRehydrate_sound _ _ _ raw st')]
  | some b, false => pure #[← `(command| theorem $(spec.id `dehydrate_inv) : ∀ st st', ($invWrap) st → ($appId).rehydrate (($appId).dehydrate st) = some st' → ($invWrap) st' := Qed.Internal.App.withSpeculative_dehydrate_inv _ _ (by dsimp only [$b:ident]; qedProveDehydrateInv))]
  | none,   false => pure #[← `(command| theorem $(spec.id `dehydrate_inv) : ∀ st st', ($invWrap) st → ($appId).rehydrate (($appId).dehydrate st) = some st' → ($invWrap) st' := by dsimp only [$appId:ident]; qedProveDehydrateInv)]

private def mkViewEqThm (thmId appId viewId stateId : Ident) : CommandElabM CmdStx :=
  `(command| theorem $thmId (s : $stateId) : Qed.Html.canonical (Qed.App.view $appId s) = Qed.Html.canonical ($viewId s) := by qedProveViewEquiv $appId $viewId)

private def mkSpecAppCmds (spec : ComponentSpec) (finalApp : Term) (compInv? : Option Term)
    (hasDecInv : Bool) (stateInvEntries : Array (Term × Option Ident)) (initCmds : Array CmdStx) : CommandElabM (Array CmdStx × CmdStx) := do
  let (appId, baseId, clsId) := (spec.id `app, spec.id `_baseApp, spec.id `_specClassify)
  let mut cmds := initCmds ++ #[
    ← `(command| def $baseId : App $(spec.stateId) $(spec.msgId) := $finalApp),
    ← `(command| $[$(spec.doc?):docComment]? def $appId : App (Qed.SpecState $(spec.stateId) $(spec.msgId)) $(spec.msgId) := Qed.Internal.App.withSpeculative $clsId $baseId)
  ] ++ (← mkSpecPropPair spec "coherent" (← `(Qed.SpecEngine.Coherent (fun s m => (($baseId).update s m).1)))
        (← `(Qed.Internal.App.withSpeculative_init_coherent $clsId $baseId)) (← `(Qed.Internal.App.withSpeculative_step_coherent $clsId $baseId)))
    ++ (← mkSpecPropPair spec "wellFormedIds" (← `(Qed.SpecEngine.WellFormedIds))
        (← `(Qed.Internal.App.withSpeculative_init_wellFormedIds $clsId $baseId)) (← `(Qed.Internal.App.withSpeculative_step_wellFormedIds $clsId $baseId)))
  if spec.queries.isEmpty && spec.subscriptions.isEmpty then
    if let (some inv, some invIds) := (compInv?, stateInvEntries.foldl (init := some #[]) fun acc (_, id?) => match acc, id? with | some arr, some id => some (arr.push id) | _, _ => none) then
      if !invIds.isEmpty then
        let initPf ← match invIds.toList with | id0 :: rest => rest.foldlM (init := ← `(($id0:ident).1)) fun acc id => `(And.intro $acc ($id:ident).1) | [] => `(trivial)
        let (sV, mV, hV) := (mkIdent `_s, mkIdent `_m, mkIdent `_h)
        cmds := cmds ++ (← mkSpecPropPair spec "inv" (← `(Qed.SpecEngine.SpecInv ($inv)))
          (← `(Qed.Internal.App.withSpeculative_init_inv $clsId $baseId $initPf))
          (← `(Qed.Internal.App.withSpeculative_step_inv $clsId $baseId (fun $sV $mV $hV => $(← mkSpecStepPf sV mV invIds.toList.reverse hV)))))
  let baseViewEqId := spec.id `_base_app_view_eq
  cmds := cmds ++ (← mkRehydrateInvCmds spec (some baseId) compInv? hasDecInv) |>.push (← mkViewEqThm baseViewEqId baseId spec.viewId spec.stateId)
  return (cmds, ← `(command| theorem $(spec.id `app_view_eq) (st : Qed.SpecState $(spec.stateId) $(spec.msgId)) :
      Qed.Html.canonical (Qed.App.view $appId st) = Qed.Html.canonical ($(spec.viewId) st.visible) := by
    simpa [Qed.Internal.App.withSpeculative_view, $appId:ident] using $baseViewEqId st.visible))

private def applyHeadDirectives (hmId stId : Ident) (dirs : Array Syntax) (tail : Term) : CommandElabM Term :=
  dirs.foldrM (init := tail) fun d acc => do match d.getKind with
    | `Qed.compHeadTitle | `Qed.compHeadDescription | `Qed.compHeadCanonical =>
        let fId := mkIdent <| match d.getKind with | `Qed.compHeadTitle => `title | `Qed.compHeadDescription => `description | _ => `canonical
        `(let $hmId:ident := { $hmId with $fId:ident := Option.some ($(← lowerCompExpr .val (d.getArg 1)) : String) }; $acc)
    | `Qed.compHeadMeta   => `(let $hmId:ident := { $hmId with metaTags := ($hmId).metaTags ++ [(($(← lowerCompExpr .val (d.getArg 1)) : String), ($(← lowerCompExpr .val (d.getArg 3)) : String))] }; $acc)
    | `Qed.compHeadStatus => `(let $stId:ident : Nat := $(← lowerCompExpr .val (d.getArg 1)); $acc)
    | `Qed.compHeadRedirect =>
        let stT ← if (d.getArg 2).getNumArgs == 4 then lowerCompExpr .val ((d.getArg 2).getArg 3) else `((302 : Nat))
        `(let $hmId:ident := { $hmId with redirect := Option.some ($(← lowerCompExpr .val (d.getArg 1)) : String) }; let $stId:ident : Nat := $stT; $acc)
    | _ => throwErrorAt d "unexpected directive in `head:`"

private def mkCompHeadCmd? (spec : ComponentSpec) : CommandElabM (Option CmdStx) := do
  let some headStx := spec.headClause? | return none
  let (hmId, stId) := (mkIdent `_qed_hm, mkIdent `_qed_st)
  let mut sharedDirs : Array Syntax := #[]; let mut caseItems : Array Syntax := #[]
  for item in (headStx.getArg 2).getArgs do
    if item.getKind == `Qed.compHeadCase then caseItems := caseItems.push item
    else if !caseItems.isEmpty then throwErrorAt item "shared `head:` directives must appear before `case` arms"
    else sharedDirs := sharedDirs.push item
  let coreTail : Term ← if caseItems.isEmpty then `(($hmId, $stId)) else do
    let some rd := spec.route? | throwErrorAt caseItems[0]! s!"`case` inside `head:` requires a `route` declaration on `component {spec.t.getId}`"
    let mut alts : Array MatchAltStx := #[]
    for c in caseItems do
      let armBody ← applyHeadDirectives hmId stId (c.getArg 3).getArgs (← `(($hmId, $stId)))
      for p in (c.getArg 1).getSepArgs do alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(← liftMacroM (lowerQedPat p)) => $armBody))
    `(match $(rd.field):ident with $[$alts:matchAlt]*)
  let fullBody ← `(let $hmId:ident : Qed.HeadMeta := {}; let $stId:ident : Nat := 200; $(← applyHeadDirectives hmId stId sharedDirs coreTail))
  return some (← `(command| set_option linter.unusedVariables false in def $(spec.id `headInfo) (s : $(spec.stateId)) : Qed.HeadMeta × Nat := $(← bindMentionedFields spec (mentionsIdent fullBody.raw) fullBody)))

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool) (stateInvEntries : Array (Term × Option Ident)) : CommandElabM (Array CmdStx × CmdStx) := do
  let mut cmds : Array CmdStx := #[]
  let startArg ← if hasStart then `($(spec.id `startCmd)) else `(Qed.Cmd.none)
  let onPortArg ← if spec.portIns.isEmpty then `(Option.none) else do
    let onPortId := spec.id `onPort
    let inTuples ← spec.portIns.mapM fun p =>
      `(($(Syntax.mkStrLit p.id.getId.toString), fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $(spec.msgCtor p.id.getId)))
    cmds := cmds.push (← `(command| def $onPortId : String → String → Option $(spec.msgId) := dispatchPorts #[$inTuples,*]))
    `(some $onPortId)
  let expandedBody ← liftMacroM <| Qed.Jsx.expandJsxIn body'.raw
  let templateTerm0 : Term := ⟨← liftMacroM <| Qed.Internal.liftViewWithFields (mkIdent `_qed_s) (spec.states.map (·.id)) expandedBody⟩
  let templateTerm ← spec.portOuts.reverse.foldlM (init := templateTerm0) fun acc po =>
    if mentionsIdent acc.raw po.id.getId then `(let $(mkIdent po.id.getId):ident := $(spec.id po.id.getId); $acc) else pure acc
  let appUpdate ← if spec.hasEffects then `($(spec.updateId)) else `(fun s m => ($(spec.updateId) s m, Qed.Cmd.none))
  let onSessionArg ← if spec.sessionField?.isSome then `(some $(spec.msgCtor `_onSession)) else `(none)
  let mut appT : Term ← (if spec.route?.isSome then
    `(Qed.Internal.mkRoutedApp $(spec.initId) $appUpdate $templateTerm (onRoute := $(spec.msgCtor `_onRoute))
        (onSession := $onSessionArg) (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg))
  else `(Qed.Internal.mkApp $(spec.initId) $appUpdate $templateTerm (onSession := $onSessionArg)
        (start := $startArg) (locals := $(spec.id `regs)) (styles := qedInternalStyles% $(spec.viewId)) (onPort := $onPortArg)))
  if !spec.themes.isEmpty then
    let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, (← getScope).openDecls)
    let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
    let thTerms ← spec.themes.mapM fun thId => do
      let some thInfo := Qed.StyleDsl.resolveInRegistry thReg env currNs openDecls thId.getId.toString | throwErrorAt thId s!"unknown `theme` `{thId.getId}`"
      pure (mkIdentFrom thId thInfo.styleConst : Term)
    appT ← `(Qed.Internal.App.withExtraStyles [$[$thTerms],*] $appT)
  if !spec.stylesheets.isEmpty then appT ← `(Qed.Internal.App.withStylesheets [$(spec.stylesheets.map Syntax.mkStrLit):str,*] $appT)
  appT ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $(spec.initId) $appT)
         else `(Qed.Internal.App.withDehydrate (Dehydrate.except $(spec.initId) [$[$spec.ephemeralFields:ident],*]) $appT)
  if !spec.queries.isEmpty then appT ← `(Qed.Internal.App.withQueries $(spec.id `queries) $appT)
  if !spec.subscriptions.isEmpty then appT ← `(Qed.Internal.App.withSubscriptions $(spec.id `subscriptions) $appT)
  if spec.headClause?.isSome then let hId := spec.id `headInfo; appT ← `(Qed.App.withSsrStatus (fun _s => ($hId _s).2) (Qed.App.withHead (fun _s => ($hId _s).1) $appT))
  let stateInvPreds := stateInvEntries.map (·.1)
  let compInv? : Option Term ← if stateInvPreds.isEmpty then pure none
    else if stateInvPreds.size == 1 then some <$> `(($(stateInvPreds[0]!) : $(spec.stateId) → Prop))
    else do let sVar := mkIdent `_qed_s; some <$> `(fun ($sVar:ident : $(spec.stateId)) => $(← mkConjBody (← stateInvPreds.mapM fun p => `(($p) $sVar))))
  let hasDecInv ← match compInv? with | some inv => canSynthDecidablePred spec.stateId inv | none => pure false
  if let (some inv, true) := (compInv?, hasDecInv) then appT ← `(Qed.App.guardRehydrate ($inv) $appT)
  if spec.hasSpeculative then return ← mkSpecAppCmds spec appT compInv? hasDecInv stateInvEntries cmds
  let appId := spec.id `app
  return (cmds.push (← `(command| $[$(spec.doc?):docComment]? def $appId : App $(spec.stateId) $(spec.msgId) := $appT)) ++
          (← mkRehydrateInvCmds spec none compInv? hasDecInv), ← mkViewEqThm (spec.id `app_view_eq) appId spec.viewId spec.stateId)

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) : CommandElabM (Array CmdStx × Bool × Bool) := do
  let (tId, fs) := (spec.t.getId, spec.states.map (·.id)); let mut cmds : Array CmdStx := #[]
  if spec.mountable then let dsT := spec.states.filterMap (·.def?); cmds := cmds.push (← `(command| def $(spec.initId) : $(spec.stateId) := { $[$fs:ident := $dsT],* }))
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart); let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  if hasStart then
    let pBinders ← mkPropsBinders spec
    let subStarts ← hoistedStarts.mapM fun h => do
      let cStart := mkIdent (h.info.fullName ++ `startCmd)
      let call ← if h.info.hasProps then `($cStart $(← mkHoistedPropsTerm h)) else `($cStart)
      `(Cmd.map $(spec.msgCtor h.ctorName) $call)
    let mut startBody ← mkCmdBatch (starts' ++ subStarts)
    if spec.mountable then
      startBody ← bindMentionedFields spec (mentionsIdent startBody.raw) startBody
      if mentionsIdent startBody.raw `s then startBody ← `(let s := $(spec.initId); $startBody)
    cmds := cmds.push (← `(command| def $(spec.id `startCmd) $[$pBinders:bracketedBinder]* : Cmd $(spec.msgId) := $startBody))
  let outCtorSpecs := spec.events.map (fun ev => (ev.id.getId, ev.params)) ++ spec.binds.map (fun bd => (bindSetName bd.id.getId, #[(mkIdent `v, bd.ty)]))
  let canEmitCodecs ← if ← spec.props.allM (canSynthJson ``FromJsonField ·.ty) then spec.states.allM (canSynthJson ``FromJsonField ·.ty) else pure false
  let outJsonOk ← if spec.outTy?.isSome then outCtorSpecs.allM fun (_, ps) => ps.allM (canSynthJson ``FromJsonField ·.2) else pure true
  if canEmitCodecs then cmds := cmds ++ (← mkCompStructJsonCmds (tId ++ `Props) spec.props) ++ (← mkCompStructJsonCmds (tId ++ `State) spec.states)
  if spec.outTy?.isSome && outJsonOk then cmds := cmds ++ (← mkOutJsonCmds tId outCtorSpecs)
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && canEmitCodecs && outJsonOk
  if hasLocalDef then cmds := cmds ++ (← mkCompLocalDefCmds spec idLit)
  let own ← if hasLocalDef then `([$(spec.id `reg)]) else `(([] : List LocalDef))
  return (cmds.push (← `(command| def $(spec.id `regs) : List LocalDef := LocalDef.dedupe ($own ++ qedInternalLocalRegistrations% $(spec.viewId)))), hasStart, hasLocalDef)

private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k else k

private def elabStatefulComponentBody (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
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
  let ownChans := rawSpec.subscriptions.foldl (init := #[]) fun a sub =>
    match sub.chInfo.kind with | .fullstack _ srvShort _ => pushUnique a (srvShort, sub.chInfo.channelName) | _ => a
  let allUsedChannels := acc.hoisted.foldl (fun a h => h.info.usedChannels.foldl pushUnique a) ownChans
  let eventNames := rawSpec.events.map (·.id.getId)
  let ownHasEffects := !rw.starts.isEmpty || !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty ||
    !rawSpec.queries.isEmpty || !rawSpec.subscriptions.isEmpty || !acc.specResolves.isEmpty ||
    acc.sites.any (fun s => s.stmts?.any (·.any (hasEffectStmt eventNames))) ||
    (rw.route?.any fun rd => rd.alts.any (hasEffectStmt eventNames)) || acc.hoisted.any (·.info.hasEffects)
  let spec ← elabStructsAndResolveTypes {
    rawSpec with route? := rw.route?, hasEffects := ownHasEffects, usedRpcs := allUsedRpcs, usedChannels := allUsedChannels,
                 specDispatches := acc.specDispatches, specNodes := acc.specNodes, specResolves := acc.specResolves
  } acc.hoisted acc.formDrafts acc.resetForms
  currentCompSessionRef.set spec.sessionField?
  let errsBefore ← getErrorCount
  (← mkViewCmds spec rw.body (← mkMsgAndUpdateCmds spec acc.sites)).forM elabCommand
  let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec rw.starts (Syntax.mkStrLit compNs.toString)
  mountCmds.forM elabCommand
  let isTopMount := spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids
  if isTopMount then
    for cmd? in #[← mkCompQueriesCmd? spec, ← mkCompSubscriptionsCmd? spec, ← mkCompHeadCmd? spec] do
      if let some c := cmd? then elabCommand c
    (← mkSpecClassifyCmds spec).forM elabCommand
  let stateInvEntries ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
  let activeInvEntries := if (← getErrorCount) == errsBefore then stateInvEntries else #[]
  if (← getErrorCount) == errsBefore then withOpenNs compNs (elabCompReachableAndWitnesses spec)
  verifyPendingRpcChecks spec (activeInvEntries.map (·.1))
  if isTopMount then
    let (appCmds, eqCmd) ← mkCompAppCmds spec rw.body hasStart activeInvEntries
    appCmds.forM elabCommand
    if (← getErrorCount) == errsBefore then elabCommand eqCmd
  let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
  for (defName, pairs) in #[(`usedRpcs, allUsedRpcs), (`usedChannels, allUsedChannels)] do
    let ts ← pairs.mapM fun (a, b) => `((($(Syntax.mkStrLit a), $(Syntax.mkStrLit b)) : String × String))
    elabCommand (← `(command| def $(spec.id defName) : List (String × String) := [$[$ts],*]))
  let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
  modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
    hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects, hasStart, mountable := spec.mountable,
    hasLocalDef, usedRpcs := allUsedRpcs, usedChannels := allUsedChannels }

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let (savedEnv, errsInit, priorTasks) := (← getEnv, ← getErrorCount, (← get).snapshotTasks.size)
  let compNs := (← getCurrNamespace) ++ (stx.getArg 2).getId
  pendingRpcChecks.set #[]; pendingPredictChecks.set #[]; currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    for stCl in rawSpec.styles do
      withOpenNs compNs do
        let sNameId : Ident := ⟨stCl.getArg 1⟩
        Qed.StyleDsl.elabStyleDef none (mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId))
          (Qed.StyleDsl.extractStyleExtends (stCl.getArg 2)) ((stCl.getArg 3).getNumArgs == 1) (stCl.getArg 5).getArgs
    withOpenNs compNs (elabStatefulComponentBody compNs rawSpec)
    okRef.set true
  finally
    pendingRpcChecks.set #[]; pendingPredictChecks.set #[]; currentCompSessionRef.set none
    let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
    let ok ← okRef.get; let errs ← getErrorCount
    if !ok || errs > errsInit || newTasks.any (Qed.Diag.snapshotTreeHasErrors 64 ·.get) then setEnv savedEnv

end CompElab
end Qed
