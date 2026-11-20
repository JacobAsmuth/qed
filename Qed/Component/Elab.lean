import Qed.Component.Codegen
import Qed.Component.AwaitLift
import Qed.Component.Speculative
import Qed.Component.Invariants
import Qed.Component.RpcChecks
import Qed.Runtime
import Qed.Resource
import Qed.Socket

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  let doc?    := spec.doc?
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  let msgV    := mkIdent `msg
  let mut pBinders ← spec.props.mapM mkStructBinder
  let mut propReadNames := spec.propNames
  for sl in spec.slots do
    propReadNames := propReadNames.push sl.id.getId
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder|
      ($(sl.id) : Html $msgV := $(← sl.def?.getDM `(Qed.Html.empty)))))
  for bd in spec.binds do
    propReadNames := propReadNames.push bd.id.getId
    let bTy ← resolveBindTy bd
    let setF := mkIdentFrom bd.id (Name.mkSimple s!"set_{bd.id.getId}")
    pBinders := pBinders.push (← mkStructBinder { bd with ty? := some bTy })
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($setF : $bTy → $msgV)))
  for ev in spec.events do
    propReadNames := propReadNames.push ev.id.getId
    let evTy ← ev.params.foldrM (init := (⟨msgV.raw⟩ : Term)) fun (_, pTy) acc => `($pTy → $acc)
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(ev.id) : $evTy)))
  if spec.hasChildren then
    propReadNames := propReadNames.push `children
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent `children) : List (Html $msgV) := [])))
  elabCommand (← `(command| structure $propsId ($msgV : Type) where $[$pBinders:structExplicitBinder]*))
  let mut viewBody := body'
  for g in propReadNames.reverse do
    if mentionsIdent viewBody.raw g then
      let gId := mkIdent g
      viewBody ← `(let $gId:ident := (p.$gId:ident); $viewBody)
  let needsProps := !pBinders.isEmpty
  let viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if needsProps then pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $propsId $msgV))]
    else pure #[← `(bracketedBinder| {$msgV : Type})]
  elabCommand (← `(command| $[$doc?:docComment]? @[inline] def $viewId $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody))
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` applies to stateful components"
    let invId := resolveInvIdent invStx tId
    let rawClauses := (invStx.getArg 2).getSepArgs
    let loweredClauses ← rawClauses.mapM (lowerCompExpr .val)
    let vPred ← match loweredClauses.toList with
      | [p] => pure p
      | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
      | [] => throwErrorAt invStx "empty view invariant"
    let predStr := String.intercalate ", " (rawClauses.toList.map fun c => (c.reprint.getD "this rule").trimmed)
    let vCall ← if needsProps then `($viewId p) else `(($viewId : Html $msgV))
    let pf? : Option Term := if (invStx.getArg 5).getNumArgs == 2 then some ⟨((invStx.getArg 5).getArg 1)⟩ else none
    let rhs ← pf?.getDM `(by
      let _qed_hv := fun (_ : Unit) => $vCall
      suffices ∀ u, ($vPred) (_qed_hv u) = true from this ()
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyTerm
      return ((← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _) &&
             ((← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _)
    catch _ => return false

private def mkStructJsonCmds (sName : Name) (decls : Array FieldDecl) :
    CommandElabM (Array (TSyntax `command)) := do
  let sId := mkIdent sName; let ids := decls.map (·.id)
  let enc ← decls.mapM fun d => `(($(Syntax.mkStrLit d.id.getId.toString), toJson (x.$(d.id):ident)))
  let dec ← decls.mapM fun d => `((FromJsonField.fromField j $(Syntax.mkStrLit d.id.getId.toString) : Except String $(d.ty)))
  pure #[
    ← `(command| instance $(mkIdent (sName ++ `instToJson)):ident : ToJson $sId := ⟨fun x => Json.obj [$[$enc],*]⟩),
    ← `(command| instance $(mkIdent (sName ++ `instFromJson)):ident : FromJson $sId := ⟨fun j => do
          $[let $ids:ident ← $dec:term]*
          return { $[$ids:ident],* }⟩) ]

private def mkOutJsonCmds (tId : Name) (outCtorSpecs : Array (Name × Array (Ident × Term))) :
    CommandElabM (Array (TSyntax `command)) := do
  let outId := mkIdent (tId ++ `Out)
  let encAlts ← outCtorSpecs.mapM fun (cName, ps) => do
    let cId := mkIdent (tId ++ `Out ++ cName)
    let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let kvPairs ← (List.range pIds.size).toArray.mapM fun i =>
      `(($(Syntax.mkStrLit (toString i)), toJson $(pIds[i]!):ident))
    let allPairs := #[← `(("t", Json.str $(Syntax.mkStrLit cName.toString)))] ++ kvPairs
    `(Lean.Parser.Term.matchAltExpr| | $cId $pTerms* => Json.obj [$[$allPairs],*])
  let mut decBody : Term ← `(Except.error "unknown Out tag")
  for (cName, ps) in outCtorSpecs.reverse do
    let cId := mkIdent (tId ++ `Out ++ cName)
    let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let decSteps ← (List.range ps.size).toArray.mapM fun i =>
      `((FromJsonField.fromField j $(Syntax.mkStrLit (toString i)) : Except String $(ps[i]!.2)))
    let okBr ← `(do
      $[let $pIds:ident ← $decSteps:term]*
      return ($cId $pTerms*))
    decBody ← `(if tag == $(Syntax.mkStrLit cName.toString) then $okBr else $decBody)
  pure #[
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instToJson)):ident : ToJson $outId := ⟨fun o => match o with $[$encAlts:matchAlt]*⟩),
    ← `(command| instance $(mkIdent (tId ++ `Out ++ `instFromJson)):ident : FromJson $outId := ⟨fun j => do
          let tag ← (FromJsonField.fromField j "t" : Except String String)
          $decBody:term⟩) ]

private def mkCompLocalDefCmds (spec : ComponentSpec) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let tId      := spec.t.getId
  let initId   := mkIdent (tId ++ `init)
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let regId    := mkIdent (tId ++ `reg)
  let mut cmds : Array (TSyntax `command) := #[
    ← (if spec.hasProps then
        if spec.outTy?.isNone then `(command| def $regId : LocalDef :=
          LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
        else `(command| def $regId : LocalDef := LocalDef.ofProps $idLit $initId $viewId $updateId)
      else if spec.outTy?.isNone then `(command| $[$doc?:docComment]? def $regId : LocalDef :=
        LocalDef.ofSimple $idLit $initId $viewId $updateId)
      else `(command| $[$doc?:docComment]? def $regId : LocalDef :=
        LocalDef.of $idLit $initId $viewId $updateId)),
    ← `(command| $[$doc?:docComment]? def $(mkIdent (tId ++ `_qed_mount)) {msg : Type} (key : String) : Attr msg :=
          localMount $idLit key) ]
  if let some o := spec.outTy? then
    cmds := cmds.push (← `(command| def $(mkIdent (tId ++ `_qed_mountWithOpt)) {msg : Type}
          (key : String) (onOut : $o → Option msg) : Attr msg :=
          localMountWith $idLit key onOut))
  return cmds

private def canSynthDecidablePred (stateId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let pVal ← Term.elabTermEnsuringType pred (← Term.elabType (← `($stateId → Prop)))
      Term.synthesizeSyntheticMVarsNoPostponing
      if ((← Core.getMessageLog).toList.drop preCount).any (·.severity == .error) then return false
      let expected ← Meta.mkAppM ``DecidablePred #[pVal]
      return (← Meta.trySynthInstance expected) matches .some _
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

private def mkCompQueriesCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.queries.isEmpty then return none
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let msgId := mkIdent (tId ++ `Msg)
  let qTerms ← spec.queries.mapM fun q => do
    let qNm := q.id
    let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
    let rspec := q.rpc
    let reqTupleTy ← mkRightTuple (`(Unit)) (fun a b => `($a × $b))
      (rspec.mInfo.paramTypeConsts.toList.map fun n => (mkIdent n : Term))
    let paramsBody ← mkRpcQueryParamsBody spec rspec
    let fetchBody ← mkRpcQueryBranches spec rspec fun qaIds => do
      let cbTerm : Term ← if !rspec.hasMsgEnsured then
          `(_qgot _qk)
        else
          let some ensConst := rspec.mInfo.ensPredConst
            | throwErrorAt rspec.rpcRef "internal: missing server `ensures` predicate in `query`"
          let ensApp ← qaIds.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
          let exPrf ← qaIds.foldrM (init := ← `(_qe.ok)) fun qa acc => `(Exists.intro $qa $acc)
          `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => _qgot _qk (_qr.map fun _qe => ⟨_qe.val, $exPrf⟩))
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      let srvId := mkIdentFrom rspec.rpcRef rspec.srvInfo.serverName
      let methId := mkIdentFrom rspec.rpcRef (Name.mkSimple rspec.mInfo.name)
      `(some $(← withRef rspec.rpcRef `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$qaTerms:term],*] $cbTerm)))
    `(Qed.Resource.rpcQuery (Req := $reqTupleTy)
        (params? := fun (s : $stateId) => $paramsBody)
        (fetch := fun (s : $stateId) _qgot _qk => $fetchBody)
        (got := $qCtor)
        (get := fun (s : $stateId) => s.$qNm:ident)
        (set := fun c (s : $stateId) => { s with $qNm:ident := c }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(mkIdent (tId ++ `queries)) : List (Query $stateId $msgId) := [$[$qTerms],*]))

private def mkCompSubscriptionsCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  if spec.subscriptions.isEmpty then return none
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let msgId := mkIdent (tId ++ `Msg)
  let subTerms ← spec.subscriptions.mapM fun sub => do
    let subNm := sub.id
    let slotLit := Syntax.mkStrLit subNm.getId.toString
    let wsKeyId := mkIdent (subKeyFnName tId sub)
    let joinCtor := mkIdent (tId ++ `Msg ++ sub.joinCtor)
    let msgCtor := mkIdent (tId ++ `Msg ++ sub.msgCtor)
    let stCtor := mkIdent (tId ++ `Msg ++ sub.statusCtor)
    let recTerm ← liftMacroM <| sub.reconnect.toSyntaxTerm
    let unsubFnId := mkIdentFrom sub.chanRef sub.chInfo.unsubHelperConst
    let chFullId := mkIdentFrom sub.chanRef sub.chInfo.fullName
    let openBody ← mkSubBranches spec sub (← `(none)) true fun qaIds => do
      let onJoinCb ← `($joinCtor _wk)
      let onStCb ← `($stCtor _wk)
      let onMsgCb ← if !sub.hasMsgEnsured then
          `($msgCtor _wk)
        else
          let some ensConst := sub.chInfo.ensPredConst
            | throwErrorAt sub.chanRef "internal: missing channel `ensures` predicate in `subscribe`"
          let evTyId := mkIdentFrom sub.chanRef sub.chInfo.eventTypeConst
          let ensApp ← qaIds.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
          let exPrf ← qaIds.foldrM (init := ← `(_we.ok)) fun qa acc => `(Exists.intro $qa $acc)
          `(fun (_we : Qed.Ensured $evTyId ($ensApp)) => $msgCtor _wk ⟨_we.val, $exPrf⟩)
      let qaTerms : Array Term := qaIds.map (⟨·.raw⟩)
      let subCmd ← withRef sub.chanRef `(qedCheckChanSub% $chFullId:ident [$[$qaTerms:term],*] $slotLit:str ($recTerm, $onJoinCb, $onMsgCb, $onStCb))
      `(some $subCmd)
    `(Qed.Subscription.mk
        $slotLit
        $wsKeyId
        (fun _wk (s : $stateId) => $openBody)
        ($unsubFnId $slotLit)
        (fun (s : $stateId) => { s with $subNm:ident := Qed.SocketStatus.disconnected }))
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $(mkIdent (tId ++ `subscriptions)) : List (Qed.Subscription $stateId $msgId) := [$[$subTerms],*]))


private def mkSpecAppCmds (spec : ComponentSpec) (tId : Name) (stateId msgId appIdent viewIdent : Ident)
    (finalApp : Term) (compInv? : Option Term) (hasDecInv : Bool)
    (stateInvEntries : Array (Term × Option Ident)) (initCmds : Array (TSyntax `command)) :
    CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let doc? := spec.doc?
  let mut cmds := initCmds
  let baseAppIdent := mkIdent (tId ++ `_baseApp)
  let clsIdent := mkIdent (tId ++ `_specClassify)
  cmds := cmds.push (← `(command| def $baseAppIdent : App $stateId $msgId := $finalApp))
  cmds := cmds.push (← `(command| $[$doc?:docComment]? def $appIdent :
    App (Qed.SpecState $stateId $msgId) $msgId :=
    Qed.Internal.App.withSpeculative $clsIdent $baseAppIdent))
  cmds := cmds.push (← `(command|
    theorem $(mkIdent (tId ++ `specApp_init_coherent)) :
        Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) ($appIdent).init.1 :=
      Qed.Internal.App.withSpeculative_init_coherent $clsIdent $baseAppIdent))
  cmds := cmds.push (← `(command|
    theorem $(mkIdent (tId ++ `specApp_preserves_coherent))
        (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
        (hcoh : Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) st) :
        Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) (($appIdent).update st msg).1 :=
      Qed.Internal.App.withSpeculative_step_coherent $clsIdent $baseAppIdent st msg hcoh))
  cmds := cmds.push (← `(command|
    theorem $(mkIdent (tId ++ `specApp_init_wellFormedIds)) :
        Qed.SpecEngine.WellFormedIds ($appIdent).init.1 :=
      Qed.Internal.App.withSpeculative_init_wellFormedIds $clsIdent $baseAppIdent))
  cmds := cmds.push (← `(command|
    theorem $(mkIdent (tId ++ `specApp_preserves_wellFormedIds))
        (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
        (hwf : Qed.SpecEngine.WellFormedIds st) :
        Qed.SpecEngine.WellFormedIds (($appIdent).update st msg).1 :=
      Qed.Internal.App.withSpeculative_step_wellFormedIds $clsIdent $baseAppIdent st msg hwf))
  if spec.queries.isEmpty && spec.subscriptions.isEmpty then
    if let some inv := compInv? then
      let invIds? : Option (Array Ident) :=
        stateInvEntries.foldl (init := some #[]) fun acc (_, id?) =>
          match acc, id? with
          | some arr, some id => some (arr.push id)
          | _, _ => none
      if let some invIds := invIds? then
        if !invIds.isEmpty then
          let initPf : Term ← match invIds.toList with
            | [id0] => `(($id0:ident).1)
            | id0 :: rest =>
                rest.foldlM (init := ← `(($id0:ident).1)) fun acc id => `(And.intro $acc ($id:ident).1)
            | [] => `(trivial)
          let sVar := mkIdent `_s
          let mVar := mkIdent `_m
          let hVar := mkIdent `_h
          let rec mkStepPf (revIds : List Ident) (hTerm : Term) : CommandElabM Term := do
            match revIds with
            | [] => `(trivial)
            | [id0] => `(($id0:ident).2 $sVar $mVar $hTerm)
            | lastId :: prevRev =>
                let leftPf ← mkStepPf prevRev (← `(($hTerm).1))
                `(And.intro $leftPf (($lastId:ident).2 $sVar $mVar ($hTerm).2))
          let stepPf ← mkStepPf invIds.toList.reverse hVar
          cmds := cmds.push (← `(command|
            theorem $(mkIdent (tId ++ `specApp_init_inv)) :
                Qed.SpecEngine.SpecInv ($inv) ($appIdent).init.1 :=
              Qed.Internal.App.withSpeculative_init_inv $clsIdent $baseAppIdent $initPf))
          cmds := cmds.push (← `(command|
            theorem $(mkIdent (tId ++ `specApp_preserves_inv))
                (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
                (h : Qed.SpecEngine.SpecInv ($inv) st) :
                Qed.SpecEngine.SpecInv ($inv) (($appIdent).update st msg).1 :=
              Qed.Internal.App.withSpeculative_step_inv $clsIdent $baseAppIdent
                (fun $sVar $mVar $hVar => $stepPf) st msg h))
  match compInv?, hasDecInv with
  | some inv, true =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `rehydrate_inv)) (raw : String) (st' : Qed.SpecState $stateId $msgId) :
            ($appIdent).rehydrate raw = some st' → Qed.SpecEngine.SpecInv ($inv) st' :=
          Qed.Internal.App.withSpeculative_rehydrate_sound _ _
            (Qed.App.guardRehydrate_sound _ _ _) raw st'))
  | some inv, false =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `dehydrate_inv)) :
            ∀ st st', Qed.SpecEngine.SpecInv ($inv) st →
              ($appIdent).rehydrate (($appIdent).dehydrate st) = some st' →
              Qed.SpecEngine.SpecInv ($inv) st' :=
          Qed.Internal.App.withSpeculative_dehydrate_inv _ _ (by
            dsimp only [$baseAppIdent:ident]; qedProveDehydrateInv)))
  | none, _ => pure ()
  let baseViewEqIdent := mkIdent (tId ++ `_base_app_view_eq)
  cmds := cmds.push (← `(command|
    theorem $baseViewEqIdent (s : $stateId) :
        Qed.Html.canonical (Qed.App.view $baseAppIdent s) = Qed.Html.canonical ($viewIdent s) := by
      qedProveViewEquiv $baseAppIdent $viewIdent))
  let appViewEqCmd ← `(command|
    theorem $(mkIdent (tId ++ `app_view_eq)) (st : Qed.SpecState $stateId $msgId) :
        Qed.Html.canonical (Qed.App.view $appIdent st) = Qed.Html.canonical ($viewIdent st.visible) := by
      simpa [Qed.Internal.App.withSpeculative_view, $appIdent:ident] using $baseViewEqIdent st.visible)
  return (cmds, appViewEqCmd)

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvEntries : Array (Term × Option Ident)) : CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let stateInvPreds := stateInvEntries.map (·.1)
  let doc?       := spec.doc?
  let tId        := spec.t.getId
  let stateId    := mkIdent (tId ++ `State)
  let initId     := mkIdent (tId ++ `init)
  let startCmdId := mkIdent (tId ++ `startCmd)
  let msgId      := mkIdent (tId ++ `Msg)
  let updateId   := mkIdent (tId ++ `update)
  let viewId     := mkIdent (tId ++ `view)
  let regsId     := mkIdent (tId ++ `regs)
  let mut cmds : Array (TSyntax `command) := #[]
  let startArg : Term ← if hasStart then `($startCmdId) else `(Qed.Cmd.none)
  let onPortArg : Term ← if spec.portIns.isEmpty then `(Option.none) else do
    let onPortId := mkIdent (tId ++ `onPort)
    let inTuples ← spec.portIns.mapM fun p => do
      let pLit := Syntax.mkStrLit p.id.getId.toString
      let pCtor := mkIdent (tId ++ `Msg ++ p.id.getId)
      `(($pLit, fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $pCtor))
    cmds := cmds.push (← `(command| def $onPortId : String → String → Option $msgId :=
      dispatchPorts #[$inTuples,*]))
    `(some $onPortId)
  let expandedBody ← liftMacroM <| Qed.Jsx.expandJsxIn body'.raw
  let mut templateTerm : Term := ⟨← liftMacroM <|
    Qed.Internal.liftViewWithFields (mkIdent `_qed_s) (spec.states.map (·.id)) expandedBody⟩
  for po in spec.portOuts.reverse do
    if mentionsIdent templateTerm.raw po.id.getId then
      let poId := mkIdent po.id.getId
      templateTerm ← `(let $poId:ident := $(mkIdent (tId ++ po.id.getId)); $templateTerm)
  let appUpdate : Term ← if spec.hasEffects then `($updateId)
    else `(fun s m => ($updateId s m, Qed.Cmd.none))
  let onSessionArg : Term ← match spec.sessionField? with
    | some _ => `(some $(mkIdent (tId ++ `Msg ++ `_onSession)))
    | none   => `(none)
  let baseApp0 : Term ← match spec.route? with
    | some _ => `(Qed.Internal.mkRoutedApp $initId $appUpdate $templateTerm
        (onRoute := $(mkIdent (tId ++ `Msg ++ `_onRoute))) (onSession := $onSessionArg)
        (start := $startArg) (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
    | none   => `(Qed.Internal.mkApp $initId $appUpdate $templateTerm (onSession := $onSessionArg)
        (start := $startArg) (locals := $regsId) (styles := qedInternalStyles% $viewId) (onPort := $onPortArg))
  let baseApp1 : Term ← if spec.themes.isEmpty then pure baseApp0 else do
    let env ← getEnv; let currNs ← getCurrNamespace; let openDecls := (← getScope).openDecls
    let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
    let mut thStyleTerms : Array Term := #[]
    for thId in spec.themes do
      let nm := thId.getId
      let thInfo? := (thReg.find? (currNs ++ nm)).orElse (fun _ => thReg.find? nm) |>.orElse fun _ =>
        openDecls.findSome? fun
          | .simple ns _ => thReg.find? (ns ++ nm)
          | .explicit id declName => if id == nm then thReg.find? declName else none
      let some thInfo := thInfo?
        | throwErrorAt thId s!"unknown `theme` `{nm}`"
      thStyleTerms := thStyleTerms.push (mkIdentFrom thId thInfo.styleConst)
    `(Qed.Internal.App.withExtraStyles [$[$thStyleTerms],*] $baseApp0)
  let baseApp : Term ← if spec.stylesheets.isEmpty then pure baseApp1 else do
    let shLits := spec.stylesheets.map Syntax.mkStrLit
    `(Qed.Internal.App.withStylesheets [$[$shLits:str],*] $baseApp1)
  let dehydApp : Term ← if spec.ephemeralFields.isEmpty then `(qedInternalAutoDehydrate% $initId $baseApp)
    else `(Qed.Internal.App.withDehydrate (Dehydrate.except $initId [$[$spec.ephemeralFields:ident],*]) $baseApp)
  let queriedApp : Term ← if spec.queries.isEmpty then pure dehydApp else
    `(Qed.Internal.App.withQueries $(mkIdent (tId ++ `queries)) $dehydApp)
  let subbedApp : Term ← if spec.subscriptions.isEmpty then pure queriedApp else
    `(Qed.Internal.App.withSubscriptions $(mkIdent (tId ++ `subscriptions)) $queriedApp)
  let compInv? : Option Term ← if stateInvPreds.isEmpty then pure none
    else if stateInvPreds.size == 1 then pure (some (← `(($(stateInvPreds[0]!) : $stateId → Prop))))
    else do
      let sVar := mkIdent `_qed_s
      let checks ← stateInvPreds.mapM fun p => `(($p) $sVar)
      pure (some (← `(fun ($sVar:ident : $stateId) => $(← mkConjBody checks))))
  let hasDecInv ← match compInv? with
    | some inv => canSynthDecidablePred stateId inv
    | none     => pure false
  let finalApp : Term ← match compInv?, hasDecInv with
    | some inv, true => `(Qed.App.guardRehydrate ($inv) $subbedApp)
    | _, _           => pure subbedApp
  let appIdent := mkIdent (tId ++ `app)
  let viewIdent := mkIdent (tId ++ `view)
  if spec.hasSpeculative then
    return ← mkSpecAppCmds spec tId stateId msgId appIdent viewIdent finalApp compInv? hasDecInv stateInvEntries cmds
  cmds := cmds.push (← `(command| $[$doc?:docComment]? def $appIdent : App $stateId $msgId :=
    $finalApp))
  match compInv?, hasDecInv with
  | some inv, true =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `rehydrate_inv)) (raw : String) (m' : $stateId) :
            ($appIdent).rehydrate raw = some m' → ($inv) m' :=
          Qed.App.guardRehydrate_sound _ _ _ raw m'))
  | some inv, false =>
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (tId ++ `dehydrate_inv)) :
            ∀ m m', ($inv) m → ($appIdent).rehydrate (($appIdent).dehydrate m) = some m' → ($inv) m' := by
          dsimp only [$appIdent:ident]; qedProveDehydrateInv))
  | none, _ => pure ()
  let appViewEqCmd ← `(command|
    theorem $(mkIdent (tId ++ `app_view_eq)) (s : $stateId) :
        Qed.Html.canonical (Qed.App.view $appIdent s) = Qed.Html.canonical ($viewIdent s) := by
      qedProveViewEquiv $appIdent $viewIdent)
  return (cmds, appViewEqCmd)

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command) × Bool × Bool) := do
  let tId        := spec.t.getId
  let fs         := spec.states.map (·.id)
  let stateId    := mkIdent (tId ++ `State)
  let initId     := mkIdent (tId ++ `init)
  let startCmdId := mkIdent (tId ++ `startCmd)
  let msgId      := mkIdent (tId ++ `Msg)
  let viewId     := mkIdent (tId ++ `view)
  let regId      := mkIdent (tId ++ `reg)
  let regsId     := mkIdent (tId ++ `regs)
  let mut cmds : Array (TSyntax `command) := #[]
  if spec.mountable then
    let dsT := spec.states.filterMap (·.def?)
    cmds := cmds.push (← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }))
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart)
  let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  if hasStart then
    let pBinders ← mkPropsBinders spec
    let subStarts ← hoistedStarts.mapM fun h => do
      let cStart := mkIdent (h.info.fullName ++ `startCmd)
      let call ← if h.info.hasProps then `($cStart $(← mkHoistedPropsTerm h)) else `($cStart)
      `(Cmd.map $(mkIdent (tId ++ `Msg ++ h.ctorName)) $call)
    let mut startBody ← mkCmdBatch (starts' ++ subStarts)
    if spec.mountable then
      startBody ← bindMentionedFields spec (mentionsIdent startBody.raw) startBody
      if mentionsIdent startBody.raw `s then
        startBody ← `(let s := $initId; $startBody)
    cmds := cmds.push (← `(command| def $startCmdId $[$pBinders:bracketedBinder]* : Cmd $msgId := $startBody))
  let outCtorSpecs : Array (Name × Array (Ident × Term)) :=
    spec.events.map (fun ev => (ev.id.getId, ev.params)) ++
    spec.binds.map (fun bd => (Name.mkSimple s!"set_{bd.id.getId}", #[(mkIdent `v, bd.ty)]))
  let propsOk ← spec.props.allM (canSynthJson ``FromJsonField ·.ty)
  let stateOk ← spec.states.allM (canSynthJson ``FromJsonField ·.ty)
  let outJsonOk ←
    if spec.outTy?.isSome then outCtorSpecs.allM fun (_, ps) => ps.allM (canSynthJson ``FromJsonField ·.2)
    else pure true
  let canEmitCodecs := propsOk && stateOk
  if canEmitCodecs then
    cmds := cmds ++ (← mkStructJsonCmds (tId ++ `Props) spec.props) ++ (← mkStructJsonCmds (tId ++ `State) spec.states)
  if spec.outTy?.isSome && outJsonOk then
    cmds := cmds ++ (← mkOutJsonCmds tId outCtorSpecs)
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && canEmitCodecs && outJsonOk
  if hasLocalDef then
    cmds := cmds ++ (← mkCompLocalDefCmds spec idLit)
  let own : Term ← if hasLocalDef then `([$regId]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
    LocalDef.dedupe ($own ++ qedInternalLocalRegistrations% $viewId)))
  return (cmds, hasStart, hasLocalDef)


private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then
    withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k
  else k

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let errsInit := (← get).messages.toList.filter (·.severity == .error) |>.length
  let compNs := (← getCurrNamespace) ++ (stx.getArg 2).getId
  pendingRpcChecks.set #[]
  pendingPredictChecks.set #[]
  currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    -- Elaborate component-colocated `style` clauses into `<Comp>.<styleName>` before opening `compNs`
    for stCl in rawSpec.styles do
      withOpenNs compNs do
        let sNameId : Ident := ⟨(stCl.getArg 1)⟩
        let qualifiedId := mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId)
        let extendsIds : Array Ident :=
          if (stCl.getArg 2).getNumArgs == 1 then (((stCl.getArg 2).getArg 0).getArg 1).getSepArgs.map (⟨·⟩) else #[]
        let strictTokens := (stCl.getArg 3).getNumArgs == 1
        let bodyStxs := (stCl.getArg 5).getArgs
        Qed.StyleDsl.elabStyleDef none qualifiedId extendsIds strictTokens bodyStxs
    withOpenNs compNs do
      if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
          rawSpec.starts.isEmpty && rawSpec.sessionField?.isNone &&
          rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty &&
          rawSpec.subscriptions.isEmpty then
        let sitesRef ← IO.mkRef #[]
        let hoistedRef ← IO.mkRef #[]
        let formDraftsRef ← IO.mkRef #[]
        let resetFormsRef ← IO.mkRef #[]
        let usedRpcsRef ← IO.mkRef #[]
        let contCtrRef ← IO.mkRef 0
        let specDispatchesRef ← IO.mkRef #[]
        let specResolvesRef ← IO.mkRef #[]
        let rCtx : RewriteCtx := {
          stateFields := #[], bindFields := rawSpec.bindNames, propNames := rawSpec.propNames,
          isPureComp := true,
          msgPath := rawSpec.t.getId ++ `Msg, hasOut := false, collections := #[],
          sites := sitesRef, hoisted := hoistedRef,
          formDrafts := formDraftsRef, resetForms := resetFormsRef,
          allowHoist := true, usedRpcs := usedRpcsRef, contCounter := contCtrRef,
          specDispatches := specDispatchesRef, specResolves := specResolvesRef }
        let body' ← lowerCompExpr .val (← rewriteIn rCtx false rawSpec.body)
        if (← hoistedRef.get).isEmpty && (← formDraftsRef.get).isEmpty && (← resetFormsRef.get).isEmpty then
          elabPureComponent rawSpec body'
          okRef.set true
          return
      let idLit := Syntax.mkStrLit compNs.toString
      let (sites, route'?, queries', starts', body', hoisted, formDrafts, resetForms, ownUsedRpcs, specDispatches, specResolves) ←
        collectSitesAndRewriteStateful rawSpec
      if !specResolves.isEmpty then
        let blockers := topLevelMountBlockers rawSpec.props rawSpec.binds rawSpec.slots
          rawSpec.hasChildren rawSpec.events rawSpec.states
        if !blockers.isEmpty then
          if let some rs0 := specResolves[0]? then
            throwErrorAt rs0.callRef s!"speculative `predict` is only supported on top-level mountable components, but `{rawSpec.t.getId}` declares {String.intercalate ", " blockers.toList}"
      let mut allUsedRpcs := ownUsedRpcs
      let mut allUsedChannels : Array (String × String) := #[]
      for sub in rawSpec.subscriptions do
        match sub.chInfo.kind with
        | .fullstack _ srvShort _ =>
            let pair := (srvShort, sub.chInfo.channelName)
            unless allUsedChannels.contains pair do
              allUsedChannels := allUsedChannels.push pair
        | .external .. => pure ()
      for h in hoisted do
        for ep in h.info.usedRpcs do
          unless allUsedRpcs.contains ep do
            allUsedRpcs := allUsedRpcs.push ep
        for ch in h.info.usedChannels do
          unless allUsedChannels.contains ch do
            allUsedChannels := allUsedChannels.push ch
      let eventNames := rawSpec.events.map (·.id.getId)
      let ownHasEffects :=
        !starts'.isEmpty ||
        !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty || !queries'.isEmpty ||
        !rawSpec.subscriptions.isEmpty ||
        !specResolves.isEmpty ||
        sites.any (fun s => s.stmts?.any (·.any (hasEffectStmt eventNames))) ||
        (route'?.any fun rd => rd.alts.any (hasEffectStmt eventNames)) ||
        hoisted.any (·.info.hasEffects)
      let spec ← elabStructsAndResolveTypes {
        rawSpec with route? := route'?, queries := queries', hasEffects := ownHasEffects,
                     usedRpcs := allUsedRpcs, usedChannels := allUsedChannels,
                     specDispatches, specResolves
      } hoisted formDrafts resetForms
      currentCompSessionRef.set spec.sessionField?
      let errsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
      let coreCmds ← mkViewCmds spec body' (← mkMsgAndUpdateCmds spec sites)
      for c in coreCmds do elabCommand c
      let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec starts' idLit
      for c in mountCmds do elabCommand c
      if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
        if let some qCmd ← mkCompQueriesCmd? spec then elabCommand qCmd
        if let some sCmd ← mkCompSubscriptionsCmd? spec then elabCommand sCmd
        for clsCmd in (← mkSpecClassifyCmds spec) do elabCommand clsCmd
      let stateInvEntries ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
      let errsAfterInvs := (← get).messages.toList.filter (·.severity == .error) |>.length
      let activeInvEntries := if errsAfterInvs == errsBefore then stateInvEntries else #[]
      verifyPendingRpcChecks spec (activeInvEntries.map (·.1))
      if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
        let (appCmds, eqCmd) ← mkCompAppCmds spec body' hasStart activeInvEntries
        for c in appCmds do elabCommand c
        let errsAfterApp := (← get).messages.toList.filter (·.severity == .error) |>.length
        if errsAfterApp == errsBefore then elabCommand eqCmd
      let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
      let usedRpcsId := mkIdent (spec.t.getId ++ `usedRpcs)
      let epTerms ← allUsedRpcs.mapM fun (sStr, mStr) =>
        `((($(Syntax.mkStrLit sStr), $(Syntax.mkStrLit mStr)) : String × String))
      elabCommand (← `(command| def $usedRpcsId : List (String × String) := [$[$epTerms],*]))
      let usedChsId := mkIdent (spec.t.getId ++ `usedChannels)
      let chTerms ← allUsedChannels.mapM fun (sStr, cStr) =>
        `((($(Syntax.mkStrLit sStr), $(Syntax.mkStrLit cStr)) : String × String))
      elabCommand (← `(command| def $usedChsId : List (String × String) := [$[$chTerms],*]))
      let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
      modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
        hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects,
        hasStart, mountable := spec.mountable, hasLocalDef,
        usedRpcs := allUsedRpcs, usedChannels := allUsedChannels }
      okRef.set true
  finally
    pendingRpcChecks.set #[]
    pendingPredictChecks.set #[]
    currentCompSessionRef.set none
    let errsEnd := (← get).messages.toList.filter (·.severity == .error) |>.length
    if !(← okRef.get) || errsEnd > errsInit then
      setEnv savedEnv

end CompElab
end Qed
