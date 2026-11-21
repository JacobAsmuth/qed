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

private def elabPureCompInvariants (spec : ComponentSpec) (viewId : Ident) (msgV : Ident)
    (needsProps : Bool) (viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :
    CommandElabM Unit := do
  let tId := spec.t.getId
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause ||
       invStx.getKind == ``compExampleClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` and `example` apply to stateful components"
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
  elabPureCompInvariants spec viewId msgV needsProps viewBinders
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

private def mkEnsuredExistentialWrap (ensConst : Name) (qaIds : Array Ident)
    (elemVar : Ident) : CommandElabM (Term × Term) := do
  let ensApp ← qaIds.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
  let exPrf ← qaIds.foldrM (init := ← `(($elemVar:ident).ok)) fun qa acc => `(Exists.intro $qa $acc)
  return (ensApp, exPrf)

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
          let qeId := mkIdent `_qe
          let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds qeId
          `(fun (_qr : Qed.Resource (Qed.Ensured $(q.ty) ($ensApp))) => _qgot _qk (_qr.map fun $qeId => ⟨($qeId:ident).val, $exPrf⟩))
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
          let weId := mkIdent `_we
          let (ensApp, exPrf) ← mkEnsuredExistentialWrap ensConst qaIds weId
          `(fun ($weId : Qed.Ensured $evTyId ($ensApp)) => $msgCtor _wk ⟨($weId:ident).val, $exPrf⟩)
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


private def mkSpecStepPf (sVar mVar : Ident) : List Ident → Term → CommandElabM Term
  | [], _ => `(trivial)
  | [id0], hTerm => `(($id0:ident).2 $sVar $mVar $hTerm)
  | lastId :: prevRev, hTerm => do
      let leftPf ← mkSpecStepPf sVar mVar prevRev (← `(($hTerm).1))
      `(And.intro $leftPf (($lastId:ident).2 $sVar $mVar ($hTerm).2))

private def mkSpecInvThmCmds (tId : Name) (stateId msgId appIdent baseAppIdent clsIdent : Ident)
    (inv : Term) (stateInvEntries : Array (Term × Option Ident)) :
    CommandElabM (Array (TSyntax `command)) := do
  let invIds? : Option (Array Ident) :=
    stateInvEntries.foldl (init := some #[]) fun acc (_, id?) =>
      match acc, id? with
      | some arr, some id => some (arr.push id)
      | _, _ => none
  let some invIds := invIds? | return #[]
  if invIds.isEmpty then return #[]
  let initPf : Term ← match invIds.toList with
    | [id0] => `(($id0:ident).1)
    | id0 :: rest =>
        rest.foldlM (init := ← `(($id0:ident).1)) fun acc id => `(And.intro $acc ($id:ident).1)
    | [] => `(trivial)
  let sVar := mkIdent `_s
  let mVar := mkIdent `_m
  let hVar := mkIdent `_h
  let stepPf ← mkSpecStepPf sVar mVar invIds.toList.reverse hVar
  pure #[
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_init_inv)) :
          Qed.SpecEngine.SpecInv ($inv) ($appIdent).init.1 :=
        Qed.Internal.App.withSpeculative_init_inv $clsIdent $baseAppIdent $initPf),
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_preserves_inv))
          (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
          (h : Qed.SpecEngine.SpecInv ($inv) st) :
          Qed.SpecEngine.SpecInv ($inv) (($appIdent).update st msg).1 :=
        Qed.Internal.App.withSpeculative_step_inv $clsIdent $baseAppIdent
          (fun $sVar $mVar $hVar => $stepPf) st msg h) ]

private def mkSpecCoreCmds (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (tId : Name) (stateId msgId appIdent baseAppIdent clsIdent : Ident) (finalApp : Term) :
    CommandElabM (Array (TSyntax `command)) := do
  pure #[
    ← `(command| def $baseAppIdent : App $stateId $msgId := $finalApp),
    ← `(command| $[$doc?:docComment]? def $appIdent :
      App (Qed.SpecState $stateId $msgId) $msgId :=
      Qed.Internal.App.withSpeculative $clsIdent $baseAppIdent),
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_init_coherent)) :
          Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) ($appIdent).init.1 :=
        Qed.Internal.App.withSpeculative_init_coherent $clsIdent $baseAppIdent),
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_preserves_coherent))
          (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
          (hcoh : Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) st) :
          Qed.SpecEngine.Coherent (fun s m => (($baseAppIdent).update s m).1) (($appIdent).update st msg).1 :=
        Qed.Internal.App.withSpeculative_step_coherent $clsIdent $baseAppIdent st msg hcoh),
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_init_wellFormedIds)) :
          Qed.SpecEngine.WellFormedIds ($appIdent).init.1 :=
        Qed.Internal.App.withSpeculative_init_wellFormedIds $clsIdent $baseAppIdent),
    ← `(command|
      theorem $(mkIdent (tId ++ `specApp_preserves_wellFormedIds))
          (st : Qed.SpecState $stateId $msgId) (msg : $msgId)
          (hwf : Qed.SpecEngine.WellFormedIds st) :
          Qed.SpecEngine.WellFormedIds (($appIdent).update st msg).1 :=
        Qed.Internal.App.withSpeculative_step_wellFormedIds $clsIdent $baseAppIdent st msg hwf) ]

private def mkSpecRehydrateCmds (tId : Name) (stateId msgId appIdent baseAppIdent : Ident)
    (compInv? : Option Term) (hasDecInv : Bool) : CommandElabM (Array (TSyntax `command)) := do
  match compInv?, hasDecInv with
  | some inv, true =>
      pure #[← `(command|
        theorem $(mkIdent (tId ++ `rehydrate_inv)) (raw : String) (st' : Qed.SpecState $stateId $msgId) :
            ($appIdent).rehydrate raw = some st' → Qed.SpecEngine.SpecInv ($inv) st' :=
          Qed.Internal.App.withSpeculative_rehydrate_sound _ _
            (Qed.App.guardRehydrate_sound _ _ _) raw st')]
  | some inv, false =>
      pure #[← `(command|
        theorem $(mkIdent (tId ++ `dehydrate_inv)) :
            ∀ st st', Qed.SpecEngine.SpecInv ($inv) st →
              ($appIdent).rehydrate (($appIdent).dehydrate st) = some st' →
              Qed.SpecEngine.SpecInv ($inv) st' :=
          Qed.Internal.App.withSpeculative_dehydrate_inv _ _ (by
            dsimp only [$baseAppIdent:ident]; qedProveDehydrateInv))]
  | none, _ => pure #[]

private def mkSpecAppCmds (spec : ComponentSpec) (tId : Name) (stateId msgId appIdent viewIdent : Ident)
    (finalApp : Term) (compInv? : Option Term) (hasDecInv : Bool)
    (stateInvEntries : Array (Term × Option Ident)) (initCmds : Array (TSyntax `command)) :
    CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let baseAppIdent := mkIdent (tId ++ `_baseApp)
  let clsIdent := mkIdent (tId ++ `_specClassify)
  let mut cmds := initCmds ++ (← mkSpecCoreCmds spec.doc? tId stateId msgId appIdent baseAppIdent clsIdent finalApp)
  if spec.queries.isEmpty && spec.subscriptions.isEmpty then
    if let some inv := compInv? then
      cmds := cmds ++ (← mkSpecInvThmCmds tId stateId msgId appIdent baseAppIdent clsIdent inv stateInvEntries)
  cmds := cmds ++ (← mkSpecRehydrateCmds tId stateId msgId appIdent baseAppIdent compInv? hasDecInv)
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

private def resolveThemeStyles (themes : Array Ident) : CommandElabM (Array Term) := do
  let env ← getEnv; let currNs ← getCurrNamespace; let openDecls := (← getScope).openDecls
  let thReg := Qed.StyleDsl.themeMetaRegistry.getState env
  let mut thStyleTerms : Array Term := #[]
  for thId in themes do
    let nm := thId.getId
    let thInfo? := (thReg.find? (currNs ++ nm)).orElse (fun _ => thReg.find? nm) |>.orElse fun _ =>
      openDecls.findSome? fun
        | .simple ns _ => thReg.find? (ns ++ nm)
        | .explicit id declName => if id == nm then thReg.find? declName else none
    let some thInfo := thInfo?
      | throwErrorAt thId s!"unknown `theme` `{nm}`"
    thStyleTerms := thStyleTerms.push (mkIdentFrom thId thInfo.styleConst)
  return thStyleTerms

private def applyHeadDirectives (hmId stId : Ident) (dirs : Array Syntax) (tail : Term) :
    CommandElabM Term := do
  dirs.foldrM (init := tail) fun d acc => do
    match d.getKind with
    | `Qed.compHeadTitle =>
        let v ← lowerCompExpr .val (d.getArg 1)
        `(let $hmId:ident := { $hmId with title := Option.some ($v : String) }; $acc)
    | `Qed.compHeadDescription =>
        let v ← lowerCompExpr .val (d.getArg 1)
        `(let $hmId:ident := { $hmId with description := Option.some ($v : String) }; $acc)
    | `Qed.compHeadCanonical =>
        let v ← lowerCompExpr .val (d.getArg 1)
        `(let $hmId:ident := { $hmId with canonical := Option.some ($v : String) }; $acc)
    | `Qed.compHeadMeta =>
        let k ← lowerCompExpr .val (d.getArg 1)
        let v ← lowerCompExpr .val (d.getArg 3)
        `(let $hmId:ident := { $hmId with metaTags := ($hmId).metaTags ++ [(($k : String), ($v : String))] }; $acc)
    | `Qed.compHeadStatus =>
        let n ← lowerCompExpr .val (d.getArg 1)
        `(let $stId:ident : Nat := $n; $acc)
    | `Qed.compHeadRedirect =>
        let u ← lowerCompExpr .val (d.getArg 1)
        let optSt := d.getArg 2
        let stT ← if optSt.getNumArgs == 4 then lowerCompExpr .val (optSt.getArg 3) else `((302 : Nat))
        `(let $hmId:ident := { $hmId with redirect := Option.some ($u : String) };
          let $stId:ident : Nat := $stT; $acc)
    | _ =>
        throwErrorAt d "unexpected directive in `head:`"

private def mkCompHeadCmd? (spec : ComponentSpec) : CommandElabM (Option (TSyntax `command)) := do
  let some headStx := spec.headClause? | return none
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let headInfoId := mkIdent (tId ++ `headInfo)
  let hmId := mkIdent `_qed_hm
  let stId := mkIdent `_qed_st
  let items := (headStx.getArg 2).getArgs
  let mut sharedDirs : Array Syntax := #[]
  let mut caseItems : Array Syntax := #[]
  for item in items do
    if item.getKind == `Qed.compHeadCase then
      caseItems := caseItems.push item
    else
      if !caseItems.isEmpty then
        throwErrorAt item "shared `head:` directives must appear before `case` arms"
      sharedDirs := sharedDirs.push item
  let coreTail : Term ←
    if caseItems.isEmpty then
      `(($hmId, $stId))
    else
      let some rd := spec.route?
        | throwErrorAt caseItems[0]! s!"`case` inside `head:` requires a `route` declaration on `component {tId}`"
      let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for c in caseItems do
        let rawPats := (c.getArg 1).getSepArgs
        let armDirs := (c.getArg 3).getArgs
        let armBody ← applyHeadDirectives hmId stId armDirs (← `(($hmId, $stId)))
        for p in rawPats do
          let patT ← liftMacroM (lowerQedPat p)
          alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $patT => $armBody))
      `(match $(rd.field):ident with $[$alts:matchAlt]*)
  let withDirs ← applyHeadDirectives hmId stId sharedDirs coreTail
  let fullBody ← `(let $hmId:ident : Qed.HeadMeta := {}; let $stId:ident : Nat := 200; $withDirs)
  let boundBody ← bindMentionedFields spec (mentionsIdent fullBody.raw) fullBody
  return some (← `(command|
    set_option linter.unusedVariables false in
    def $headInfoId (s : $stateId) : Qed.HeadMeta × Nat := $boundBody))

private def buildCompFinalApp (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvPreds : Array Term) :
    CommandElabM (Array (TSyntax `command) × Term × Option Term × Bool) := do
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
    let thStyleTerms ← resolveThemeStyles spec.themes
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
  let headedApp : Term ← if spec.headClause?.isNone then pure subbedApp else do
    let headInfoId := mkIdent (tId ++ `headInfo)
    `(Qed.App.withSsrStatus (fun _s => ($headInfoId _s).2)
        (Qed.App.withHead (fun _s => ($headInfoId _s).1) $subbedApp))
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
    | some inv, true => `(Qed.App.guardRehydrate ($inv) $headedApp)
    | _, _           => pure headedApp
  return (cmds, finalApp, compInv?, hasDecInv)

private def mkCompAppCmds (spec : ComponentSpec) (body' : Term) (hasStart : Bool)
    (stateInvEntries : Array (Term × Option Ident)) : CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let tId       := spec.t.getId
  let stateId   := mkIdent (tId ++ `State)
  let msgId     := mkIdent (tId ++ `Msg)
  let appIdent  := mkIdent (tId ++ `app)
  let viewIdent := mkIdent (tId ++ `view)
  let (initCmds, finalApp, compInv?, hasDecInv) ←
    buildCompFinalApp spec body' hasStart (stateInvEntries.map (·.1))
  if spec.hasSpeculative then
    return ← mkSpecAppCmds spec tId stateId msgId appIdent viewIdent finalApp compInv? hasDecInv stateInvEntries initCmds
  let doc? := spec.doc?
  let mut cmds := initCmds.push (← `(command| $[$doc?:docComment]? def $appIdent : App $stateId $msgId :=
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

private def elabCompStyles (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
  for stCl in rawSpec.styles do
    withOpenNs compNs do
      let sNameId : Ident := ⟨(stCl.getArg 1)⟩
      let qualifiedId := mkIdentFrom sNameId (rawSpec.t.getId ++ sNameId.getId)
      let extendsIds : Array Ident :=
        if (stCl.getArg 2).getNumArgs == 1 then (((stCl.getArg 2).getArg 0).getArg 1).getSepArgs.map (⟨·⟩) else #[]
      let strictTokens := (stCl.getArg 3).getNumArgs == 1
      let bodyStxs := (stCl.getArg 5).getArgs
      Qed.StyleDsl.elabStyleDef none qualifiedId extendsIds strictTokens bodyStxs

private def collectCompEndpoints (rawSpec : ComponentSpec) (hoisted : Array HoistedSub)
    (ownUsedRpcs : Array (String × String)) : Array (String × String) × Array (String × String) := Id.run do
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
  return (allUsedRpcs, allUsedChannels)

private def elabCompRegistryAndMeta (spec : ComponentSpec) (hasStart hasLocalDef : Bool)
    (allUsedRpcs allUsedChannels : Array (String × String)) : CommandElabM Unit := do
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

private def elabStatefulComponentBody (compNs : Name) (rawSpec : ComponentSpec) : CommandElabM Unit := do
  if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
      rawSpec.starts.isEmpty && rawSpec.sessionField?.isNone &&
      rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty &&
      rawSpec.subscriptions.isEmpty && rawSpec.headClause?.isNone then
    let rCtx ← mkRewriteCtx rawSpec true (allowHoist := true)
    let body' ← lowerCompExpr .val (← rewriteIn rCtx false rawSpec.body)
    if (← rCtx.hoisted.get).isEmpty && (← rCtx.formDrafts.get).isEmpty && (← rCtx.resetForms.get).isEmpty then
      elabPureComponent rawSpec body'
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
  let (allUsedRpcs, allUsedChannels) := collectCompEndpoints rawSpec hoisted ownUsedRpcs
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
  let isTopMount := spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids
  if isTopMount then
    if let some qCmd ← mkCompQueriesCmd? spec then elabCommand qCmd
    if let some sCmd ← mkCompSubscriptionsCmd? spec then elabCommand sCmd
    if let some hCmd ← mkCompHeadCmd? spec then elabCommand hCmd
    for clsCmd in (← mkSpecClassifyCmds spec) do elabCommand clsCmd
  let stateInvEntries ← withOpenNs compNs (elabInlineInvariantsPhase spec false)
  let errsAfterInvs := (← get).messages.toList.filter (·.severity == .error) |>.length
  let activeInvEntries := if errsAfterInvs == errsBefore then stateInvEntries else #[]
  if errsAfterInvs == errsBefore then
    withOpenNs compNs (elabCompReachableAndWitnesses spec activeInvEntries)
  verifyPendingRpcChecks spec (activeInvEntries.map (·.1))
  if isTopMount then
    let (appCmds, eqCmd) ← mkCompAppCmds spec body' hasStart activeInvEntries
    for c in appCmds do elabCommand c
    let errsAfterApp := (← get).messages.toList.filter (·.severity == .error) |>.length
    if errsAfterApp == errsBefore then elabCommand eqCmd
  let _ ← withOpenNs compNs (elabInlineInvariantsPhase spec true)
  elabCompRegistryAndMeta spec hasStart hasLocalDef allUsedRpcs allUsedChannels

private def compSnapshotTreeHasErrors : Nat → Language.SnapshotTree → Bool
  | 0, tree => tree.element.diagnostics.msgLog.hasErrors
  | fuel + 1, tree =>
      tree.element.diagnostics.msgLog.hasErrors ||
      tree.children.any fun t => compSnapshotTreeHasErrors fuel t.get

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let errsInit := (← get).messages.toList.filter (·.severity == .error) |>.length
  let priorTasks := (← get).snapshotTasks.size
  let compNs := (← getCurrNamespace) ++ (stx.getArg 2).getId
  pendingRpcChecks.set #[]
  pendingPredictChecks.set #[]
  currentCompSessionRef.set none
  let okRef ← IO.mkRef false
  try
    let rawSpec ← withOpenNs compNs (parseComponentSpec stx)
    elabCompStyles compNs rawSpec
    withOpenNs compNs (elabStatefulComponentBody compNs rawSpec)
    okRef.set true
  finally
    pendingRpcChecks.set #[]
    pendingPredictChecks.set #[]
    currentCompSessionRef.set none
    let errsEnd := (← get).messages.toList.filter (·.severity == .error) |>.length
    let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
    let asyncErr := newTasks.any fun t => compSnapshotTreeHasErrors 64 t.get
    if !(← okRef.get) || errsEnd > errsInit || asyncErr then
      setEnv savedEnv

end CompElab
end Qed
