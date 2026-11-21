import Qed.Runtime.AppCore
import Qed.Runtime.Local
import Qed.Runtime.Verify
import Qed.Lang

namespace Qed

namespace Internal

def mkApp (init : Model) (update : Model → Msg → Model × Cmd Msg)
    (template : View Model Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) :
    App Model Msg :=
  mkAppCore init update template start locals styles onPort onSession valid_view

def mkRoutedApp {R : Type} [Router R] [Inhabited R]
    (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) :
    App Model Msg :=
  mkRoutedAppCore init update template onRoute start locals styles onPort onSession valid_view

defAppProjSimps mkApp (init : Model) (u : Model → Msg → Model × Cmd Msg)
    (t : View Model Msg) (s l st p os hv) => mkApp init u t s l st p os hv with
  [init := (init, s), update := u, template := t, dehydrate := fun _ => "", rehydrate := fun _ => none]

defAppProjSimps mkRoutedApp {R : Type} [Router R] [Inhabited R]
    (init : Model) (u : Model → Msg → Model × Cmd Msg) (t : View Model Msg) (r : R → Msg) (s l st p os hv) =>
    mkRoutedApp init u t r s l st p os hv with
  [init := (init, s), update := u, template := t, dehydrate := fun _ => "", rehydrate := fun _ => none]

@[reducible] def App.withDehydrate {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m := by
      qedProveDehydrateView) : App Model Msg :=
  App.withDehydrateCore d app hview

defAppProjSimps App.withDehydrate (d : Dehydrate Model) (app : App Model Msg) (hv) =>
    App.withDehydrate d app hv with
  [init := app.init, update := app.update, template := app.template,
   dehydrate := d.dehydrate, rehydrate := d.rehydrate]

@[simp] theorem App.withDehydrate_rehydrate_dehydrate (d : Dehydrate Model) (app : App Model Msg) (hv) (m : Model) :
    (App.withDehydrate d app hv).rehydrate ((App.withDehydrate d app hv).dehydrate m) = some (d.project m) :=
  d.round_trip m

@[reducible] def App.withFullDehydrate {Model Msg : Type} [LawfulJson Model] (app : App Model Msg) : App Model Msg :=
  App.withDehydrate Dehydrate.full app (fun _ => rfl)

end Internal

set_option linter.unusedVariables false in
def App.guardRehydrate {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv]
    (app : App Model Msg)
    (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m' := by
      qedProveDehydrateInv) : App Model Msg :=
  App.guardRehydrateCore Inv app hpres

defAppProjSimps App.guardRehydrate {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv]
    (app : App Model Msg) (hp) => App.guardRehydrate Inv app hp with
  [init := app.init, update := app.update, template := app.template, dehydrate := app.dehydrate]

theorem App.guardRehydrate_sound {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv]
    (app : App Model Msg) (hp) (raw : String) (m' : Model)
    (h : (App.guardRehydrate Inv app hp).rehydrate raw = some m') : Inv m' := by
  dsimp only [App.guardRehydrate, App.guardRehydrateCore] at h
  cases hr : app.rehydrate raw with
  | none => simp [hr] at h
  | some m =>
      simp only [hr] at h
      split at h <;> simp at h
      subst h
      exact of_decide_eq_true ‹_›

theorem App.guardRehydrate_complete {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv]
    (app : App Model Msg) (hp) (m : Model) (hm : Inv m) :
    (App.guardRehydrate Inv app hp).rehydrate ((App.guardRehydrate Inv app hp).dehydrate m) =
      app.rehydrate (app.dehydrate m) := by
  dsimp only [App.guardRehydrate, App.guardRehydrateCore]
  cases hr : app.rehydrate (app.dehydrate m) with
  | none => rfl
  | some m' => simp [decide_eq_true (hp m m' hm hr)]

section AutoDehydrate
open Lean Meta Elab Term

private def mkNestedTuple : List Term → MacroM Term
  | []      => `(())
  | [x]     => pure x
  | x :: xs => do `(($x, $(← mkNestedTuple xs)))

private def mkSndChain : Nat → Term → MacroM Term
  | 0,     t => pure t
  | n + 1, t => do mkSndChain n (← `(Prod.snd $t))

private def mkTupleProjTerm (base : Term) (idx total : Nat) : MacroM Term := do
  if total ≤ 1 then return base
  let s ← mkSndChain idx base
  if idx + 1 < total then `(Prod.fst $s) else return s

private def prodTypeOf (pad : Bool) : List Expr → Expr
  | []      => Lean.mkConst ``Unit
  | [t]     => if pad then mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) t (Lean.mkConst ``Unit) else t
  | t :: ts => mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) t (prodTypeOf false ts)

private def mkTupleVal (pad : Bool) : List (Expr × Expr) → Expr
  | []           => Lean.mkConst ``Unit.unit
  | [(ty, v)]    =>
      if pad then mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) ty (Lean.mkConst ``Unit) v (Lean.mkConst ``Unit.unit)
      else v
  | (ty, v) :: r =>
      mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) ty (prodTypeOf false (r.map Prod.fst)) v (mkTupleVal false r)

private def projTupleVals (pad : Bool) : List Expr → Expr → List Expr
  | [],        _ => []
  | [_],       p => [if pad then Expr.proj ``Prod 0 p else p]
  | _ :: rest, p => (Expr.proj ``Prod 0 p) :: projTupleVals false rest (Expr.proj ``Prod 1 p)

private def sumTypeOf : List Expr → Expr
  | []      => Lean.mkConst ``Unit
  | [t]     => t
  | t :: ts => mkApp2 (Lean.mkConst ``Sum [Level.zero, Level.zero]) t (sumTypeOf ts)

private def injSumVal : List Expr → Nat → Expr → Expr
  | [],      _,     v => v
  | [_],     _,     v => v
  | p :: ps, 0,     v => mkApp3 (Lean.mkConst ``Sum.inl [Level.zero, Level.zero]) p (sumTypeOf ps) v
  | p :: ps, j + 1, v => mkApp3 (Lean.mkConst ``Sum.inr [Level.zero, Level.zero]) p (sumTypeOf ps) (injSumVal ps j v)

private def buildSumFromB (ty : Expr) : List (Expr × Bool × List Expr × Expr) → MetaM Expr
  | [] => withLocalDeclD `u (Lean.mkConst ``Unit) fun u => mkLambdaFVars #[u] u
  | [(cApp, pad, fTys, pTy)] =>
      withLocalDeclD `p pTy fun p => mkLambdaFVars #[p] (mkAppN cApp (projTupleVals pad fTys p).toArray)
  | (cApp, pad, fTys, pTy) :: rest => do
      let rSumTy := sumTypeOf (rest.map (·.2.2.2))
      let sTy := mkApp2 (Lean.mkConst ``Sum [Level.zero, Level.zero]) pTy rSumTy
      let leftFn ← withLocalDeclD `p pTy fun p => mkLambdaFVars #[p] (mkAppN cApp (projTupleVals pad fTys p).toArray)
      let rightFn ← buildSumFromB ty rest
      let motive ← withLocalDeclD `s sTy fun s => mkLambdaFVars #[s] ty
      withLocalDeclD `s sTy fun s => do
        mkLambdaFVars #[s] (← mkAppOptM ``Sum.casesOn #[some pTy, some rSumTy, some motive, some s, some leftFn, some rightFn])

private def mapOptM {α β : Type} {m : Type → Type} [Monad m] (f : α → m (Option β)) : List α → m (Option (List β))
  | []      => return some []
  | x :: xs => do
      let some y ← f x | return none
      return (← mapOptM f xs).map (y :: ·)

private def substFVar (fv val e : Expr) : Expr := (e.abstract #[fv]).instantiate1 val

private def synthDirect? (ty : Expr) : MetaM (Option (Expr × Option Expr)) := do
  let .some inst ← trySynthInstance (Lean.mkApp (Lean.mkConst ``Qed.LawfulJson) ty) | return none
  let toJ ← mkAppOptM ``Qed.LawfulJson.toToJson #[ty, inst]
  let nn? ← match ← trySynthInstance (mkApp2 (Lean.mkConst ``Qed.NonNullJson) ty toJ) with
    | .some nn => pure (some nn)
    | _        => pure none
  return some (inst, nn?)

private def withLocalJson (ty instVal : Expr) (nnVal? : Option Expr)
    (k : MetaM (Option (Expr × Option Expr))) : MetaM (Option (Expr × Option Expr)) := do
  let ljTy := Lean.mkApp (Lean.mkConst ``Qed.LawfulJson) ty
  withLetDecl `_qed_lj ljTy instVal fun fvLJ => do
    let linsts1 := (← getLocalInstances).push { className := ``Qed.LawfulJson, fvar := fvLJ }
    let res1? ← withLCtx (← getLCtx) linsts1 do
      match nnVal? with
      | none => k
      | some nnVal =>
          let toJ ← mkAppOptM ``Qed.LawfulJson.toToJson #[ty, fvLJ]
          let nnTy := mkApp2 (Lean.mkConst ``Qed.NonNullJson) ty toJ
          withLetDecl `_qed_nn nnTy nnVal fun fvNN => do
            let linsts2 := (← getLocalInstances).push { className := ``Qed.NonNullJson, fvar := fvNN }
            let res2? ← withLCtx (← getLCtx) linsts2 k
            return res2?.map fun (i, n?) => (substFVar fvNN nnVal i, n?.map (substFVar fvNN nnVal))
    return res1?.map fun (i, n?) => (substFVar fvLJ instVal i, n?.map (substFVar fvLJ instVal))

private def withEnsuredTypes (synth : Expr → MetaM (Option (Expr × Option Expr))) :
    List Expr → MetaM (Option (Expr × Option Expr)) → MetaM (Option (Expr × Option Expr))
  | [],      k => k
  | t :: ts, k => do
      let t ← instantiateMVars t
      if t.hasMVar || t.hasFVar || (← whnf (← inferType t)) != .sort Level.one then
        withEnsuredTypes synth ts k
      else if (← synthDirect? t).isSome then
        withEnsuredTypes synth ts k
      else
        let some (tInst, tNN?) ← synth t | return none
        withLocalJson t tInst tNN? (withEnsuredTypes synth ts k)

def synthLawfulJsonAux : Nat → Expr → MetaM (Option (Expr × Option Expr))
  | 0, _ => return none
  | fuel + 1, rawTy => do
      let ty ← instantiateMVars rawTy
      if ty.hasMVar || ty.hasFVar || (← whnf (← inferType ty)) != .sort Level.one then return none
      if let some hit ← synthDirect? ty then return some hit
      let ty ← whnfR ty
      let (fn, args) := ty.getAppFnArgs
      withEnsuredTypes (synthLawfulJsonAux fuel) args.toList do
        if let some hit ← synthDirect? ty then return some hit
        let env ← getEnv
        let modRoot := match env.getModuleIdxFor? fn with
          | some idx => (env.header.moduleNames.getD idx.toNat Name.anonymous).getRoot
          | none     => Name.anonymous
        if modRoot == `Init || modRoot == `Std || modRoot == `Lean || modRoot == `Lake then return none
        let some (.inductInfo indVal) := env.find? fn | return none
        let casesName := mkCasesOnName fn
        if indVal.isRec || indVal.numIndices != 0 || args.size != indVal.numParams ||
           indVal.ctors.isEmpty || !env.contains casesName then return none
        let ctorLevels := ty.getAppFn.constLevels!
        let some ctorRaw ← mapOptM (fun cName => do
          let some (.ctorInfo cVal) := env.find? cName | return none
          let cApp := mkAppN (Lean.mkConst cName ctorLevels) args
          forallBoundedTelescope (← inferType cApp) (some cVal.numFields) fun fvars _ => do
            let some fTys ← mapOptM (fun fv => do
              let fTy ← instantiateMVars (← inferType fv)
              if fvars.any (fun o => o != fv && fTy.containsFVar o.fvarId!) then return none
              if (← whnf (← inferType fTy)) != .sort Level.one then return none
              return some fTy) fvars.toList | return none
            return some (cApp, fTys)) indVal.ctors | return none
        let allFieldTys := ctorRaw.foldr (fun (_, fs) acc => fs ++ acc) []
        withEnsuredTypes (synthLawfulJsonAux fuel) allFieldTys do
          let ctorEntries ← ctorRaw.mapM fun (cApp, fTys) => do
            let pad ← match ctorRaw.length == 1, fTys with
              | true, [fTy] => pure ((← synthDirect? fTy).bind Prod.snd).isNone
              | _,    _     => pure false
            return (cApp, pad, fTys, prodTypeOf pad fTys)
          let payloadTys := ctorEntries.map (·.2.2.2)
          let sumTy := sumTypeOf payloadTys
          let some (sumInst, some sumNN) ← synthDirect? sumTy | return none
          let mkDecls (fTys : List Expr) :=
            ((List.range fTys.length).zip fTys).map (fun (i, fTy) => (Name.mkSimple s!"_x_{i}", fTy)) |>.toArray
          let toMinors ← ((List.range ctorEntries.length).zip ctorEntries).mapM fun (j, (_, pad, fTys, _)) =>
            withLocalDeclsDND (mkDecls fTys) fun xs =>
              mkLambdaFVars xs (injSumVal payloadTys j (mkTupleVal pad (fTys.zip xs.toList)))
          let toMotive ← withLocalDeclD `x ty fun x => mkLambdaFVars #[x] sumTy
          let toB ← withLocalDeclD `x ty fun x => do
            mkLambdaFVars #[x] (← mkAppOptM casesName (args.map some ++ #[some toMotive, some x] ++ toMinors.toArray.map some))
          let fromB ← buildSumFromB ty ctorEntries
          let some invMinors ← mapOptM (fun (cApp, _, fTys, _) =>
            withLocalDeclsDND (mkDecls fTys) fun xs => do
              let cTerm := mkAppN cApp xs
              unless (← isDefEq (Lean.mkApp fromB (Lean.mkApp toB cTerm)) cTerm) do return none
              return some (← mkLambdaFVars xs (mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) ty cTerm))) ctorEntries | return none
          let eqMotive ← withLocalDeclD `x ty fun x =>
            mkLambdaFVars #[x] (mkApp3 (Lean.mkConst ``Eq [Level.one]) ty (Lean.mkApp fromB (Lean.mkApp toB x)) x)
          let leftInv ← withLocalDeclD `x ty fun x => do
            mkLambdaFVars #[x] (← mkAppOptM casesName (args.map some ++ #[some eqMotive, some x] ++ invMinors.toArray.map some))
          let isoInst := mkApp6 (Lean.mkConst ``Qed.LawfulJson.iso) ty sumTy sumInst toB fromB leftInv
          let isoNN := mkApp7 (Lean.mkConst ``Qed.NonNullJson.iso) ty sumTy sumInst sumNN toB fromB leftInv
          unless (← isTypeCorrect isoInst) do return none
          return some (isoInst, some isoNN)

def elabStructFieldsSlice (ref : Syntax) (initVal modelTy : Expr) (fArr : Array Ident) : TermElabM Expr := do
  if fArr.isEmpty then return mkApp2 (Lean.mkConst ``Dehydrate.const) modelTy initVal
  let mId := mkIdentFrom ref `_qed_m
  let pId := mkIdentFrom ref `_qed_p
  let getterBody ← liftMacroM <| mkNestedTuple (← fArr.mapM fun f => `($mId.$f:ident)).toList
  let projTerms ← liftMacroM <| (List.range fArr.size).toArray.mapM fun i => mkTupleProjTerm ⟨pId.raw⟩ i fArr.size
  let alphaMVar ← mkFreshExprMVar (mkSort Level.one)
  let getterVal ← elabTermEnsuringType (← `(fun $mId => $getterBody)) (← mkArrow modelTy alphaMVar)
  synthesizeSyntheticMVarsNoPostponing
  let alphaTy ← instantiateMVars alphaMVar
  let setterVal ← elabTermEnsuringType (← `(fun $mId $pId => { $mId with $[$fArr:ident := $projTerms],* }))
    (← mkArrow modelTy (← mkArrow alphaTy modelTy))
  synthesizeSyntheticMVarsNoPostponing
  let some (instAlpha, _) ← synthLawfulJsonAux 16 alphaTy
    | do
        let mut badFields : Array MessageData := #[]
        for f in fArr do
          let fTy? ← withLocalDeclD `_qed_m modelTy fun m => do
            try
              let fTy ← instantiateMVars (← inferType (← mkProjection m f.getId))
              if (← synthLawfulJsonAux 16 fTy).isNone then return some fTy else return none
            catch _ => return none
          if let some fTy := fTy? then
            badFields := badFields.push m!"`{f.getId} : {← ppExpr fTy}`"
        if !badFields.isEmpty then
          let listMd := MessageData.joinSep badFields.toList ", "
          throwErrorAt ref m!"cannot serialize dehydrated state field(s) {listMd} for SSR (missing `LawfulJson` instance).\nMark non-serializable fields as `ephemeral` (if not rendered by the view or constrained by an invariant), or define `LawfulJson` for their type."
        else
          throwErrorAt ref m!"could not synthesize a verified JSON codec (`LawfulJson`) for dehydrated field slice `{← ppExpr alphaTy}`"
  return mkApp6 (Lean.mkConst ``Dehydrate.slice) modelTy alphaTy instAlpha initVal getterVal setterVal

private def elabInitModel (initStx : Syntax) : TermElabM (Expr × Expr) := do
  let initVal ← elabTerm initStx none
  synthesizeSyntheticMVarsNoPostponing
  let initVal ← instantiateMVars initVal
  return (initVal, ← instantiateMVars (← inferType initVal))

elab "Dehydrate.except " init:term:max " [" es:ident,* "]" : term => do
  let exArr := es.getElems
  let (initVal, modelTy) ← elabInitModel init
  let (fn, _) := (← whnfR modelTy).getAppFnArgs
  let env ← getEnv
  unless isStructure env fn do
    throwError m!"Dehydrate.except requires a structure model type, got `{← ppExpr modelTy}`"
  let allFields := getStructureFieldsFlattened env fn (includeSubobjectFields := false)
  for e in exArr do
    unless allFields.contains e.getId do
      throwErrorAt e m!"unknown field `{e.getId}` on `{fn}` (fields: {allFields.toList})"
  let ref ← getRef
  elabStructFieldsSlice ref initVal modelTy (allFields.filter (fun f => !exArr.any (·.getId == f)) |>.map (mkIdentFrom ref))

elab "qedInternalAutoDehydrate% " init:term:max app:term:max : term <= expectedType => do
  let stx ← getRef
  let appVal ← elabTerm app (some expectedType)
  synthesizeSyntheticMVarsNoPostponing
  let appVal ← instantiateMVars appVal
  let (appFn, appArgs) := (← instantiateMVars (← whnfR (← inferType appVal))).getAppFnArgs
  unless appFn == ``Qed.App && appArgs.size == 2 do return appVal
  let modelTy ← instantiateMVars appArgs[0]!
  let msgTy   ← instantiateMVars appArgs[1]!
  if let some (instModel, _) ← synthLawfulJsonAux 16 modelTy then
    return mkApp4 (Lean.mkConst ``Internal.App.withFullDehydrate) modelTy msgTy instModel appVal
  let (fn, _) := (← whnfR modelTy).getAppFnArgs
  let env ← getEnv
  if isStructure env fn then
    let allFields := getStructureFieldsFlattened env fn (includeSubobjectFields := false)
    let initVal ← instantiateMVars (← elabTermEnsuringType init modelTy <* synthesizeSyntheticMVarsNoPostponing)
    let goodFields ← allFields.filterM fun f =>
      withLocalDeclD `_qed_m modelTy fun m => do
        try return (← synthLawfulJsonAux 16 (← instantiateMVars (← inferType (← mkProjection m f)))).isSome
        catch _ => return false
    if !goodFields.isEmpty then
      let saved ← saveState
      let preMsgs := (← Core.getMessageLog).toList.length
      let sliceAttempt? ← try
          let dSlice ← elabStructFieldsSlice stx initVal modelTy (goodFields.map (mkIdentFrom stx))
          let fn4 := mkApp4 (Lean.mkConst ``Qed.Internal.App.withDehydrate) modelTy msgTy dSlice appVal
          let pfMVar ← mkFreshExprMVar (← inferType fn4).bindingDomain!
          let unsolved ← Tactic.run pfMVar.mvarId! (Tactic.evalTactic (← `(tactic| qedProveDehydrateView)))
          let pf ← instantiateMVars pfMVar
          if unsolved.isEmpty && ((← Core.getMessageLog).toList.drop preMsgs).all (·.severity != .error) && !pf.hasExprMVar then
            pure (some (Lean.mkApp fn4 pf))
          else pure none
        catch _ => pure none
      if let some wrapped := sliceAttempt? then return wrapped
      restoreState saved
  return appVal

end AutoDehydrate

end Qed
