import Qed.Runtime.AppCore
import Qed.Runtime.Verify
import Qed.Lang

namespace Qed

private def wrapLocalView {S M O : Type} [ToJson S] [FromJson S] [ToJson O] (init : S) (view : S → Html M) (update : S → M → S × Option O) : String → Html LocalMsg :=
  let dec (s : String) : S := ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  fun s => (view (dec s)).map fun m => { run := fun st => let (s', o) := update (dec st) m; (Json.render (ToJson.toJson s'), o.map (Json.render ∘ toJson)) }

def LocalDef.of {S M O : Type} [ToJson S] [FromJson S] [ToJson O] (id : String) (init : S) (view : S → Html M) (update : S → M → S × Option O)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  { id, init := Json.render (ToJson.toJson init), view := wrapLocalView init view update, valid_view := ⟨fun _ => by simpa [wrapLocalView, Html.valid] using hvalid _, trivial⟩ }

def LocalDef.ofSimple {S M : Type} [ToJson S] [FromJson S] (id : String) (init : S) (view : S → Html M) (update : S → M → S)
    (hvalid : ∀ s, Html.valid (view s) = true := by qedProveValidHtml) : LocalDef :=
  LocalDef.of (O := String) id init view (fun s m => (update s m, none)) hvalid

def LocalDef.ofProps {P S M O : Type} [FromJson P] [ToJson S] [FromJson S] [ToJson O] (id : String) (init : S) (view : P → S → Html M) (update : P → S → M → S × Option O)
    (hvalid : ∀ p s, Html.valid (view p s) = true := by qedProveValidHtml) : LocalDef :=
  { id, init := Json.render (toJson init), view := fun _ => .text ""
    viewProps := some fun props => match (Json.parse props).bind (FromJson.fromJson (α := P)) with
      | .error e => fun _ => .text s!"Invalid component props: {e}" | .ok p => wrapLocalView init (view p) (update p)
    valid_view := ⟨fun _ => rfl, fun props _ => by dsimp only; cases (Json.parse props).bind (FromJson.fromJson (α := P)) with | error _ => rfl | ok p => simpa [wrapLocalView, Html.valid] using hvalid p _⟩ }

theorem LocalDef.of_view_roundtrip {S M O : Type} [LawfulJson S] [ToJson O] (id : String) (init s : S) (view : S → Html M)
    (update : S → M → S × Option O) (hvalid : ∀ x, Html.valid (view x) = true) (hdepth : LawfulJson.depthBound S ≤ 64) :
    (LocalDef.of id init view update hvalid).view (Json.render (toJson s)) =
      (view s).map (fun m => { run := fun st =>
        let (s', o) := update (((Json.parse st).bind FromJson.fromJson).toOption.getD init) m
        (Json.render (ToJson.toJson s'), o.map fun x => Json.render (ToJson.toJson x)) }) := by
  simp only [LocalDef.of, wrapLocalView, LocalDef.decode_toJson_eq s init hdepth]; rfl

theorem LocalDef.ofProps_view_roundtrip {P S M O : Type} [LawfulJson P] [LawfulJson S] [ToJson O] (id : String) (init s : S) (p : P)
    (view : P → S → Html M) (update : P → S → M → S × Option O) (hvalid : ∀ p x, Html.valid (view p x) = true)
    (hdepthP : LawfulJson.depthBound P ≤ 64) (hdepthS : LawfulJson.depthBound S ≤ 64) :
    (LocalDef.ofProps id init view update hvalid).viewForProps (Json.render (toJson p)) (Json.render (toJson s)) =
      (view p s).map (fun m => { run := fun st =>
        let (next, out) := update p (((Json.parse st).bind FromJson.fromJson).toOption.getD init) m
        (Json.render (toJson next), out.map (Json.render ∘ toJson)) }) := by
  simp only [LocalDef.viewForProps, LocalDef.ofProps, wrapLocalView, Option.map_some, Option.getD_some]
  rw [LawfulJson.parse_render_toJson p hdepthP]; simp only [LocalDef.decode_toJson_eq s init hdepthS]

namespace Internal

def mkApp (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg) (start : Cmd Msg := .none)
    (locals : List LocalDef := []) (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none) (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) : App Model Msg :=
  mkAppCore init update template start locals styles onPort onSession valid_view

def mkRoutedApp {R : Type} [Router R] [Inhabited R] (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := []) (styles : List Style := [])
    (onPort : Option (String → String → Option Msg) := none) (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) : App Model Msg :=
  mkRoutedAppCore init update template onRoute start locals styles onPort onSession valid_view

defAppProjSimps mkApp (init : Model) (u : Model → Msg → Model × Cmd Msg) (t : View Model Msg) (s l st p os hv) => mkApp init u t s l st p os hv with
  [init := (init, s), update := u, template := t, dehydrate := fun _ => "", rehydrate := fun _ => none]
defAppProjSimps mkRoutedApp {R : Type} [Router R] [Inhabited R] (init : Model) (u : Model → Msg → Model × Cmd Msg) (t : View Model Msg) (r : R → Msg) (s l st p os hv) =>
    mkRoutedApp init u t r s l st p os hv with
  [init := (init, s), update := u, template := t, dehydrate := fun _ => "", rehydrate := fun _ => none]

@[reducible] def App.withDehydrate {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m := by qedProveDehydrateView) : App Model Msg :=
  App.withDehydrateCore d app hview

defAppProjSimps App.withDehydrate (d : Dehydrate Model) (app : App Model Msg) (hv) => App.withDehydrate d app hv with
  [init := app.init, update := app.update, template := app.template, dehydrate := d.dehydrate, rehydrate := d.rehydrate]
@[simp] theorem App.withDehydrate_rehydrate_dehydrate (d : Dehydrate Model) (app : App Model Msg) (hv) (m : Model) :
    (App.withDehydrate d app hv).rehydrate ((App.withDehydrate d app hv).dehydrate m) = some (d.project m) := d.round_trip m
@[reducible] def App.withFullDehydrate {Model Msg : Type} [LawfulJson Model] (app : App Model Msg) : App Model Msg :=
  App.withDehydrate Dehydrate.full app (fun _ => rfl)

end Internal

set_option linter.unusedVariables false in
def App.guardRehydrate {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv] (app : App Model Msg)
    (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m' := by qedProveDehydrateInv) : App Model Msg :=
  App.guardRehydrateCore Inv app hpres

defAppProjSimps App.guardRehydrate {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv] (app : App Model Msg) (hp) =>
    App.guardRehydrate Inv app hp with [init := app.init, update := app.update, template := app.template, dehydrate := app.dehydrate]

theorem App.guardRehydrate_sound {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv] (app : App Model Msg) (hp) (raw : String) (m' : Model)
    (h : (App.guardRehydrate Inv app hp).rehydrate raw = some m') : Inv m' := (App.guardRehydrate_step_eq_some Inv app.rehydrate h).2

theorem App.guardRehydrate_complete {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv] (app : App Model Msg) (hp) (m : Model) (hm : Inv m) :
    (App.guardRehydrate Inv app hp).rehydrate ((App.guardRehydrate Inv app hp).dehydrate m) = app.rehydrate (app.dehydrate m) := by
  dsimp only [App.guardRehydrate, App.guardRehydrateCore]
  cases hr : app.rehydrate (app.dehydrate m) with | none => rfl | some m' => simp [decide_eq_true (hp m m' hm hr)]

section AutoDehydrate
open Lean Meta Elab Term

private def mkTy2 (c : Name) (a b : Expr) : Expr := mkApp2 (Lean.mkConst c [Level.zero, Level.zero]) a b
private def prodTypeOf (pad : Bool) : List Expr → Expr | [] => Lean.mkConst ``Unit | [t] => if pad then mkTy2 ``Prod t (Lean.mkConst ``Unit) else t | t :: ts => mkTy2 ``Prod t (prodTypeOf false ts)
private def mkTupleVal (pad : Bool) : List (Expr × Expr) → Expr
  | [] => Lean.mkConst ``Unit.unit
  | [(ty, v)] => if pad then mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) ty (Lean.mkConst ``Unit) v (Lean.mkConst ``Unit.unit) else v
  | (ty, v) :: r => mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) ty (prodTypeOf false (r.map Prod.fst)) v (mkTupleVal false r)
private def projTupleVals (pad : Bool) : List Expr → Expr → List Expr
  | [], _ => [] | [_], p => [if pad then Expr.proj ``Prod 0 p else p] | _ :: rest, p => Expr.proj ``Prod 0 p :: projTupleVals false rest (Expr.proj ``Prod 1 p)
private def sumTypeOf : List Expr → Expr | [] => Lean.mkConst ``Unit | [t] => t | t :: ts => mkTy2 ``Sum t (sumTypeOf ts)
private def injSumVal : List Expr → Nat → Expr → Expr
  | [], _, v | [_], _, v => v
  | p :: ps, 0, v => mkApp3 (Lean.mkConst ``Sum.inl [Level.zero, Level.zero]) p (sumTypeOf ps) v
  | p :: ps, j + 1, v => mkApp3 (Lean.mkConst ``Sum.inr [Level.zero, Level.zero]) p (sumTypeOf ps) (injSumVal ps j v)

@[noinline] private def buildSumFromB (ty : Expr) : List (Expr × Bool × List Expr × Expr) → MetaM Expr
  | [] => withLocalDeclD `u (Lean.mkConst ``Unit) fun u => mkLambdaFVars #[u] u
  | [(cApp, pad, fTys, pTy)] => withLocalDeclD `p pTy fun p => mkLambdaFVars #[p] (mkAppN cApp (projTupleVals pad fTys p).toArray)
  | (cApp, pad, fTys, pTy) :: rest => do
      let rSumTy := sumTypeOf (rest.map (·.2.2.2)); let sTy := mkTy2 ``Sum pTy rSumTy
      let leftFn ← withLocalDeclD `p pTy fun p => mkLambdaFVars #[p] (mkAppN cApp (projTupleVals pad fTys p).toArray)
      let rightFn ← buildSumFromB ty rest
      let motive ← withLocalDeclD `s sTy fun s => mkLambdaFVars #[s] ty
      withLocalDeclD `s sTy fun s => do mkLambdaFVars #[s] (← mkAppOptM ``Sum.casesOn #[some pTy, some rSumTy, some motive, some s, some leftFn, some rightFn])

private def substFVar (fv val e : Expr) : Expr := (e.abstract #[fv]).instantiate1 val
private def isClosedType0 (t : Expr) : MetaM Bool := do if t.hasMVar || t.hasFVar then return false else return (← whnf (← inferType t)) == .sort Level.one

private def synthDirect? (ty : Expr) : MetaM (Option (Expr × Option Expr)) := do
  let .some inst ← trySynthInstance (Lean.mkApp (Lean.mkConst ``Qed.LawfulJson) ty) | return none
  let toJ ← mkAppOptM ``Qed.LawfulJson.toToJson #[ty, inst]
  return some (inst, (← trySynthInstance (mkApp2 (Lean.mkConst ``Qed.NonNullJson) ty toJ)).toOption)

private def withLocalInst (nm cls : Name) (ty val : Expr) (k : Expr → MetaM (Option (Expr × Option Expr))) : MetaM (Option (Expr × Option Expr)) :=
  withLetDecl nm ty val fun fv => do
    let res? ← withLCtx (← getLCtx) ((← getLocalInstances).push { className := cls, fvar := fv }) (k fv)
    return res?.map fun (i, n?) => (substFVar fv val i, n?.map (substFVar fv val))

@[noinline] private def withEnsuredTypes (synth : Expr → MetaM (Option (Expr × Option Expr))) : List Expr → MetaM (Option (Expr × Option Expr)) → MetaM (Option (Expr × Option Expr))
  | [], k => k
  | t :: ts, k => do
      let t ← instantiateMVars t
      if !(← isClosedType0 t) then withEnsuredTypes synth ts k
      else if (← synthDirect? t).isSome then withEnsuredTypes synth ts k
      else
        let some (tInst, tNN?) ← synth t | return none
        withLocalInst `_qed_lj ``Qed.LawfulJson (Lean.mkApp (Lean.mkConst ``Qed.LawfulJson) t) tInst fun fvLJ =>
          match tNN? with
          | none => withEnsuredTypes synth ts k
          | some nnVal => do
              let toJ ← mkAppOptM ``Qed.LawfulJson.toToJson #[t, fvLJ]
              withLocalInst `_qed_nn ``Qed.NonNullJson (mkApp2 (Lean.mkConst ``Qed.NonNullJson) t toJ) nnVal fun _ => withEnsuredTypes synth ts k

@[noinline] def synthLawfulJsonAux : Nat → Expr → MetaM (Option (Expr × Option Expr))
  | 0, _ => return none
  | fuel + 1, rawTy => do
      let ty ← instantiateMVars rawTy; if !(← isClosedType0 ty) then return none
      if let some hit ← synthDirect? ty then return some hit
      let ty ← whnfR ty; let (fn, args) := ty.getAppFnArgs
      withEnsuredTypes (synthLawfulJsonAux fuel) args.toList do
        if let some hit ← synthDirect? ty then return some hit
        let env ← getEnv; if Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env fn) then return none
        let some (.inductInfo indVal) := env.find? fn | return none
        let casesName := mkCasesOnName fn
        if indVal.isRec || indVal.numIndices != 0 || args.size != indVal.numParams || indVal.ctors.isEmpty || !env.contains casesName then return none
        let ctorLevels := ty.getAppFn.constLevels!
        let some ctorRaw ← (indVal.ctors.mapM fun cName => OptionT.mk do
          let some (.ctorInfo cVal) := env.find? cName | return none
          let cApp := mkAppN (Lean.mkConst cName ctorLevels) args
          forallBoundedTelescope (← inferType cApp) (some cVal.numFields) fun fvars _ => do
            let some fTys ← (fvars.toList.mapM fun fv => OptionT.mk do
              let fTy ← instantiateMVars (← inferType fv)
              if fvars.any (fun o => o != fv && fTy.containsFVar o.fvarId!) then return none
              if (← whnf (← inferType fTy)) != .sort Level.one then return none
              return some fTy).run | return none
            return some (cApp, fTys)).run | return none
        withEnsuredTypes (synthLawfulJsonAux fuel) (ctorRaw.foldr (fun (_, fs) acc => fs ++ acc) []) do
          let ctorEntries ← ctorRaw.mapM fun (cApp, fTys) => do
            let pad ← match ctorRaw.length == 1, fTys with | true, [fTy] => pure ((← synthDirect? fTy).bind Prod.snd).isNone | _, _ => pure false
            return (cApp, pad, fTys, prodTypeOf pad fTys)
          let payloadTys := ctorEntries.map (·.2.2.2); let sumTy := sumTypeOf payloadTys
          let some (sumInst, some sumNN) ← synthDirect? sumTy | return none
          let mkDecls (fTys : List Expr) := ((List.range fTys.length).zip fTys).map (fun (i, fTy) => (Name.mkSimple s!"_x_{i}", fTy)) |>.toArray
          let mkCasesFn (motiveBody : Expr → Expr) (minors : List Expr) : MetaM Expr := do
            let motive ← withLocalDeclD `x ty fun x => mkLambdaFVars #[x] (motiveBody x)
            withLocalDeclD `x ty fun x => do mkLambdaFVars #[x] (← mkAppOptM casesName (args.map some ++ #[some motive, some x] ++ minors.toArray.map some))
          let toMinors ← ((List.range ctorEntries.length).zip ctorEntries).mapM fun (j, (_, pad, fTys, _)) =>
            withLocalDeclsDND (mkDecls fTys) fun xs => mkLambdaFVars xs (injSumVal payloadTys j (mkTupleVal pad (fTys.zip xs.toList)))
          let toB ← mkCasesFn (fun _ => sumTy) toMinors; let fromB ← buildSumFromB ty ctorEntries
          let some invMinors ← (OptionT.run <| ctorEntries.mapM fun (cApp, _, fTys, _) => OptionT.mk <|
            withLocalDeclsDND (mkDecls fTys) fun xs => do
              let cTerm := mkAppN cApp xs
              unless ← isDefEq (Lean.mkApp fromB (Lean.mkApp toB cTerm)) cTerm do return none
              return some (← mkLambdaFVars xs (mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) ty cTerm))) | return none
          let leftInv ← mkCasesFn (fun x => mkApp3 (Lean.mkConst ``Eq [Level.one]) ty (Lean.mkApp fromB (Lean.mkApp toB x)) x) invMinors
          let isoInst := mkApp6 (Lean.mkConst ``Qed.LawfulJson.iso) ty sumTy sumInst toB fromB leftInv
          let isoNN := mkApp7 (Lean.mkConst ``Qed.NonNullJson.iso) ty sumTy sumInst sumNN toB fromB leftInv
          unless ← isTypeCorrect isoInst do return none
          return some (isoInst, some isoNN)

private def fieldJsonStatus (modelTy : Expr) (field : Name) : MetaM (Option (Expr × Bool)) :=
  withLocalDeclD `_qed_m modelTy fun m => try
    let fTy ← instantiateMVars (← inferType (← mkProjection m field)); return some (fTy, (← synthLawfulJsonAux 16 fTy).isSome)
  catch _ => return none

private def elabClosed (stx : Syntax) (ty? : Option Expr) : TermElabM Expr := do
  let e ← match ty? with | some ty => elabTermEnsuringType stx ty | none => elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing; instantiateMVars e

@[noinline] def elabStructFieldsSlice (ref : Syntax) (initVal modelTy : Expr) (fArr : Array Ident) : TermElabM Expr := do
  if fArr.isEmpty then return mkApp2 (Lean.mkConst ``Dehydrate.const) modelTy initVal
  let (mId, pId) := (mkIdentFrom ref `_qed_m, mkIdentFrom ref `_qed_p)
  let getterBody ← Qed.Lang.buildTupleVal (← fArr.mapM fun f => `($mId.$f:ident))
  let projTerms ← Qed.Lang.extractTupleProjections pId fArr.size
  let alphaMVar ← mkFreshExprMVar (mkSort Level.one)
  let getterVal ← elabClosed (← `(fun $mId => $getterBody)) (some (← mkArrow modelTy alphaMVar))
  let alphaTy ← instantiateMVars alphaMVar
  let setterVal ← elabClosed (← `(fun $mId $pId => { $mId with $[$fArr:ident := $projTerms],* })) (some (← mkArrow modelTy (← mkArrow alphaTy modelTy)))
  let some (instAlpha, _) ← synthLawfulJsonAux 16 alphaTy | do
    let badFields ← fArr.filterMapM fun f => do
      if let some (fTy, false) ← fieldJsonStatus modelTy f.getId then return some m!"`{f.getId} : {← ppExpr fTy}`" else return none
    if !badFields.isEmpty then
      throwErrorAt ref m!"cannot serialize dehydrated state field(s) {MessageData.joinSep badFields.toList ", "} for SSR (missing `LawfulJson` instance).\nMark non-serializable fields as `ephemeral` (if not rendered by the view or constrained by an invariant), or define `LawfulJson` for their type."
    else throwErrorAt ref m!"could not synthesize a verified JSON codec (`LawfulJson`) for dehydrated field slice `{← ppExpr alphaTy}`"
  return mkApp6 (Lean.mkConst ``Dehydrate.slice) modelTy alphaTy instAlpha initVal getterVal setterVal

elab "Dehydrate.except " init:term:max " [" es:ident,* "]" : term => do
  let exArr := es.getElems; let initVal ← elabClosed init none; let modelTy ← instantiateMVars (← inferType initVal)
  let (fn, _) := (← whnfR modelTy).getAppFnArgs; let env ← getEnv
  unless isStructure env fn do throwError m!"Dehydrate.except requires a structure model type, got `{← ppExpr modelTy}`"
  let allFields := getStructureFieldsFlattened env fn (includeSubobjectFields := false)
  for e in exArr do unless allFields.contains e.getId do throwErrorAt e m!"unknown field `{e.getId}` on `{fn}` (fields: {allFields.toList})"
  let ref ← getRef; elabStructFieldsSlice ref initVal modelTy (allFields.filter (fun f => !exArr.any (·.getId == f)) |>.map (mkIdentFrom ref))

elab "qedInternalAutoDehydrate% " init:term:max app:term:max : term <= expectedType => do
  let stx ← getRef; let appVal ← elabClosed app (some expectedType)
  let (appFn, appArgs) := (← instantiateMVars (← whnfR (← inferType appVal))).getAppFnArgs
  unless appFn == ``Qed.App && appArgs.size == 2 do return appVal
  let modelTy ← instantiateMVars appArgs[0]!; let msgTy ← instantiateMVars appArgs[1]!
  if let some (instModel, _) ← synthLawfulJsonAux 16 modelTy then return mkApp4 (Lean.mkConst ``Internal.App.withFullDehydrate) modelTy msgTy instModel appVal
  let (fn, _) := (← whnfR modelTy).getAppFnArgs; let env ← getEnv
  if isStructure env fn then
    let allFields := getStructureFieldsFlattened env fn (includeSubobjectFields := false)
    let initVal ← elabClosed init (some modelTy)
    let goodFields ← allFields.filterM fun f => return (← fieldJsonStatus modelTy f).any Prod.snd
    if !goodFields.isEmpty then
      let saved ← saveState; let preMsgs := (← Core.getMessageLog).toList.length
      let sliceAttempt? ← try
          let dSlice ← elabStructFieldsSlice stx initVal modelTy (goodFields.map (mkIdentFrom stx))
          let fn4 := mkApp4 (Lean.mkConst ``Qed.Internal.App.withDehydrate) modelTy msgTy dSlice appVal
          let pfMVar ← mkFreshExprMVar (← inferType fn4).bindingDomain!
          let unsolved ← Tactic.run pfMVar.mvarId! (Tactic.evalTactic (← `(tactic| qedProveDehydrateView)))
          let pf ← instantiateMVars pfMVar
          if unsolved.isEmpty && !pf.hasExprMVar then
            if ((← Core.getMessageLog).toList.drop preMsgs).all (·.severity != .error) then pure (some (Lean.mkApp fn4 pf)) else pure none
          else pure none
        catch _ => pure none
      if let some wrapped := sliceAttempt? then return wrapped
      restoreState saved
  return appVal

end AutoDehydrate
end Qed
