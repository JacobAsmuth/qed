import Qed.Runtime.Cmd
import Qed.Runtime.Local
import Qed.Render
import Qed.View.Core
import Qed.Router
import Qed.Runtime.Verify

namespace Qed

structure App (Model : Type) (Msg : Type) where
  init           : Model × Cmd Msg
  update         : Model → Msg → Model × Cmd Msg
  template       : View Model Msg
  onUrlChange    : Option (String → Msg) := none
  locals         : List LocalDef := []
  onPort         : Option (String → String → Option Msg) := none
  dehydrate      : Model → String := fun _ => ""
  rehydrate      : String → Option Model := fun _ => none
  styles         : List Style := []
  valid_view     : ∀ m, Html.valid (View.render template m) = true
  dehydrate_view : ∀ m m', rehydrate (dehydrate m) = some m' →
                     View.render template m' = View.render template m := by
                     intro _ _ h; cases h

def App.view (app : App Model Msg) (m : Model) : Html Msg := View.render app.template m

theorem App.valid_app_view (app : App Model Msg) (m : Model) :
    Html.valid (app.view m) = true :=
  app.valid_view m

class ToStep (Model : Type) (Msg : Type) (α : Type) where
  toStep : α → Model × Cmd Msg
instance : ToStep Model Msg Model := ⟨fun m => (m, .none)⟩
instance : ToStep Model Msg (Model × Cmd Msg) := ⟨id⟩
instance : ToStep Model Msg (Model × List (Cmd Msg)) := ⟨fun (m, cs) => (m, .batch cs)⟩

@[simp] theorem ToStep.toStep_model (m : Model) :
    (ToStep.toStep m : Model × Cmd Msg) = (m, .none) := rfl
@[simp] theorem ToStep.toStep_pair (p : Model × Cmd Msg) :
    (ToStep.toStep p : Model × Cmd Msg) = p := rfl
@[simp] theorem ToStep.toStep_listPair (p : Model × List (Cmd Msg)) :
    (ToStep.toStep p : Model × Cmd Msg) = (p.1, .batch p.2) := rfl

def mkApp [ToStep Model Msg α] (init : Model) (update : Model → Msg → α)
    (template : View Model Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) :
    App Model Msg :=
  { init := (init, start), update := fun m msg => ToStep.toStep (update m msg),
    template, locals, onPort, valid_view }

def mkRoutedApp {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (update : Model → Msg → α) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true := by qedProveValidHtml) :
    App Model Msg :=
  { mkApp init update template start locals onPort valid_view with
    onUrlChange := some (fun p => onRoute ((Router.fromURL p).getD default)) }

def App.addLocals (app : App Model Msg) (locals : List LocalDef) (styles : List Style := []) : App Model Msg :=
  { app with locals := LocalDef.dedupe (app.locals ++ locals), styles := app.styles ++ styles }

@[simp] theorem mkApp_init [ToStep Model Msg α] (init : Model) (u : Model → Msg → α)
    (t : View Model Msg) (s l p hv) :
    (mkApp init u t s l p hv).init = (init, s) := rfl
@[simp] theorem mkApp_update [ToStep Model Msg α] (init : Model) (u : Model → Msg → α)
    (t : View Model Msg) (s l p hv) (m : Model) (msg : Msg) :
    (mkApp init u t s l p hv).update m msg = ToStep.toStep (u m msg) := rfl
@[simp] theorem mkApp_template [ToStep Model Msg α] (init : Model) (u : Model → Msg → α)
    (t : View Model Msg) (s l p hv) :
    (mkApp init u t s l p hv).template = t := rfl
@[simp] theorem mkRoutedApp_init {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (u : Model → Msg → α) (t : View Model Msg) (r : R → Msg) (s l p hv) :
    (mkRoutedApp init u t r s l p hv).init = (init, s) := rfl
@[simp] theorem mkRoutedApp_update {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (u : Model → Msg → α) (t : View Model Msg) (r : R → Msg) (s l p hv) (m : Model) (msg : Msg) :
    (mkRoutedApp init u t r s l p hv).update m msg = ToStep.toStep (u m msg) := rfl
@[simp] theorem mkRoutedApp_template {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (u : Model → Msg → α) (t : View Model Msg) (r : R → Msg) (s l p hv) :
    (mkRoutedApp init u t r s l p hv).template = t := rfl
@[simp] theorem App.addLocals_init (app : App Model Msg) (l s) :
    (app.addLocals l s).init = app.init := rfl
@[simp] theorem App.addLocals_update (app : App Model Msg) (l s) :
    (app.addLocals l s).update = app.update := rfl
@[simp] theorem App.addLocals_template (app : App Model Msg) (l s) :
    (app.addLocals l s).template = app.template := rfl

structure Dehydrate (Model : Type) where
  project    : Model → Model := id
  dehydrate  : Model → String
  rehydrate  : String → Option Model
  round_trip : ∀ m, rehydrate (dehydrate m) = some (project m)

namespace Dehydrate

def full {Model : Type} [LawfulJson Model] : Dehydrate Model where
  project    := id
  dehydrate  := fun m => Json.render (toJson m)
  rehydrate  := fun s => ((Json.parse s (max 64 (LawfulJson.depthBound Model))).bind fromJson).toOption
  round_trip := fun m => by
    simp [LawfulJson.parse_render_toJson m (Nat.le_max_right 64 _), Except.toOption]

def slice {Model α : Type} [LawfulJson α] (init : Model)
    (get : Model → α) (set : Model → α → Model) : Dehydrate Model where
  project    := fun m => set init (get m)
  dehydrate  := fun m => Json.render (toJson (get m))
  rehydrate  := fun s => (((Json.parse s (max 64 (LawfulJson.depthBound α))).bind fromJson).toOption).map (set init)
  round_trip := fun m => by
    simp [LawfulJson.parse_render_toJson (get m) (Nat.le_max_right 64 _), Except.toOption]

def route {Model R : Type} [Router R] (init : Model)
    (get : Model → R) (set : Model → R → Model) : Dehydrate Model :=
  slice init get set

def fromRoute {Model Msg R α : Type} [Router R] [ToStep Model Msg α]
    (init : Model) (update : Model → Msg → α) (onRoute : R → Msg) (get : Model → R) : Dehydrate Model :=
  slice init get (fun _ r => (ToStep.toStep (update init (onRoute r)) : Model × Cmd Msg).1)

@[simp] theorem full_project {Model : Type} [LawfulJson Model] (m : Model) :
    (full : Dehydrate Model).project m = m := rfl

@[simp] theorem slice_project {Model α : Type} [LawfulJson α] (init : Model)
    (get : Model → α) (set : Model → α → Model) (m : Model) :
    (slice init get set).project m = set init (get m) := rfl

@[simp] theorem route_project {Model R : Type} [Router R] (init : Model)
    (get : Model → R) (set : Model → R → Model) (m : Model) :
    (route init get set).project m = set init (get m) := rfl

@[simp] theorem fromRoute_project {Model Msg R α : Type} [Router R] [ToStep Model Msg α]
    (init : Model) (update : Model → Msg → α) (onRoute : R → Msg) (get : Model → R) (m : Model) :
    (fromRoute init update onRoute get).project m =
      (ToStep.toStep (update init (onRoute (get m))) : Model × Cmd Msg).1 := rfl

theorem dehydrate_view_of_project {Model Msg : Type}
    (d : Dehydrate Model) (tmpl : View Model Msg)
    (hproj : ∀ m, View.render tmpl (d.project m) = View.render tmpl m) :
    ∀ m m', d.rehydrate (d.dehydrate m) = some m' →
      View.render tmpl m' = View.render tmpl m := by
  intro m m' h
  have hrt := d.round_trip m
  rw [hrt] at h
  cases h
  exact hproj m

end Dehydrate

def App.withDehydrate {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m := by
      qedProveDehydrateView) : App Model Msg :=
  { app with
    dehydrate      := d.dehydrate
    rehydrate      := d.rehydrate
    dehydrate_view := Dehydrate.dehydrate_view_of_project d app.template hview }

@[simp] theorem App.withDehydrate_init (d : Dehydrate Model) (app : App Model Msg) (hv) :
    (App.withDehydrate d app hv).init = app.init := rfl
@[simp] theorem App.withDehydrate_update (d : Dehydrate Model) (app : App Model Msg) (hv) :
    (App.withDehydrate d app hv).update = app.update := rfl
@[simp] theorem App.withDehydrate_template (d : Dehydrate Model) (app : App Model Msg) (hv) :
    (App.withDehydrate d app hv).template = app.template := rfl

open Lean in
private def mkNestedTuple : List Term → MacroM Term
  | []      => `(())
  | [x]     => pure x
  | x :: xs => do
      let rest ← mkNestedTuple xs
      `(($x, $rest))

open Lean in
macro "Dehydrate.fields " init:term:max " [" fs:ident,* "]" : term => do
  let fArr := fs.getElems
  if fArr.isEmpty then
    Macro.throwError "Dehydrate.fields requires at least one field name"
  let projs ← fArr.mapM fun f => `(m.$f:ident)
  let getter ← mkNestedTuple projs.toList
  let vIds := (List.range fArr.size).toArray.map fun i =>
    mkIdent (Name.mkSimple s!"_qed_d_{i}")
  let pat ← mkNestedTuple (vIds.toList.map fun v => (⟨v.raw⟩ : Term))
  let vTerms : Array Term := vIds.map fun v => ⟨v.raw⟩
  `(Dehydrate.slice $init (fun m => $getter) (fun m $pat => { m with $[$fArr:ident := $vTerms],* }))

class ToPortOpt (Msg : Type) (α : Type) where
  toPortOpt : α → Option (String → String → Option Msg)
instance : ToPortOpt Msg (String → String → Option Msg) := ⟨some⟩
instance : ToPortOpt Msg (Option (String → String → Option Msg)) := ⟨id⟩

end Qed
