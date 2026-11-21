import Qed.Runtime.Cmd
import Qed.Runtime.LocalCore
import Qed.Render
import Qed.View.Core
import Qed.Router.Basic

namespace Qed

/-- Per-route HTML `<head>` metadata rendered safely during SSR. -/
structure HeadMeta where
  title       : Option String := none
  description : Option String := none
  metaTags    : List (String × String) := []
  canonical   : Option String := none
  redirect    : Option String := none
deriving Inhabited, DecidableEq, Repr

structure App (Model : Type) (Msg : Type) where
  private mk ::
  init           : Model × Cmd Msg
  update         : Model → Msg → Model × Cmd Msg
  template       : View Model Msg
  onUrlChange    : Option (String → Msg) := none
  onSession      : Option (Option String → Msg) := none
  onHydrate      : Model → Cmd Msg := fun _ => .none
  locals         : List LocalDef := []
  onPort         : Option (String → String → Option Msg) := none
  dehydrate      : Model → String := fun _ => ""
  rehydrate      : String → Option Model := fun _ => none
  styles         : List Style := []
  stylesheets    : List String := []
  headFor        : Model → HeadMeta := fun _ => {}
  ssrStatus      : Model → Nat := fun _ => 200
  valid_view     : ∀ m, Html.valid (View.render template m) = true
  dehydrate_view : ∀ m m', rehydrate (dehydrate m) = some m' →
                     View.render template m' = View.render template m := by
                     intro _ _ h; cases h

def App.view (app : App Model Msg) (m : Model) : Html Msg := View.render app.template m

theorem App.valid_app_view (app : App Model Msg) (m : Model) :
    Html.valid (app.view m) = true :=
  app.valid_view m

declare_syntax_cat appProjPair
syntax ident " := " term : appProjPair

macro "defAppProjSimps " pre:ident binders:bracketedBinder* " => " lhs:term
    " with " "[" pairs:appProjPair,* "]" : command => do
  let mut cmds := #[]
  for p in pairs.getElems do
    match p with
    | `(appProjPair| $fld:ident := $rhs:term) =>
        let thm := Lean.mkIdentFrom pre (pre.getId.appendAfter ("_" ++ fld.getId.eraseMacroScopes.toString))
        cmds := cmds.push (← `(command| @[simp] theorem $thm $binders* : ($lhs).$fld = $rhs := rfl))
    | _ => Lean.Macro.throwUnsupported
  return ⟨Lean.mkNullNode cmds⟩

macro "defAppProjSimps " pre:ident binders:bracketedBinder* " => " lhs:term " preserves " app:ident : command =>
  `(command| defAppProjSimps $pre $binders* => $lhs with
      [init := ($app).init, update := ($app).update, template := ($app).template,
       dehydrate := ($app).dehydrate, rehydrate := ($app).rehydrate])

namespace Internal

def mkAppCore (init : Model) (update : Model → Msg → Model × Cmd Msg)
    (template : View Model Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true) :
    App Model Msg :=
  { init := (init, start), update, template, locals, styles, onPort, onSession, valid_view }

def mkRoutedAppCore {R : Type} [Router R] [Inhabited R]
    (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true) :
    App Model Msg :=
  { mkAppCore init update template start locals styles onPort onSession valid_view with
    onUrlChange := some (fun p => onRoute ((Router.fromURL p).getD default)) }

def App.setInitAndUpdate (app : App Model Msg) (init : Model × Cmd Msg)
    (u : Model → Msg → Model × Cmd Msg) : App Model Msg :=
  { app with init := init, update := u }

def App.setInitUpdateHydrate (app : App Model Msg) (init : Model × Cmd Msg)
    (u : Model → Msg → Model × Cmd Msg) (onHydrate : Model → Cmd Msg) : App Model Msg :=
  { app with init := init, update := u, onHydrate := onHydrate }

def App.liftModel {Model Model' Msg : Type}
    (embed : Model → Model') (proj : Model' → Model)
    (hproj : ∀ m, proj (embed m) = m)
    (u : Model' → Msg → Model' × Cmd Msg)
    (app : App Model Msg) : App Model' Msg where
  init           := (embed app.init.1, app.init.2)
  update         := u
  template       := app.template.mapScope proj
  onUrlChange    := app.onUrlChange
  onSession      := app.onSession
  onHydrate      := fun st => app.onHydrate (proj st)
  locals         := app.locals
  onPort         := app.onPort
  dehydrate      := fun st => app.dehydrate (proj st)
  rehydrate      := fun raw => (app.rehydrate raw).map embed
  styles         := app.styles
  stylesheets    := app.stylesheets
  headFor        := fun st => app.headFor (proj st)
  ssrStatus      := fun st => app.ssrStatus (proj st)
  valid_view     := fun st => by rw [View.render_mapScope]; exact app.valid_view (proj st)
  dehydrate_view := fun st st' h => by
    simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨m', hm', rfl⟩
    simp only [View.render_mapScope, hproj]
    exact app.dehydrate_view (proj st) m' hm'

def App.withStylesheets (sheets : List String) (app : App Model Msg) : App Model Msg :=
  { app with stylesheets := app.stylesheets ++ sheets }

def App.withExtraStyles (extra : List Style) (app : App Model Msg) : App Model Msg :=
  { app with styles := extra ++ app.styles }

defAppProjSimps App.withStylesheets (sheets : List String) (app : App Model Msg) =>
  App.withStylesheets sheets app preserves app

defAppProjSimps App.withExtraStyles (extra : List Style) (app : App Model Msg) =>
  App.withExtraStyles extra app preserves app

end Internal

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

def const {Model : Type} (init : Model) : Dehydrate Model :=
  slice (α := Unit) init (fun _ => ()) (fun m _ => m)

@[simp] theorem full_project {Model : Type} [LawfulJson Model] (m : Model) :
    (full : Dehydrate Model).project m = m := rfl

@[simp] theorem slice_project {Model α : Type} [LawfulJson α] (init : Model)
    (get : Model → α) (set : Model → α → Model) (m : Model) :
    (slice init get set).project m = set init (get m) := rfl

@[simp] theorem const_project {Model : Type} (init m : Model) :
    (const init).project m = init := rfl

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

namespace Internal

def App.withDehydrateCore {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m) :
    App Model Msg :=
  { app with
    dehydrate      := d.dehydrate
    rehydrate      := d.rehydrate
    dehydrate_view := Dehydrate.dehydrate_view_of_project d app.template hview }

theorem App.dehydrate_preserves_of_project {Model Msg : Type} (Inv : Model → Prop)
    (app : App Model Msg) (proj : Model → Model)
    (hrt : ∀ m, app.rehydrate (app.dehydrate m) = some (proj m))
    (hproj : ∀ m, Inv m → Inv (proj m)) :
    ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m' := by
  intro m m' hm hr
  rw [hrt m] at hr
  cases hr
  exact hproj m hm

end Internal

set_option linter.unusedVariables false in
def App.guardRehydrateCore {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv]
    (app : App Model Msg)
    (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m') :
    App Model Msg :=
  { app with
    rehydrate := fun s =>
      match app.rehydrate s with
      | some m => if decide (Inv m) then some m else none
      | none   => none
    dehydrate_view := fun m m' h => by
      cases hr : app.rehydrate (app.dehydrate m) with
      | none => simp [hr] at h
      | some m0 =>
          simp only [hr] at h
          split at h <;> simp at h
          subst h
          exact app.dehydrate_view m m0 hr }

/-- Attaches dynamic per-route `<head>` metadata (title, description, meta tags, canonical URL, redirect) for SSR. -/
def App.withHead (f : Model → HeadMeta) (app : App Model Msg) : App Model Msg :=
  { app with headFor := f }

/-- Attaches a per-model SSR HTTP status code (default `200`; e.g. `404` on unknown routes or `302` redirects). -/
def App.withSsrStatus (f : Model → Nat) (app : App Model Msg) : App Model Msg :=
  { app with ssrStatus := f }

defAppProjSimps App.withHead (f : Model → HeadMeta) (app : App Model Msg) =>
  App.withHead f app preserves app

defAppProjSimps App.withSsrStatus (f : Model → Nat) (app : App Model Msg) =>
  App.withSsrStatus f app preserves app

end Qed
