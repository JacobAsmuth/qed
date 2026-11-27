import Qed.Runtime.Cmd
import Qed.Runtime.LocalCore
import Qed.Render
import Qed.View.Core
import Qed.Router.Basic

namespace Qed

structure HeadMeta where
  (title description : Option String := none) (metaTags : List (String × String) := []) (canonical redirect : Option String := none)
deriving Inhabited, DecidableEq

structure App (Model Msg : Type) where
  private mk ::
  (init : Model × Cmd Msg) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg)
  (onUrlChange : Option (String → Msg) := none) (onSession : Option (Option String → Msg) := none)
  (onHydrate : Model → Cmd Msg := fun _ => .none) (locals : List LocalDef := [])
  (onPort : Option (String → String → Option Msg) := none)
  (dehydrate : Model → String := fun _ => "") (rehydrate : String → Option Model := fun _ => none)
  (styles : List Style := []) (stylesheets : List String := [])
  (headFor : Model → HeadMeta := fun _ => {}) (ssrStatus : Model → Nat := fun _ => 200)
  (valid_view : ∀ m, Html.valid (View.render template m) = true)
  (dehydrate_view : ∀ m m', rehydrate (dehydrate m) = some m' → View.render template m' = View.render template m := by intro _ _ h; cases h)

def App.view (app : App Model Msg) (m : Model) : Html Msg := View.render app.template m

declare_syntax_cat appProjPair
syntax ident " := " term : appProjPair
macro "defAppProjSimps " pre:ident binders:bracketedBinder* " => " lhs:term " with " "[" pairs:appProjPair,* "]" : command => do
  let cmds ← pairs.getElems.mapM fun
    | `(appProjPair| $fld:ident := $rhs:term) => `(command| @[simp] theorem $(Lean.mkIdentFrom pre (pre.getId.appendAfter ("_" ++ fld.getId.eraseMacroScopes.toString))) $binders* : ($lhs).$fld = $rhs := rfl)
    | _ => Lean.Macro.throwUnsupported
  return ⟨Lean.mkNullNode cmds⟩
macro "defAppProjSimps " pre:ident binders:bracketedBinder* " => " lhs:term " preserves " app:ident : command =>
  `(command| defAppProjSimps $pre $binders* => $lhs with [init := ($app).init, update := ($app).update, template := ($app).template, dehydrate := ($app).dehydrate, rehydrate := ($app).rehydrate])

namespace Internal
def mkAppCore (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg) (start : Cmd Msg := .none)
    (locals : List LocalDef := []) (styles : List Style := []) (onPort : Option (String → String → Option Msg) := none)
    (onSession : Option (Option String → Msg) := none) (valid_view : ∀ m, Html.valid (View.render template m) = true) : App Model Msg :=
  { init := (init, start), update, template, locals, styles, onPort, onSession, valid_view }
@[noinline, nospecialize] def mkRoutedAppCore {R : Type} [Router R] [Inhabited R] (init : Model) (update : Model → Msg → Model × Cmd Msg) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := []) (styles : List Style := [])
    (onPort : Option (String → String → Option Msg) := none) (onSession : Option (Option String → Msg) := none)
    (valid_view : ∀ m, Html.valid (View.render template m) = true) : App Model Msg :=
  { mkAppCore init update template start locals styles onPort onSession valid_view with onUrlChange := some fun p => onRoute ((Router.fromURL p).getD default) }
def App.setInitAndUpdate (app : App Model Msg) (init : Model × Cmd Msg) (u : Model → Msg → Model × Cmd Msg) : App Model Msg := { app with init, update := u }
def App.setInitUpdateHydrate (app : App Model Msg) (init : Model × Cmd Msg) (u : Model → Msg → Model × Cmd Msg) (onHydrate : Model → Cmd Msg) : App Model Msg := { app with init, update := u, onHydrate }

@[noinline, nospecialize] def App.liftModel {Model Model' Msg : Type} (embed : Model → Model') (proj : Model' → Model)
    (hproj : ∀ m, proj (embed m) = m) (u : Model' → Msg → Model' × Cmd Msg) (app : App Model Msg) : App Model' Msg where
  init := (embed app.init.1, app.init.2); update := u; template := app.template.mapScope proj
  onUrlChange := app.onUrlChange; onSession := app.onSession; onHydrate := app.onHydrate ∘ proj
  locals := app.locals; onPort := app.onPort; dehydrate := app.dehydrate ∘ proj
  rehydrate := fun raw => (app.rehydrate raw).map embed; styles := app.styles; stylesheets := app.stylesheets
  headFor := app.headFor ∘ proj; ssrStatus := app.ssrStatus ∘ proj
  valid_view := fun st => by rw [View.render_mapScope]; exact app.valid_view (proj st)
  dehydrate_view := fun st st' h => by rcases Option.map_eq_some_iff.1 h with ⟨m', hm', rfl⟩; simp only [View.render_mapScope, hproj]; exact app.dehydrate_view (proj st) m' hm'

def App.withStylesheets (sheets : List String) (app : App Model Msg) : App Model Msg := { app with stylesheets := app.stylesheets ++ sheets }
def App.withExtraStyles (extra : List Style) (app : App Model Msg) : App Model Msg := { app with styles := extra ++ app.styles }
defAppProjSimps App.withStylesheets (sheets : List String) (app : App Model Msg) => App.withStylesheets sheets app preserves app
defAppProjSimps App.withExtraStyles (extra : List Style) (app : App Model Msg) => App.withExtraStyles extra app preserves app
end Internal

structure Dehydrate (Model : Type) where
  (project : Model → Model := id) (dehydrate : Model → String) (rehydrate : String → Option Model)
  (round_trip : ∀ m, rehydrate (dehydrate m) = some (project m))

namespace Dehydrate
@[noinline, nospecialize] private def parseLawful (α : Type) [LawfulJson α] (s : String) : Option α := ((Json.parse s (max 64 (LawfulJson.depthBound α))).bind fromJson).toOption
private theorem parseLawful_render {α : Type} [LawfulJson α] (a : α) : parseLawful α (Json.render (toJson a)) = some a := by
  simp [parseLawful, LawfulJson.parse_render_toJson a (Nat.le_max_right 64 _), Except.toOption]
@[noinline, nospecialize] def full {Model : Type} [LawfulJson Model] : Dehydrate Model := ⟨id, fun m => Json.render (toJson m), parseLawful Model, parseLawful_render⟩
@[noinline, nospecialize] def slice {Model α : Type} [LawfulJson α] (init : Model) (get : Model → α) (set : Model → α → Model) : Dehydrate Model :=
  ⟨fun m => set init (get m), fun m => Json.render (toJson (get m)), fun s => (parseLawful α s).map (set init), fun m => by simp [parseLawful_render]⟩
@[noinline, nospecialize] def const {Model : Type} (init : Model) : Dehydrate Model := slice (α := Unit) init (fun _ => ()) (fun m _ => m)
@[simp] theorem full_project {Model : Type} [LawfulJson Model] (m : Model) : (full : Dehydrate Model).project m = m := rfl
@[simp] theorem slice_project {Model α : Type} [LawfulJson α] (init : Model) (get : Model → α) (set : Model → α → Model) (m : Model) : (slice init get set).project m = set init (get m) := rfl
@[simp] theorem const_project {Model : Type} (init m : Model) : (const init).project m = init := rfl
theorem dehydrate_view_of_project {Model Msg : Type} (d : Dehydrate Model) (tmpl : View Model Msg)
    (hproj : ∀ m, View.render tmpl (d.project m) = View.render tmpl m) :
    ∀ m m', d.rehydrate (d.dehydrate m) = some m' → View.render tmpl m' = View.render tmpl m := fun m m' h => by rw [d.round_trip m] at h; cases h; exact hproj m
end Dehydrate

namespace Internal
@[noinline, nospecialize] def App.withDehydrateCore {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg)
    (hview : ∀ m, View.render app.template (d.project m) = View.render app.template m) : App Model Msg :=
  { app with dehydrate := d.dehydrate, rehydrate := d.rehydrate, dehydrate_view := Dehydrate.dehydrate_view_of_project d app.template hview }
theorem App.dehydrate_preserves_of_project {Model Msg : Type} (Inv : Model → Prop) (app : App Model Msg) (proj : Model → Model)
    (hrt : ∀ m, app.rehydrate (app.dehydrate m) = some (proj m)) (hproj : ∀ m, Inv m → Inv (proj m)) :
    ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m' := fun m m' hm hr => by rw [hrt m] at hr; cases hr; exact hproj m hm
end Internal

theorem App.guardRehydrate_step_eq_some {Model : Type} (Inv : Model → Prop) [DecidablePred Inv] (rehydrate : String → Option Model) {raw : String} {m' : Model}
    (h : (match rehydrate raw with | some m => if decide (Inv m) then some m else none | none => none) = some m') : rehydrate raw = some m' ∧ Inv m' := by
  cases hr : rehydrate raw with | none => simp [hr] at h | some m => simp only [hr] at h; split at h <;> simp at h; subst h; exact ⟨rfl, of_decide_eq_true ‹_›⟩

set_option linter.unusedVariables false in
@[noinline, nospecialize] def App.guardRehydrateCore {Model Msg : Type} (Inv : Model → Prop) [DecidablePred Inv] (app : App Model Msg)
    (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m') : App Model Msg :=
  { app with rehydrate := fun s => match app.rehydrate s with | some m => if decide (Inv m) then some m else none | none => none
             dehydrate_view := fun m m' h => app.dehydrate_view m m' (App.guardRehydrate_step_eq_some Inv app.rehydrate h).1 }

def App.withHead (f : Model → HeadMeta) (app : App Model Msg) : App Model Msg := { app with headFor := f }
def App.withSsrStatus (f : Model → Nat) (app : App Model Msg) : App Model Msg := { app with ssrStatus := f }
defAppProjSimps App.withHead (f : Model → HeadMeta) (app : App Model Msg) => App.withHead f app preserves app
defAppProjSimps App.withSsrStatus (f : Model → Nat) (app : App Model Msg) => App.withSsrStatus f app preserves app

namespace KeyedLifecycle
def composeKey {PModel CModel Props : Type} (getKey : PModel → String) (getProps : PModel → Option Props)
    (getState : PModel → CModel) (childKey : Props → CModel → String) (pm : PModel) : String :=
  let pk := getKey pm
  if pk.isEmpty then "" else match getProps pm with
    | none => "" | some p => let ck := childKey p (getState pm); if ck.isEmpty then "" else pk ++ "|" ++ ck
end KeyedLifecycle
end Qed
