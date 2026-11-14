import Qed.Runtime.Cmd
import Qed.Runtime.Local
import Qed.Render
import Qed.View.Core
import Qed.Router

namespace Qed

structure App (Model : Type) (Msg : Type) where
  init        : Model × Cmd Msg
  update      : Model → Msg → Model × Cmd Msg
  template    : View Model Msg
  onUrlChange : Option (String → Msg) := none
  locals      : List LocalDef := []
  onPort      : Option (String → String → Option Msg) := none
  dehydrate   : Model → String := fun _ => ""
  rehydrate   : String → Option Model := fun _ => none
  styles      : List Style := []

def App.view (app : App Model Msg) (m : Model) : Html Msg := View.render app.template m

class ToStep (Model : Type) (Msg : Type) (α : Type) where
  toStep : α → Model × Cmd Msg
instance : ToStep Model Msg Model := ⟨fun m => (m, .none)⟩
instance : ToStep Model Msg (Model × Cmd Msg) := ⟨id⟩

@[simp] theorem ToStep.toStep_model (m : Model) :
    (ToStep.toStep m : Model × Cmd Msg) = (m, .none) := rfl
@[simp] theorem ToStep.toStep_pair (p : Model × Cmd Msg) :
    (ToStep.toStep p : Model × Cmd Msg) = p := rfl

def mkApp [ToStep Model Msg α] (init : Model) (update : Model → Msg → α)
    (template : View Model Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none) : App Model Msg :=
  { init := (init, start), update := fun m msg => ToStep.toStep (update m msg),
    template, locals, onPort }

def mkRoutedApp {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (update : Model → Msg → α) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none) : App Model Msg :=
  { mkApp init update template start locals onPort with
    onUrlChange := some (fun p => onRoute ((Router.fromURL p).getD default)) }

def App.addLocals (app : App Model Msg) (locals : List LocalDef) (styles : List Style := []) : App Model Msg :=
  { app with locals := LocalDef.dedupe (app.locals ++ locals), styles := app.styles ++ styles }

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

end Dehydrate

def App.withDehydrate {Model Msg : Type} (d : Dehydrate Model) (app : App Model Msg) : App Model Msg :=
  { app with dehydrate := d.dehydrate, rehydrate := d.rehydrate }

end Qed
