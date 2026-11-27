import Qed.Socket.Basic
import Qed.Runtime.AppCore

namespace Qed

namespace KeyedLifecycle
variable {Item Model Msg : Type}
@[reducible, simp] def applyRes (cmd : Cmd Msg) (res : Model × Option (Cmd Msg)) : Model × Cmd Msg :=
  (res.1, res.2.elim cmd (.batch [cmd, ·]))
@[reducible, simp] def boot (key : Item → Model → String) (onBoot : Item → String → Model → Model × Option (Cmd Msg))
    (items : List Item) (ic : Model × Cmd Msg) : Model × Cmd Msg :=
  items.foldl (fun mc it => let k0 := key it mc.1; if k0.isEmpty then mc else applyRes mc.2 (onBoot it k0 mc.1)) ic
@[reducible, simp] def wrap (key : Item → Model → String) (onLeave : Item → Model → Model × Option (Cmd Msg))
    (onEnter : Item → String → Model → Model × Option (Cmd Msg)) (items : List Item)
    (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  fun old msg => items.foldl (fun mc it =>
    let kNew := key it mc.1
    if key it old == kNew then mc else applyRes mc.2 (if kNew.isEmpty then onLeave it mc.1 else onEnter it kNew mc.1)) (update old msg)
private theorem foldl_preserves {α β : Type} (P : α → Prop) (f : α → β → α) :
    ∀ (xs : List β) (acc : α), P acc → (∀ x ∈ xs, ∀ a, P a → P (f a x)) → P (xs.foldl f acc)
  | [], _, hacc, _ => hacc
  | x :: rest, _, hacc, hf => foldl_preserves P f rest _ (hf x (.head _) _ hacc) fun y hy => hf y (.tail _ hy)
theorem boot_preserves_inv (Inv : Model → Prop) (key : Item → Model → String)
    (onBoot : Item → String → Model → Model × Option (Cmd Msg)) (items : List Item) (ic : Model × Cmd Msg)
    (hinit : Inv ic.1) (hboot : ∀ it ∈ items, ∀ k m, Inv m → Inv (onBoot it k m).1) : Inv (boot key onBoot items ic).1 :=
  foldl_preserves (Inv ·.1) _ items ic hinit fun it hit mc hmc => by dsimp only; split <;> first | exact hmc | exact hboot it hit _ _ hmc
theorem wrap_preserves_inv (Inv : Model → Prop) (key : Item → Model → String)
    (onLeave : Item → Model → Model × Option (Cmd Msg)) (onEnter : Item → String → Model → Model × Option (Cmd Msg))
    (items : List Item) (upd : Model → Msg → Model × Cmd Msg) (old : Model) (msg : Msg) (hacc : Inv (upd old msg).1)
    (hleave : ∀ it ∈ items, ∀ m, Inv m → Inv (onLeave it m).1) (henter : ∀ it ∈ items, ∀ k m, Inv m → Inv (onEnter it k m).1) :
    Inv (wrap key onLeave onEnter items upd old msg).1 :=
  foldl_preserves (Inv ·.1) _ items (upd old msg) hacc fun it hit mc hmc => by
    dsimp only; split; · exact hmc
    · dsimp only [applyRes]; split <;> first | exact hleave it hit _ hmc | exact henter it hit _ _ hmc
theorem wrap_noop_when_keys_unchanged (key : Item → Model → String)
    (onLeave : Item → Model → Model × Option (Cmd Msg)) (onEnter : Item → String → Model → Model × Option (Cmd Msg))
    (items : List Item) (upd : Model → Msg → Model × Cmd Msg) (old : Model) (msg : Msg)
    (hsame : ∀ it ∈ items, key it old = key it (upd old msg).1) : wrap key onLeave onEnter items upd old msg = upd old msg :=
  foldl_preserves (· = upd old msg) _ items (upd old msg) rfl fun it hit mc hmc => by subst hmc; simp only [beq_iff_eq.2 (hsame it hit), ↓reduceIte]
end KeyedLifecycle

structure Subscription (Model Msg : Type) where
  slot     : String
  key      : Model → String
  openCmd  : String → Model → Option (Cmd Msg)
  closeCmd : Cmd Msg
  onClose  : Model → Model := id

namespace Subscription
variable {Model Msg : Type}
def boot (subs : List (Subscription Model Msg)) (ic : Model × Cmd Msg) : Model × Cmd Msg :=
  KeyedLifecycle.boot (·.key) (fun s k m => (m, s.openCmd k m)) subs ic
def hydrateCmds (subs : List (Subscription Model Msg)) (m : Model) : Cmd Msg :=
  .batch <| subs.filterMap fun s => let k := s.key m; if k.isEmpty then none else s.openCmd k m
def wrap (subs : List (Subscription Model Msg)) (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  KeyedLifecycle.wrap (·.key) (fun s m => (s.onClose m, some s.closeCmd))
    (fun s k m => (s.openCmd k m).elim (s.onClose m, some s.closeCmd) (m, some ·)) subs update
theorem boot_state_eq (subs : List (Subscription Model Msg)) (ic : Model × Cmd Msg) : (boot subs ic).1 = ic.1 :=
  KeyedLifecycle.boot_preserves_inv (· = ic.1) _ _ subs ic rfl fun _ _ _ _ h => h
theorem boot_preserves_inv (P : Model → Prop) (subs : List (Subscription Model Msg)) (ic : Model × Cmd Msg) (hinit : P ic.1) : P (boot subs ic).1 :=
  boot_state_eq subs ic ▸ hinit
theorem wrap_preserves_inv (P : Model → Prop) (subs : List (Subscription Model Msg)) (update : Model → Msg → Model × Cmd Msg)
    (hupd : ∀ m msg, P m → P (update m msg).1) (hclose : ∀ s ∈ subs, ∀ m, P m → P (s.onClose m)) :
    ∀ m msg, P m → P (wrap subs update m msg).1 :=
  fun old msg hm => KeyedLifecycle.wrap_preserves_inv P _ _ _ subs update old msg (hupd old msg hm) hclose
    fun s hs k m hm => by cases s.openCmd k m <;> first | exact hclose s hs m hm | exact hm
theorem wrap_noop_when_keys_unchanged (subs : List (Subscription Model Msg)) (update : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg) (hsame : ∀ s ∈ subs, s.key old = s.key (update old msg).1) : wrap subs update old msg = update old msg := by
  unfold wrap; exact KeyedLifecycle.wrap_noop_when_keys_unchanged _ _ _ subs update old msg hsame
def liftWithProps {PModel PMsg CModel CMsg Props : Type}
    (getKey : PModel → String) (getProps : PModel → Option Props)
    (getState : PModel → CModel) (setState : CModel → PModel → PModel) (wrapMsg : CMsg → PMsg)
    (slot : String) (childKey : Props → CModel → String)
    (childOpen : String → Props → String → CModel → Option (Cmd CMsg))
    (childClose : String → Cmd CMsg) (childOnClose : CModel → CModel) : Subscription PModel PMsg :=
  { slot,
    key := KeyedLifecycle.composeKey getKey getProps getState childKey,
    openCmd := fun _ pm =>
      match getProps pm with
      | none => none
      | some p =>
          let ck := childKey p (getState pm)
          if ck.isEmpty then none else (childOpen slot p ck (getState pm)).map (Cmd.map wrapMsg),
    closeCmd := Cmd.map wrapMsg (childClose slot),
    onClose := fun pm => setState (childOnClose (getState pm)) pm }
end Subscription

namespace Internal
def App.withSubscriptions {Model Msg : Type} (subs : List (Subscription Model Msg)) (app : App Model Msg) : App Model Msg :=
  Internal.App.setInitUpdateHydrate app (Subscription.boot subs app.init) (Subscription.wrap subs app.update)
    (fun m => .batch [app.onHydrate m, Subscription.hydrateCmds subs m])
defAppProjSimps App.withSubscriptions (subs : List (Subscription Model Msg)) (app : App Model Msg) =>
    App.withSubscriptions subs app with
  [init := Subscription.boot subs app.init, update := Subscription.wrap subs app.update,
   template := app.template, dehydrate := app.dehydrate, rehydrate := app.rehydrate]
end Internal
end Qed
