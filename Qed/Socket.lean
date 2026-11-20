import Qed.Socket.Basic
import Qed.Runtime.AppCore

namespace Qed

/-! ## Reactive WebSocket Subscriptions (`Subscription`) & Formal Lifecycle Guarantees -/

/-- A reactive, key-driven WebSocket subscription attached to a component `App`.
    When `key m` is empty, the subscription is inactive; whenever `key` changes across
    state transitions (e.g., route change or logout), the runtime automatically unsubscribes
    or replaces the active subscription with a fresh `subId`. -/
structure Subscription (Model Msg : Type) where
  slot     : String
  key      : Model → String
  openCmd  : String → Model → Option (Cmd Msg)
  closeCmd : Cmd Msg
  onClose  : Model → Model := id

namespace Subscription

/-- Starts any subscriptions whose initial key is non-empty on non-SSR client boot. -/
def boot {Model Msg : Type} (subs : List (Subscription Model Msg))
    (ic : Model × Cmd Msg) : Model × Cmd Msg :=
  subs.foldl (fun (mc : Model × Cmd Msg) s =>
    let k0 := s.key mc.1
    if k0.isEmpty then mc
    else
      match s.openCmd k0 mc.1 with
      | some c => (mc.1, .batch [mc.2, c])
      | none   => mc) ic

/-- Starts active subscriptions after SSR rehydration on the browser client. -/
def hydrateCmds {Model Msg : Type} (subs : List (Subscription Model Msg)) (m : Model) : Cmd Msg :=
  .batch <| subs.filterMap fun s =>
    let k := s.key m
    if k.isEmpty then none else s.openCmd k m

/-- Wraps `App.update` to diff subscription keys across every transition:
    unchanged keys are a guaranteed no-op; cleared keys emit `closeCmd` and reset status;
    new keys emit `openCmd` (which atomically supersedes the prior `subId` in the host). -/
def wrap {Model Msg : Type} (subs : List (Subscription Model Msg))
    (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  fun old msg =>
    let (new, cmd) := update old msg
    subs.foldl (fun (mc : Model × Cmd Msg) s =>
      let kNew := s.key mc.1
      if s.key old == kNew then mc
      else if kNew.isEmpty then (s.onClose mc.1, .batch [mc.2, s.closeCmd])
      else
        match s.openCmd kNew mc.1 with
        | some c => (mc.1, .batch [mc.2, c])
        | none   => (s.onClose mc.1, .batch [mc.2, s.closeCmd])) (new, cmd)

theorem boot_state_eq {Model Msg : Type} (subs : List (Subscription Model Msg))
    (ic : Model × Cmd Msg) :
    (boot subs ic).1 = ic.1 := by
  induction subs generalizing ic with
  | nil => rfl
  | cons s rest ih =>
      simp only [boot, List.foldl_cons] at ih ⊢
      split
      · exact ih ic
      · cases s.openCmd (s.key ic.1) ic.1 with
        | none   => exact ih ic
        | some c => exact ih (ic.1, .batch [ic.2, c])

theorem boot_preserves_inv {Model Msg : Type} (P : Model → Prop)
    (subs : List (Subscription Model Msg)) (ic : Model × Cmd Msg)
    (hinit : P ic.1) :
    P (boot subs ic).1 := by
  rw [boot_state_eq]
  exact hinit

theorem wrap_preserves_inv {Model Msg : Type} (P : Model → Prop)
    (subs : List (Subscription Model Msg))
    (update : Model → Msg → Model × Cmd Msg)
    (hupd : ∀ m msg, P m → P (update m msg).1)
    (hclose : ∀ s ∈ subs, ∀ m, P m → P (s.onClose m)) :
    ∀ m msg, P m → P (wrap subs update m msg).1 := by
  intro old msg hm
  unfold wrap
  have h0 : P (update old msg).1 := hupd old msg hm
  suffices ∀ (ss : List (Subscription Model Msg)) (mc : Model × Cmd Msg),
      (∀ s ∈ ss, ∀ m, P m → P (s.onClose m)) → P mc.1 →
      P (ss.foldl (fun (mc : Model × Cmd Msg) s =>
        let kNew := s.key mc.1
        if s.key old == kNew then mc
        else if kNew.isEmpty then (s.onClose mc.1, .batch [mc.2, s.closeCmd])
        else
          match s.openCmd kNew mc.1 with
          | some c => (mc.1, .batch [mc.2, c])
          | none   => (s.onClose mc.1, .batch [mc.2, s.closeCmd])) mc).1 by
    exact this subs (update old msg) hclose h0
  intro ss
  induction ss with
  | nil => intro mc _ hmc; exact hmc
  | cons s rest ih =>
      intro mc hcl hmc
      simp only [List.foldl_cons]
      have hrest : ∀ r ∈ rest, ∀ m, P m → P (r.onClose m) :=
        fun r hr => hcl r (List.mem_cons_of_mem s hr)
      have hs : ∀ m, P m → P (s.onClose m) := hcl s (List.mem_cons_self ..)
      split
      · exact ih mc hrest hmc
      · split
        · exact ih (s.onClose mc.1, _) hrest (hs mc.1 hmc)
        · cases s.openCmd (s.key mc.1) mc.1 with
          | some c => exact ih (mc.1, _) hrest hmc
          | none   => exact ih (s.onClose mc.1, _) hrest (hs mc.1 hmc)

theorem wrap_noop_when_keys_unchanged {Model Msg : Type}
    (subs : List (Subscription Model Msg))
    (update : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg)
    (hsame : ∀ s ∈ subs, s.key old = s.key (update old msg).1) :
    wrap subs update old msg = update old msg := by
  unfold wrap
  suffices ∀ (ss : List (Subscription Model Msg)) (mc : Model × Cmd Msg),
      (∀ s ∈ ss, s.key old = s.key mc.1) →
      ss.foldl (fun (mc : Model × Cmd Msg) s =>
        let kNew := s.key mc.1
        if s.key old == kNew then mc
        else if kNew.isEmpty then (s.onClose mc.1, .batch [mc.2, s.closeCmd])
        else
          match s.openCmd kNew mc.1 with
          | some c => (mc.1, .batch [mc.2, c])
          | none   => (s.onClose mc.1, .batch [mc.2, s.closeCmd])) mc = mc by
    exact this subs (update old msg) hsame
  intro ss
  induction ss with
  | nil => intro mc _; rfl
  | cons s rest ih =>
      intro mc hall
      simp only [List.foldl_cons]
      have hs : (s.key old == s.key mc.1) = true := beq_iff_eq.2 (hall s (List.mem_cons_self ..))
      simp only [hs, ↓reduceIte]
      exact ih mc (fun r hr => hall r (List.mem_cons_of_mem s hr))

end Subscription

namespace Internal

def App.withSubscriptions {Model Msg : Type} (subs : List (Subscription Model Msg))
    (app : App Model Msg) : App Model Msg :=
  Internal.App.setInitUpdateHydrate app
    (Subscription.boot subs app.init)
    (Subscription.wrap subs app.update)
    (fun m => .batch [app.onHydrate m, Subscription.hydrateCmds subs m])

@[simp] theorem App.withSubscriptions_init (subs : List (Subscription Model Msg)) (app : App Model Msg) :
    (App.withSubscriptions subs app).init = Subscription.boot subs app.init := rfl
@[simp] theorem App.withSubscriptions_update (subs : List (Subscription Model Msg)) (app : App Model Msg) :
    (App.withSubscriptions subs app).update = Subscription.wrap subs app.update := rfl
@[simp] theorem App.withSubscriptions_template (subs : List (Subscription Model Msg)) (app : App Model Msg) :
    (App.withSubscriptions subs app).template = app.template := rfl
@[simp] theorem App.withSubscriptions_dehydrate (subs : List (Subscription Model Msg)) (app : App Model Msg) :
    (App.withSubscriptions subs app).dehydrate = app.dehydrate := rfl
@[simp] theorem App.withSubscriptions_rehydrate (subs : List (Subscription Model Msg)) (app : App Model Msg) :
    (App.withSubscriptions subs app).rehydrate = app.rehydrate := rfl

end Internal


end Qed
