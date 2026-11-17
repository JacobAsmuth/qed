import Qed.Runtime
import Qed.Proto

namespace Qed

inductive Resource (α : Type) where
  | idle
  | loading
  | ok (val : α)
  | failed (err : String)
deriving Inhabited, Repr

namespace Resource

def fetch [FromJson α] (url : String) (toMsg : Resource α → msg) : Cmd msg :=
  Cmd.getJson url (fun a => toMsg (.ok a)) (fun e => toMsg (.failed e))

def post [ToJson req] [FromJson resp] (url : String) (body : req) (toMsg : Resource resp → msg) : Cmd msg :=
  Cmd.postJson url (Json.render (toJson body)) (fun a => toMsg (.ok a)) (fun e => toMsg (.failed e))

def rpc [ToProto req] [FromProto resp] (url : String) (body : req) (toMsg : Resource resp → msg) : Cmd msg :=
  Cmd.rpc url body fun
    | .ok a    => toMsg (.ok a)
    | .error e => toMsg (.failed e)

def view (r : Resource α) (ready : α → Html msg)
    (loading : Html msg := .text "Loading…")
    (failed  : String → Html msg := fun e => .text e)
    (idle    : Html msg := .text "") : Html msg :=
  match r with
  | .idle     => idle
  | .loading  => loading
  | .ok a     => ready a
  | .failed e => failed e

def get? : Resource α → Option α
  | .ok a => some a
  | _     => none

def map (f : α → β) : Resource α → Resource β
  | .idle     => .idle
  | .loading  => .loading
  | .ok a     => .ok (f a)
  | .failed e => .failed e

def someOr (err : String := "Not found") : Resource (Option α) → Resource α
  | .ok (some a) => .ok a | .ok none => .failed err
  | .idle => .idle | .loading => .loading | .failed e => .failed e

@[simp] theorem validIn_view {α msg : Type} (ctx : HtmlCtx) (r : Resource α)
    (ready : α → Html msg) (loading : Html msg) (failed : String → Html msg) (idle : Html msg) :
    Html.validIn ctx (r.view ready loading failed idle) =
      match r with
      | .idle     => Html.validIn ctx idle
      | .loading  => Html.validIn ctx loading
      | .ok a     => Html.validIn ctx (ready a)
      | .failed e => Html.validIn ctx (failed e) := by
  cases r <;> rfl

end Resource

structure Cached (α : Type) where
  state : Resource α := .idle
  seen  : List (String × α) := []
deriving Inhabited

namespace Cached

def lookup (c : Cached α) (key : String) : Option α :=
  (c.seen.find? (·.1 == key)).map (·.2)

def put (c : Cached α) (issuedKey : String) (r : Resource α) (currentKey : String) : Cached α :=
  let seen := match r with
    | .ok a => ((issuedKey, a) :: c.seen.filter (·.1 != issuedKey)).take 32
    | _     => c.seen
  { state := if issuedKey == currentKey then r else c.state, seen := seen }

def view (c : Cached α) (ready : α → Html msg)
    (loading : Html msg := .text "Loading…")
    (failed  : String → Html msg := fun e => .text e)
    (idle    : Html msg := .text "") : Html msg :=
  c.state.view ready loading failed idle

@[simp] theorem validIn_view {α msg : Type} (ctx : HtmlCtx) (c : Cached α)
    (ready : α → Html msg) (loading : Html msg) (failed : String → Html msg) (idle : Html msg) :
    Html.validIn ctx (c.view ready loading failed idle) =
      Html.validIn ctx (c.state.view ready loading failed idle) := rfl

end Cached

structure Query (Model : Type) (Msg : Type) where
  key  : Model → String
  load : String → Model → Model × Cmd Msg
  idle : Model → Model

def Resource.query {Model Msg α : Type} [FromJson α]
    (key : Model → String) (url : String → String)
    (got : String → Resource α → Msg)
    (get : Model → Cached α) (set : Cached α → Model → Model) : Query Model Msg :=
  { key
    load := fun k m =>
      let c := get m
      let state := match c.lookup k with | some a => .ok a | none => .loading
      (set { c with state := state } m, Resource.fetch (url k) (got k))
    idle := fun m => set { get m with state := .idle } m }

def Query.wrap {Model Msg : Type} (qs : List (Query Model Msg))
    (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  fun old msg =>
    let (new, cmd) := update old msg
    qs.foldl (fun (mc : Model × Cmd Msg) q =>
      let kNew := q.key new
      if q.key old == kNew then mc
      else if kNew.isEmpty then (q.idle mc.1, mc.2)
      else
        let (m', c') := q.load kNew mc.1
        (m', .batch [mc.2, c'])) (new, cmd)

namespace Internal

def App.withQueries {Model Msg : Type} (qs : List (Query Model Msg))
    (app : App Model Msg) : App Model Msg :=
  Internal.App.setUpdate app (Query.wrap qs app.update)

@[simp] theorem App.withQueries_init (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).init = app.init := rfl
@[simp] theorem App.withQueries_update (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).update = Query.wrap qs app.update := rfl
@[simp] theorem App.withQueries_template (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).template = app.template := rfl

end Internal

#guard (match (({} : Cached Nat).put "a" (.ok 1) "b").state with | .idle => true | _ => false)
#guard ((({} : Cached Nat).put "a" (.ok 1) "b").lookup "a" == some 1)
#guard (match (({} : Cached Nat).put "a" (.ok 7) "a").state with | .ok 7 => true | _ => false)

instance [ToJson α] : ToJson (Resource α) := ⟨fun
  | .idle     => .obj [("t", .str "idle")]
  | .loading  => .obj [("t", .str "loading")]
  | .ok a     => .obj [("t", .str "ok"), ("v", toJson a)]
  | .failed e => .obj [("t", .str "failed"), ("e", .str e)]⟩

instance [FromJson α] : FromJson (Resource α) := ⟨fun j =>
  match (j.get? "t").bind (·.str?) with
  | some "idle"    => .ok .idle
  | some "loading" => .ok .loading
  | some "ok"      => match j.get? "v" with
                      | some v => (FromJson.fromJson v : Except String α).map .ok
                      | none   => .error "Resource.ok: missing 'v'"
  | some "failed"  => .ok (.failed (((j.get? "e").bind (·.str?)).getD ""))
  | _              => .error "expected a Resource (tagged object)"⟩

instance [LawfulJson α] : LawfulJson (Resource α) where
  depthBound := 1 + LawfulJson.depthBound α
  depth_toJson
    | .idle | .loading | .failed _ => Nat.le_add_right 1 _
    | .ok a => Nat.add_le_add_left (Json.maxObj_le_iff.2 (by
        intro kv hkv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hkv
        rcases hkv with rfl | rfl
        · exact Nat.zero_le _
        · exact LawfulJson.depth_toJson a)) 1
  fromJson_toJson
    | .idle | .loading | .failed _ => rfl
    | .ok a => by
        change (fromJson (toJson a) : Except String α).map Resource.ok = Except.ok (Resource.ok a)
        rw [LawfulJson.fromJson_toJson a]; rfl

instance [ToJson α] : NonNullJson (Resource α) :=
  ⟨fun | .idle | .loading | .ok _ | .failed _ => nofun⟩

private def encodeResourceFields [ToProto α] : Resource α → List (Nat × Proto.WireVal)
  | .idle     => [(1, .varint 0)]
  | .loading  => [(1, .varint 1)]
  | .ok a     => [(1, .varint 2), (2, ToProto.toProtoVal a)]
  | .failed e => [(1, .varint 3), (2, ToProto.toProtoVal e)]

private def decodeResourceFields [FromProto α] (fs : List (Nat × Proto.WireVal)) :
    Except String (Resource α) :=
  match Proto.lookupField 1 fs with
  | some (.varint 0) => .ok .idle
  | some (.varint 1) => .ok .loading
  | some (.varint 2) =>
      match Proto.lookupField 2 fs with
      | some w => (FromProto.fromProtoVal (α := α) w).map .ok
      | none   => .error "Resource.ok: missing field 2"
  | some (.varint 3) =>
      match Proto.lookupField 2 fs with
      | some w => (FromProto.fromProtoVal (α := String) w).map .failed
      | none   => .error "Resource.failed: missing field 2"
  | _ => .error "protobuf: invalid Resource tag"

instance [ToProto α]   : ToProto (Resource α)   := .ofFields encodeResourceFields
instance [FromProto α] : FromProto (Resource α) := .ofFields decodeResourceFields

instance [LawfulProto α] : LawfulProto (Resource α) :=
  .ofFields encodeResourceFields decodeResourceFields
    (by intro r kw h; cases r <;>
          (simp only [encodeResourceFields, List.mem_cons, List.not_mem_nil, or_false] at h
           rcases h with rfl | rfl <;> simp))
    (by intro r; cases r <;> simp [encodeResourceFields, decodeResourceFields, Proto.lookupField, Except.map])

/-- Overloaded callback adapter allowing generated `server` RPC client functions to accept either
    `Resource α → msg` or `Except String α → msg` with zero wrapper ceremony. -/
class RpcCallback (α : Type) (msg : outParam Type) (cb : Type) where
  adapt : cb → Except String α → msg

instance {α msg : Type} : RpcCallback α msg (Resource α → msg) :=
  ⟨fun f => fun | .ok a => f (.ok a) | .error e => f (.failed e)⟩

instance (priority := low) {α msg : Type} : RpcCallback (Option α) msg (Resource α → msg) :=
  ⟨fun f => fun | .ok (some a) => f (.ok a) | .ok none => f (.failed "Not found") | .error e => f (.failed e)⟩

instance {α msg : Type} : RpcCallback α msg (Except String α → msg) := ⟨id⟩

class ToResource (ρ : Type) (α : outParam Type) where
  toResource : ρ → Resource α

@[reducible] instance {α : Type} : ToResource (Resource α) α := ⟨id⟩
@[reducible] instance {α : Type} : ToResource (Cached α) α := ⟨Cached.state⟩

@[reducible] def Resource.awaitView {ρ α msg : Type} [ToResource ρ α]
    (src : ρ) (ready : α → Html msg) (loading : Html msg)
    (failed : String → Html msg) (idle : Html msg) : Html msg :=
  (ToResource.toResource src).view ready loading failed idle

/-! ## Async `Cached` Race-Safety & `Query.wrap` Theorems -/

theorem Cached.put_stale_preserves_state {α : Type} (c : Cached α)
    (issuedKey currentKey : String) (r : Resource α) (hne : issuedKey ≠ currentKey) :
    (c.put issuedKey r currentKey).state = c.state := by
  have hbeq : (issuedKey == currentKey) = false := beq_eq_false_iff_ne.2 hne
  simp [Cached.put, hbeq]

@[simp] theorem Cached.put_matching_updates_state {α : Type} (c : Cached α)
    (k : String) (r : Resource α) :
    (c.put k r k).state = r := by
  simp [Cached.put]

theorem Cached.put_non_ok_preserves_seen {α : Type} (c : Cached α)
    (k currentKey : String) (r : Resource α) (hnotOk : ∀ v, r ≠ .ok v) :
    (c.put k r currentKey).seen = c.seen := by
  cases r with
  | idle | loading | failed _ => rfl
  | ok v => exact False.elim (hnotOk v rfl)

theorem Cached.lookup_put_ok {α : Type} (c : Cached α)
    (k currentKey : String) (v : α) :
    (c.put k (.ok v) currentKey).lookup k = some v := by
  simp [Cached.lookup, Cached.put]

private theorem find_take_mem {α : Type} (p : α → Bool) :
    ∀ (n : Nat) (xs : List α) (a : α), (xs.take n).find? p = some a → xs.find? p = some a
  | 0, _, _, h => by simp at h
  | _ + 1, [], _, h => by simp at h
  | n + 1, x :: xs, a, h => by
      simp only [List.take_succ_cons, List.find?] at h ⊢
      cases hp : p x with
      | true => simpa [hp] using h
      | false =>
          simp only [hp] at h
          exact find_take_mem p n xs a h

private theorem find_filter_ne {α : Type} (p q : α → Bool) :
    ∀ (xs : List α) (a : α),
      (xs.filter q).find? p = some a →
      (∀ x, p x = true → q x = true) →
      xs.find? p = some a
  | [], _, h, _ => by simp at h
  | x :: xs, a, h, hqp => by
      simp only [List.filter_cons] at h
      cases hq : q x with
      | true =>
          simp only [hq, ↓reduceIte, List.find?] at h
          cases hp : p x with
          | true =>
              simp only [hp] at h
              cases h
              simp [List.find?, hp]
          | false =>
              simp only [hp] at h
              simp only [List.find?, hp]
              exact find_filter_ne p q xs a h hqp
      | false =>
          simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
          have hpF : p x = false := by
            cases hp : p x with
            | false => rfl
            | true => have := hqp x hp; simp [hq] at this
          simp only [List.find?, hpF]
          exact find_filter_ne p q xs a h hqp

theorem Cached.lookup_put_ok_sound {α : Type} (c : Cached α)
    (k k' currentKey : String) (v v' : α)
    (h : (c.put k (.ok v) currentKey).lookup k' = some v') :
    (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ c.lookup k' = some v') := by
  simp only [Cached.lookup, Cached.put, Option.map_eq_some_iff] at h
  rcases h with ⟨kv, hfind, rfl⟩
  have hmem := find_take_mem (fun x => x.1 == k') 32
    ((k, v) :: c.seen.filter (fun x => x.1 != k)) kv hfind
  simp only [List.find?] at hmem
  by_cases heq : k = k'
  · subst heq
    simp only [beq_self_eq_true] at hmem
    cases hmem
    exact .inl ⟨rfl, rfl⟩
  · have hbeq : (k == k') = false := beq_eq_false_iff_ne.2 heq
    simp only [hbeq] at hmem
    have horig := find_filter_ne (fun x => x.1 == k') (fun x => x.1 != k) c.seen kv hmem
      (fun x hx => by
        have hxk : x.1 = k' := eq_of_beq hx
        subst hxk
        exact bne_iff_ne.2 (fun h => heq h.symm))
    refine .inr ⟨fun h => heq h.symm, ?_⟩
    simp [Cached.lookup, horig]

theorem Cached.put_seen_length_le {α : Type} (c : Cached α) (k currentKey : String) (r : Resource α) :
    (c.put k r currentKey).seen.length ≤ Nat.max 32 c.seen.length := by
  cases r with
  | idle | loading | failed _ => exact Nat.le_max_right _ _
  | ok _ =>
      simp only [Cached.put]
      exact Nat.le_trans (List.length_take_le _ _) (Nat.le_max_left _ _)

theorem Query.wrap_preserves_inv {Model Msg : Type} (Inv : Model → Prop)
    (qs : List (Query Model Msg)) (upd : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg)
    (hold : Inv old)
    (hupd : ∀ m, Inv m → Inv (upd m msg).1)
    (hqs : ∀ q ∈ qs, (∀ m, Inv m → Inv (q.idle m)) ∧ (∀ k m, Inv m → Inv (q.load k m).1)) :
    Inv (Query.wrap qs upd old msg).1 := by
  unfold Query.wrap
  dsimp only
  let new := (upd old msg).1
  have h0 : Inv new := hupd old hold
  suffices hgen : ∀ (qs' : List (Query Model Msg)) (acc : Model × Cmd Msg),
      Inv acc.1 →
      (∀ q ∈ qs', (∀ m, Inv m → Inv (q.idle m)) ∧ (∀ k m, Inv m → Inv (q.load k m).1)) →
      Inv (qs'.foldl (fun (mc : Model × Cmd Msg) q =>
        let kNew := q.key new
        if q.key old == kNew then mc
        else if kNew.isEmpty then (q.idle mc.1, mc.2)
        else
          let (m', c') := q.load kNew mc.1
          (m', .batch [mc.2, c'])) acc).1 by
    exact hgen qs (upd old msg) h0 hqs
  intro qs'
  induction qs' with
  | nil => intro acc hacc _; exact hacc
  | cons q rest ih =>
      intro acc hacc hq
      rcases hq q (List.mem_cons_self ..) with ⟨hidle, hload⟩
      have hrest : ∀ q' ∈ rest, (∀ m, Inv m → Inv (q'.idle m)) ∧ (∀ k m, Inv m → Inv (q'.load k m).1) :=
        fun q' hq' => hq q' (List.mem_cons_of_mem q hq')
      apply ih _ _ hrest
      dsimp only
      split
      · exact hacc
      · split
        · exact hidle acc.1 hacc
        · exact hload _ acc.1 hacc

theorem Query.wrap_noop_when_keys_unchanged {Model Msg : Type}
    (qs : List (Query Model Msg)) (upd : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg)
    (hunchanged : ∀ q ∈ qs, q.key (upd old msg).1 = q.key old) :
    Query.wrap qs upd old msg = upd old msg := by
  unfold Query.wrap
  dsimp only
  induction qs with
  | nil => rfl
  | cons q rest ih =>
      have hq : q.key (upd old msg).1 = q.key old := hunchanged q (List.mem_cons_self ..)
      have hrest : ∀ q' ∈ rest, q'.key (upd old msg).1 = q'.key old :=
        fun q' h => hunchanged q' (List.mem_cons_of_mem q h)
      simp only [List.foldl_cons, hq, beq_self_eq_true, ↓reduceIte]
      exact ih hrest

end Qed
