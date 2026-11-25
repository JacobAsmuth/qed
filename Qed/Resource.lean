import Qed.Resource.Basic
import Qed.Runtime.AppCore
import Qed.Server.Ensured
import Qed.Socket

namespace Qed

namespace Resource
variable {α : Type}
def fetch [FromJson α] (url : String) (toMsg : Resource α → msg) : Cmd msg := Cmd.getJson url (toMsg ∘ .ok) (toMsg ∘ .failed)
def post [ToJson req] [FromJson resp] (url : String) (body : req) (toMsg : Resource resp → msg) : Cmd msg :=
  Cmd.postJson url (Json.render (toJson body)) (toMsg ∘ .ok) (toMsg ∘ .failed)
def view (r : Resource α) (ready : α → Html msg) (loading : Html msg := .text "Loading…")
    (failed : String → Html msg := fun e => .text e) (idle : Html msg := .text "") : Html msg :=
  match r with | .idle => idle | .loading => loading | .ok a => ready a | .failed e => failed e
def get? : Resource α → Option α | .ok a => some a | _ => none
def getD (r : Resource α) (fallback : α) : α := (r.get?).getD fallback
def isOk : Resource α → Bool | .ok _ => true | _ => false
def isLoading : Resource α → Bool | .loading => true | _ => false
def map (f : α → β) : Resource α → Resource β
  | .idle => .idle | .loading => .loading | .ok a => .ok (f a) | .failed e => .failed e
def someOr (err : String := "Not found") : Resource (Option α) → Resource α
  | .ok (some a) => .ok a | .ok none => .failed err | .idle => .idle | .loading => .loading | .failed e => .failed e
def all (P : α → Prop) : Resource α → Prop | .ok a => P a | _ => True
@[simp] theorem all_idle (P : α → Prop) : Resource.all P .idle := trivial
@[simp] theorem all_loading (P : α → Prop) : Resource.all P .loading := trivial
@[simp] theorem all_failed (P : α → Prop) (e : String) : Resource.all P (.failed e) := trivial
@[simp] theorem all_ok (P : α → Prop) (a : α) : Resource.all P (.ok a) = P a := rfl
instance {P : α → Prop} [DecidablePred P] : DecidablePred (Resource.all P)
  | .ok a => inferInstanceAs (Decidable (P a)) | .idle | .loading | .failed _ => isTrue trivial
@[simp] theorem validIn_view {msg : Type} (ctx : HtmlCtx) (r : Resource α) (ready : α → Html msg)
    (loading : Html msg) (failed : String → Html msg) (idle : Html msg) :
    Html.validIn ctx (r.view ready loading failed idle) = match r with
      | .idle => Html.validIn ctx idle | .loading => Html.validIn ctx loading
      | .ok a => Html.validIn ctx (ready a) | .failed e => Html.validIn ctx (failed e) := by cases r <;> rfl
end Resource

namespace Cached
variable {α : Type}
def lookup (c : Cached α) (key : String) : Option α := (c.seen.find? (·.1 == key)).map (·.2)
def put (c : Cached α) (issuedKey : String) (r : Resource α) (currentKey : String) : Cached α :=
  { state := if issuedKey == currentKey then r else c.state
    seen  := match r with | .ok a => ((issuedKey, a) :: c.seen.filter (·.1 != issuedKey)).take 32 | _ => c.seen }
def activate (c : Cached α) (k : String) : Cached α := { c with state := (c.lookup k).elim .loading .ok }
def map (f : α → β) (c : Cached α) : Cached β :=
  { state := c.state.map f, seen := c.seen.map fun (k, v) => (k, f v) }
def getD (c : Cached α) (fallback : α) : α := c.state.getD fallback
def isOk (c : Cached α) : Bool := c.state.isOk
def isLoading (c : Cached α) : Bool := c.state.isLoading
def updateCurrent (c : Cached α) (currentKey : String) (f : α → α) : Cached α :=
  match c.state with
  | .ok a => c.put currentKey (.ok (f a)) currentKey
  | _ => c
def setKey (c : Cached α) (currentKey : String) (val : α) : Cached α :=
  c.put currentKey (.ok val) currentKey
def invalidateKey (c : Cached α) (currentKey : String) : Cached α :=
  { state := .idle, seen := c.seen.filter (·.1 != currentKey) }
def view (c : Cached α) (ready : α → Html msg) (loading : Html msg := .text "Loading…")
    (failed : String → Html msg := fun e => .text e) (idle : Html msg := .text "") : Html msg :=
  c.state.view ready loading failed idle
def all (P : α → Prop) (c : Cached α) : Prop := c.state.all P ∧ ∀ kv ∈ c.seen, P kv.2
instance {P : α → Prop} [DecidablePred P] : DecidablePred (Cached.all P) :=
  fun c => inferInstanceAs (Decidable (c.state.all P ∧ ∀ kv ∈ c.seen, P kv.2))
@[simp] theorem validIn_view {msg : Type} (ctx : HtmlCtx) (c : Cached α) (ready : α → Html msg)
    (loading : Html msg) (failed : String → Html msg) (idle : Html msg) :
    Html.validIn ctx (c.view ready loading failed idle) = Html.validIn ctx (c.state.view ready loading failed idle) := rfl
end Cached

structure Query (Model Msg : Type) where
  key  : Model → String
  load : String → Model → Model × Cmd Msg
  idle : Model → Model
def rpcQueryKey {Req : Type} [ToProto Req] : Option Req → String
  | none => "" | some req => "q:" ++ Proto.encodeHex (Proto.encode req)
theorem rpcQueryKey_injective {Req : Type} [LawfulProto Req] {a b : Option Req} (h : rpcQueryKey a = rpcQueryKey b) : a = b := by
  match a, b, h with
  | none, none, _ => rfl
  | some _, some _, h => exact congrArg some (Proto.encodeHex_encode_injective Proto.encode Proto.decode Proto.decode_encode h)
  | none, some _, h | some _, none, h => have := congrArg String.toList h; simp [rpcQueryKey] at this
def Resource.query {Model Msg α : Type} [FromJson α] (key : Model → String) (url : String → String)
    (got : String → Resource α → Msg) (get : Model → Cached α) (set : Cached α → Model → Model) : Query Model Msg :=
  { key, load := fun k m => (set ((get m).activate k) m, Resource.fetch (url k) (got k))
    idle := fun m => set { get m with state := .idle } m }
def Resource.rpcQuery {Model Msg Req α ResMsg : Type} [ToProto Req] (params? : Model → Option Req)
    (fetch : Model → (String → Resource ResMsg → Msg) → String → Option (Cmd Msg))
    (got : String → Resource ResMsg → Msg) (get : Model → Cached α) (set : Cached α → Model → Model) : Query Model Msg :=
  { key := fun m => rpcQueryKey (params? m)
    load := fun k m => (fetch m got k).elim (set { get m with state := .idle } m, .none) (set ((get m).activate k) m, ·)
    idle := fun m => set { get m with state := .idle } m }
def Query.boot {Model Msg : Type} (qs : List (Query Model Msg)) (ic : Model × Cmd Msg) : Model × Cmd Msg :=
  KeyedLifecycle.boot (·.key) (fun q k m => let r := q.load k m; (r.1, some r.2)) qs ic
def Query.wrap {Model Msg : Type} (qs : List (Query Model Msg)) (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  KeyedLifecycle.wrap (·.key) (fun q m => (q.idle m, none)) (fun q k m => let r := q.load k m; (r.1, some r.2)) qs update
def Query.liftWithProps {PModel PMsg CModel CMsg Props : Type}
    (getKey : PModel → String) (getProps : PModel → Option Props)
    (getState : PModel → CModel) (setState : CModel → PModel → PModel) (wrapMsg : CMsg → PMsg)
    (childQuery : Props → Query CModel CMsg) : Query PModel PMsg :=
  { key := fun pm =>
      let pk := getKey pm
      if pk.isEmpty then ""
      else match getProps pm with
        | none => ""
        | some p => let ck := (childQuery p).key (getState pm); if ck.isEmpty then "" else pk ++ "|" ++ ck,
    load := fun _ pm =>
      match getProps pm with
      | none => (pm, .none)
      | some p =>
          let q := childQuery p
          let ck := q.key (getState pm)
          let (cs', c) := q.load ck (getState pm)
          (setState cs' pm, Cmd.map wrapMsg c),
    idle := fun pm =>
      match getProps pm with
      | none => pm
      | some p => setState ((childQuery p).idle (getState pm)) pm }

namespace Internal
def App.withQueries {Model Msg : Type} (qs : List (Query Model Msg)) (app : App Model Msg) : App Model Msg :=
  Internal.App.setInitAndUpdate app (Query.boot qs app.init) (Query.wrap qs app.update)
defAppProjSimps App.withQueries (qs : List (Query Model Msg)) (app : App Model Msg) =>
    App.withQueries qs app with
  [init := Query.boot qs app.init, update := Query.wrap qs app.update,
   template := app.template, dehydrate := app.dehydrate, rehydrate := app.rehydrate]
end Internal

instance [ToJson α] : ToJson (Resource α) := ⟨fun
  | .idle => .obj [("t", .str "idle")] | .loading => .obj [("t", .str "loading")]
  | .ok a => .obj [("t", .str "ok"), ("v", toJson a)] | .failed e => .obj [("t", .str "failed"), ("e", .str e)]⟩
instance [FromJson α] : FromJson (Resource α) := ⟨fun j => match j.strAt? "t" with
  | some "idle" => .ok .idle | some "loading" => .ok .loading
  | some "ok" => ((j.field "v").bind fromJson).map .ok | some "failed" => .ok (.failed (j.strAtD "e"))
  | _ => .error "expected a Resource (tagged object)"⟩
instance [LawfulJson α] : LawfulJson (Resource α) where
  depthBound := 1 + LawfulJson.depthBound α
  depth_toJson
    | .idle | .loading | .failed _ => Nat.le_add_right 1 _
    | .ok a => Nat.add_le_add_left (by simpa [Json.maxObj, Json.depth] using LawfulJson.depth_toJson a) 1
  fromJson_toJson
    | .idle | .loading | .failed _ => rfl
    | .ok a => by change (fromJson (toJson a) : Except String α).map Resource.ok = _; rw [LawfulJson.fromJson_toJson a]; rfl
instance [ToJson α] : NonNullJson (Resource α) := ⟨fun | .idle | .loading | .ok _ | .failed _ => nofun⟩
qed_equiv_codec% json [α] (Cached α, fun c => (c.state, c.seen), fun p : Resource α × List (String × α) => ⟨p.1, p.2⟩, fun ⟨_, _⟩ => rfl)
private def encodeResourceFields [ToProto α] : Resource α → List (Nat × Proto.WireVal)
  | .idle => [(1, .varint 0)] | .loading => [(1, .varint 1)]
  | .ok a => [(1, .varint 2), (2, ToProto.toProtoVal a)] | .failed e => [(1, .varint 3), (2, ToProto.toProtoVal e)]
private def decodeResourceFields [FromProto α] (fs : List (Nat × Proto.WireVal)) : Except String (Resource α) :=
  match Proto.lookupField 1 fs with
  | some (.varint 0) => .ok .idle | some (.varint 1) => .ok .loading
  | some (.varint 2) => (Proto.decodeFieldVal 2 fs "Resource.ok: missing field 2").map .ok
  | some (.varint 3) => (Proto.decodeFieldVal 2 fs "Resource.failed: missing field 2").map .failed
  | _ => .error "protobuf: invalid Resource tag"
qed_proto_fields% [α] (Resource α, encodeResourceFields, decodeResourceFields,
  by intro r kw h; cases r <;> (simp only [encodeResourceFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> simp),
  by intro r; cases r <;> simp [encodeResourceFields, decodeResourceFields, Proto.decodeFieldVal, Proto.lookupField, Except.map])

def Resource.stripEnsured {α : Type} {p : α → Prop} (r : Resource (Ensured α p)) : Resource α := r.map (·.val)
theorem Resource.all_stripEnsured_of_imp {α : Type} {P Q : α → Prop} {r : Resource (Ensured α P)}
    (h : ∀ a, P a → Q a) : (Resource.stripEnsured r).all Q := by cases r with | ok e => exact h e.val e.ok | _ => trivial
instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} : RpcCallback (Ensured α p) msg (Resource α → msg) :=
  ⟨fun | f, .ok e => f (.ok e.val) | f, .error s => f (.failed s)⟩
instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} : RpcCallback (Option (Ensured α p)) msg (Resource α → msg) :=
  ⟨fun | f, .ok (some e) => f (.ok e.val) | f, .ok none => f (.failed "Not found") | f, .error s => f (.failed s)⟩
instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} : RpcCallback (Option (Ensured α p)) msg (Resource (Option α) → msg) :=
  ⟨fun | f, .ok opt => f (.ok (opt.map Ensured.val)) | f, .error s => f (.failed s)⟩

class ToResource (ρ : Type) (α : outParam Type) where toResource : ρ → Resource α
@[reducible] instance {α : Type} : ToResource (Resource α) α := ⟨id⟩
@[reducible] instance {α : Type} : ToResource (Cached α) α := ⟨Cached.state⟩
@[reducible] def Resource.awaitView {ρ α msg : Type} [ToResource ρ α] (src : ρ) (ready : α → Html msg)
    (loading : Html msg) (failed : String → Html msg) (idle : Html msg) : Html msg :=
  (ToResource.toResource src).view ready loading failed idle
theorem Resource.validIn_view_intro {α msg : Type} (ctx : HtmlCtx) (r : Resource α) (ready : α → Html msg)
    (loading : Html msg) (failed : String → Html msg) (idle : Html msg) (hidle : Html.validIn ctx idle = true)
    (hload : Html.validIn ctx loading = true) (hready : ∀ a, Html.validIn ctx (ready a) = true)
    (hfail : ∀ e, Html.validIn ctx (failed e) = true) : Html.validIn ctx (r.view ready loading failed idle) = true := by
  cases r with | idle => exact hidle | loading => exact hload | ok a => exact hready a | failed e => exact hfail e
theorem Resource.validIn_awaitView_intro {ρ α msg : Type} [ToResource ρ α] (ctx : HtmlCtx) (src : ρ) (ready : α → Html msg)
    (loading : Html msg) (failed : String → Html msg) (idle : Html msg) (hidle : Html.validIn ctx idle = true)
    (hload : Html.validIn ctx loading = true) (hready : ∀ a, Html.validIn ctx (ready a) = true)
    (hfail : ∀ e, Html.validIn ctx (failed e) = true) : Html.validIn ctx (Resource.awaitView src ready loading failed idle) = true :=
  Resource.validIn_view_intro ctx (ToResource.toResource src) ready loading failed idle hidle hload hready hfail

section CachedProofs
variable {α : Type}
theorem Cached.put_stale_preserves_state (c : Cached α) (issuedKey currentKey : String) (r : Resource α) (hne : issuedKey ≠ currentKey) :
    (c.put issuedKey r currentKey).state = c.state := by simp [Cached.put, beq_eq_false_iff_ne.2 hne]
@[simp] theorem Cached.put_matching_updates_state (c : Cached α) (k : String) (r : Resource α) :
    (c.put k r k).state = r := by simp [Cached.put]
theorem Cached.put_non_ok_preserves_seen (c : Cached α) (k currentKey : String) (r : Resource α) (hnotOk : ∀ v, r ≠ .ok v) :
    (c.put k r currentKey).seen = c.seen := by cases r with | ok v => exact (hnotOk v rfl).elim | _ => rfl
theorem Cached.lookup_put_ok (c : Cached α) (k currentKey : String) (v : α) :
    (c.put k (.ok v) currentKey).lookup k = some v := by simp [Cached.lookup, Cached.put]
theorem Cached.lookup_put_ok_sound (c : Cached α) (k k' currentKey : String) (v v' : α)
    (h : (c.put k (.ok v) currentKey).lookup k' = some v') : (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ c.lookup k' = some v') := by
  simp only [Cached.lookup, Cached.put, Option.map_eq_some_iff] at h; rcases h with ⟨kv, hfind, rfl⟩
  have hmem : ((k, v) :: c.seen.filter (·.1 != k)).find? (·.1 == k') = some kv := by
    rw [← List.take_append_drop 32 ((k, v) :: _), List.find?_append, hfind]; rfl
  by_cases heq : k = k'
  · subst heq; simp only [List.find?, beq_self_eq_true, Option.some.injEq] at hmem; cases hmem; exact .inl ⟨rfl, rfl⟩
  · simp only [List.find?, beq_eq_false_iff_ne.2 heq, List.find?_filter] at hmem
    have hfn : (fun a : String × α => decide ((a.1 != k) = true ∧ (a.1 == k') = true)) = (·.1 == k') := funext fun x => by
      cases hx : (x.1 == k') <;> simp [bne_iff_ne]; exact fun h => heq (h ▸ eq_of_beq hx)
    exact .inr ⟨Ne.symm heq, by simp [Cached.lookup, hfn ▸ hmem]⟩
theorem Cached.put_seen_length_le (c : Cached α) (k currentKey : String) (r : Resource α) :
    (c.put k r currentKey).seen.length ≤ Nat.max 32 c.seen.length := by
  cases r with | ok _ => exact Nat.le_trans (List.length_take_le _ _) (Nat.le_max_left _ _) | _ => exact Nat.le_max_right _ _
@[simp] theorem Cached.all_empty (P : α → Prop) : ({} : Cached α).all P := ⟨trivial, fun _ h => nomatch h⟩
theorem Cached.lookup_of_all {P : α → Prop} {c : Cached α} {k : String} {a : α} (hall : c.all P) (hlk : c.lookup k = some a) : P a := by
  simp only [Cached.lookup, Option.map_eq_some_iff] at hlk; rcases hlk with ⟨kv, hfind, rfl⟩; exact hall.2 kv (List.mem_of_find?_eq_some hfind)
theorem Cached.all_put {P : α → Prop} {c : Cached α} {k currentKey : String} {r : Resource α} (hall : c.all P) (hr : r.all P) :
    (c.put k r currentKey).all P :=
  ⟨by dsimp only [Cached.put]; split <;> first | exact hr | exact hall.1, fun kv hkv => by
    cases r with
    | ok _ => rcases List.mem_cons.1 (List.mem_of_mem_take hkv) with rfl | hflt
              · exact hr
              · exact hall.2 kv (List.mem_filter.1 hflt).1
    | _ => exact hall.2 kv hkv⟩
theorem Cached.all_lookup_state {P : α → Prop} {c : Cached α} {k : String} (hall : c.all P) : (c.activate k).all P :=
  ⟨by dsimp only [Cached.activate]; cases hlk : c.lookup k with | none => trivial | some a => exact Cached.lookup_of_all (P := P) hall hlk, hall.2⟩
theorem Cached.all_setKey {P : α → Prop} {c : Cached α} {k : String} {v : α} (hall : c.all P) (hv : P v) :
    (c.setKey k v).all P := Cached.all_put hall hv
theorem Cached.all_updateCurrent {P : α → Prop} {c : Cached α} {k : String} {f : α → α} (hall : c.all P)
    (hf : ∀ a, P a → P (f a)) : (c.updateCurrent k f).all P := by
  unfold Cached.updateCurrent; cases hs : c.state with
  | ok a => have h1 := hall.1; rw [hs] at h1; exact Cached.all_put hall (hf a h1)
  | _ => exact hall
theorem Cached.all_invalidateKey {P : α → Prop} {c : Cached α} {k : String} (hall : c.all P) :
    (c.invalidateKey k).all P :=
  ⟨trivial, fun kv hkv => hall.2 kv (List.mem_filter.1 hkv).1⟩
end CachedProofs

section QueryProofs
variable {Model Msg : Type}
theorem Query.boot_preserves_inv (Inv : Model → Prop) (qs : List (Query Model Msg)) (ic : Model × Cmd Msg) (hinit : Inv ic.1)
    (hqs : ∀ q ∈ qs, ∀ k m, Inv m → Inv (q.load k m).1) : Inv (Query.boot qs ic).1 :=
  KeyedLifecycle.boot_preserves_inv Inv _ _ qs ic hinit hqs
theorem Query.wrap_preserves_inv (Inv : Model → Prop) (qs : List (Query Model Msg)) (upd : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg) (hold : Inv old) (hupd : ∀ m, Inv m → Inv (upd m msg).1)
    (hqs : ∀ q ∈ qs, (∀ m, Inv m → Inv (q.idle m)) ∧ (∀ k m, Inv m → Inv (q.load k m).1)) : Inv (Query.wrap qs upd old msg).1 :=
  KeyedLifecycle.wrap_preserves_inv Inv _ _ _ qs upd old msg (hupd old hold) (fun q hq => (hqs q hq).1) (fun q hq => (hqs q hq).2)
theorem Query.wrap_noop_when_keys_unchanged (qs : List (Query Model Msg)) (upd : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg) (hunchanged : ∀ q ∈ qs, q.key (upd old msg).1 = q.key old) : Query.wrap qs upd old msg = upd old msg := by
  unfold Query.wrap; exact KeyedLifecycle.wrap_noop_when_keys_unchanged _ _ _ qs upd old msg fun q hq => (hunchanged q hq).symm
end QueryProofs
end Qed
