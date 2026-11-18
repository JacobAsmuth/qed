import Qed.Runtime
import Qed.Proto
import Lean

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

def all {α : Type} (P : α → Prop) : Resource α → Prop
  | .ok a => P a
  | _     => True

@[simp] theorem all_idle {α : Type} (P : α → Prop) : Resource.all P .idle := trivial
@[simp] theorem all_loading {α : Type} (P : α → Prop) : Resource.all P .loading := trivial
@[simp] theorem all_failed {α : Type} (P : α → Prop) (e : String) : Resource.all P (.failed e) := trivial
@[simp] theorem all_ok {α : Type} (P : α → Prop) (a : α) : Resource.all P (.ok a) = P a := rfl

instance {α : Type} {P : α → Prop} [DecidablePred P] : DecidablePred (Resource.all P)
  | .ok a                       => inferInstanceAs (Decidable (P a))
  | .idle | .loading | .failed _ => isTrue trivial

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

def activate (c : Cached α) (k : String) : Cached α :=
  { c with state := match c.lookup k with | some a => .ok a | none => .loading }

def view (c : Cached α) (ready : α → Html msg)
    (loading : Html msg := .text "Loading…")
    (failed  : String → Html msg := fun e => .text e)
    (idle    : Html msg := .text "") : Html msg :=
  c.state.view ready loading failed idle

def all {α : Type} (P : α → Prop) (c : Cached α) : Prop :=
  c.state.all P ∧ ∀ kv ∈ c.seen, P kv.2

instance {α : Type} {P : α → Prop} [DecidablePred P] : DecidablePred (Cached.all P) :=
  fun c => inferInstanceAs (Decidable (c.state.all P ∧ ∀ kv ∈ c.seen, P kv.2))

@[simp] theorem validIn_view {α msg : Type} (ctx : HtmlCtx) (c : Cached α)
    (ready : α → Html msg) (loading : Html msg) (failed : String → Html msg) (idle : Html msg) :
    Html.validIn ctx (c.view ready loading failed idle) =
      Html.validIn ctx (c.state.view ready loading failed idle) := rfl

end Cached

structure Query (Model : Type) (Msg : Type) where
  key  : Model → String
  load : String → Model → Model × Cmd Msg
  idle : Model → Model

/-- Deterministic, collision-free cache key for a typed RPC request (`LawfulProto`). -/
def rpcQueryKey {Req : Type} [ToProto Req] : Option Req → String
  | none     => ""
  | some req => "q:" ++ Proto.encodeHex (Proto.encode req)

theorem rpcQueryKey_injective {Req : Type} [LawfulProto Req] {a b : Option Req}
    (h : rpcQueryKey a = rpcQueryKey b) : a = b := by
  cases a <;> cases b
  · rfl
  · have := congrArg String.toList h; simp [rpcQueryKey] at this
  · have := congrArg String.toList h; simp [rpcQueryKey] at this
  · rename_i x y
    have hlist := congrArg String.toList h
    simp only [rpcQueryKey, String.toList_append] at hlist
    have hBytes := congrArg Proto.decodeHex (show Proto.encodeHex (Proto.encode x) = _ by
      simpa [String.ofList_toList] using congrArg String.ofList hlist)
    simp only [Proto.decodeHex_encodeHex] at hBytes
    have hDec := congrArg (Proto.decode (α := Req)) (Except.ok.inj hBytes)
    simp only [Proto.decode_encode] at hDec
    exact congrArg some (Except.ok.inj hDec)

def Resource.query {Model Msg α : Type} [FromJson α]
    (key : Model → String) (url : String → String)
    (got : String → Resource α → Msg)
    (get : Model → Cached α) (set : Cached α → Model → Model) : Query Model Msg :=
  { key
    load := fun k m => (set ((get m).activate k) m, Resource.fetch (url k) (got k))
    idle := fun m => set { get m with state := .idle } m }

/-- Server-backed reactive `Query` using collision-free `rpcQueryKey` and typed binary Protobuf RPCs. -/
def Resource.rpcQuery {Model Msg Req α ResMsg : Type} [ToProto Req]
    (params? : Model → Option Req)
    (fetch   : Model → (String → Resource ResMsg → Msg) → String → Option (Cmd Msg))
    (got     : String → Resource ResMsg → Msg)
    (get     : Model → Cached α)
    (set     : Cached α → Model → Model) : Query Model Msg :=
  { key  := fun m => rpcQueryKey (params? m)
    load := fun k m =>
      match fetch m got k with
      | some cmd => (set ((get m).activate k) m, cmd)
      | none     => (set { get m with state := .idle } m, .none)
    idle := fun m => set { get m with state := .idle } m }

/-- Triggers active queries at initial component boot (`init` / SSR entry). -/
def Query.boot {Model Msg : Type} (qs : List (Query Model Msg))
    (ic : Model × Cmd Msg) : Model × Cmd Msg :=
  qs.foldl (fun (mc : Model × Cmd Msg) q =>
    let k0 := q.key mc.1
    if k0.isEmpty then mc
    else
      let (m', c') := q.load k0 mc.1
      (m', .batch [mc.2, c'])) ic

def Query.wrap {Model Msg : Type} (qs : List (Query Model Msg))
    (update : Model → Msg → Model × Cmd Msg) : Model → Msg → Model × Cmd Msg :=
  fun old msg =>
    let (new, cmd) := update old msg
    qs.foldl (fun (mc : Model × Cmd Msg) q =>
      let kNew := q.key mc.1
      if q.key old == kNew then mc
      else if kNew.isEmpty then (q.idle mc.1, mc.2)
      else
        let (m', c') := q.load kNew mc.1
        (m', .batch [mc.2, c'])) (new, cmd)

namespace Internal

def App.withQueries {Model Msg : Type} (qs : List (Query Model Msg))
    (app : App Model Msg) : App Model Msg :=
  Internal.App.setInitAndUpdate app (Query.boot qs app.init) (Query.wrap qs app.update)

@[simp] theorem App.withQueries_init (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).init = Query.boot qs app.init := rfl
@[simp] theorem App.withQueries_update (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).update = Query.wrap qs app.update := rfl
@[simp] theorem App.withQueries_template (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).template = app.template := rfl
@[simp] theorem App.withQueries_dehydrate (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).dehydrate = app.dehydrate := rfl
@[simp] theorem App.withQueries_rehydrate (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).rehydrate = app.rehydrate := rfl

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

instance [ToJson α] : ToJson (Cached α) :=
  ⟨fun c => toJson (c.state, c.seen)⟩

instance [FromJson α] : FromJson (Cached α) :=
  ⟨fun j => (FromJson.fromJson (α := Resource α × List (String × α)) j).map fun p => ⟨p.1, p.2⟩⟩

instance [LawfulJson α] : LawfulJson (Cached α) where
  depthBound := LawfulJson.depthBound (Resource α × List (String × α))
  depth_toJson c := LawfulJson.depth_toJson (c.state, c.seen)
  fromJson_toJson c := by
    rcases c with ⟨st, sn⟩
    change (FromJson.fromJson (toJson (st, sn)) : Except String (Resource α × List (String × α))).map
      (fun p => Cached.mk p.1 p.2) = .ok ⟨st, sn⟩
    rw [LawfulJson.fromJson_toJson (st, sn)]
    rfl

instance [ToJson α] : NonNullJson (Cached α) := ⟨nofun⟩

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

/-! ## Proof-Carrying RPC Responses (`Ensured`) & Typed Domain Outcomes -/

/-- Value paired with an erased proof of a server `ensures` postcondition `p val`.
    Encodes identically on the Protobuf wire to `α` (`Proto.encode e = Proto.encode e.val`),
    while `FromProto` re-verifies `p` on untrusted bytes so `LawfulProto` holds zero-trust. -/
structure Ensured (α : Type) (p : α → Prop) where
  val : α
  ok  : p val

@[reducible, inline] instance {α : Type} {p : α → Prop} : Qed.Lang.QedVal (Ensured α p) α := ⟨Ensured.val⟩
@[simp] theorem QedVal.val_ensured {α : Type} {p : α → Prop} (e : Ensured α p) :
    Qed.Lang.QedVal.val e = e.val := rfl

@[reducible] instance {α : Type} {p : α → Prop} : CoeOut (Ensured α p) α := ⟨Ensured.val⟩
@[reducible] instance {α msg : Type} {p : α → Prop} [Coe α (Html msg)] : CoeHTCT (Ensured α p) (Html msg) :=
  ⟨fun e => (e.val : Html msg)⟩
@[reducible] instance {α : Type} {p : α → Prop} : CoeHTCT (Option (Ensured α p)) (Option α) :=
  ⟨Option.map Ensured.val⟩
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Ensured α p) := ⟨fun e => toString e.val⟩
instance {α : Type} {p : α → Prop} [BEq α] : BEq (Ensured α p) := ⟨fun a b => a.val == b.val⟩
instance {α : Type} {p : α → Prop} [Repr α] : Repr (Ensured α p) := ⟨fun e n => reprPrec e.val n⟩
instance {α : Type} {p : α → Prop} [DecidableEq α] : DecidableEq (Ensured α p) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => if h : a = b then isTrue (by cases h; rfl) else isFalse (by intro heq; injection heq; exact h ‹_›)

instance {α : Type} {p : α → Prop} [ToJson α] : ToJson (Ensured α p) := ⟨fun e => toJson e.val⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [FromJson α] : FromJson (Ensured α p) :=
  ⟨fun j => do let a ← (fromJson j : Except String α); if h : p a then .ok ⟨a, h⟩ else .error "failed RPC ensures postcondition"⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulJson α] : LawfulJson (Ensured α p) where
  depthBound := LawfulJson.depthBound α
  depth_toJson e := LawfulJson.depth_toJson e.val
  fromJson_toJson e := by
    rcases e with ⟨val, hok⟩
    change (fromJson (toJson val) : Except String α).bind
      (fun a => if h : p a then Except.ok (Ensured.mk a h) else Except.error _) = Except.ok (Ensured.mk val hok)
    rw [LawfulJson.fromJson_toJson val]; dsimp only [bind, Except.bind]; rw [dif_pos hok]
instance {α : Type} {p : α → Prop} [ToJson α] [NonNullJson α] : NonNullJson (Ensured α p) :=
  ⟨fun e => NonNullJson.toJson_ne_null e.val⟩

instance {α : Type} {p : α → Prop} [ToProto α] : ToProto (Ensured α p) where
  toProtoVal e := ToProto.toProtoVal e.val
  toProtoMsg e := ToProto.toProtoMsg e.val

instance {α : Type} {p : α → Prop} [DecidablePred p] [FromProto α] : FromProto (Ensured α p) where
  fromProtoVal w := do
    let a ← FromProto.fromProtoVal (α := α) w
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed RPC ensures postcondition"
  fromProtoMsg fs := do
    let a ← FromProto.fromProtoMsg (α := α) fs
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed RPC ensures postcondition"

instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulProto α] : LawfulProto (Ensured α p) where
  msg_tags_pos e := LawfulProto.msg_tags_pos e.val
  fromProtoVal_toProtoVal := fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoVal, FromProto.fromProtoVal, bind, Except.bind]
    rw [LawfulProto.fromProtoVal_toProtoVal val]
    dsimp only
    rw [dif_pos hok]
  fromProtoMsg_toProtoMsg := fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoMsg, FromProto.fromProtoMsg, bind, Except.bind]
    rw [LawfulProto.fromProtoMsg_toProtoMsg val]
    dsimp only
    rw [dif_pos hok]

def Resource.stripEnsured {α : Type} {p : α → Prop} (r : Resource (Ensured α p)) : Resource α :=
  r.map (·.val)

theorem Resource.all_stripEnsured_of_imp {α : Type} {P Q : α → Prop}
    {r : Resource (Ensured α P)} (h : ∀ a, P a → Q a) : (Resource.stripEnsured r).all Q := by
  cases r with | ok e => exact h e.val e.ok | _ => trivial

@[simp] theorem Proto.encode_ensured {α : Type} {p : α → Prop} [ToProto α] (e : Ensured α p) :
    Proto.encode e = Proto.encode e.val := rfl

/-- Typed application-level RPC failure transmitted cleanly inside binary Protobuf responses. -/
structure RpcDomainError (ε : Type) where
  tag     : ε
  message : String
deriving Inhabited, DecidableEq, Repr

instance {ε : Type} [ToJson ε] : ToJson (RpcDomainError ε) where
  toJson e := toJson (e.tag, e.message)

instance {ε : Type} [FromJson ε] : FromJson (RpcDomainError ε) where
  fromJson j := (FromJson.fromJson (α := ε × String) j).map fun p => RpcDomainError.mk p.1 p.2

instance {ε : Type} [LawfulJson ε] : LawfulJson (RpcDomainError ε) where
  depthBound := LawfulJson.depthBound (ε × String)
  depth_toJson e := LawfulJson.depth_toJson (e.tag, e.message)
  fromJson_toJson e := by
    rcases e with ⟨t, m⟩
    change (FromJson.fromJson (toJson (t, m)) : Except String (ε × String)).map
      (fun p => RpcDomainError.mk p.1 p.2) = .ok (RpcDomainError.mk t m)
    rw [LawfulJson.fromJson_toJson (t, m)]
    rfl

instance {ε : Type} [ToJson ε] : NonNullJson (RpcDomainError ε) := ⟨nofun⟩

instance {ε : Type} [ToProto ε]   : ToProto (RpcDomainError ε)   := .ofEquiv fun e => (e.tag, e.message)
instance {ε : Type} [FromProto ε] : FromProto (RpcDomainError ε) := .ofEquiv fun p : ε × String => RpcDomainError.mk p.1 p.2
instance {ε : Type} [LawfulProto ε] : LawfulProto (RpcDomainError ε) :=
  .ofEquiv (fun e => (e.tag, e.message)) (fun p => RpcDomainError.mk p.1 p.2) (fun ⟨_, _⟩ => rfl)

/-- Outcome of an RPC declared with typed `fail(.tag)` domain errors. -/
inductive RpcOutcome (ε : Type) (α : Type) where
  | ok     (val : α)
  | err    (tag : ε) (message : String)
  | failed (message : String)
deriving Inhabited, DecidableEq, Repr

/-- Outcome of an RPC without typed domain error tags. -/
inductive RpcSimpleOutcome (α : Type) where
  | ok     (val : α)
  | failed (message : String)
deriving Inhabited, DecidableEq, Repr

/-- Overloaded callback adapter allowing generated `server` RPC client functions to accept
    `Resource α → msg`, `RpcOutcome ε α → msg`, `RpcSimpleOutcome α → msg`, or `Except String α → msg`. -/
class RpcCallback (α : Type) (msg : outParam Type) (cb : Type) where
  adapt : cb → Except String α → msg

instance {α msg : Type} : RpcCallback α msg (Resource α → msg) :=
  ⟨fun f => fun | .ok a => f (.ok a) | .error e => f (.failed e)⟩

instance (priority := low) {α msg : Type} : RpcCallback (Option α) msg (Resource α → msg) :=
  ⟨fun f => fun | .ok (some a) => f (.ok a) | .ok none => f (.failed "Not found") | .error e => f (.failed e)⟩

instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} :
    RpcCallback (Ensured α p) msg (Resource α → msg) :=
  ⟨fun f => fun | .ok e => f (.ok e.val) | .error s => f (.failed s)⟩

instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} :
    RpcCallback (Option (Ensured α p)) msg (Resource α → msg) :=
  ⟨fun f => fun | .ok (some e) => f (.ok e.val) | .ok none => f (.failed "Not found") | .error s => f (.failed s)⟩

instance (priority := low) {α : Type} {p : α → Prop} {msg : Type} :
    RpcCallback (Option (Ensured α p)) msg (Resource (Option α) → msg) :=
  ⟨fun f => fun | .ok opt => f (.ok (opt.map Ensured.val)) | .error s => f (.failed s)⟩

instance {ε α msg : Type} :
    RpcCallback (Except (RpcDomainError ε) α) msg (RpcOutcome ε α → msg) :=
  ⟨fun f => fun
    | .ok (.ok a)    => f (.ok a)
    | .ok (.error d) => f (.err d.tag d.message)
    | .error s       => f (.failed s)⟩

instance {α msg : Type} : RpcCallback α msg (RpcSimpleOutcome α → msg) :=
  ⟨fun f => fun | .ok a => f (.ok a) | .error s => f (.failed s)⟩

instance (priority := low) {ε α β msg : Type} [RpcCallback α msg (Resource β → msg)] :
    RpcCallback (Except (RpcDomainError ε) α) msg (Resource β → msg) :=
  ⟨fun f => fun
    | .ok (.ok a)    => RpcCallback.adapt (α := α) f (.ok a)
    | .ok (.error d) => f (.failed d.message)
    | .error s       => f (.failed s)⟩

instance {α msg : Type} : RpcCallback α msg (Except String α → msg) := ⟨id⟩

/-! ## Persistent Server RPC Metadata Registry (`serverRegistry`) -/

structure ServerMethodInfo where
  name            : String
  paramNames      : Array Lean.Name := #[]
  paramCount      : Nat
  isReadOnly      : Bool
  isAsync         : Bool
  isFallible      : Bool
  isOption        : Bool
  hasClientReq    : Bool := false
  requiresAuth    : Bool := false
  clientReqConst  : Option Lean.Name := none
  clientReqLabel  : String := ""
  hasEnsures      : Bool := false
  ensPredConst    : Option Lean.Name := none
  domainErrTags   : Array String := #[]
  errTypeConst    : Option Lean.Name := none
  rawRpcConst     : Lean.Name := .anonymous
  outcomeConst    : Lean.Name := .anonymous
  paramTypeConsts : Array Lean.Name := #[]
deriving Inhabited, Repr

structure ServerInfo where
  serverName       : Lean.Name
  shortName        : String
  hasState         : Bool
  secrets          : Array String
  envVars          : Array (String × String × Option String)
  externalServices : Array (String × String)
  methods          : Array ServerMethodInfo
deriving Inhabited

initialize serverRegistry :
    Lean.SimplePersistentEnvExtension ServerInfo (Lean.NameMap ServerInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.serverName info) acc) {}
    addEntryFn := fun m info => m.insert info.serverName info
  }

/-- Resolves a `Server.fn` reference from a component (`Catalog.order`, `CloudBooks.Catalog.order`,
    or an `open Catalog` method name) against `serverRegistry`. -/
def lookupServerMethod? (env : Lean.Environment) (currNs : Lean.Name)
    (openDecls : List Lean.OpenDecl) (callName : Lean.Name) :
    Option (ServerInfo × ServerMethodInfo) :=
  let reg := serverRegistry.getState env
  let resolved := Lean.ResolveName.resolveGlobalName env {} currNs openDecls callName
  let byResolved := resolved.findSome? fun (fullConst, _) =>
    reg.toList.findSome? fun (_, srvInfo) =>
      srvInfo.methods.findSome? fun mInfo =>
        let pubConst := srvInfo.serverName ++ Lean.Name.mkSimple mInfo.name
        if fullConst == pubConst || fullConst == mInfo.rawRpcConst then some (srvInfo, mInfo)
        else none
  byResolved.orElse fun _ =>
    match callName with
    | .str srvPart mStr =>
        let srvClean := srvPart.eraseMacroScopes
        let cand1 := currNs ++ srvClean
        let srv? := (reg.find? cand1).orElse (fun _ => reg.find? srvClean)
          |>.orElse (fun _ => reg.toList.findSome? fun (_, info) =>
            if info.shortName == srvClean.toString then some info else none)
        srv?.bind fun srvInfo =>
          (srvInfo.methods.find? (·.name == mStr)).map (srvInfo, ·)
    | _ => none

class ToResource (ρ : Type) (α : outParam Type) where
  toResource : ρ → Resource α

@[reducible] instance {α : Type} : ToResource (Resource α) α := ⟨id⟩
@[reducible] instance {α : Type} : ToResource (Cached α) α := ⟨Cached.state⟩

@[reducible] def Resource.awaitView {ρ α msg : Type} [ToResource ρ α]
    (src : ρ) (ready : α → Html msg) (loading : Html msg)
    (failed : String → Html msg) (idle : Html msg) : Html msg :=
  (ToResource.toResource src).view ready loading failed idle

theorem Resource.validIn_view_intro {α msg : Type} (ctx : HtmlCtx) (r : Resource α)
    (ready : α → Html msg) (loading : Html msg) (failed : String → Html msg) (idle : Html msg)
    (hidle : Html.validIn ctx idle = true)
    (hload : Html.validIn ctx loading = true)
    (hready : ∀ a, Html.validIn ctx (ready a) = true)
    (hfail : ∀ e, Html.validIn ctx (failed e) = true) :
    Html.validIn ctx (r.view ready loading failed idle) = true := by
  cases r with
  | idle => exact hidle
  | loading => exact hload
  | ok a => exact hready a
  | failed e => exact hfail e

theorem Resource.validIn_awaitView_intro {ρ α msg : Type} [ToResource ρ α] (ctx : HtmlCtx)
    (src : ρ) (ready : α → Html msg) (loading : Html msg) (failed : String → Html msg) (idle : Html msg)
    (hidle : Html.validIn ctx idle = true)
    (hload : Html.validIn ctx loading = true)
    (hready : ∀ a, Html.validIn ctx (ready a) = true)
    (hfail : ∀ e, Html.validIn ctx (failed e) = true) :
    Html.validIn ctx (Resource.awaitView src ready loading failed idle) = true :=
  Resource.validIn_view_intro ctx (ToResource.toResource src) ready loading failed idle hidle hload hready hfail

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

@[simp] theorem Cached.all_empty {α : Type} (P : α → Prop) : ({} : Cached α).all P :=
  ⟨trivial, fun _ h => False.elim (List.not_mem_nil h)⟩

theorem Cached.lookup_of_all {α : Type} {P : α → Prop} {c : Cached α} {k : String} {a : α}
    (hall : c.all P) (hlk : c.lookup k = some a) : P a := by
  simp only [Cached.lookup, Option.map_eq_some_iff] at hlk
  rcases hlk with ⟨kv, hfind, rfl⟩
  exact hall.2 kv (List.mem_of_find?_eq_some hfind)

theorem Cached.all_put {α : Type} {P : α → Prop} {c : Cached α} {k currentKey : String} {r : Resource α}
    (hall : c.all P) (hr : r.all P) : (c.put k r currentKey).all P := by
  refine ⟨?_, ?_⟩
  · cases r <;> simp only [Cached.put] <;> split <;> first | exact hall.1 | exact hr
  · intro kv hkv
    cases r with
    | idle | loading | failed _ => exact hall.2 kv hkv
    | ok a =>
        simp only [Cached.put] at hkv
        have hmem := List.mem_of_mem_take hkv
        rcases List.mem_cons.1 hmem with rfl | hflt
        · exact hr
        · exact hall.2 kv (List.mem_filter.1 hflt).1

theorem Cached.all_lookup_state {α : Type} {P : α → Prop} {c : Cached α} {k : String}
    (hall : c.all P) : (c.activate k).all P := by
  refine ⟨?_, hall.2⟩
  dsimp only [Cached.activate]
  cases hlk : c.lookup k with
  | none => trivial
  | some a =>
      change P a
      exact Cached.lookup_of_all hall hlk

theorem Query.boot_preserves_inv {Model Msg : Type} (Inv : Model → Prop)
    (qs : List (Query Model Msg)) (ic : Model × Cmd Msg)
    (hinit : Inv ic.1)
    (hqs : ∀ q ∈ qs, ∀ k m, Inv m → Inv (q.load k m).1) :
    Inv (Query.boot qs ic).1 := by
  unfold Query.boot
  induction qs generalizing ic with
  | nil => exact hinit
  | cons q rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp only
        split
        · exact hinit
        · exact hqs q (List.mem_cons_self ..) _ _ hinit
      · intro q' hq'
        exact hqs q' (List.mem_cons_of_mem q hq')

theorem Query.wrap_preserves_inv {Model Msg : Type} (Inv : Model → Prop)
    (qs : List (Query Model Msg)) (upd : Model → Msg → Model × Cmd Msg)
    (old : Model) (msg : Msg)
    (hold : Inv old)
    (hupd : ∀ m, Inv m → Inv (upd m msg).1)
    (hqs : ∀ q ∈ qs, (∀ m, Inv m → Inv (q.idle m)) ∧ (∀ k m, Inv m → Inv (q.load k m).1)) :
    Inv (Query.wrap qs upd old msg).1 := by
  unfold Query.wrap
  dsimp only
  have hacc := hupd old hold
  generalize upd old msg = acc at hacc ⊢
  induction qs generalizing acc with
  | nil => exact hacc
  | cons q rest ih =>
      rcases hqs q (List.mem_cons_self ..) with ⟨hidle, hload⟩
      let hrest := fun q' hq' => hqs q' (List.mem_cons_of_mem q hq')
      simp only [List.foldl_cons]
      split
      · exact ih hrest acc hacc
      · split
        · exact ih hrest (_, _) (hidle acc.1 hacc)
        · exact ih hrest ((q.load (q.key acc.1) acc.1).1, Cmd.batch [acc.2, (q.load (q.key acc.1) acc.1).2])
            (hload (q.key acc.1) acc.1 hacc)

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
