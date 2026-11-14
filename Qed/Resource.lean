import Qed.Runtime

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

def App.withQueries {Model Msg : Type} (qs : List (Query Model Msg))
    (app : App Model Msg) : App Model Msg :=
  { app with update := Query.wrap qs app.update }

@[simp] theorem App.withQueries_init (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).init = app.init := rfl
@[simp] theorem App.withQueries_update (qs : List (Query Model Msg)) (app : App Model Msg) :
    (App.withQueries qs app).update = Query.wrap qs app.update := rfl

open Lean in
syntax:max (name := queryForTerm) "Resource.queryFor " ident (ppSpace Lean.Parser.Term.argument)* : term

open Lean in
@[macro queryForTerm] def expandQueryFor : Macro := fun stx => do
  let field : Ident := ⟨stx[1]⟩
  let userArgs := stx[2].getArgs
  let base ← `(Resource.query (get := fun m => m.$field:ident) (set := fun c m => { m with $field:ident := c }))
  -- Put user-supplied arguments (`key`, `url`, `got`) before `get`/`set` so `Model` is inferred before `m.$field`.
  let baseArgs := base.raw[1].getArgs
  return Syntax.node .none ``Lean.Parser.Term.app #[base.raw[0], mkNullNode (userArgs ++ baseArgs)]

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

end Qed
