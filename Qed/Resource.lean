/-
  Qed.Resource — remote data as a typed value, not a pile of flags.

  Almost every real screen fetches something and has to render "not started yet",
  "loading", "loaded", and "failed". Hand-rolled, that's an `Option (Except String α)`
  (or worse, parallel `loading : Bool` / `error : String` fields) plus a result message
  that splits success and failure, plus a four-way `match` in the view.

  `Resource α` is that state as one type, with two helpers:

  * `Resource.fetch url toMsg` — a `Cmd` that GETs + decodes the JSON and reports the
    outcome as a *single* message (`toMsg (.ok a)` / `toMsg (.failed e)`), so an app needs
    one message and one transition arm per resource, not two.
  * `r.view ready` — render the loaded value, with sensible defaults for the other three
    states (override `loading`/`failed`/`idle` as needed).

  Pure data over the verified `Cmd.getJson` (which decodes through `Qed.Json`); adds no
  axioms. The pattern: set the field to `.loading` in the transition that starts the fetch,
  fire `Resource.fetch`, and let its message drop the result back in.
-/
import Qed.Runtime

namespace Qed

/-- The lifecycle of a piece of fetched data. `idle` = not requested yet. -/
inductive Resource (α : Type) where
  | idle
  | loading
  | ok (val : α)
  | failed (err : String)
deriving Inhabited, Repr

namespace Resource

/-- A `Cmd` that GETs `url`, decodes the JSON to `α`, and reports the outcome as one
    message: `toMsg (.ok a)` on success, `toMsg (.failed e)` on a network/decode error. -/
def fetch [FromJson α] (url : String) (toMsg : Resource α → msg) : Cmd msg :=
  Cmd.getJson url (fun a => toMsg (.ok a)) (fun e => toMsg (.failed e))

/-- Render a resource: `ready` for the loaded value, with defaults for the other states. -/
def view (r : Resource α) (ready : α → Html msg)
    (loading : Html msg := .text "Loading…")
    (failed  : String → Html msg := fun e => .text e)
    (idle    : Html msg := .text "") : Html msg :=
  match r with
  | .idle     => idle
  | .loading  => loading
  | .ok a     => ready a
  | .failed e => failed e

/-- The loaded value, if any. -/
def get? : Resource α → Option α
  | .ok a => some a
  | _     => none

/-- Transform the loaded value, leaving the other states unchanged. -/
def map (f : α → β) : Resource α → Resource β
  | .idle     => .idle
  | .loading  => .loading
  | .ok a     => .ok (f a)
  | .failed e => .failed e

end Resource

/-- An SWR-style cache for one auto-refetched resource: the live `state` for the current key, plus
    values loaded on earlier visits keyed by the request key they came from. Revisiting a key shows
    its cached value immediately while it revalidates, and a response for a key you have navigated
    away from updates the cache but NOT the screen — so a slow earlier request can't overwrite a
    newer one (the stale-response race). Use it as a field in place of a bare `Resource α`, default
    `{}` (empty / `idle`), and render with `.view`. -/
structure Cached (α : Type) where
  state : Resource α := .idle
  seen  : List (String × α) := []
deriving Inhabited

namespace Cached

/-- The value loaded for `key` on a previous visit, if any. -/
def lookup (c : Cached α) (key : String) : Option α :=
  (c.seen.find? (·.1 == key)).map (·.2)

/-- Fold in a result fetched for `issuedKey`, given the key now displayed (`currentKey`). A
    successful value is always cached; the visible `state` is updated ONLY when the result is still
    current — a late response for a key the user already left is dropped from the view (race fix). -/
def put (c : Cached α) (issuedKey : String) (r : Resource α) (currentKey : String) : Cached α :=
  let seen := match r with
    | .ok a => ((issuedKey, a) :: c.seen.filter (·.1 != issuedKey)).take 32   -- cache (bounded)
    | _     => c.seen
  { state := if issuedKey == currentKey then r else c.state, seen := seen }

/-- Render the cached resource (delegates to `Resource.view` on the live `state`). -/
def view (c : Cached α) (ready : α → Html msg)
    (loading : Html msg := .text "Loading…")
    (failed  : String → Html msg := fun e => .text e)
    (idle    : Html msg := .text "") : Html msg :=
  c.state.view ready loading failed idle

end Cached

/-! ### Auto-refetch on dependency

A `Query` ties a `Cached` resource field to a *key* derived from the model. Attach a list of queries
to an app — `ui (queries := …)`, or `App.withQueries` — and the framework refetches whenever the key
changes: it shows the cached value (or `.loading`) and fires the fetch on a change to a non-empty
key, and clears the view to `.idle` when the key empties. You still write the one arm that folds the
result in (`Cached.put`); because `got` carries the issued key, a stale response is dropped.

Pure: the "previous key" is just the old model the wrapped `update` already receives, so there is no
subscription runtime and no driver change. On a fresh routed load the initial fetch fires through the
URL dispatch (the key goes from `""` to the route); a dehydrated load dispatches nothing, so it does
not refetch — the data is already in the model. -/

/-- A declared dependency: the model value a resource tracks (`key`) and how to (re)load it.
    Build with `Resource.query`; collect a list and pass to `ui (queries := …)`. -/
structure Query (Model : Type) (Msg : Type) where
  /-- The dependency as a string (stringify ids). `""` means "nothing to fetch". -/
  key  : Model → String
  /-- On a change to the non-empty key `k`: the model with its field set `.loading`, plus the
      fetch `Cmd`. -/
  load : String → Model → Model × Cmd Msg
  /-- On a change to an empty key: the model with its field set back to `.idle`. -/
  idle : Model → Model

/-- Declare an auto-refetching, cached resource. `key` is the model value it depends on (e.g. a
    route param), `url` builds the request, `got` is the result message — which carries the *issued
    key*, so the arm can drop a stale response via `Cached.put` — and `get`/`set` are the lens onto
    the `Cached α` field. On a key change it shows the cached value (revalidating) or `.loading` and
    fetches; on an empty key it clears the view to `.idle`, keeping the cache. -/
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

/-- Wrap a transition so each query refetches when its key changes. After the user's update,
    compare every query's key on the old vs new model: unchanged → leave it; emptied → set
    `.idle`; changed to a non-empty key → set `.loading` and append its fetch. -/
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

/-- Attach a list of auto-refetching queries to an app — the `ui (queries := …)` option expands
    to this. Wraps the app's `update` with `Query.wrap`; nothing else changes. -/
def App.withQueries {Model Msg : Type} (qs : List (Query Model Msg))
    (app : App Model Msg) : App Model Msg :=
  { app with update := Query.wrap qs app.update }

-- The cache + race-drop semantics, checked at build time:
-- a response for a key the user has navigated away from is cached but does NOT touch the view…
#guard (match (({} : Cached Nat).put "a" (.ok 1) "b").state with | .idle => true | _ => false)
#guard ((({} : Cached Nat).put "a" (.ok 1) "b").lookup "a" == some 1)
-- …while a response that is still current does update the view.
#guard (match (({} : Cached Nat).put "a" (.ok 7) "a").state with | .ok 7 => true | _ => false)

/-- JSON for a `Resource`, so a server can dehydrate fetched data into the page and the client
    rehydrate it (the `t` tag selects the case; `ok` carries the value, `failed` the error). -/
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

end Qed
