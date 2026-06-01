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
