/-
  Qed.Ssr: the per-request server step, the framework half of `dist/ssr.mjs`.

  Server-side rendering is not code an app author writes. The app already declares its
  routes (`onRoute`) and its data needs (`queries := …`), so a server can *run* it for a
  request: dispatch the route, see which HTTP fetches the update requested, perform them,
  feed the results back through `update`, and render the settled model with the same
  verified `view` the browser runs, dehydrated into the page so the client adopts it
  without refetching.

  `App.ssrStep` is that run as one pure, total, resumable function, so the JS host stays
  a dumb loop. It replays the boot deterministically: initial model, route dispatch,
  then the command queue in discovery order. An HTTP `request` leaf consumes the next
  entry of `resultsJson` (the responses gathered so far, in the same discovery order);
  the first one with no response stops delivery, and everything still pending is returned
  as `{"need": [{method, url, body}, …]}`. The host fetches those, appends the responses,
  and calls again; replay is cheap (a few `update`s) and the round count is the data
  dependency depth. When nothing is pending the answer is `{"html": <the document>}`.

  Effects that only mean something in a browser (timers, storage, focus, sockets,
  streams, ports, clipboard, `pushUrl`, `now`) are dropped: the client re-runs nothing on
  a dehydrated load, and anything long-lived belongs to the live page, not the snapshot.

  Pure and total: termination is by (results left to consume, queue length), every
  delivery consumes a result. The transpiled export is generic (`Qed.App.ssrStep`); the
  host passes the app value exported next to it, so no per-app Lean is generated.
-/
import Qed.Runtime
import Qed.Json

namespace Qed

/-- One round of the SSR replay loop: walk the command queue in discovery order,
    delivering fetched responses to `request` leaves and collecting the ones that still
    need fetching. See the module docs for the protocol. -/
private def ssrDrain (app : App Model Msg) (results : Array (Bool × String)) :
    Model → List (Cmd Msg) → Nat → Array (String × String × String) →
    Model × Array (String × String × String)
  | m, [], _, needs => (m, needs)
  | m, c :: rest, i, needs =>
    match c with
    | .request method url body onResult =>
        if h : needs.isEmpty ∧ i < results.size then
          let (ok, text) := results[i]
          let (m', c') := app.update m (onResult (if ok then .ok text else .error text))
          ssrDrain app results m' (rest ++ Cmd.flatten c') (i + 1) needs
        else
          ssrDrain app results m rest i (needs.push (method, url, body))
    -- the queue holds leaves only (every enqueue goes through `Cmd.flatten`), so a
    -- `batch` cannot appear here; it falls into the drop case with the other non-HTTP
    -- effects, which is also what keeps the loop's termination measure decreasing
    | _ => ssrDrain app results m rest i needs
  termination_by _ q i _ => (results.size - i, q.length)

/-- Decode the host's gathered responses: a JSON array of `{ok, body}` in discovery
    order. Anything malformed reads as an empty list (the step then just reports what it
    needs). -/
private def ssrResults (resultsJson : String) : Array (Bool × String) :=
  match Json.parse resultsJson with
  | .ok (.arr es) => es.foldl (fun acc e =>
      match e with
      | .obj fields =>
          let ok := match fields.lookup "ok" with | some (.bool b) => b | _ => false
          match fields.lookup "body" with
          | some (.str b) => acc.push (ok, b)
          | _             => acc
      | _ => acc) #[]
  | _ => #[]

/-- The per-request step `dist/ssr.mjs` loops: replay the app's boot for `path` with the
    responses gathered so far, and answer either `{"need": […]}` (fetch these, call
    again) or `{"html": <full document>}` (the settled model rendered, with the
    dehydrated state embedded so the client starts from it). -/
def App.ssrStep (app : App Model Msg) (path title script resultsJson : String) : String :=
  let results := ssrResults resultsJson
  let m0 := app.init.1
  let (m1, cRoute) := match app.onUrlChange with
    | some f => app.update m0 (f path)
    | none   => (m0, .none)
  let queue := Cmd.flatten cRoute ++ Cmd.flatten app.init.2
  let (m, needs) := ssrDrain app results m1 queue 0 #[]
  if needs.isEmpty then
    Json.render (.obj [("html",
      .str (renderDocument title (app.renderModel m) script (state := app.dehydrate m)))])
  else
    Json.render (.obj [("need", .arr (needs.toList.map fun (method, url, body) =>
      .obj [("method", .str method), ("url", .str url), ("body", .str body)]))])

end Qed
