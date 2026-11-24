import Qed
import Tests.CheckHelper
open Qed

namespace VerificationChecks

/-! ## 1A. Schema `example` & Vacuity Detection -/
schema OrderWithExample:
  name        : String where 1 <= name.length, name.length <= 40
  quantity    : Nat    where 1 <= quantity, quantity <= 10
  acceptTerms : Bool   where acceptTerms == true
  example validOrder: name = "Alice", quantity = 3, acceptTerms = true
  example maxOrder: name = "Bob", quantity = 10, acceptTerms = true
schema BoundedQty:
  quantity : Nat where 10 <= quantity, quantity <= 20
example : (∃ _x : OrderWithExample, True) ∧ (∃ _x : BoundedQty, True) ∧ Nonempty OrderWithExample ∧ Nonempty BoundedQty ∧
    OrderWithExample.validOrder.quantity.val = 3 ∧ OrderWithExample.maxOrder.quantity.val = 10 :=
  ⟨OrderWithExample.satisfiable, BoundedQty.satisfiable, inferInstance, inferInstance, rfl, rfl⟩
expect_err "Schema `UnsatRange` is unsatisfiable: field `quantity` has contradictory `where` constraints" in
schema UnsatRange:
  quantity : Nat where 10 <= quantity, quantity <= 5
expect_err "Schema `UnsatBool` is unsatisfiable: field `flag` has contradictory `where` constraints" in
schema UnsatBool:
  flag : Bool where flag == true, flag == false
expect_err "Schema `BadExampleVal` example `tooMany` failed `where` constraint on field `quantity`:\n  • value `99` does not satisfy `1 <= quantity, quantity <= 10`" in
schema BadExampleVal:
  name     : String where 1 <= name.length
  quantity : Nat    where 1 <= quantity, quantity <= 10
  example tooMany: name = "Alice", quantity = 99
expect_err "Schema `MissingExampleField` example `incomplete`: missing required field `quantity`" in
schema MissingExampleField:
  name     : String where 1 <= name.length
  quantity : Nat    where 1 <= quantity
  example incomplete: name = "Alice"

/-! ## 1B. Unified Component `example` (Concrete & Parametric Proofs) -/
component ReachCounter:
  state count : Nat = 0
  action inc(n: Nat): if count + n <= 10: count += n
  action reset: count = 0
  invariant bounded: count <= 10
  example canAdd5:    .inc(5) -> count == 5
  example canReach8:  .inc(5), .inc(3) -> count == 8
  example staysCap:   .inc(5), .inc(9) -> count == 5
  example addAny(n: Nat) where n <= 10:             .inc(n) -> count == n
  example addTwo(a: Nat, b: Nat) where a + b <= 10: .inc(a), .inc(b) -> count == a + b
  example addThenReset(n: Nat):                     .inc(n), .reset -> count == 0
  example ignoreOverflow(n: Nat) where n > 10:      .inc(n) -> count == 0
  view: <div><button onClick={.inc(1)}>Add</button><span>{count}</span></div>
example : (∃ s : ReachCounter.State, s.count ≤ 10 ∧ s.count = 5) ∧ (∀ n ≤ 10, ∃ s : ReachCounter.State, s.count ≤ 10 ∧ s.count = n) :=
  ⟨Qed.inv_nonvacuous_of_reachable ReachCounter.canAdd5 ReachCounter.bounded.1 ReachCounter.bounded.2,
   fun n h => Qed.inv_nonvacuous_of_reachable (ReachCounter.addAny n h) ReachCounter.bounded.1 ReachCounter.bounded.2⟩
expect_err "Example `BadReach.cantReach5` failed to prove `count == 5`:\n  • must satisfy:  False" in
component BadReach:
  state count : Nat = 0
  action inc: count += 1
  example cantReach5: .inc, .inc -> count == 5
  view: <span>{count}</span>
expect_err "Example `BadParamReach.addTooMuch` failed to prove `count == n`:\n  • must satisfy:  0 = n" in
component BadParamReach:
  state count : Nat = 0
  action inc(n: Nat): if count + n <= 10: count += n
  example addTooMuch(n: Nat): .inc(n) -> count == n
  view: <span>{count}</span>

/-! ## 2. Compile-Time Accessibility (A11y) Proofs -/
style a11yPrimary:
  background: #1d4ed8
  color: #ffffff
component AccessibleCard:
  state openMenu : Bool = false
  action toggle: openMenu = not openMenu
  view: <main ariaRole="main" id="main-content"><h1>Dashboard</h1><nav ariaRole="navigation" id="primary-nav"><a href={url("/home")}><img src={url("/logo.png")} alt="Home"/></a><img src={url("/divider.png")} alt=""/></nav><section><h2>Controls</h2><button role="primary" {a11yPrimary} aria-label="Toggle menu" onClick={.toggle}>{"Close" if openMenu else "Open"}</button><label for="email-input">Email</label><input id="email-input" type="email"/><label><span>Notes</span><textarea id="notes-box"></textarea></label><h3>Details</h3></section><h2>Summary</h2></main>
  invariant accessible: a11yValid
  invariant granular: imgsHaveAlt, buttonsAccessible, validAriaRoles, labelsAssociated, noDuplicateIds, headingsOrdered
  invariant styledToo: roleHas("primary", a11yPrimary)
component PhotoTile:
  state id : Nat
  state title : String
  key id
  view: <article><img src={url("/photo.jpg")} alt="Photo"/><button aria-label="Like">Like</button></article>
  invariant imgsOk: imgsHaveAlt
  invariant btnsOk: buttonsAccessible
component PhotoGallery:
  collection tiles : PhotoTile
  view: <section>{for tile in tiles: <PhotoTile state={tile}/>}</section>
  invariant allImgsOk: PhotoTile.imgsOk for_each tiles
  invariant allBtnsOk: PhotoTile.btnsOk for_each tiles
example : (∀ m, Qed.a11yValid (AccessibleCard.app.view m) = true) ∧
    Qed.htmlHasLang (el "html" [attr "lang" "en"] [el "body" [] ["Hello"]] : Html Unit) = true ∧
    Qed.a11yValid ((el "div" [] [el "img" [alt "Ok"] []] : Html Nat).map (· + 1)) = true :=
  ⟨AccessibleCard.accessible_app, rfl, (Html.a11yValid_map _ _).trans rfl⟩
bad_a11y imgsHaveAlt       : <div><img src={url("/banner.png")}/></div>
bad_a11y buttonsAccessible : <div><button></button></div>
bad_a11y validAriaRoles    : <div ariaRole="definitely-not-a-role">Hi</div>
bad_a11y labelsAssociated  : <div><label>Orphan label</label></div>
bad_a11y noDuplicateIds    : <div><span id="dup">A</span><span id="dup">B</span></div>
bad_a11y headingsOrdered   : <div><h1>Title</h1><h3>Skipped h2</h3></div>
bad_a11y htmlHasLang       : <html><body>Hello</body></html>

/-! ## 3. Binary File Uploads & Verified Base64 -/
example (bs : ByteArray) : Qed.Base64.decode (Qed.Base64.encode bs) = .ok bs ∧
    (Qed.Base64.encode bs).length = Qed.Base64.encodedLength bs.size ∧
    (Qed.Base64.encodeUrl bs).length = Qed.Base64.encodedUrlLength bs.size :=
  ⟨Qed.Base64.decode_encode bs, Qed.Base64.encode_length bs, Qed.Base64.encodeUrl_length bs⟩
#guard Qed.Base64.encode (ByteArray.mk #[]) == "" && Qed.Base64.encode (ByteArray.mk #[0, 1, 2, 255]) == "AAEC/w==" &&
  (match Qed.FileBytes.decode "{\"name\":\"pic.png\",\"mime\":\"image/png\",\"size\":4,\"base64\":\"AAEC/w==\"}" with
   | .ok fb => (fb.name, fb.mime, fb.size, fb.bytes.data) == ("pic.png", "image/png", 4, #[0, 1, 2, 255]) | .error _ => false) &&
  (match Qed.FileBytes.decode "{\"error\":\"file too large\"}" with | .error "file too large" => true | _ => false) &&
  (match Qed.Cmd.pickFileBytes (msg := Unit) "image/*" 4096 (fun _ => ()) with | .fxResult "file.pickBytes" "image/*" "4096" _ => true | _ => false)

/-! ## 4. Verified Scheduled / Background Server Jobs -/
external HealthPing:
  base "https://status.example.com"
  get "/ok" ping() -> String
server ScheduledWorker:
  state count : Nat = 0
  state total : Nat = 0
  invariant bounded: count <= 100
  invariant mono: total >= old(total)
  def status() -> Nat: return count
  every 500ms tick: if count < 100: count += 1; total += 1
  every 60s cleanup: atomic: count = 0
  every 5m syncRemote: let _ = await HealthPing.ping()?; atomic: total += 1
  every 1h hourlyNote: atomic: if count < 100: count += 1
server StatelessCron:
  def ping() -> String: return "pong"
  every 10s heartbeat: let _ = await HealthPing.ping()?; return
example : ScheduledWorker.jobs.size = 4 ∧ ScheduledWorker.verifiedJobs.size = 4 ∧
    ScheduledWorker.jobNames = ["tick", "cleanup", "syncRemote", "hourlyNote"] ∧ StatelessCron.jobs.size = 1 := ⟨rfl, rfl, rfl, rfl⟩
example (s : ScheduledWorker.State) : Qed.Server.MultiCoreStep ScheduledWorker.StateInv ⟨s, []⟩
    ⟨s, [(ScheduledWorker.verifiedJobs[0]'(by decide)).runM (m := Qed.Server.ThreadProg ScheduledWorker.State)]⟩ :=
  Qed.Server.verifiedJob_spawn_step (ScheduledWorker.verifiedJobs[0]'(by decide)) s []
bad_srv_st "background job `badZero` interval must be positive (got `0s`)" BadZeroJob n : Nat = 0 | every 0s badZero: n += 1
bad_srv_st "unknown duration unit `d` in `every 2d badUnit`" BadUnitJob n : Nat = 0 | every 2d badUnit: n += 1
bad_srv_inv "Server invariant `bounded` failed in `overflow`:\n  • must satisfy:  count + 1 <= 10" BadInvJob count : Nat = 0 | bounded : count <= 10 | every 1s overflow: count += 1
bad_srv_inv "Server invariant `mono` failed in `shrink`:\n  • must satisfy:  s.total - 1 >= s.total" BadMonoJob total : Nat = 5 | mono : total >= old(total) | every 10s shrink: atomic: total -= 1
bad_srv_st "cannot access server state `count` outside an `atomic` block in `racySync`" BadRacyJob count : Nat = 0 | every 30s racySync: let _ = await HealthPing.ping()?; count += 1
bad_srv_st "cannot use `await` inside an `atomic` block" BadAwaitInAtomicJob count : Nat = 0 | every 30s badLock: atomic: let _ = await HealthPing.ping()?; count += 1

/-! ## 5. Verified Typed Dictionaries (`{K: V}`) -/
example : Qed.LawfulJson (Qed.Dict String Nat) × Qed.LawfulJson (Qed.Dict Nat String) ×
    Qed.LawfulProto (Qed.Dict String Nat) × Qed.LawfulProto (Qed.Dict Nat (Array String)) :=
  (inferInstance, inferInstance, inferInstance, inferInstance)
#guard let d : Qed.Dict String Nat := Qed.Dict.ofList [("alice", 10), ("bob", 20)]
  Qed.Json.render (Qed.toJson d) == "{\"alice\":10,\"bob\":20}" &&
  (match Qed.Proto.decode (α := Qed.Dict String Nat) (Qed.Proto.encode d) with | .ok d' => d' == d | .error _ => false)
component Scoreboard:
  state scores : {String: Nat}
  state preset = {"alice": 10, "bob": 20}
  invariant capped: scores.size <= 100
  action record(name: String, pts: Nat): if scores.size < 100 or name in scores: scores[name] = pts
  action clear(name: String): scores.remove(name)
  action resetAll: scores = {}
  example recordConcrete: .record("alice", 42) -> scores["alice"] == some(42)
  example recordAndRead(name: String, pts: Nat): .record(name, pts) -> scores[name] == some(pts)
  example recordThenClear(name: String, pts: Nat): .record(name, pts), .clear(name) -> name not in scores
  view: <section><h2>Scores ({scores.size})</h2><ul>{for (name, pts) in scores.entries: <li key={name}>{name}: {pts}</li>}</ul></section>
server ScoreboardApi:
  state scores : {String: Nat}
  state nested : {String: Nat[]}
  invariant capped: scores.size <= 100
  def record(name: String, pts: Nat) -> {String: Nat}:
    if scores.size < 100 or name in scores: scores[name] = pts
    return scores
  def lookup(name: String) -> Nat?: return scores[name]
  def clear(name: String) -> Unit: scores.remove(name)
  get "/scores": return json(scores)
  get "/by-id":
    let byId : {Nat: String} = {1: "one", 2: "two"}
    return json(byId)
expect_err "Server invariant `capped` failed in `recordUnsafe`:\n  • must satisfy:  (if scores.contains name = true then scores.size else scores.size + 1) <= 100" in
server BadDictCap:
  state scores : {String: Nat}
  invariant capped: scores.size <= 100
  def recordUnsafe(name: String, pts: Nat) -> Unit: scores[name] = pts

end VerificationChecks
