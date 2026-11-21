import Qed
open Qed

namespace VerificationChecks

/-! ## 1A. Schema `example` & Automatic Vacuity Detection -/

schema OrderWithExample:
  name        : String where 1 <= name.length, name.length <= 40
  quantity    : Nat    where 1 <= quantity, quantity <= 10
  acceptTerms : Bool   where acceptTerms == true
  example validOrder: name = "Alice", quantity = 3, acceptTerms = true
  example maxOrder:
    name = "Bob",
    quantity = 10,
    acceptTerms = true

example : ∃ _x : OrderWithExample, True := OrderWithExample.satisfiable
example : Nonempty OrderWithExample := inferInstance
example : OrderWithExample.validOrder.quantity.val = 3 := rfl
example : OrderWithExample.maxOrder.quantity.val = 10 := rfl

schema BoundedQty:
  quantity : Nat where 10 <= quantity, quantity <= 20

example : ∃ _x : BoundedQty, True := BoundedQty.satisfiable
example : Nonempty BoundedQty := inferInstance

-- Negative: contradictory Nat `where` clauses are caught at compile time
/--
error: Schema `UnsatRange` is unsatisfiable: field `quantity` has contradictory `where` constraints (`10 <= quantity, quantity <= 5`) — no value can ever satisfy it.

Hint: Fix or remove the conflicting `where` conditions on `quantity`.
-/
#guard_msgs in
schema UnsatRange:
  quantity : Nat where 10 <= quantity, quantity <= 5

-- Negative: contradictory Bool `where` clauses are caught at compile time
/--
error: Schema `UnsatBool` is unsatisfiable: field `flag` has contradictory `where` constraints (`flag == true, flag == false`) — no value can ever satisfy it.

Hint: Fix or remove the conflicting `where` conditions on `flag`.
-/
#guard_msgs in
schema UnsatBool:
  flag : Bool where flag == true, flag == false

-- Negative: example failing a `where` constraint emits clear diagnostic
/--
error: Schema `BadExampleVal` example `tooMany` failed `where` constraint on field `quantity`:
  • value `99` does not satisfy `1 <= quantity, quantity <= 10`

Hint: Update `quantity` in example `tooMany` so it satisfies `1 <= quantity, quantity <= 10`, or weaken the `where` rule.
-/
#guard_msgs in
schema BadExampleVal:
  name     : String where 1 <= name.length
  quantity : Nat    where 1 <= quantity, quantity <= 10
  example tooMany: name = "Alice", quantity = 99

-- Negative: example missing a required field
/--
error: Schema `MissingExampleField` example `incomplete`: missing required field `quantity`
-/
#guard_msgs in
schema MissingExampleField:
  name     : String where 1 <= name.length
  quantity : Nat    where 1 <= quantity
  example incomplete: name = "Alice"

/-! ## 1B. Unified Component `example` (Concrete & Universally Quantified Parametric Proofs) -/

component ReachCounter:
  state count : Nat = 0
  action inc(n: Nat):
    if count + n <= 10:
      count += n
  action reset:
    count = 0
  invariant bounded: count <= 10

  -- Concrete single-step & multi-step examples
  example canAdd5:    .inc(5) -> count == 5
  example canReach8:  .inc(5), .inc(3) -> count == 8
  example staysCap:   .inc(5), .inc(9) -> count == 5

  -- Universally quantified parametric proofs (for ALL values satisfying `where`!)
  example addAny(n: Nat) where n <= 10:               .inc(n) -> count == n
  example addTwo(a: Nat, b: Nat) where a + b <= 10:   .inc(a), .inc(b) -> count == a + b
  example addThenReset(n: Nat):                       .inc(n), .reset -> count == 0
  example ignoreOverflow(n: Nat) where n > 10:        .inc(n) -> count == 0

  view:
    <div>
      <button onClick={.inc(1)}>Add</button>
      <span>{count}</span>
    </div>

example : ∃ s : ReachCounter.State, s.count ≤ 10 ∧ s.count = 5 :=
  Qed.inv_nonvacuous_of_reachable ReachCounter.canAdd5 ReachCounter.bounded.1 ReachCounter.bounded.2

example (n : Nat) (h : n ≤ 10) : ∃ s : ReachCounter.State, s.count ≤ 10 ∧ s.count = n :=
  Qed.inv_nonvacuous_of_reachable (ReachCounter.addAny n h) ReachCounter.bounded.1 ReachCounter.bounded.2

-- Negative: concrete `example` fails when trace does not reach the target state
/--
error: Example `BadReach.cantReach5` failed to prove `count == 5`:
  • must satisfy:  False

Hint: Verify the action sequence reaches a state satisfying `count == 5` (or strengthen the `where` preconditions for parametric examples).
-/
#guard_msgs in
component BadReach:
  state count : Nat = 0
  action inc:
    count += 1
  example cantReach5: .inc, .inc -> count == 5
  view: <span>{count}</span>

-- Negative: universally quantified `example` fails when `where` precondition is missing/too weak
/--
error: Example `BadParamReach.addTooMuch` failed to prove `count == n`:
  • must satisfy:  0 = n

Hint: Verify the action sequence reaches a state satisfying `count == n` (or strengthen the `where` preconditions for parametric examples).
-/
#guard_msgs in
component BadParamReach:
  state count : Nat = 0
  action inc(n: Nat):
    if count + n <= 10:
      count += n
  example addTooMuch(n: Nat): .inc(n) -> count == n
  view: <span>{count}</span>

/-! ## 2. Compile-Time Accessibility (A11y) Proofs -/

style a11yPrimary:
  background: #1d4ed8
  color: #ffffff

component AccessibleCard:
  state openMenu : Bool = false
  action toggle: openMenu = not openMenu
  view:
    <main ariaRole="main" id="main-content">
      <h1>Dashboard</h1>
      <nav ariaRole="navigation" id="primary-nav">
        <a href={url("/home")}>
          <img src={url("/logo.png")} alt="Home"/>
        </a>
        <img src={url("/divider.png")} alt=""/>
      </nav>
      <section>
        <h2>Controls</h2>
        <button role="primary" {a11yPrimary} aria-label="Toggle menu" onClick={.toggle}>
          {"Close" if openMenu else "Open"}
        </button>
        <label for="email-input">Email</label>
        <input id="email-input" type="email"/>
        <label>
          <span>Notes</span>
          <textarea id="notes-box"></textarea>
        </label>
        <h3>Details</h3>
      </section>
      <h2>Summary</h2>
    </main>
  invariant accessible: a11yValid
  invariant granular: imgsHaveAlt, buttonsAccessible, validAriaRoles, labelsAssociated, noDuplicateIds, headingsOrdered
  invariant styledToo: roleHas("primary", a11yPrimary)

-- Confirm `Html.a11yValid` also proves on `App.view` via canonical congruence
example : ∀ m, Qed.a11yValid (AccessibleCard.app.view m) = true := AccessibleCard.accessible_app

-- Confirm `Html.map` invariance and `for_each` child component lift
component PhotoTile:
  state id : Nat
  state title : String
  key id
  view:
    <article>
      <img src={url("/photo.jpg")} alt="Photo"/>
      <button aria-label="Like">Like</button>
    </article>
  invariant imgsOk: imgsHaveAlt
  invariant btnsOk: buttonsAccessible

component PhotoGallery:
  collection tiles : PhotoTile
  view:
    <section>{for tile in tiles:
      <PhotoTile state={tile}/>}</section>
  invariant allImgsOk: PhotoTile.imgsOk for_each tiles
  invariant allBtnsOk: PhotoTile.btnsOk for_each tiles

-- Confirm `htmlHasLang` positive case
example : Qed.htmlHasLang (el "html" [attr "lang" "en"] [el "body" [] ["Hello"]] : Html Unit) = true := rfl
example : Qed.a11yValid ((el "div" [] [el "img" [alt "Ok"] []] : Html Nat).map (· + 1)) = true := by
  simp [Html.a11yValid_map, Html.a11yValid, Html.imgsHaveAlt, Html.imgsHaveAltList,
    Html.buttonsAccessible, Html.buttonsAccessibleList, Html.validAriaRoles, Html.validAriaRolesList,
    Html.labelsAssociated, Html.labelsAssociatedList, Html.noDuplicateIds, Html.collectIds,
    Html.collectIdsList, Html.headingsOrdered, Html.collectHeadings, Html.collectHeadingsList,
    Html.htmlHasLang, Html.htmlHasLangList, attrsValidAriaRoles, hasAttr, attrValue,
    listNoDups, headingLevelsOrderedFrom, headingLevel?, el, alt]

-- Negative A11y checks (each rule rejects bad markup at compile time)
/--
error: Accessibility invariant `MissingImgAlt.ok` failed in `MissingImgAlt.view`:
  • `imgsHaveAlt` does not hold in every state

Hint: An `<img>` element in `MissingImgAlt.view` is missing an `alt` attribute. Add `alt="..."` (or `alt=""` for decorative images).
-/
#guard_msgs in
component MissingImgAlt:
  state x : Nat = 0
  view:
    <div>
      <img src={url("/banner.png")}/>
    </div>
  invariant ok: imgsHaveAlt

/--
error: Accessibility invariant `UnlabeledButton.ok` failed in `UnlabeledButton.view`:
  • `buttonsAccessible` does not hold in every state

Hint: A `<button>` or `<a>` element in `UnlabeledButton.view` has no accessible name in some branch. Provide non-empty text, `aria-label`, `aria-labelledby`, `title`, or a child `<img>` with non-empty `alt`.
-/
#guard_msgs in
component UnlabeledButton:
  state x : Nat = 0
  view:
    <div>
      <button></button>
    </div>
  invariant ok: buttonsAccessible

/--
error: Accessibility invariant `BadAriaRole.ok` failed in `BadAriaRole.view`:
  • `validAriaRoles` does not hold in every state

Hint: An element in `BadAriaRole.view` has an unrecognized WAI-ARIA `role` attribute. Use a valid WAI-ARIA 1.2 role name.
-/
#guard_msgs in
component BadAriaRole:
  state x : Nat = 0
  view:
    <div ariaRole="definitely-not-a-role">Hi</div>
  invariant ok: validAriaRoles

/--
error: Accessibility invariant `UnassociatedLabel.ok` failed in `UnassociatedLabel.view`:
  • `labelsAssociated` does not hold in every state

Hint: A `<label>` element in `UnassociatedLabel.view` neither has a non-empty `for` attribute nor wraps a form control (`<input>`, `<select>`, `<textarea>`).
-/
#guard_msgs in
component UnassociatedLabel:
  state x : Nat = 0
  view:
    <div>
      <label>Orphan label</label>
    </div>
  invariant ok: labelsAssociated

/--
error: Accessibility invariant `DuplicateId.ok` failed in `DuplicateId.view`:
  • `noDuplicateIds` does not hold in every state

Hint: Two elements in `DuplicateId.view` share the same `id` attribute in some branch. Ensure every non-empty `id` is unique.
-/
#guard_msgs in
component DuplicateId:
  state x : Nat = 0
  view:
    <div>
      <span id="dup">A</span>
      <span id="dup">B</span>
    </div>
  invariant ok: noDuplicateIds

/--
error: Accessibility invariant `SkippedHeading.ok` failed in `SkippedHeading.view`:
  • `headingsOrdered` does not hold in every state

Hint: Headings in `SkippedHeading.view` skip a level (e.g. `<h1>` directly to `<h3>`). Use sequential heading levels.
-/
#guard_msgs in
component SkippedHeading:
  state x : Nat = 0
  view:
    <div>
      <h1>Title</h1>
      <h3>Skipped h2</h3>
    </div>
  invariant ok: headingsOrdered

/--
error: Accessibility invariant `MissingHtmlLang.ok` failed in `MissingHtmlLang.view`:
  • `htmlHasLang` does not hold in every state

Hint: An `<html>` element in `MissingHtmlLang.view` is missing a non-empty `lang` attribute (e.g. `<html lang="en">`).
-/
#guard_msgs in
component MissingHtmlLang:
  state x : Nat = 0
  view:
    <html>
      <body>Hello</body>
    </html>
  invariant ok: htmlHasLang

/-! ## 3. Binary File Uploads & Verified Base64 -/

example (bs : ByteArray) : Qed.Base64.decode (Qed.Base64.encode bs) = .ok bs :=
  Qed.Base64.decode_encode bs

#guard Qed.Base64.encode (ByteArray.mk #[]) == ""
#guard Qed.Base64.encode (ByteArray.mk #[0, 1, 2, 255]) == "AAEC/w=="
#guard match Qed.FileBytes.decode "{\"name\":\"pic.png\",\"mime\":\"image/png\",\"size\":4,\"base64\":\"AAEC/w==\"}" with
  | .ok fb => fb.name == "pic.png" && fb.mime == "image/png" && fb.size == 4 && fb.bytes.data == #[0, 1, 2, 255]
  | .error _ => false
#guard match Qed.FileBytes.decode "{\"error\":\"file too large\"}" with
  | .error "file too large" => true
  | _ => false
#guard match Qed.Cmd.pickFileBytes (msg := Unit) "image/*" 4096 (fun _ => ()) with
  | .fxResult "file.pickBytes" "image/*" "4096" _ => true
  | _ => false

/-! ## 4. Verified Scheduled / Background Server Jobs -/

external HealthPing:
  base "https://status.example.com"
  get "/ok"
    ping() -> String

server ScheduledWorker:
  state count : Nat = 0
  state total : Nat = 0

  invariant bounded: count <= 100
  invariant mono: total >= old(total)

  def status() -> Nat:
    return count

  every 500ms tick:
    if count < 100:
      count += 1
      total += 1

  every 60s cleanup:
    atomic:
      count = 0

  every 5m syncRemote:
    let _ = await HealthPing.ping()?
    atomic:
      total += 1

  every 1h hourlyNote:
    atomic:
      if count < 100:
        count += 1

example : ScheduledWorker.jobs.size = 4 := rfl
example : ScheduledWorker.verifiedJobs.size = 4 := rfl
example : ScheduledWorker.jobNames = ["tick", "cleanup", "syncRemote", "hourlyNote"] := rfl
example (s : ScheduledWorker.State) :
    Qed.Server.MultiCoreStep ScheduledWorker.StateInv ⟨s, []⟩
      ⟨s, [(ScheduledWorker.verifiedJobs[0]'(by decide)).runM (m := Qed.Server.ThreadProg ScheduledWorker.State)]⟩ :=
  Qed.Server.verifiedJob_spawn_step (ScheduledWorker.verifiedJobs[0]'(by decide)) s []

server StatelessCron:
  def ping() -> String:
    return "pong"

  every 10s heartbeat:
    let _ = await HealthPing.ping()?
    return

example : StatelessCron.jobs.size = 1 := rfl

-- Negative: zero-duration job rejected at compile time
/--
error: background job `badZero` interval must be positive (got `0s`)
-/
#guard_msgs in
server BadZeroJob:
  state n : Nat = 0
  every 0s badZero:
    n += 1

-- Negative: unknown duration unit rejected at compile time
/--
error: unknown duration unit `d` in `every 2d badUnit`; supported units are `ms`, `s`, `m`, `h`
-/
#guard_msgs in
server BadUnitJob:
  state n : Nat = 0
  every 2d badUnit:
    n += 1

-- Negative: job violating single-state invariant rejected at compile time
/--
error: Server invariant `bounded` failed in `overflow`:
  • must satisfy:  count + 1 <= 10

Hint: Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadInvJob:
  state count : Nat = 0
  invariant bounded: count <= 10
  every 1s overflow:
    count += 1

-- Negative: job violating `old(...)` monotonicity invariant rejected at compile time
/--
error: Server invariant `mono` failed in `shrink`:
  • must satisfy:  s.total - 1 >= s.total

Hint: Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadMonoJob:
  state total : Nat = 5
  invariant mono: total >= old(total)
  every 10s shrink:
    atomic:
      total -= 1

-- Negative: job accessing state outside `atomic:` when using `await` is rejected
/--
error: cannot access server state `count` outside an `atomic` block in `racySync` because `racySync` uses `await` (prevents TOCTOU data races across suspension points)
-/
#guard_msgs in
server BadRacyJob:
  state count : Nat = 0
  every 30s racySync:
    let _ = await HealthPing.ping()?
    count += 1

-- Negative: job using `await` inside `atomic:` is rejected
/--
error: cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls
-/
#guard_msgs in
server BadAwaitInAtomicJob:
  state count : Nat = 0
  every 30s badLock:
    atomic:
      let _ = await HealthPing.ping()?
      count += 1

/-! ## 5. Verified Typed Dictionaries (`{K: V}`) — Components, Servers, JSON, Proto & Proofs -/

example : Qed.LawfulJson (Qed.Dict String Nat) := inferInstance
example : Qed.LawfulJson (Qed.Dict Nat String) := inferInstance
example : Qed.LawfulProto (Qed.Dict String Nat) := inferInstance
example : Qed.LawfulProto (Qed.Dict Nat (Array String)) := inferInstance

#guard
  let d : Qed.Dict String Nat := Qed.Dict.ofList [("alice", 10), ("bob", 20)]
  Qed.Json.render (Qed.toJson d) == "{\"alice\":10,\"bob\":20}"

#guard
  let d : Qed.Dict String Nat := Qed.Dict.ofList [("alice", 10), ("bob", 20)]
  match Qed.Proto.decode (α := Qed.Dict String Nat) (Qed.Proto.encode d) with
  | .ok d' => d' == d
  | .error _ => false

component Scoreboard:
  state scores : {String: Nat}
  state preset = {"alice": 10, "bob": 20}

  invariant capped: scores.size <= 100

  action record(name: String, pts: Nat):
    if scores.size < 100 or name in scores:
      scores[name] = pts

  action clear(name: String):
    scores.remove(name)

  action resetAll:
    scores = {}

  example recordConcrete:
    .record("alice", 42) -> scores["alice"] == some(42)

  example recordAndRead(name: String, pts: Nat):
    .record(name, pts) -> scores[name] == some(pts)

  example recordThenClear(name: String, pts: Nat):
    .record(name, pts), .clear(name) -> name not in scores

  view:
    <section>
      <h2>Scores ({scores.size})</h2>
      <ul>
        {for (name, pts) in scores.entries:
          <li key={name}>{name}: {pts}</li>}
      </ul>
    </section>

server ScoreboardApi:
  state scores : {String: Nat}
  state nested : {String: Nat[]}
  invariant capped: scores.size <= 100

  def record(name: String, pts: Nat) -> {String: Nat}:
    if scores.size < 100 or name in scores:
      scores[name] = pts
    return scores

  def lookup(name: String) -> Nat?:
    return scores[name]

  def clear(name: String) -> Unit:
    scores.remove(name)

  get "/scores":
    return json(scores)

  get "/by-id":
    let byId : {Nat: String} = {1: "one", 2: "two"}
    return json(byId)

-- Negative: dictionary mutation violating size invariant is rejected at compile time
/--
error: Server invariant `capped` failed in `recordUnsafe`:
  • must satisfy:  (if scores.contains name = true then scores.size else scores.size + 1) <= 100

Hint: Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadDictCap:
  state scores : {String: Nat}
  invariant capped: scores.size <= 100
  def recordUnsafe(name: String, pts: Nat) -> Unit:
    scores[name] = pts

end VerificationChecks
