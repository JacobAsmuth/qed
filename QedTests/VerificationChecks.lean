import Qed
import QedTests.CheckHelper
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
bad_schema "Schema `UnsatRange` is unsatisfiable: field `quantity` has contradictory `where` constraints" UnsatRange : quantity : Nat where 10 <= quantity, quantity <= 5
bad_schema "Schema `UnsatBool` is unsatisfiable: field `flag` has contradictory `where` constraints" UnsatBool : flag : Bool where flag == true, flag == false
bad_schema "Schema `BadExampleVal` example `tooMany` failed `where` constraint on field `quantity`:\n  • value `99` does not satisfy `1 <= quantity, quantity <= 10`" BadExampleVal :
  name : String where 1 <= name.length || quantity : Nat where 1 <= quantity, quantity <= 10 || example tooMany: name = "Alice", quantity = 99
bad_schema "Schema `MissingExampleField` example `incomplete`: missing required field `quantity`" MissingExampleField :
  name : String where 1 <= name.length || quantity : Nat where 1 <= quantity || example incomplete: name = "Alice"

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
bad_comp "Example `BadReach.cantReach5` failed to prove `count == 5`:\n  • must satisfy:  False" BadReach : state count : Nat = 0 || action inc: count += 1 || example cantReach5: .inc, .inc -> count == 5 || view: <span>{count}</span>
bad_comp "Example `BadParamReach.addTooMuch` failed to prove `count == n`:\n  • must satisfy:  0 = n" BadParamReach : state count : Nat = 0 || action inc(n: Nat): if count + n <= 10: count += n || example addTooMuch(n: Nat): .inc(n) -> count == n || view: <span>{count}</span>

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
example : (∀ m, Qed.a11yValid (AccessibleCard.app.view m) = true) ∧ Qed.htmlHasLang (el "html" [attr "lang" "en"] [el "body" [] ["Hello"]] : Html Unit) = true ∧
    Qed.a11yValid ((el "div" [] [el "img" [alt "Ok"] []] : Html Nat).map (· + 1)) = true := ⟨AccessibleCard.accessible_app, rfl, (Html.a11yValid_map _ _).trans rfl⟩
bad_a11y imgsHaveAlt       : <div><img src={url("/banner.png")}/></div>
bad_a11y buttonsAccessible : <div><button></button></div>
bad_a11y validAriaRoles    : <div ariaRole="definitely-not-a-role">Hi</div>
bad_a11y labelsAssociated  : <div><label>Orphan label</label></div>
bad_a11y noDuplicateIds    : <div><span id="dup">A</span><span id="dup">B</span></div>
bad_a11y headingsOrdered   : <div><h1>Title</h1><h3>Skipped h2</h3></div>
bad_a11y htmlHasLang       : <html><body>Hello</body></html>

/-! ## 3. Binary File Uploads & Verified Base64 -/
example (bs : ByteArray) : Qed.Base64.decode (Qed.Base64.encode bs) = .ok bs ∧ (Qed.Base64.encode bs).length = Qed.Base64.encodedLength bs.size ∧
    (Qed.Base64.encodeUrl bs).length = Qed.Base64.encodedUrlLength bs.size := ⟨Qed.Base64.decode_encode bs, Qed.Base64.encode_length bs, Qed.Base64.encodeUrl_length bs⟩

/-! ## 4. Verified Scheduled / Background Server Jobs -/
external HealthPing:
  base "https://status.example.com"
  get "/ok" ping() -> String
server ScheduledWorker:
  state count : Nat = 0
  state total : Nat = 0
  invariant bounded: count <= 100
  invariant mono: total >= old(total)
  rpc status() -> Nat: return count
  every 500ms tick: if count < 100: count += 1; total += 1
  every 60s cleanup: atomic: count = 0
  every 5m syncRemote: let _ = await HealthPing.ping()?; atomic: total += 1
  every 1h hourlyNote: atomic: if count < 100: count += 1
server StatelessCron:
  rpc ping() -> String: return "pong"
  every 10s heartbeat: let _ = await HealthPing.ping()?; return
example : ScheduledWorker.jobs.size = 4 ∧ ScheduledWorker.verifiedJobs.size = 4 ∧ ScheduledWorker.jobNames = ["tick", "cleanup", "syncRemote", "hourlyNote"] ∧ StatelessCron.jobs.size = 1 := ⟨rfl, rfl, rfl, rfl⟩
example (s : ScheduledWorker.State) : Qed.Server.MultiCoreStep ScheduledWorker.StateInv ⟨s, []⟩
    ⟨s, [(ScheduledWorker.verifiedJobs[0]'(by decide)).runM (m := Qed.Server.ThreadProg ScheduledWorker.State)]⟩ :=
  Qed.Server.verifiedJob_spawn_step (ScheduledWorker.verifiedJobs[0]'(by decide)) s []
bad_srv "background job `badZero` interval must be positive (got `0s`)" BadZeroJob : state n : Nat = 0 || every 0s badZero: n += 1
bad_srv "unknown duration unit `d` in `every 2d badUnit`" BadUnitJob : state n : Nat = 0 || every 2d badUnit: n += 1
bad_srv "Server invariant `bounded` failed in `overflow`:\n  • must satisfy:  count + 1 <= 10" BadInvJob : state count : Nat = 0 || invariant bounded: count <= 10 || every 1s overflow: count += 1
bad_srv "Server invariant `mono` failed in `shrink`:\n  • must satisfy:  s.total - 1 >= s.total" BadMonoJob : state total : Nat = 5 || invariant mono: total >= old(total) || every 10s shrink: atomic: total -= 1
bad_srv "cannot access server state `count` outside an `atomic` block in `racySync`" BadRacyJob : state count : Nat = 0 || every 30s racySync: let _ = await HealthPing.ping()?; count += 1
bad_srv "cannot use `await` inside an `atomic` block" BadAwaitInAtomicJob : state count : Nat = 0 || every 30s badLock: atomic: let _ = await HealthPing.ping()?; count += 1

/-! ## 5. Verified Typed Dictionaries (`{K: V}`) -/
example : Qed.LawfulJson (Qed.Dict String Nat) × Qed.LawfulJson (Qed.Dict Nat String) × Qed.LawfulProto (Qed.Dict String Nat) × Qed.LawfulProto (Qed.Dict Nat (Array String)) :=
  (inferInstance, inferInstance, inferInstance, inferInstance)
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
  rpc record(name: String, pts: Nat) -> {String: Nat}:
    if scores.size < 100 or name in scores: scores[name] = pts
    return scores
  rpc lookup(name: String) -> Nat?: return scores[name]
  rpc clear(name: String) -> Unit: scores.remove(name)
  get "/scores": return json(scores)
  get "/by-id": let byId : {Nat: String} = {1: "one", 2: "two"}; return json(byId)
bad_srv "Server invariant `capped` failed in `recordUnsafe`:\n  • must satisfy:  (if scores.contains name = true then scores.size else scores.size + 1) <= 100" BadDictCap : state scores : {String: Nat} || invariant capped: scores.size <= 100 || rpc recordUnsafe(name: String, pts: Nat) -> Unit: scores[name] = pts

/-! ## 6. Multi-Child Hoisted Component Verification & Flat Reconcile -/
component HoistedPane:
  port ping : String
  session user
  prop title : String = ""
  state ticks : Nat = 0
  event onPicked(label : String)
  start ping.send("boot")
  action tick: ticks += 1
  action pick: onPicked.emit(title)
  view: <div><span>{title}</span><button onClick={.tick}>{ticks}</button><button onClick={.pick}>Pick</button></div>
inductive DashTab where | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8 | t9 deriving BEq, DecidableEq
component HoistedDashboard:
  port audit : String
  session user
  state tab : DashTab = .t0
  state modalOpen : Bool = false
  state upgradePrompt : String? = none
  state lastPick : String = ""
  state sortCol : String = ""
  state sortAsc : Bool = true
  state count : Nat = 0
  state k0 : String = "a"
  state k1 : String = "b"
  action toggleModal: modalOpen = not modalOpen
  action promptUpgrade(feat : String): upgradePrompt = some(feat)
  action dismissUpgrade: upgradePrompt = none
  action setTab(t : DashTab): tab = t
  action onPick(v : String): lastPick = v; audit.send(v)
  action bump: if count < 10: count += 1
  action sortBy(col : String):
    if sortCol == col: sortAsc = not sortAsc
    else:
      sortCol = col
      sortAsc = true
  invariant countBounded: count <= 10
  example toggleModalEx: .toggleModal -> modalOpen == true
  example toggleModalRfl: .toggleModal -> modalOpen == true prove: rfl
  example upgradeRoundtrip(feat : String): .promptUpgrade(feat), .dismissUpgrade -> upgradePrompt == none
  example upgradeRoundtripRfl(feat : String): .promptUpgrade(feat), .dismissUpgrade -> upgradePrompt == none prove: rfl
  example sortFlip(col : String) where col != "": .sortBy(col), .sortBy(col) -> sortAsc == false
  example sortTracksCol(col : String): .sortBy(col), .sortBy(col) -> sortCol == col
  view:
    <div>
      {match tab:
        case .t0: <HoistedPane key={k0} title={k0} onPicked={.onPick}/>
        case .t1: <HoistedPane key={k1} title={k1} onPicked={.onPick}/>
        case .t2: <HoistedPane key={k0} title={k0} onPicked={.onPick}/>
        case .t3: <HoistedPane key={k1} title={k1} onPicked={.onPick}/>
        case .t4: <HoistedPane key={k0} title={k0} onPicked={.onPick}/>
        case .t5: <HoistedPane key={k1} title={k1} onPicked={.onPick}/>
        case .t6: <HoistedPane key={k0} title={k0} onPicked={.onPick}/>
        case .t7: <HoistedPane key={k1} title={k1} onPicked={.onPick}/>
        case .t8: <HoistedPane key={sortCol} title={sortCol} onPicked={.onPick}/>
        case .t9: <HoistedPane key={lastPick} title={lastPick} onPicked={.onPick}/>}
    </div>
component HoistedEmitter:
  state showPane : Bool = true
  event done(ok : Bool)
  action finish: done.emit(true)
  action hide: showPane = false
  view: <div>{<HoistedPane key="p" title="P"/> if showPane else <span/>}</div>

/-! ## 7. Upgraded Component `example` Blocks (`with props`, `from`, `emits`, Async `on Server.rpc => ...`) -/
component PropsAndEmitsCard:
  prop step : Nat = 1
  prop maxVal : Nat = 10
  event changed(next: Nat)
  state count : Nat = 0
  invariant bounded: count <= maxVal
  action inc: if count + step <= maxVal: count += step; changed.emit(count)
  action reset: count = 0; changed.emit(0)
  example defaultProps: .inc, .inc -> count == 2
  example customPropsAndEmits with props { step = 3, maxVal = 10 } from { count = 1 }: .inc, .inc -> count == 7 emits .changed(7)
  example parametricProp(s: Nat, m: Nat) with props { step = s, maxVal = m }: .reset -> count == 0 emits .changed(0)
  view: <button onClick={.inc}>{count}</button>
server stateless LaunchRpcSrv:
  rpc trigger(appId: String) -> String!:
    requires auth
    if appId == "full": return fail(.quota, "limit reached")
    if appId == "deny": return fail(.forbidden)
    return f"rel-{appId}"
component AsyncLaunchPanel:
  prop appId : String
  session user
  event launched(relId: String)
  state busy : Bool = false
  state lastRel : String = ""
  state errMsg : String = ""
  action start:
    if user != none:
      busy = true
      errMsg = ""
      let rel = await LaunchRpcSrv.trigger(appId) catch:
        case .quota(msg): busy = false; errMsg = f"quota:{msg}"
        case .forbidden: busy = false; errMsg = "forbidden"
        case .failed(msg): busy = false; errMsg = msg
      busy = false
      lastRel = rel
      launched.emit(rel)
  action startGuarded:
    let some(_) = user else: return
    busy = true
    let rel = await LaunchRpcSrv.trigger(appId) catch:
      case .quota(msg): busy = false; errMsg = f"quota:{msg}"
      case .forbidden: busy = false; errMsg = "forbidden"
      case .failed(msg): busy = false; errMsg = msg
    busy = false
    lastRel = rel
    launched.emit(rel)
  example guardedUnauth with props { appId = "web" }: .startGuarded -> not busy and lastRel == ""
  example guardedHappy with props { appId = "web" } from { user = some("alice") }: .startGuarded, on LaunchRpcSrv.trigger => ok("rel-g") -> not busy and lastRel == "rel-g" emits .launched("rel-g")
  example happyPath with props { appId = "web" } from { user = some("alice") }: .start, on LaunchRpcSrv.trigger => ok("rel-web") -> not busy and lastRel == "rel-web" and errMsg == "" emits .launched("rel-web")
  example quotaDomainError with props { appId = "full" } from { user = some("alice") }: .start, on LaunchRpcSrv.trigger => error(.quota, "limit reached") -> not busy and errMsg == "quota:limit reached"
  example networkError with props { appId = "web" } from { user = some("alice") }: .start, on LaunchRpcSrv.trigger => error("timeout") -> not busy and errMsg == "timeout"
  example unauthNoOp with props { appId = "web" }: .start -> not busy and lastRel == ""
  view: <section><button onClick={.start}>Launch</button><span>{lastRel}</span><span>{errMsg}</span></section>
bad_comp "Example `BadCompExEmits.badEmits` failed" BadCompExEmits : prop step : Nat = 1 || event changed(next: Nat) || state count : Nat = 0 || action inc: count += step; changed.emit(count) || example badEmits with props { step = 2 }: .inc -> count == 2 emits .changed(99) || view: <span>{count}</span>
bad_comp "`on ... => ...` in `example danglingReply` requires component `BadCompExNoAsync` to have `await` / async effects" BadCompExNoAsync : prop appId : String || session user || state busy : Bool = false || action noop: pass || example danglingReply with props { appId = "web" }: .noop, on LaunchRpcSrv.trigger => ok("rel-web") -> not busy || view: <span>{appId}</span>
bad_comp "Example `BadCompExUnmatchedRpc.danglingReply` failed" BadCompExUnmatchedRpc : prop appId : String || session user || state busy : Bool = false || action noop: pass ||
  action start:
    if user != none:
      let _ = await LaunchRpcSrv.trigger(appId) catch:
        case _: pass
      busy = false
  || example danglingReply with props { appId = "web" }: .noop, on LaunchRpcSrv.trigger => ok("rel-web") -> not busy || view: <span>{appId}</span>
end VerificationChecks
