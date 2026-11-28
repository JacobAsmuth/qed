import Qed
import QedTests.CheckHelper
open Qed

namespace SyntaxChecks
component Counter:
  prop step : Nat = 1
  state count : Nat = 0
  state saved : Nat = 0
  event emitted(n: Nat)
  action advance(times: Nat): if times > 0: count = count + step * times; saved = count; emitted.emit(count)
  view: <button onClick={.advance(2)}>{count}</button>
def defaults : Html Unit := <Counter initial={{ count = 8 }}/>
namespace LocalNested
component Tag:
  prop label = "Pin"
  state on = false
  event onToggle(pinned: Bool)
  action toggle: on = not on; onToggle.emit(on)
  view: <button onClick={.toggle}>{"on" if on else label}</button>
component Widget:
  prop id : Nat
  prop label : String
  state note = ""
  state pinned = false
  event onReport(count: Int)
  view: <div><span>{note}</span><Tag key={f"t{id}"} label={label} onToggle={pinned = _}/></div>
structure Row where (id : Nat) (label : String)
inductive ParentMsg | reported (id : Nat) (count : Int)
end LocalNested
def importedHelper (r : LocalNested.Row) : Html LocalNested.ParentMsg :=
  <LocalNested.Widget key={r.id} id={r.id} label={r.label} initial={{ note = r.label }} onReport={LocalNested.ParentMsg.reported(r.id)}/>
component HelperApp:
  state draft : String = ""
  action localEvent(m: LocalNested.ParentMsg): pass
  view: importedHelper({ id = 8, label = draft }).map(.localEvent)
bad_comp "`label` is a read-only `prop` and cannot be assigned (`state` fields: `count`)" ReadOnly : prop label : String || state count : Nat = 0 || action change: label = "changed" || view: <span>{label}</span>
bad_comp "duplicate action name `save`" DuplicateAction : state count : Nat = 0 || action save: count = 1 || action save: count = 2 || view: <span>{count}</span>
component Owned:
  prop caption : String
  state id : Nat
  state count : Nat
  key id
  action increment: count = count + 1
  view: <button title={caption} onClick={.increment}>{count}</button>
enum Section:
  overview
  architecture = "arch"
  benchmarks   = "bench"
router DocRoute:
  home = ""
  sec(s: Section, page: Nat) = "docs"
style navOn:
  font-weight: 700
style navOff:
  font-weight: 400
def navView (s : Section) : Html Unit :=
  <nav><a role="nav-overview" {navOn if s == .overview else navOff}>{"Overview"}</a><a role="nav-arch" {navOn if s == .architecture else navOff}>{"Arch"}</a><a role="nav-bench" {navOn if s == .benchmarks else navOff}>{"Bench"}</a></nav>
invariant navExclusive : exactlyOneOf(["nav-overview", "nav-arch", "nav-bench"], navOn, navOff) holds_in navView
component RoutedDehydrated:
  route r : DocRoute = .home
  view: <div>{Router.toURL(r)}</div>
expect_err "Styling invariant `badVacuousRole` failed in `navView`:\n  • `roleHasOneOf(\"nonexistent\", [navOn, navOff])` does not hold in every state" in invariant badVacuousRole : roleHasOneOf("nonexistent", [navOn, navOff]) holds_in navView
def bothStylesView (b : Bool) : Html Unit := <button role="btn" {navOn} {navOff if b else navOff}>{"x"}</button>
expect_err "Styling invariant `badDualStyle` failed in `bothStylesView`:\n  • `roleHasOneOf(\"btn\", [navOn, navOff])` does not hold in every state" in invariant badDualStyle : roleHasOneOf("btn", [navOn, navOff]) holds_in bothStylesView
structure AppModel where route : DocRoute deriving DecidableEq
def activeSection : DocRoute → Section | .home => .overview | .sec s _ => s
def compositeNav (m : AppModel) : Html Unit := <div>{navView(activeSection(m.route))}</div>
invariant compositeNavExclusive : exactlyOneOf(["nav-overview", "nav-arch", "nav-bench"], navOn, navOff) holds_in compositeNav
def validCountView (n : Nat) : Html Unit := <span role="pos" {navOn if n > 0 else navOff}>{toString(n)}</span>
invariant posStyledFromInv : roleHas("pos", navOn) holds_in validCountView assuming (n => n > 0)
component PositiveCard:
  state id    : Nat = 0
  state score : Nat = 1
  key id
  action bump: score += 1
  invariant positive: 1 <= score
  view: <span>{score}</span>
component TypedLink:
  prop target : DocRoute
  state cur : DocRoute = .home
  view: <a href={target} class={"active" if cur == target else ""}>{"Go"}</a>
component AutoStyled:
  state route : DocRoute = .home
  action noop: pass
  view: compositeNav({ route = route }).map(_ => .noop)
theme ResetTheme:
  color borderSubtle = #ccc
  reset *, *::before:
    margin: 0px
style typedBorderStyle:
  border: 1px solid ResetTheme.borderSubtle
  border-bottom: 2px dashed #333
  border-top: none
component SubBanner:
  prop sec : Section
  view: <header><a href={DocRoute.sec(sec, 1)}>{Router.toURL(DocRoute.sec(sec, 1))}</a></header>
component ParentPage:
  state route : DocRoute = .home
  invariant parentPageHasHeader: hasTag("header")
  view: <div><SubBanner sec={activeSection(route)}/></div>
style chipStyle:
  padding-inline: 6px
  margin-top: 2px
component ModernCounter:
  state quantity = 1
  state draft    = ""
  state active   = true
  action increase: if quantity < 10: let step = 1; quantity += step
  action decrease: if 1 < quantity: quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  invariant qtyStyled: roleHasOneOf("qty", [chipStyle])
  view: <div><button onClick={.decrease}>−</button><span role="qty" {chipStyle}>{quantity}</span><button onClick={.increase}>+</button><button onClick={quantity = 5; draft = "five"}>Five</button><input bind={draft}/><input type="checkbox" bind={active}/></div>
router RepoRoute:
  index = "/"
  blob  = "/orgs/:org/repos/:repo"
  edit  = "/orgs/:org/repos/:repo/edit"
  issues(page: Nat) = "/orgs/:org/issues/:page"
schema Ticket:
  id       : jsonOnly(String)
  title    : String where title.length >= 3
  priority : Nat    where 1 <= priority <= 5
  urgent   : Bool
  kind     : select([("bug", "Bug"), ("feat", "Feature")])
def jsxErgonomicsView (items : Array Nat) (note? : Option String) (highlight : Bool) : Html Unit :=
  <div {chipStyle if highlight} data-tag={"hi" if highlight}><><span>Header</span>{<em>!</em> if highlight}{if let some(note) = note?: <p>{note}</p>}</><ul><li key="head">Top</li>{for n in items: <li key={n}>{n}</li>}{for n in ([3, 4] : List Nat): <li key={f"l{n}"}>{n}</li>}</ul></div>
def jsxElseBranchesView (note? : Option String) (highlight : Bool) (extra : List (Html Unit)) : Html Unit :=
  <div>{if highlight: <span>yes</span> else: <span>no</span>}{if let some(note) = note?: <p>{note}</p> else: <p>empty</p>}{if highlight: extra else: <><b>f1</b><b>f2</b></>}{if let some(_) = note?: extra else: <><i>m1</i><i>m2</i></>}</div>
inductive FilterTab | all | tagged (tag : String) deriving DecidableEq
structure PlainNote where (id : Nat) (text : String) deriving DecidableEq
component RichAuto:
  state tab   : FilterTab = .all
  state notes : PlainNote[]
  state pick  : PlainNote?
  state cache : Cached String = {}
  state child : Counter.State = { count = 0, saved = 0 }
  view: <div>{notes.size}{child.count}</div>
component PartialFn:
  state count : Nat = 1
  state fn    : Nat -> Nat = (x => x + 10)
  action bump(d: Nat): count = count + d
  view: <div>{count}</div>
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 2) = ({ count := 10, saved := 10 }, some (.emitted 10)) ∧
    Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 0) = ({ count := 4, saved := 0 }, none) ∧
    (Owned.update { caption := "Live" } { id := 4, count := 2 } .increment).count = 3 ∧
    ModernCounter.init.quantity = 1 ∧ ModernCounter.init.draft = "" ∧ AutoStyled.app.styles.length = 2 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : (let ids := HelperApp.app.locals.map (·.id)
  ids.length == 3 && ["SyntaxChecks.HelperApp", "SyntaxChecks.LocalNested.Widget", "SyntaxChecks.LocalNested.Tag"].all ids.contains) = true := by decide +kernel

-- Compile-time rejection checks
expect_err "URL attribute `href` cannot take raw string literal `\"/raw\"`" in def badRawHref : Html Unit := <a href="/raw">bad</a>
expect_err "unsafe URL literal `javascript:alert(1)`" in def badJsUrl : Url := url("javascript:alert(1)")
expect_err "unsafe URL literal `data:text/html,<script>alert(1)</script>`" in def badDataUrl : Url := url("data:text/html,<script>alert(1)</script>")
expect_err "unsafe URL literal `//evil.example/x`" in def badProtocolRelativeUrl : Url := url("//evil.example/x")
expect_err "<script> is forbidden in Qed views" in def badScriptTag : Html Unit := <script>{"alert(1)"}</script>
expect_err "inline event attribute `onclick` is forbidden" in def badInlineHandler : Html Unit := <div onclick="alert(1)"/>
expect_err "`srcdoc` is forbidden in Qed views" in def badSrcdoc : Html Unit := <iframe srcdoc="<script>alert(1)</script>"/>
expect_err "invalid HTML5 nesting: <div> is not allowed inside <p>" in def badNestedParagraph : Html Unit := <p><div>bad</div></p>
expect_err "invalid HTML5 nesting: <button> is not allowed inside <button>" in def badNestedInteractive : Html Unit := <button><button>bad</button></button>
expect_err "invalid HTML5 nesting: <span> is not allowed inside <ul>" in def badListChild : Html Unit := <ul><span>bad</span></ul>

def goodSafeUrl : Url := url("/docs/guide")
component GoodLazy:
  state m : Nat = 7
  view: <div><a href={goodSafeUrl}>Docs</a><a href={url("/about")}>About</a>{Qed.lazy((k: Nat) => <span>{k}</span>, m / 2)}</div>
def sneakyBlock {msg : Type} : Html msg := <div>bad</div>
bad_comp_view "Invalid HTML / XSS check failed for this view:\n  • `<div>` cannot be nested inside `<p>` or a heading (`<h1>-<h6>`)" BadOpaqueNesting u : Unit = () || <p>{sneakyBlock}</p>
bad_comp_view "Qed.lazy function must not capture state directly" BadLazyCapturesModel m : Nat = 1 || <div>{Qed.lazy((k: Nat) => <span>{k + m}</span>, m / 2)}</div>
bad_comp "SSR hydration mismatch: `ephemeral` field affects the rendered view:\n  • view mismatch after rehydration:  \"hi\" = b" BadEphemeralReadByView : state a : Nat = 1 || ephemeral b : String = "hi" || view: <div>{a}{b}</div>

-- Sub-components, `Field`, `<Await>`, & fractional CSS checks
style fracStyle:
  text-align: center
  padding: 0.35rem 0 0.5rem
  margin: 2rem auto
  gap: 4px 8px
  line-height: 1.5
  font-weight: 600
  opacity: 0.85
  z-index: -1
component Card:
  prop title : String
  prop badge : Html
  view: <div class="card"><header><h3>{title}</h3>{badge}</header><div class="card-body">{children}</div></div>
component SearchBar:
  bind query : String = ""
  event onClear
  event onSubmitQuery(q: String)
  view: <div class="search-bar"><input bind={query}/><button class="clear" onClick={onClear}>Clear</button><button class="go" onClick={onSubmitQuery(query)}>Go</button></div>
component ListChip:
  prop text : String
  view: <li class="chip">{text}</li>
expect_err "invalid HTML5 nesting: <Card> (root <div>) is not allowed inside <p>" in def badCardInParagraph : Html Unit := <p><Card title="Nope"><span>x</span></Card></p>
expect_err "invalid HTML5 nesting: <ListChip> (root <li>) is not allowed inside <div>" in def badChipInDiv : Html Unit := <div><ListChip text="Orphan"/></div>
component Accordion:
  prop heading : String
  prop extra   : Html
  state openPanel = false
  action toggle: openPanel = not openPanel
  view: <section class="accordion"><header><button class="toggle" onClick={.toggle}>{heading}</button>{extra}</header>{<div class="panel">{children}</div> if openPanel}</section>
component PickerBox:
  bind filter : String = ""
  state highlighted = 0
  event onPick(choice: String)
  action next: highlighted += 1
  view: <div class="picker"><input bind={filter}/><button onClick={onPick(filter)}>Pick</button></div>
component CompositeDemo:
  state query     = "init"
  state picked    = ""
  state clicks    = 1
  ephemeral scratch = 99
  collection rows : PositiveCard
  action bump: clicks += 1
  invariant clicksPos: 1 <= clicks
  view: <div class="demo"><SearchBar bind:query={query} onClear={query = ""} onSubmitQuery={picked = _}/><PickerBox bind:filter={query} onPick={picked = _}/><Accordion heading="Details" extra={<span>!</span>}><button class="inner" onClick={.bump}>{clicks}</button></Accordion><div>{for r in rows: <PositiveCard state={r}/>}</div></div>
def awaitSample (r : Resource Ticket) : Html Unit :=
  <Await of={r} as={t} err={e} loading={<p>Wait</p>} failed={<p class="err">{e}</p>}><article><h2>{t.title}</h2><span>{t.priority}</span></article></Await>
component EarlyReturnCheck:
  state x : Int = 0
  action step(n: Int):
    if n <= 0: return
    x += n
  view: <span>{x}</span>
  invariant xPos: 0 <= x prove: intro m msg h; cases msg <;> simp_all [update] <;> split <;> simp_all <;> omega
def lazyBadge {msg : Type} (k : Nat) : Html msg := <span>{k}</span>
component FineGrainedCheck:
  state count : Nat = 1
  state items : Nat[] = [1, 2]
  action bump: count += 1
  view: <div><span class="c">{count}</span>{<p>zero</p> if count == 0 else <p>nonzero</p>}{Qed.lazy(lazyBadge, count)}<ul>{for n in items: <li key={n}>{n}</li>}</ul></div>
example : ((EarlyReturnCheck.update { x := 5 } (.step 0)).x == 5 && (EarlyReturnCheck.update { x := 5 } (.step 3)).x == 8 &&
  (match FineGrainedCheck.app.template with | .element "div" _ [.element "span" _ [.dyn _], .ifElse _ _ _, .memo _, .keyedList "ul" _ _ _ _ _ _ (some _)] => true | _ => false)) = true := by decide +kernel
bad_comp_inv "Invariant `BadUnguardedDecrease.inRange` failed in `BadUnguardedDecrease.update`:\n  • action `decrease` must satisfy:  1 <= quantity - 1 and quantity - 1 <= 10" BadUnguardedDecrease quantity : Nat = 1 || inRange : 1 <= quantity <= 10 || decrease : quantity -= 1
bad_comp_act "`qunatity` is not a `state` field of this component (did you mean `quantity`?) (`state` fields: `quantity`)" BadStateFieldTypo quantity : Nat = 1 || inc : qunatity += 1
style safeBtnStyle:
  background-color: #111
style dangerBtnStyle:
  background-color: #999
component StyleLacksGood:
  state ok : Bool = true
  view: <div><button role="submit" {safeBtnStyle}>OK</button><span>safe</span></div>
  invariant noDanger: roleLacks("submit", dangerBtnStyle), tagLacks("span", dangerBtnStyle)
bad_comp "Styling invariant `BadRoleLacks.noDanger` failed in `BadRoleLacks.view`:\n  • `roleLacks(\"submit\", dangerBtnStyle)` does not hold in every state" BadRoleLacks : state ok : Bool = true || view: <button role="submit" {dangerBtnStyle}>Bad</button> || invariant noDanger: roleLacks("submit", dangerBtnStyle)
bad_comp "Invariant `BadPropInit.nonNeg` failed on initial state `BadPropInit.init`:\n  • initial state must satisfy:  0 <= -1" BadPropInit : prop offset : Int = 0 || state count : Int = -1 || action nop: pass || invariant nonNeg: 0 <= count || view: <span>{count}</span>
bad_comp "SSR rehydration can violate the component's state invariant:\n  • after rehydration must satisfy:  5 <= shown + 0" BadEphemeralInv : state shown : Int = 5 || ephemeral cache : Int = 0 || action shift: shown = 0; cache = 5 || invariant totalMin: 5 <= shown + cache || view: <span>{shown}</span>

-- Self-hosted `<Schema.Form>` & unified syntax checks
component SelfHostedFormKeep:
  state picked : Ticket?
  view: <Ticket.Form onSubmit={picked = some(_)}/>
component SelfHostedFormReset:
  state picked : Ticket?
  view: <Ticket.Form reset onSubmit={picked = some(_)}/>
component MultiParamAndAutoDefaults:
  state xs : Nat[]
  state x  : Nat?
  event emitted(a: Nat, b: String)
  action pushBoth(a: Nat, b: String): xs.push(a); x = some(a); emitted.emit(a, b)
  view: <button onClick={.pushBoth(4, "hi")}>{xs.size}</button>
example : MultiParamAndAutoDefaults.update MultiParamAndAutoDefaults.init (.pushBoth 4 "hi") = ({ xs := #[4], x := some 4 }, some (.emitted 4 "hi")) ∧
    MultiParamAndAutoDefaults.init.xs = #[] ∧ MultiParamAndAutoDefaults.init.x = none := ⟨rfl, rfl, rfl⟩
bad_comp_view "use `Nat[]` instead of `Array Nat`" BadArrayType xs : Array Nat = [] || <span>{xs.size}</span>
bad_schema "use `Nat?` instead of `Option Nat`" BadOptType : val : Option Nat
bad_schema "use `jsonOnly(String)` with parentheses instead of `jsonOnly String`" BadJsonOnly : id : jsonOnly String

-- Python-esque ergonomics checks
component PythonicShowcase:
  state score : Nat = 5
  state tags  : String[] = ["lean"]
  state pick  : Nat? = some(2)
  state label : String = ""
  action classify(n: Nat):
    if 0 <= n <= 100:
      if n < 10: label = f"low:{n}"
      elif n < 50: label = f"mid:{n}"
      else: label = f"high:{n}"
  action addTag(t: String):
    if t in tags: return
    tags.push(t)
    label = f"tags:{tags.size}"
  action usePick: if let some(v) = pick: if v > 0: score = v * 2; label = f"score={score}"
  action describeTab(tab: FilterTab):
    match tab:
      case .all: label = "all"
      case .tagged(t): label = f"tag:{t}"
  action exprBranches(n: Nat, opt: Nat?):
    let a = if n > 0: "pos" else: "zero"
    let b = if let some(v) = opt: f":{v}" else: ":none"
    label = a ++ b
  invariant exprElseProp: (if score > 0: score else: 0) == score and (if let some(v) = pick: v else: 0) >= 0
  view: <div><span>{label}</span><span>{"has-lean" if "lean" in tags and pick is not none else "none"}</span></div>
bad_srv "`if cond: ...` expression requires `else:` here" BadExprIfNoElse : rpc go() -> Nat: return if true: 1
bad_srv "`if let pat = expr: ...` expression requires `else:` here" BadExprIfLetNoElse : rpc go(opt: Nat?) -> Nat: return if let some(v) = opt: v
expect_err "invalid HTML5 nesting: <div> is not allowed inside <p>" in def badElseBranchNesting : Html Unit := <p>{if true: <span>ok</span> else: <div>bad</div>}</p>

-- Automated Quantified, Collection-Query, Nonlinear & Extended `for_each` Invariants
schema LineItem:
  id    : Nat
  price : Nat
  done  : Bool
  ts    : Nat
component SmartLedger:
  state rows       : LineItem[] = []
  state nextId     : Nat = 0
  state lastTs     : Nat = 0
  state totalCents : Nat = 0
  state doneCount  : Nat = 0
  action addItem(price: Nat, done: Bool): let ts = lastTs + 1; rows.push(LineItem(id=nextId, price=price, done=done, ts=ts)); nextId += 1; lastTs = ts; totalCents += price; if done: doneCount += 1
  action reverseView: rows = rows.reverse
  action sortByPrice: rows = rows.sortBy((a, b) => a.price <= b.price)
  invariant idsAndUnique: (all r in rows: r.id < nextId) and rows.uniqueBy(r => r.id)
  invariant totalSynced:  rows.sumBy(r => r.price) == totalCents
  invariant doneSynced:   rows.countWhere(r => r.done) == doneCount and doneCount <= rows.size
  view: <div><span>{totalCents}</span><span>{doneCount}</span></div>
component SortedTimeline:
  state events : LineItem[] = []
  state lastTs : Nat = 0
  action append(price: Nat): let ts = lastTs + 1; events.push(LineItem(id=ts, price=price, done=false, ts=ts)); lastTs = ts
  action dropLast: events = events.pop
  action keepExpensive(minPrice: Nat): events = events.filter(e => e.price >= minPrice)
  action sortByTs: events = events.sortBy((a, b) => decide(a.ts <= b.ts))
  invariant ordered: (all e in events: e.ts <= lastTs) and events.isSortedBy(e => e.ts)
  view: <span>{events.size}</span>
component BudgetCalc:
  state price    : Nat = 10
  state qty      : Nat = 2
  state maxPrice : Nat = 100
  state maxQty   : Nat = 50
  state total    : Nat = 200
  action setPrice(p: Nat): if p <= maxPrice: price = p
  action setQty(q: Nat): if q <= maxQty: qty = q
  action addTotal(delta: Nat): if total + delta <= 1000: total += delta
  invariant bounds: price <= maxPrice and qty <= maxQty and total <= 1000 and price * qty <= maxPrice * maxQty and total / 10 <= 100 and (qty + 1) * price == qty * price + price
  view: <span>{price * qty}</span>
component ExtendedDeck:
  collection cards : PositiveCard
  action addCard(nid: Nat): cards.push(PositiveCard.State(id=nid, score=1))
  action popCard: cards = cards.pop
  action flipDeck: cards = cards.reverse
  action sliceTop: cards = cards.extract(0, 5)
  action dropAt(i: Nat): cards = cards.eraseIdxIfInBounds(i)
  action swapCards(i: Nat, j: Nat): cards = cards.swapIfInBounds(i, j)
  action replaceAt(i: Nat, nid: Nat): cards = cards.setIfInBounds(i, PositiveCard.State(id=nid, score=5))
  action boostAt(i: Nat): cards = cards.modify(i, c => PositiveCard.State(id=c.id, score=c.score + 1))
  invariant deckSafe: PositiveCard.positive for_each cards
  view: <div>{for c in cards: <PositiveCard state={c}/>}</div>

-- `enum`, `record`, `schema` Option/Bare-Type Lawfulness & Proto Mapping
enum GamePhase:
  lobby
  playing
enum RoleCard:
  none
  spy
  agent(role: String, note: String?)
enum TickEvent:
  empty
  tick(t: Nat, label: String)
schema RoomSnapshotRec:
  code       : String
  phase      : GamePhase = .lobby
  spyCount   : Nat       = 1 where 1 <= spyCount <= 4
  scores     : (String, Nat)[] = []
  role       : RoleCard? = none
  secretLoc  : String?   = none
  example sample: code = "ABCD", phase = .playing, spyCount = 2, scores = [("a", 1)], role = some(.agent("Pilot", some("hi"))), secretLoc = some("Airplane")
schema OptSchema:
  title : String
  note  : String?
  phase : GamePhase?
deriving instance Repr, DecidableEq for OptSchema
schema CustomInhabRec:
  count : Nat
instance : Inhabited CustomInhabRec := ⟨{ count := 42 }⟩
example (s : OptSchema) : String × Option String := (s.title, s.note)
example : (default : GamePhase) = .lobby ∧ (default : RoomSnapshotRec).phase = .lobby ∧ (default : RoomSnapshotRec).spyCount.val = 1 ∧ (default : CustomInhabRec).count = 42 := ⟨rfl, rfl, rfl, rfl⟩
example : LawfulJson GamePhase × LawfulProto GamePhase × LawfulJson (Option GamePhase) ×
    LawfulJson RoleCard × LawfulProto RoleCard × LawfulJson (Option RoleCard) ×
    LawfulJson TickEvent × LawfulProto TickEvent × LawfulJson RoomSnapshotRec × LawfulProto RoomSnapshotRec ×
    LawfulJson (Option RoomSnapshotRec) × LawfulJson OptSchema × LawfulProto OptSchema ×
    DecidableEq RoomSnapshotRec × Repr RoomSnapshotRec × DecidableEq RoleCard × Repr RoleCard :=
  (inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
   inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance)
mapping RoomFrameMap:
  from RoomSnapshotRec
  to String
  encode(v): return Proto.encodeHex(Proto.encode(v))
  decode(frame):
    let bytes = Proto.decodeHex(frame)?
    return Proto.decode(bytes)?
bad_enum "duplicate variant `a` in `enum DupEnum`" DupEnum : a || a
bad_enum "duplicate field `x` in variant `pair` of `enum DupEnumField`" DupEnumField : pair(x: Nat, x: String)
bad_schema "Schema `BadRecDefault` default for field `qty` failed `where` constraint" BadRecDefault : qty : Nat = 99 where 1 <= qty <= 4
bad_schema "Schema `UnsatRec` is unsatisfiable: field `qty` has contradictory `where` constraints" UnsatRec : qty : Nat where 10 <= qty, qty <= 2

-- Pure `fn` contracts (`requires`, `ensures`, `if`, `blindTo`)
schema SecretRoom:
  code           : String
  secretLocation : String
  secretPack     : String
  spyIds         : String[]
schema RedactedView:
  code           : String
  secretLocation : String?
  secretPack     : String?
  isSpy          : Bool
fn projectSecretRoom(room: SecretRoom, viewerId: String) -> RedactedView:
  requires room.code != ""
  if viewerId in room.spyIds:
    ensures result.secretLocation == none, result.secretPack == none, result.isSpy == true
    blindTo room.{secretLocation, secretPack}
  if viewerId not in room.spyIds:
    ensures result.secretLocation == some(room.secretLocation), result.isSpy == false
  let isSpy = viewerId in room.spyIds
  return { code = room.code, secretLocation = none if isSpy else some(room.secretLocation), secretPack = none if isSpy else some(room.secretPack), isSpy = isSpy }
fn clampRoundMins(n: Nat) -> Nat:
  ensures 3 <= result, result <= 15
  if n < 3: return 3
  if n > 15: return 15
  return n
fn hideWholeParam(pubTag: String, secret: String, masked: Bool) -> String:
  if masked:
    ensures result == pubTag
    blindTo secret
  if masked: return pubTag
  return secret
fn redactSingleField(room: SecretRoom, viewerId: String) -> String?:
  if viewerId in room.spyIds: blindTo room.secretLocation
  if viewerId in room.spyIds: return none
  return some(room.secretLocation)
check_decls [projectSecretRoom_ensures_1, projectSecretRoom_ensures_2, projectSecretRoom_blindTo,
  clampRoundMins_ensures, hideWholeParam_ensures, hideWholeParam_blindTo, redactSingleField_blindTo]
bad_fn "`blindTo room.secretLocation` failed in `leakyProjection`" leakyProjection(room: SecretRoom, viewerId: String) -> RedactedView ||
  if viewerId in room.spyIds:
    ensures result.secretLocation == none
    blindTo room.secretLocation
  : let isSpy = viewerId in room.spyIds || return { code = f"{room.code}:{room.secretLocation}", secretLocation = none if isSpy else some(room.secretLocation), secretPack = none, isSpy = isSpy }
bad_fn "`ensures` contract failed for `badClamp`" badClamp(n: Nat) -> Nat || ensures result <= 10 : return n

-- Component `fn` (pure + state-mutating), implication invariants, per-action `prove:`, and keyed hoisted sub-components
enum ViewTab:
  home
  room(code: String)
component PureFnBadge:
  prop name : String
  fn label(prefixStr: String) -> String: return f"{prefixStr}: {name}"
  view: <span>{label("Hi")}</span>
component CompFnAndProve:
  state tab : ViewTab = .home
  state title : String = ""
  state busy : Bool = false
  state counter : Nat = 0
  fn isHome() -> Bool:
    match tab:
      case .home: return true
      case .room(_): return false
  fn heading(pfx: String) -> String: return f"{pfx} {title} ({counter})"
  fn applyRoom(t: String, clearBusy: Bool):
    title = t
    if clearBusy: busy = false
  action openRoom(c: String, t: String): tab = .room(c); applyRoom(t, true)
  action goHome: tab = .home; title = ""; busy = false
  action rename(t: String):
    match tab:
      case .home: pass
      case .room(_): applyRoom(t, false)
  action inc: counter += 1
  invariant homeClean: isHome() -> title == ""
  invariant nonNeg: counter >= 0
    prove:
      case inc: omega
  view: <div><span>{heading("Room")}</span><PureFnBadge name={title}/></div>
check_decls [CompFnAndProve.homeClean, CompFnAndProve.nonNeg, CompFnAndProve.app_view_eq]
bad_comp "unknown action/message `noSuchAction` in `prove:` on invariant `BadProveCase.ok`" BadProveCase : state n : Nat = 0 || action inc: n += 1 ||
  invariant ok: n >= 0
    prove:
      case noSuchAction: omega
  || view: <span>{n}</span>
bad_comp "`fn reset` has no `-> ReturnType` and mutates component state" BadMutFnInPure : prop x : Nat = 0 || fn reset(): pass || view: <span>{x}</span>

-- Keyed / conditional hoisted sub-components with lifecycle reset, `start`, and lifted `subscribe`
server SubHostSrv:
  channel feed(code: String) -> String:
    on_join -> String: return code
component SubRoomChild:
  prop code : String
  state ticks : Nat = 0
  state latest : String = ""
  start Cmd.after(10, .tick)
  subscribe ws = SubHostSrv.feed(code):
    on_message(msg): latest = msg
  action tick: ticks += 1
  view: <div><span>{code}</span><span>{ticks}</span><span>{latest}</span></div>
component SubHostShell:
  state tab : ViewTab = .home
  action openRoom(c: String): tab = .room(c)
  action leaveRoom: tab = .home
  view:
    <div>
      {match tab:
        case .home: <p>Home</p>
        case .room(code): <SubRoomChild key={code} code={code}/>}
    </div>
example :
  let (s1, _) := SubHostShell.update SubHostShell.init (.openRoom "AAA")
  let (s2, _) := SubHostShell.update s1 (._sub_0 .tick)
  let (s3, _) := SubHostShell.update s2 (.openRoom "BBB")
  let (s4, _) := SubHostShell.update s3 (._sub_0 .tick)
  let (s5, _) := SubHostShell.update s4 .leaveRoom
  s2._sub_0.ticks = 1 ∧ s3._sub_0.ticks = 0 ∧ s4._sub_0.ticks = 1 ∧ s5._sub_0.ticks = 0 ∧ SubHostShell.subscriptions.length = 1 := by decide

-- Pure component forwarding events to pure children, keyed local children, and `bind:` children
component PureLangSelect:
  prop lang : String
  event onSelect(code : String)
  event onReset
  view: <div class="lang-select"><button class="fr" onClick={onSelect("fr")}>{lang}</button><button class="rst" onClick={onReset}>Reset</button></div>
component KeyedTagPicker:
  state count : Nat = 0
  event onPick(tag : String)
  action pick: count += 1; onPick.emit("picked")
  view: <button class="tag-pick" onClick={.pick}>{count}</button>
component PureContentPage:
  prop lang : String
  bind query : String = ""
  event onLang(code : String)
  event onClear
  event onTag(tag : String)
  view:
    <section class="content-page">
      <PureLangSelect lang={lang} onSelect={onLang} onReset={onClear}/>
      <PureLangSelect lang={lang} onSelect={c => onLang(c)} onReset={onClear}/>
      <SearchBar bind:query={query} onClear={query = ""} onSubmitQuery={onTag}/>
      <KeyedTagPicker key="tp" onPick={onTag}/>
    </section>
component PureForwardHost:
  state lang : String = "en"
  state query : String = ""
  state tag : String = ""
  action setLang(c : String): lang = c
  view: <main><PureContentPage lang={lang} bind:query={query} onLang={.setLang} onClear={lang = "en"} onTag={tag = _}/></main>
check_decls [PureForwardHost.app_view_eq]
example : Type → Type := PureContentPage.Props

/-! ## Track 2, 4 & 5: Session propagation, query controls, async component `fn`, nested struct mutation, or-patterns, JSX `let`, CSS dup check, `Qed.Str`/`Qed.Time` -/
enum PolishTab:
  overview
  db         = "database"
  deployLogs = "deploy-logs"
enum PolishEvent:
  deployStarted(id: String) = "deploy-started"
  deployFailed(err: String) = "deploy-failed"
field ShortSlug : String where s => 1 <= s.length <= 32
field ServicePort : Nat where p => 1 <= p <= 65535
field BoundedStr(maxLen: Nat) : String where s => 1 <= s.length <= maxLen
schema ServiceFieldForm:
  slug : ShortSlug
  port : ServicePort
  tag  : BoundedStr 16
router PolishRoute:
  home                              = "/"
  account                           = "/account"
  tokens                            = "/tokens"
  item                              = "/items/:id"
  appTab(slug: ShortSlug, tab: PolishTab) = "/apps/:slug/:tab"
  report(day: Date)                 = "/reports/:day"
schema NestedFilter:
  page   : Nat      = 0
  search : String   = ""
  tags   : String[] = []
server PolishRpcSrv:
  rpc listItems(q: String) -> String[]!: return [q, "item-a"]
  rpc saveItem(name: String) -> String!:
    if name == "": return fail(.badInput, "empty")
    return f"saved:{name}"
component SessionChildPanel:
  session user
  prop tab : String = "main"
  state clicks : Nat = 0
  action inc: clicks += 1
  view: <div class="sess-child">{user.getD("anon")}:{tab}:{clicks}</div>
component SessionParentShell:
  route current : PolishRoute = .home:
    case .account | .tokens: visits += 1
    case _: pass
  state visits : Nat = 0
  state flt : NestedFilter = { page = 0, search = "", tags = ["a"] }
  state lastSaved : String = ""
  query items = PolishRpcSrv.listItems(flt.search)
  query homeItems = PolishRpcSrv.listItems(flt.search) if current == .home
  head:
    title "Polish App"
    canonical f"https://qed.cloud{current}"
    case .account | .tokens:
      title "Settings"
      redirect PolishRoute.home, status = 301
    case _:
      title "Home"
      canonical PolishRoute.home
  fn doSave(label: String):
    let res = await PolishRpcSrv.saveItem(label) catch:
      case .badInput(e) | .failed(e): lastSaved = f"err:{e}"
    lastSaved = f"{label}->{res}"
    items.refetch()
  action saveCurrent: doSave(flt.search)
  action bumpNested: flt.page += 1; flt.tags.push("b"); flt.tags[0] = "z"
  action refreshItems: items.invalidate()
  action invBoth: invalidate(items, homeItems)
  action searchAndRefetch(q: String): flt.search = q; items.refetch()
  action refetchThenSearch(q: String): items.refetch(); flt.search = q
  action goExternal: Cmd.openExternal(url("https://checkout.stripe.com/c/pay_1"))
  action optimisticAdd(x: String): items.update(xs => xs.push(x))
  action replaceItems(xs: String[]): items.set(xs)
  view:
    <main>
      <input bind={flt.search}/>
      <button onClick={flt.page = 0}>Reset Page</button>
      <button onClick={items.refetch()}>Refetch</button>
      <SessionChildPanel key={match current: case .account | .tokens: "settings" case _: "other"} tab={match current: case .account | .tokens: "settings" case _: "main"}/>
      {let trimmed = Qed.Str.trim(flt.search); let ts = Qed.Time.formatIsoUtc(0); <p class="let-view">{trimmed}|{ts}</p>}
      <ul>{let xs = flt.tags; for t in xs: <li>{t}</li>}</ul>
    </main>
style spliceBaseBtn:
  padding: 4px 8px
style spliceActiveBtn:
  background-color: #2563eb
component MultiStyleSpliceDemo:
  state active : Bool = false
  action toggle: active = not active
  view: <button {spliceBaseBtn} {spliceActiveBtn if active} onClick={.toggle}>Go</button>
bad_style "duplicate CSS property `padding` in the same style block" BadDupCssProp :
  padding: 4px
  padding: 8px
bad_comp "recursive `await` call cycle in component `fn ping`" BadAsyncCycleComp : state x : String = "" ||
  fn ping():
    let _r = await PolishRpcSrv.saveItem("a") catch:
      case _: pass
    pong()
  || fn pong(): ping() || action go: ping() || view: <span>{x}</span>
bad_comp "cannot use `await` inside pure component `fn pureBad`; remove `-> ReturnType` for an async mutating helper, or perform `await` in the calling `action`" BadPureAwaitComp : state x : String = "" || fn pureBad() -> String: let r = await PolishRpcSrv.saveItem("a"); return r || view: <span>{x}</span>
bad_enum "duplicate wire name `dup` in `enum BadDupWireEnum`" BadDupWireEnum : a = "dup" || b = "dup"
expect_err "Field `BadImpossibleField` is unsatisfiable" in field BadImpossibleField : Nat where n => n > 10, n < 5
check_decls [ShortSlug.satisfiable, ServicePort.satisfiable, SessionParentShell.app_view_eq, MultiStyleSpliceDemo.app_view_eq]

/-! ## Wide Schema Proof Synthesis (24 fields under default heartbeats) -/
schema Wide24Schema:
  f01 : String
  f02 : String
  f03 : String
  f04 : String
  f05 : String
  f06 : String
  f07 : String
  f08 : String
  f09 : String
  f10 : String
  f11 : String
  f12 : String
  f13 : String
  f14 : String
  f15 : String
  f16 : String
  f17 : Nat
  f18 : Nat
  f19 : Bool
  f20 : Bool
  f21 : String where 1 <= f21.length <= 64
  f22 : Nat where 1 <= f22 <= 100
  f23 : String
  f24 : String
example : Qed.LawfulJson Wide24Schema × Qed.LawfulProto Wide24Schema × Qed.LawfulJson Wide24Schema.Draft :=
  (inferInstance, inferInstance, inferInstance)

/-! ## Grammar Upgrades (`private`/`const`, `for`/`mut`/`range`/`break`/`continue`, `??`, enum examples) -/
private schema PrivateToken:
  label : String where 1 <= label.length <= 16
  score : Nat    where score <= 100
  example okTok: label = "alpha", score = 42
  rejects badTok: label = "", score = 5
private enum PrivateStage:
  queued
  running = "in-progress"
  done
private enum PrivateMsg:
  ping
  note(text: String)
const DEFAULT_STEP : Nat = 3
private const SECRET_CAP = 100
const ALLOWED_REGIONS : String[] = ["us", "eu"]
enum OrderRole:
  viewer
  editor
  admin
fn OrderRole.rank(self: OrderRole) -> Nat:
  match self:
    case .viewer: return 0
    case .editor: return 1
    case .admin: return 2
fn OrderRole.atLeast(self: OrderRole, other: OrderRole) -> Bool:
  example refl(r: OrderRole): r.atLeast(r) == true
  example trans(a: OrderRole, b: OrderRole, c: OrderRole) where a.atLeast(b) == true, b.atLeast(c) == true: a.atLeast(c) == true
  example rankMonotone(r: OrderRole, bonus: Nat): r.rank() + bonus >= r.rank()
  return self.rank() >= other.rank()
private fn OrderRole.isPrivileged(self: OrderRole) -> Bool: return self.atLeast(.editor)
fn sumRange1(n: Nat) -> Nat:
  let mut acc = 0
  for i in range(n): acc += i
  return acc
fn sumRange2(lo: Nat, hi: Nat) -> Nat:
  let mut acc = 0
  for i in range(lo, hi): acc += i
  return acc
fn sumRange3(lo: Nat, hi: Nat, step: Nat) -> Nat:
  let mut acc = 0
  for i in range(lo, hi, step): acc += i
  return acc
fn findFirstOver(xs: Nat[], limit: Nat) -> Nat?:
  for x in xs:
    if x <= limit: continue
    if x > 100: break
    return some(x)
  return none
fn collectEvens(n: Nat) -> Nat[]:
  let mut out : Nat[] = []
  for i in range(0, n, 2): out.push(i)
  return out
fn nestedBreak(rows: Nat, cols: Nat) -> Nat:
  let mut total = 0
  for r in range(rows):
    for c in range(cols):
      if c == 2: break
      total += r * 10 + c
  return total
fn mutArith(n: Nat) -> Nat:
  let mut x = n
  x -= 2
  x = x + 1
  return x
fn coalesceOpt(a: Nat?, b: Nat?, fallback: Nat) -> Nat: return a ?? b ?? fallback
fn coalesceRes(r: Resource Nat, fallback: Nat) -> Nat: return r ?? fallback
fn coalesceCached(c: Cached Nat, fallback: Nat) -> Nat: return c ?? fallback
example : (let tok := PrivateToken.okTok
  tok.label.val == "alpha" && tok.score.val == 42 && LawfulKey.toKey PrivateStage.running == "in-progress" &&
  (match PrivateMsg.note "ok" with | .note s => s == "ok" | .ping => false) &&
  DEFAULT_STEP == 3 && SECRET_CAP == 100 && ALLOWED_REGIONS == #["us", "eu"] &&
  OrderRole.admin.isPrivileged && !OrderRole.viewer.isPrivileged) = true := by decide +kernel
bad_fn "`break` can only be used inside a `for` loop" badBreakOutsideFor(n: Nat) -> Nat : break || return n
bad_fn "`continue` can only be used inside a `for` loop" badContinueOutsideFor(n: Nat) -> Nat : continue || return n
bad_fn "cannot assign to `x` in pure" badAssignImmutable(n: Nat) -> Nat : let x = n || x = 5 || return x
bad_fn "mutable variable `acc` is already declared in this scope" badDupLetMut(n: Nat) -> Nat : let mut acc = 0 || let mut acc = n || return acc
bad_fn "shadows mutable variable `acc`" badForShadowMut(n: Nat) -> Nat : let mut acc = 0 || for acc in range(n): acc += 1 || return acc
bad_fn "`range(...)` expects 1, 2, or 3 arguments" badRangeZero() -> Nat : let mut s = 0 || for i in range(): s += i || return s
bad_fn "`range(...)` expects 1, 2, or 3 arguments" badRangeFour() -> Nat : let mut s = 0 || for i in range(0, 10, 2, 1): s += i || return s

/-! ## Ground Kernel `example`, Cons Patterns, Tuple `let`, Multiline Signatures & Type Inference -/
fn parseBigJsonAndEncode(raw: String) -> Except String String:
  example largeJsonGround:
    parseBigJsonAndEncode("{\"service\":\"qed-cloud-api\",\"region\":\"us-east1\",\"replicas\":3,\"env\":\"production\",\"tags\":[\"verified\",\"kernel\",\"kernel-checked\",\"fast-decide\"],\"description\":\"ground example over 150 characters touching Json.parse, String.toUTF8, and Base64\"}") == .ok("cWVkLWNsb3VkLWFwaQ==")
  match Qed.Json.parse(raw):
    case .error(e): return .error(e)
    case .ok(j):
      let name = j.strAtD("service", "")
      return .ok(Qed.Base64.encode(name.toUTF8))
fn multilineAndErgo(
  xs: List Nat,
  pair: (Nat, String),
  arr: String[]
) -> Except String Json:
  example ergoPureWorks:
    multilineAndErgo([10, 20], (3, "ok"), ["first"]) == .ok(Json.object([("sum", Qed.toJson(33)), ("first", .str("first")), ("items", Json.array([.str("ok")]))]))
  let (n, label) = pair
  let mut items : List Json = []
  items = .str(label) :: items
  let mut total = n
  match xs:
    case []: total += 0
    case a :: b :: _: total += a + b
    case a :: _: total += a
  let first = arr[0]? ?? "none"
  return .ok(Json.object([("sum", Qed.toJson(total)), ("first", .str(first)), ("items", Json.array(items.toArray))]))
component ErgoComp:
  state items : List Nat = [1, 2, 3]
  state out   : Nat = 0
  action step(p: (Nat, Nat)):
    let (a, b) = p
    match items:
      case []: out = a + b
      case h :: rest: items = rest; out = h + a + b
  view: <div>{match items: case []: <span>"empty"</span> case h :: _: <span>{h}</span>}</div>

/-! ## Relational `ensures` (`all`, self-calls, one-armed `if`/`if let`, O(k + S) string injectivity) -/
fn isValidGcpSecretId(s: String) -> Bool:
  return s.length > 0 and s.length <= 255 and s.all(c => ('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z') or ('0' <= c and c <= '9') or c == '-' or c == '_')
fn mkGcpSecretId?(tenantId: Nat, appId: Nat, env: String, name: String) -> String?:
  ensures if let some(id) = result: isValidGcpSecretId(id)
  ensures all t2: Nat, a2: Nat, e2: String, n2: String:
    if result.isSome and result == mkGcpSecretId?(t2, a2, e2, n2):
      tenantId == t2 and appId == a2 and env == e2 and name == n2
  if env not in ["dev", "staging", "prod"]: return none
  if name.length == 0 or name.length > 64: return none
  if not name.all(c => ('a' <= c and c <= 'z') or ('0' <= c and c <= '9') or c == '_'): return none
  if toString(tenantId).length > 20 or toString(appId).length > 20: return none
  return some(f"qed-t{tenantId}-a{appId}-{env}-{name}")
fn mkBucketKey?(tenantId: Nat, env: String, name: String) -> String?:
  ensures all t2, e2, n2: result.isSome and result == mkBucketKey?(t2, e2, n2) -> tenantId == t2 and env == e2 and name == n2
  if env.length == 0 or not env.all(c => ('a' <= c and c <= 'z') or ('0' <= c and c <= '9')): return none
  if name.length == 0: return none
  return some(f"bkt/{tenantId}/{env}/{name}")
fn mkIntKey?(x: Int, y: Int, tag: String) -> String?:
  ensures all x2, y2, t2: if result.isSome and result == mkIntKey?(x2, y2, t2): x == x2 and y == y2 and tag == t2
  if tag.length == 0 or tag.contains('/'): return none
  return some(f"k/{x}/{y}/{tag}")
fn isCleanSlug(s: String) -> Bool:
  return s.length > 0 and s.all(c => ('a' <= c and c <= 'z') or ('0' <= c and c <= '9'))
fn mkHelperKey?(org: String, repo: String) -> String?:
  ensures all o2, r2: if result.isSome and result == mkHelperKey?(o2, r2): org == o2 and repo == r2
  if not isCleanSlug(org) or not isCleanSlug(repo): return none
  return some(f"gh:{org}/{repo}")
fn clamp0_100(x: Int) -> Int:
  ensures all x2: Int: x <= x2 -> result <= clamp0_100(x2)
  if x < 0: return 0
  if x > 100: return 100
  return x
fn normalizePort(p: Nat) -> Nat:
  ensures normalizePort(result) == result
  if p == 0: return 80
  if p > 65535: return 65535
  return p
fn mkScopedKey(isAdmin: Bool, tenantId: Nat) -> String:
  ensures all b2: Bool, t2: Nat: result == mkScopedKey(b2, t2) -> isAdmin == b2 and tenantId == t2
  if isAdmin: return f"adm-{tenantId}"
  return f"usr-{tenantId}"
fn mkDeepKey10?(a: Nat, b: Nat, c: Nat, g: Nat, d: String, e: String, f: String) -> String?:
  ensures all a2, b2, c2, g2, d2, e2, f2:
    if result.isSome and result == mkDeepKey10?(a2, b2, c2, g2, d2, e2, f2):
      a == a2 and b == b2 and c == c2 and g == g2 and d == d2 and e == e2 and f == f2
  if a == 0: return none
  if b == 0: return none
  if c == 0: return none
  if g == 0: return none
  if a > 1000000: return none
  if b > 1000000: return none
  if d not in ["us", "eu", "ap"]: return none
  if e.length == 0 or not e.all(ch => ('a' <= ch and ch <= 'z') or ('0' <= ch and ch <= '9')): return none
  if f.length == 0 or f.length > 64: return none
  if toString(c).length > 10 or toString(g).length > 10: return none
  return some(f"pfx-{a}-{b}-{c}-{g}-{d}-{e}-{f}")
check_decls [mkGcpSecretId?_ensures_1, mkGcpSecretId?_ensures_2, mkBucketKey?_ensures, mkIntKey?_ensures,
  mkHelperKey?_ensures, clamp0_100_ensures, normalizePort_ensures, mkScopedKey_ensures, mkDeepKey10?_ensures]
bad_fn "`ensures` contract failed for `mkBadSecretId?`:\n  • action `right` must satisfy:  env = e2\n  • action `right` must satisfy:  name = n2" mkBadSecretId?(tenantId: Nat, env: String, name: String) -> String? ||
  ensures all t2: Nat, e2: String, n2: String: if result.isSome and result == mkBadSecretId?(t2, e2, n2): tenantId == t2 and env == e2 and name == n2 :
  if env not in ["dev", "dev-eu", "prod"]: return none || if name.length == 0: return none || return some(f"qed-t{tenantId}-{env}-{name}")
bad_fn "`ensures` contract failed for `mkBadConcat`:\n  • action `left` must satisfy:  a = a2\n  • action `right` must satisfy:  b = b2" mkBadConcat(a: Nat, b: Nat) -> String || ensures all a2: Nat, b2: Nat: result == mkBadConcat(a2, b2) -> a == a2 and b == b2 : return f"k-{a}{b}"
bad_fn "`ensures` contract failed for `mkBadValidity?`" mkBadValidity?(tenantId: Nat, name: String) -> String? || ensures if let some(id) = result: isValidGcpSecretId(id) : if name.length == 0: return none || return some(f"k-{tenantId}-{name}")

/-! ## Issue #22 Section 2: Ground `String.all`, Helper `Char -> Bool`, `List.mem_cons`, `::`, `qedSeqLit%`, `Repr Json` -/
fn isGcpSecretCharHelper(c: Char) -> Bool:
  if c == '-' or c == '_': return true
  return c.isLower or c.isUpper or c.isDigit
fn isValidGcpSecretIdHelper(s: String) -> Bool:
  example ok: isValidGcpSecretIdHelper("qed-t1-a2-prod-api_key") == true
  example bad: isValidGcpSecretIdHelper("bad/key") == false
  return s.length > 0 and s.length <= 255 and s.all(isGcpSecretCharHelper)
fn mkSecretWithHelper?(tenantId: Nat, name: String) -> String?:
  ensures if let some(id) = result: isValidGcpSecretIdHelper(id) and id.toList.all(isGcpSecretCharHelper)
  if name.length == 0 or name.length > 64: return none
  if not name.all(c => c.isLower or c.isDigit or c == '_'): return none
  if toString(tenantId).length > 20: return none
  return some(f"t-{tenantId}-{name}")
schema Sec2AlertEv:
  kind: String
  msg: String
schema Sec2Snap:
  requests: Nat
  errors: Nat
  latencyMs: Nat
fn evaluateSec2Alerts(snap: Sec2Snap) -> Sec2AlertEv[]:
  ensures snap.requests == 0 -> (all ev in result: ev.kind != "high_error_rate")
  if snap.requests > 0 and snap.errors * 100 >= snap.requests * 5:
    return [{ kind = "high_error_rate", msg = f"errors={snap.errors}" }]
  if snap.latencyMs > 1000:
    return [{ kind = "high_latency", msg = f"latency={snap.latencyMs}ms" }]
  return []
fn evaluateSec2AlertsMut(snap: Sec2Snap) -> Sec2AlertEv[]:
  ensures snap.requests == 0 -> (all ev in result: ev.kind != "high_error_rate")
  let mut out : Sec2AlertEv[] = []
  if snap.requests > 0 and snap.errors * 100 >= snap.requests * 5:
    out.push({ kind = "high_error_rate", msg = f"errors={snap.errors}" })
  if snap.latencyMs > 1000:
    out.push({ kind = "high_latency", msg = f"latency={snap.latencyMs}ms" })
  if snap.latencyMs > 5000:
    out.push({ kind = "critical_latency", msg = f"crit={snap.latencyMs}ms" })
  return out
fn consAndJsonExample(n: Nat, xs: List Nat) -> List Nat:
  example consOk: consAndJsonExample(2, [10]) == 3 :: 4 :: [10]
  example jsonPolOk:
    let pol = Json.object([("k", .str("v")), ("bindings", Json.array([Json.object([("role", .str("r")), ("members", Json.array([.str("m")]))])]))]);
    pol.strAtD("k") == "v"
  return n + 1 :: n + 2 :: xs
schema JsonPayloadRec:
  label: String
  body: Json
example : Repr JsonPayloadRec := inferInstance
check_decls [isValidGcpSecretIdHelper_example_ok, isValidGcpSecretIdHelper_example_bad, mkSecretWithHelper?_ensures,
  evaluateSec2Alerts_ensures, evaluateSec2AlertsMut_ensures, consAndJsonExample_example_consOk, consAndJsonExample_example_jsonPolOk]
bad_fn "`example` failed for `badGroundStrAll`" badGroundStrAll(s: String) -> Bool || example wrong: badGroundStrAll("abc") == false : return s.all(c => c >= 'a' and c <= 'z')
bad_fn "`example` failed for `badGroundBigBase64`" badGroundBigBase64(s: String) -> String ||
  example wrong: badGroundBigBase64("abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz") == "wrong" :
  return Qed.Base64.encode(s.toUTF8)

/-! ## Issue #22 Section 1.3: Pure `fn` `for`-Loop Invariants (Phase A + Phase B + Diagnostics) -/
schema LoopShard:
  id     : String
  active : Bool
  used   : Nat
  cap    : Nat
fn selectAvailableShard(shards: LoopShard[]) -> LoopShard?:
  ensures if let some(b) = result: b in shards
  ensures if let some(b) = result: b.active and b.used < b.cap
  ensures if let some(b) = result: all s in shards: (s.active and s.used < s.cap) -> b.used <= s.used
  ensures (any s in shards: s.active and s.used < s.cap) -> result.isSome
  let mut best : LoopShard? = none
  for shard in shards:
    if shard.active and shard.used < shard.cap:
      match best:
        case none: best = some(shard)
        case some(cur):
          if shard.used < cur.used: best = some(shard)
  return best
fn findActiveShard(shards: LoopShard[]) -> LoopShard?:
  ensures if let some(b) = result: b in shards and b.active
  ensures (any s in shards: s.active) -> result.isSome
  for shard in shards:
    if shard.active: return some(shard)
  return none
fn filterActiveShards(shards: LoopShard[]) -> LoopShard[]:
  ensures all e in result: e in shards and e.active
  ensures result.size <= shards.size
  let mut out : LoopShard[] = []
  for shard in shards:
    if shard.active: out.push(shard)
  return out
fn sumPositiveLoop(xs: Nat[]) -> Nat:
  ensures result >= xs.size
  let mut acc : Nat = 0
  for x in xs:
    acc = acc + x + 1
  return acc
fn countToLoop(n: Nat) -> Nat:
  ensures result == n
  let mut acc : Nat = 0
  for _i in range(n):
    acc = acc + 1
  return acc
fn guardedLoopSum(xs: Nat[]) -> Nat:
  ensures result >= xs.size
  if xs.size == 0: return 0
  let mut acc : Nat = 0
  for x in xs:
    acc = acc + x + 1
  return acc
fn findFirstGtLoop(xs: Nat[], threshold: Nat) -> Nat?:
  ensures if let some(v) = result: v in xs and v > threshold
  let mut found : Nat? = none
  for x in xs:
    if x <= threshold: continue
    found = some(x)
    break
  return found
schema LoopCand:
  id       : String
  active   : Bool
  weight   : Nat
  priority : Nat
fn loopCandScore(x: LoopCand) -> Nat:
  return x.weight * 2 + x.priority
fn pickBestCand(items: LoopCand[]) -> LoopCand?:
  ensures if let some(b) = result: b in items and b.active
  ensures if let some(b) = result: all x in items: x.active -> loopCandScore(b) >= loopCandScore(x)
  ensures (any x in items: x.active) -> result.isSome
  let mut best : LoopCand? = none
  let mut bestScore : Nat = 0
  for item in items:
    invariant if let some(b) = best: bestScore == loopCandScore(b)
    if item.active:
      let sc = loopCandScore(item)
      if best.isNone or sc > bestScore:
        best = some(item)
        bestScore = sc
  return best
fn pickBestActiveCand(items: LoopCand[]) -> LoopCand?:
  ensures if let some(b) = result: b in items and b.active
  ensures if let some(b) = result: all x in items: x.active -> b.weight <= x.weight
  let mut active : LoopCand[] = []
  for item in items:
    invariant all a in active: a in items and a.active
    invariant all x in seen: x.active -> x in active
    if item.active: active.push(item)
  let mut best : LoopCand? = none
  for item in active:
    match best:
      case none: best = some(item)
      case some(cur):
        if item.weight < cur.weight: best = some(item)
  return best
fn triangularLoop(n: Nat) -> Nat:
  ensures 2 * result == n * (n + 1)
  let mut acc : Nat = 0
  for i in range(n):
    invariant 2 * acc == seen.length * (seen.length + 1) prove:
      subst ‹i = seen.length›
      have h : (seen.length + 1) * (seen.length + 1 + 1) = seen.length * (seen.length + 1) + 2 * (seen.length + 1) := by
        simp [Nat.mul_add, Nat.add_mul]; omega
      omega
    acc = acc + (i + 1)
  return acc
fn standaloneLoopInv(xs: Nat[]) -> Nat:
  let mut total : Nat = 0
  for x in xs:
    invariant total >= seen.length
    total = total + x + 1
  return total
fn multiClauseLoopInv(xs: Nat[]) -> Nat:
  ensures result >= xs.size
  let mut a : Nat = 0
  let mut b : Nat = 0
  for x in xs:
    invariant a >= seen.length, b >= a
    a = a + 1
    b = b + x + 1
  return b
fn nestedLoopSum(grid: Nat[][]) -> Nat:
  ensures result >= grid.size
  let mut total : Nat = 0
  for row in grid:
    invariant total >= seen.length
    let mut rowSum : Nat = 1
    for cell in row:
      invariant rowSum >= 1
      rowSum = rowSum + cell
    total = total + rowSum
  return total
fn sumWithInvGround(xs: Nat[]) -> Nat:
  example groundOk: sumWithInvGround([1, 2, 3]) == 9
  ensures result >= xs.size
  let mut acc : Nat = 0
  for x in xs:
    invariant acc >= seen.length
    acc = acc + x + 1
  return acc
check_decls [selectAvailableShard_ensures_1, selectAvailableShard_ensures_2, selectAvailableShard_ensures_3, selectAvailableShard_ensures_4,
  findActiveShard_ensures_1, findActiveShard_ensures_2, filterActiveShards_ensures_1, filterActiveShards_ensures_2,
  sumPositiveLoop_ensures, countToLoop_ensures, guardedLoopSum_ensures, findFirstGtLoop_ensures,
  pickBestCand_ensures_1, pickBestCand_ensures_2, pickBestCand_ensures_3,
  pickBestActiveCand_ensures_1, pickBestActiveCand_ensures_2,
  triangularLoop_ensures, standaloneLoopInv_loop_invariants, multiClauseLoopInv_ensures, nestedLoopSum_ensures,
  sumWithInvGround_ensures, sumWithInvGround_example_groundOk]
expect_err "loop invariant failed before the first iteration (`seen = []`):\n      must satisfy:  0 >= 1" in
  fn badLoopInit(xs: Nat[]) -> Nat:
    let mut acc : Nat = 0
    for x in xs:
      invariant acc >= 1
      acc = acc + x + 1
    return acc
expect_err "quantifies over the full collection without referencing `seen`" in
  fn badLoopFullColl(shards: LoopShard[]) -> LoopShard?:
    ensures if let some(b) = result: all s in shards: s.active -> b.used <= s.used
    let mut best : LoopShard? = none
    for shard in shards:
      invariant if let some(b) = best: all s in shards: s.active -> b.used <= s.used
      if shard.active:
        match best:
          case none: best = some(shard)
          case some(cur):
            if shard.used < cur.used: best = some(shard)
    return best
expect_err "updates multiple `let mut` variables; add an `invariant <expr>` inside the `for` loop" in
  fn badLoopMultiMut(items: LoopCand[]) -> LoopCand?:
    ensures if let some(b) = result: all x in items: x.active -> loopCandScore(b) >= loopCandScore(x)
    let mut best : LoopCand? = none
    let mut bestScore : Nat = 0
    for item in items:
      if item.active:
        let sc = loopCandScore(item)
        if best.isNone or sc > bestScore:
          best = some(item)
          bestScore = sc
    return best
expect_err "inner `for` loop; add an `invariant <expr>` inside the inner `for` loop too" in
  fn badLoopNested(grid: Nat[][]) -> Nat:
    ensures result >= grid.size
    let mut total : Nat = 0
    for row in grid:
      invariant total >= seen.length
      let mut a : Nat = 1
      let mut b : Nat = 0
      for cell in row:
        b = a
        a = a + cell
      total = total + b
    return total
expect_err "this function has multiple `for` loops; add an `invariant <expr>` inside the first `for` loop" in
  fn badLoopSeq(shards: LoopShard[]) -> LoopShard?:
    ensures if let some(b) = result: b in shards and b.active
    let mut active : LoopShard[] = []
    for shard in shards:
      if shard.active: active.push(shard)
    let mut best : LoopShard? = none
    for shard in active:
      best = some(shard)
    return best
expect_err "loop invariant held, but was not strong enough to prove `ensures` after the loop:\n      must satisfy:  acc >= xs.size + 10" in
  fn badLoopWeakInv(xs: Nat[]) -> Nat:
    ensures result >= xs.size + 10
    let mut acc : Nat = 0
    for x in xs:
      invariant acc >= seen.length
      acc = acc + x + 1
    return acc
expect_err "loop invariant was not preserved on an iteration step (`seen` -> `seen ++ [_x]`):\n      must satisfy:  acc + 1 >= (seen.length + 1) * 2" in
  fn badLoopStandaloneStep(xs: Nat[]) -> Nat:
    let mut acc : Nat = 0
    for _x in xs:
      invariant acc >= seen.length * 2
      acc = acc + 1
    return acc
expect_err "loop `invariant` clauses are only supported in pure `fn` functions" in
  server BadSrvLoopInv:
    state n : Nat = 0
    rpc ping(xs: Nat[]) -> Nat:
      for x in xs:
        invariant n >= 0
        n += x
      return n

/-! ## Verified Collection `min`, `max`, `sort`, `sortDesc`, `isSorted`, `isMinOf`, `isMaxOf`, `filter`, `map` -/
fn selectShardOneLiner(shards: LoopShard[]) -> LoopShard?:
  ensures if let some(b) = result: b in shards and b.active and b.used < b.cap
  ensures if let some(b) = result: all s in shards: (s.active and s.used < s.cap) -> b.used <= s.used
  ensures (any s in shards: s.active and s.used < s.cap) -> result.isSome
  ensures result.isMinOf(shards.filter(s => s.active and s.used < s.cap), s => s.used)
  example picksLeast:
    selectShardOneLiner([
      { id = "a", active = false, used = 0, cap = 10 },
      { id = "b", active = true, used = 5, cap = 10 },
      { id = "c", active = true, used = 2, cap = 10 }
    ]) == some({ id = "c", active = true, used = 2, cap = 10 })
  example noneFull:
    selectShardOneLiner([{ id = "a", active = true, used = 10, cap = 10 }]) == none
  return shards.filter(s => s.active and s.used < s.cap).min(s => s.used)

fn pickBestCandOneLiner(items: LoopCand[]) -> LoopCand?:
  ensures if let some(b) = result: b in items and b.active
  ensures if let some(b) = result: all x in items: x.active -> loopCandScore(x) <= loopCandScore(b)
  ensures (any x in items: x.active) -> result.isSome
  ensures result.isMaxOf(filter(items, x => x.active), loopCandScore)
  example bestScore:
    pickBestCandOneLiner([
      { id = "a", active = true, weight = 3, priority = 1 },
      { id = "b", active = true, weight = 2, priority = 10 },
      { id = "c", active = false, weight = 99, priority = 99 }
    ]) == some({ id = "b", active = true, weight = 2, priority = 10 })
  return max(filter(items, x => x.active), loopCandScore)

fn rankShardsLex(shards: LoopShard[]) -> LoopShard[]:
  ensures result.size == shards.size
  ensures all s in result: s in shards
  ensures all s in shards: s in result
  ensures result.isSorted(s => (Desc(s.active), s.used, Desc(s.cap), s.id))
  example orderCheck:
    rankShardsLex([
      { id = "d", active = false, used = 0, cap = 10 },
      { id = "b", active = true, used = 5, cap = 10 },
      { id = "a", active = true, used = 5, cap = 20 },
      { id = "c", active = true, used = 1, cap = 5 }
    ]) == [
      { id = "c", active = true, used = 1, cap = 5 },
      { id = "a", active = true, used = 5, cap = 20 },
      { id = "b", active = true, used = 5, cap = 10 },
      { id = "d", active = false, used = 0, cap = 10 }
    ]
  return shards.sort(s => (Desc(s.active), s.used, Desc(s.cap), s.id))

fn pickShardTieBreak(shards: LoopShard[]) -> LoopShard?:
  ensures if let some(b) = result: b in shards
  ensures if let some(b) = result: all s in shards: b.used <= s.used and (b.used == s.used -> b.id <= s.id)
  return shards.min(s => (s.used, s.id))

fn firstSortedShard(shards: LoopShard[]) -> LoopShard?:
  ensures result.isMinOf(shards, s => s.used)
  return shards.sort(s => s.used)[0]?

fn sortedActiveShards(shards: LoopShard[]) -> LoopShard[]:
  ensures result.isSorted(s => s.used)
  ensures all s in result: s in shards and s.active
  ensures result.size <= shards.size
  return shards.sort(s => s.used).filter(s => s.active)

fn filterKeepsSorted(shards: LoopShard[]) -> LoopShard[]:
  requires shards.isSorted(s => s.used)
  ensures result.isSorted(s => s.used)
  return shards.filter(s => s.active)

fn freeFnCollPipeline(xs: Nat[]) -> Nat[]:
  ensures result.size <= xs.size
  ensures all y in result: y >= 1
  ensures isSorted(result)
  example pipelineOk: freeFnCollPipeline([3, 0, 2, 1]) == [2, 3, 4]
  return sort(map(filter(xs, x => x > 0), x => x + 1))

fn sortDescNats(xs: Nat[]) -> Nat[]:
  ensures result.size == xs.size
  ensures result.isSortedDesc()
  example descOk: sortDescNats([1, 4, 2, 3]) == [4, 3, 2, 1]
  return sortDesc(xs)

fn clampScalarMinMax(x: Nat, lo: Nat, hi: Nat) -> Nat:
  requires lo <= hi
  ensures result >= lo and result <= hi
  ensures result == min(max(x, lo), hi)
  if x < lo: return lo
  if x > hi: return hi
  return x

fn minListNats(xs: List Nat) -> Nat?:
  ensures result.isMinOf(xs)
  ensures if let some(m) = result: m in xs and (all x in xs: m <= x)
  return min(xs)

fn sortListCands(items: List LoopCand) -> List LoopCand:
  ensures result.length == items.length
  ensures isSorted(result, loopCandScore)
  return sort(items, loopCandScore)

fn checkSortedBool(xs: Nat[]) -> Bool:
  example yes: checkSortedBool([1, 2, 2, 5]) == true
  example no: checkSortedBool([1, 3, 2]) == false
  return xs.isSorted()

fn ensureSortedFlow(xs: Nat[]) -> Nat[]:
  ensures result.isSorted()
  ensures result.size == xs.size
  if xs.isSorted(): return xs
  return xs.sort()

fn shardCustomCmp(a: LoopShard, b: LoopShard) -> Bool:
  return a.used < b.used or (a.used == b.used and a.cap >= b.cap)

fn sortCustomLam(shards: LoopShard[]) -> LoopShard[]:
  ensures result.size == shards.size
  ensures result.isSorted((a, b) => a.used < b.used or (a.used == b.used and a.cap >= b.cap))
  return shards.sort((a, b) => a.used < b.used or (a.used == b.used and a.cap >= b.cap))

fn minCustomLam(shards: LoopShard[]) -> LoopShard?:
  ensures result.isMinOf(shards, (a, b) => a.used < b.used or (a.used == b.used and a.cap >= b.cap))
  return shards.min((a, b) => a.used < b.used or (a.used == b.used and a.cap >= b.cap))

fn sortCustomNamed(shards: LoopShard[]) -> LoopShard[]:
  ensures result.size == shards.size
  ensures result.isSorted(shardCustomCmp)
  return shards.sort(shardCustomCmp)

fn maxCustomNamed(shards: LoopShard[]) -> LoopShard?:
  ensures result.isMaxOf(shards, shardCustomCmp)
  return max(shards, shardCustomCmp)

fn manualLoopIsMinOf(shards: LoopShard[]) -> LoopShard?:
  ensures result.isMinOf(shards.filter(s => s.active and s.used < s.cap), s => s.used)
  let mut best : LoopShard? = none
  for s in shards:
    if s.active and s.used < s.cap:
      match best:
        case none: best = some(s)
        case some(cur):
          if s.used < cur.used: best = some(s)
  return best

fn manualLoopEqMin(shards: LoopShard[]) -> LoopShard?:
  ensures result == shards.min(s => s.used)
  let mut best : LoopShard? = none
  for s in shards:
    match best:
      case none: best = some(s)
      case some(cur):
        if s.used < cur.used: best = some(s)
  return best

fn manualLoopTieBreakStr(shards: LoopShard[]) -> LoopShard?:
  ensures if let some(b) = result: if let some(m) = shards.min(s => s.id): b.id == m.id
  let mut best : LoopShard? = none
  for s in shards:
    invariant if let some(b) = best: b in seen and (all x in seen: b.id <= x.id)
    invariant best.isNone -> seen.isEmpty
    match best:
      case none: best = some(s)
      case some(cur):
        if s.id <= cur.id: best = some(s)
  return best

fn sortStringsAndInts(xs: String[]) -> String[]:
  ensures result.isSorted()
  ensures result.size == xs.size
  example alpha: sortStringsAndInts(["pear", "apple", "banana"]) == ["apple", "banana", "pear"]
  example sortedProp: sortStringsAndInts(["c", "a", "b"]).isSorted()
  return sort(xs)

fn minIntVals(xs: Int[]) -> Int?:
  ensures result.isMinOf(xs)
  example negs: minIntVals([3, -5, 2, -1]) == some(-5)
  example minProp: minIntVals([3, -5, 2]).isMinOf([3, -5, 2])
  return min(xs)

fn sortPreservesSum(shards: LoopShard[]) -> LoopShard[]:
  ensures result.sumBy(s => s.used) == shards.sumBy(s => s.used)
  ensures result.isSorted(s => s.used)
  return shards.sort(s => s.used)

component SortedCollectionComp:
  state items : Nat[] = []
  action addPos(x: Nat):
    if x > 0:
      items = items.push(x).sort()
  action keepPos(xs: Nat[]):
    items = sort(map(filter(xs, x => x > 0), x => x + 1))
  invariant allPos: all x in items: x > 0
  invariant alwaysSorted: items.isSorted()
  view: <div>{items.size}</div>

check_decls [selectShardOneLiner_ensures_1, selectShardOneLiner_ensures_2, selectShardOneLiner_ensures_3, selectShardOneLiner_ensures_4,
  selectShardOneLiner_example_picksLeast, selectShardOneLiner_example_noneFull,
  pickBestCandOneLiner_ensures_1, pickBestCandOneLiner_ensures_2, pickBestCandOneLiner_ensures_3, pickBestCandOneLiner_ensures_4,
  rankShardsLex_ensures_1, rankShardsLex_ensures_2, rankShardsLex_ensures_3, rankShardsLex_ensures_4, rankShardsLex_example_orderCheck,
  pickShardTieBreak_ensures_1, pickShardTieBreak_ensures_2, firstSortedShard_ensures,
  sortedActiveShards_ensures_1, sortedActiveShards_ensures_2, sortedActiveShards_ensures_3, filterKeepsSorted_ensures,
  freeFnCollPipeline_ensures_1, freeFnCollPipeline_ensures_2, freeFnCollPipeline_ensures_3, freeFnCollPipeline_example_pipelineOk,
  sortDescNats_ensures_1, sortDescNats_ensures_2, sortDescNats_example_descOk,
  clampScalarMinMax_ensures_1, clampScalarMinMax_ensures_2,
  minListNats_ensures_1, minListNats_ensures_2, sortListCands_ensures_1, sortListCands_ensures_2,
  checkSortedBool_example_yes, checkSortedBool_example_no, ensureSortedFlow_ensures_1, ensureSortedFlow_ensures_2,
  sortCustomLam_ensures_1, sortCustomLam_ensures_2, minCustomLam_ensures,
  sortCustomNamed_ensures_1, sortCustomNamed_ensures_2, maxCustomNamed_ensures,
  manualLoopIsMinOf_ensures, manualLoopEqMin_ensures, manualLoopTieBreakStr_ensures,
  sortStringsAndInts_ensures_1, sortStringsAndInts_ensures_2, sortStringsAndInts_example_alpha, sortStringsAndInts_example_sortedProp,
  minIntVals_ensures, minIntVals_example_negs, minIntVals_example_minProp,
  sortPreservesSum_ensures_1, sortPreservesSum_ensures_2]

expect_err "custom comparator failed totality check" in
  fn badStrictCmp(shards: LoopShard[]) -> LoopShard[]:
    ensures result.isSorted((a, b) => a.used < b.used)
    return shards.sort((a, b) => a.used < b.used)
expect_err "custom comparator failed transitivity check" in
  fn badNonTransCmp(xs: Nat[]) -> Nat[]:
    ensures result.isSorted((a, b) => a <= b + 1)
    return xs.sort((a, b) => a <= b + 1)
expect_err "`ensures` contract failed for `badUnsortedFn`" in
  fn badUnsortedFn(xs: Nat[]) -> Nat[]:
    ensures result.isSorted()
    return xs

/-! ## Issue #22 Item 1: Bitwise (`&`, `|`, `^`, `<<`, `>>`, `~`), Exponentiation (`**`), & Constant-Time Equality -/

schema BitOpsOut:
  powVal  : Nat
  bandVal : Nat
  borVal  : Nat
  bxorVal : Nat
  shlVal  : Nat
  shrVal  : Nat
  negPow  : Int

fn bitOpsAndPowDemo(a: Nat, b: Nat) -> BitOpsOut:
  example powRightAssoc: (bitOpsAndPowDemo(2, 3)).powVal == 512
  example bitPrec:
    let r = bitOpsAndPowDemo(0xf0, 0x3c);
    r.bandVal == 0x30 and r.borVal == 0xfc and r.bxorVal == 0xcc and r.shlVal == 0x3c0 and r.shrVal == 0x3c and r.negPow == -4
  return {
    powVal = a ** 3 ** 2,
    bandVal = a & b,
    borVal = a | b,
    bxorVal = a ^ b,
    shlVal = a << 2,
    shrVal = a >> 2,
    negPow = -(2 : Int) ** 2
  }

fn bitPrecedenceChecks(x: Nat, opt: Nat?) -> (Bool, Nat, Nat):
  example tightCmp: (bitPrecedenceChecks(0x5a, none)).fst == true
  example tightCoal: (bitPrecedenceChecks(0, none)).snd.fst == 0x3
  example xorTighterThanOr: (bitPrecedenceChecks(0, some(5))).snd.snd == 1
  return (x & 0x0f == 0x0a, opt ?? 0x1 | 0x2, 1 | 2 ^ 3)

fn bitNotU8(x: UInt8) -> UInt8:
  example invLow: bitNotU8(0x0f) == 0xf0
  return ~x

fn fnv1a64(s: String) -> UInt64:
  example emptyVec: fnv1a64("") == 0xcbf29ce484222325
  example foobarVec: fnv1a64("foobar") == 0x85944171f73967e8
  let bytes = s.toUTF8
  let mut h : UInt64 = 0xcbf29ce484222325
  for i in range(bytes.size):
    let b = bytes.get!(i).toUInt64
    h = (h ^ b) * 0x100000001b3
  return h

fn u64ToHexLower(v: UInt64) -> String:
  example zeroHex: u64ToHexLower(0) == "0000000000000000"
  example deadbeefHex: u64ToHexLower(0x0123456789abcdef) == "0123456789abcdef"
  let digits = "0123456789abcdef".toUTF8
  let mut out = ByteArray.emptyWithCapacity(16)
  for i in range(16):
    let shift : UInt64 = ((15 - i) * 4).toUInt64
    let nib = ((v >> shift) & 0xf).toNat
    out = out.push(digits.get!(nib))
  return String.fromUTF8!(out)

fn verifyBytesCtEq(a: Bytes, b: Bytes) -> Bool:
  ensures result == (a == b)
  example eqSame: verifyBytesCtEq("secret".toUTF8, "secret".toUTF8) == true
  example neqDiff: verifyBytesCtEq("secret".toUTF8, "secrex".toUTF8) == false
  example neqLen: verifyBytesCtEq("abc".toUTF8, "abcd".toUTF8) == false
  return Bytes.ctEq(a, b)

fn verifyBytesDotCtEq(a: Bytes, b: Bytes) -> Bool:
  ensures result == (a == b)
  return a.ctEq(b)

fn verifyStrCtEq(a: String, b: String) -> Bool:
  ensures result == (a == b)
  example eqStr: verifyStrCtEq("tok_123", "tok_123") == true
  example neqStr: verifyStrCtEq("tok_123", "tok_124") == false
  return Str.ctEq(a, b)

fn verifyStrDotCtEq(a: String, b: String) -> Bool:
  ensures result == (a == b)
  return a.ctEq(b)

check_decls [bitOpsAndPowDemo_example_powRightAssoc, bitOpsAndPowDemo_example_bitPrec,
  bitPrecedenceChecks_example_tightCmp, bitPrecedenceChecks_example_tightCoal, bitPrecedenceChecks_example_xorTighterThanOr,
  bitNotU8_example_invLow, fnv1a64_example_emptyVec, fnv1a64_example_foobarVec,
  u64ToHexLower_example_zeroHex, u64ToHexLower_example_deadbeefHex,
  verifyBytesCtEq_ensures, verifyBytesCtEq_example_eqSame, verifyBytesCtEq_example_neqDiff, verifyBytesCtEq_example_neqLen,
  verifyBytesDotCtEq_ensures, verifyStrCtEq_ensures, verifyStrCtEq_example_eqStr, verifyStrCtEq_example_neqStr,
  verifyStrDotCtEq_ensures]

bad_fn "`ensures` contract failed for `badCtEqFlip`" badCtEqFlip(a: String, b: String) -> Bool ||
  ensures result == (a == b) : return not Str.ctEq(a, b)

/-! ## Grammar Simplification: Contextual Keywords, Unified `schema`, and `prove:` Everywhere -/

/-- Documented schema proving previously reserved Qed keywords are usable as field names. -/
schema ContextualKwFields:
  schema    : String = "public"
  style     : String = "default"
  theme     : String = "light"
  server    : String = "api"
  database  : String = "main"
  router    : String = "root"
  deploy    : String = "prod"
  external  : String = "ext"
  fullstack : String = "web"
  component : String = "app"
  keyframes : String = "fade"
  invariant : String = "ok"
  holds_in  : String = "v"
  assuming  : String = "p"

fn contextualKwParams(schema: String, style: String, theme: String, server: String, database: String, router: String) -> String:
  example allJoined: contextualKwParams("s", "st", "th", "sv", "db", "rt") == "s:st:th:sv:db:rt"
  return f"{schema}:{style}:{theme}:{server}:{database}:{router}"

private structure OpaquePlainVal where (n : Nat) deriving DecidableEq, Repr, Inhabited

schema PlainNonCodecSchema:
  tag : String = "ok"
  raw : OpaquePlainVal

private def encStep (n : Nat) : Nat := n + 7
private def decStep (n : Nat) : Except String Nat := if n >= 7 then .ok (n - 7) else .error "small"

mapping ManualProveMap:
  from x : Nat where x <= 50
  to   y : Nat where y <= 57
  encode(x): return encStep(x)
  decode(y): return decStep(y)?
  prove:
    case encode_ok:
      simp only [ManualProveMap.toTarget, ManualProveMap.SourceInv, ManualProveMap.TargetInv, encStep, Qed.Lang.QedVal.val_id] at *; omega
    case roundtrip:
      simp only [ManualProveMap.toSource, ManualProveMap.rawDecode, ManualProveMap.toTarget, ManualProveMap.SourceInv,
        encStep, decStep, Qed.Lang.QedVal.val_id, ge_iff_le] at *
      have h7 : ∀ n : Nat, 7 ≤ n + 7 := fun n => Nat.le_add_left 7 n
      simp only [h7, ↓reduceIte, Qed.MappingUnwrap.unwrap_ok, Except.bind, Nat.add_sub_cancel]
      exact dite_eq_left ‹_›

/-- Documented top-level invariant with explicit `prove:` block. -/
invariant topLevelManualProve: 2 + 2 == 4
  prove:
    rfl

check_decls [contextualKwParams_example_allJoined, ManualProveMap.encode_ok, ManualProveMap.roundtrip,
  ManualProveMap.decode_encode, topLevelManualProve]
example : (default : ContextualKwFields).schema = "public" ∧ (default : ContextualKwFields).router = "root" ∧
    (default : PlainNonCodecSchema).tag = "ok" := ⟨rfl, rfl, rfl⟩

/-! ## Remaining Expected Syntax: `elif`/`elif let`, `for (k, v)`, `.1`/`.2`, Compound Assigns, `any x:`, `field` `example`/`rejects`, `///` & `private` Parity -/

fn exprElifDemo(n: Nat) -> String:
  example z: exprElifDemo(0) == "zero"
  example s: exprElifDemo(5) == "small"
  example m: exprElifDemo(42) == "medium"
  example l: exprElifDemo(100) == "large"
  return if n == 0: "zero"
    elif n < 10: "small"
    elif n < 100: "medium"
    else: "large"

fn exprElifLetDemo(a: Nat?, b: Nat?, flag: Bool) -> Nat:
  example hitA: exprElifLetDemo(some(3), some(7), true) == 3
  example hitB: exprElifLetDemo(none, some(7), true) == 70
  example hitFlag: exprElifLetDemo(none, none, true) == 42
  example hitElse: exprElifLetDemo(none, none, false) == 0
  return if let some(x) = a: x
    elif let some(y) = b: y * 10
    elif flag: 42
    else: 0

fn stmtIfLetElifDemo(a: Nat?, b: Nat?, flag: Bool) -> Nat:
  example sA: stmtIfLetElifDemo(some(4), none, false) == 5
  example sB: stmtIfLetElifDemo(none, some(6), false) == 12
  example sF: stmtIfLetElifDemo(none, none, true) == 99
  example sE: stmtIfLetElifDemo(none, none, false) == 0
  if let some(x) = a:
    return x + 1
  elif let some(y) = b:
    return y * 2
  elif flag:
    return 99
  else:
    return 0

fn sumTuplePairs(pairs: (Nat, Nat)[]) -> Nat:
  ensures result >= pairs.size
  example twoPairs: sumTuplePairs([(1, 2), (3, 4)]) == 12
  let mut acc : Nat = 0
  for (a, b) in pairs:
    invariant acc >= seen.length
    acc += a + b + 1
  return acc

fn sumNestedTuples(xs: (Nat, (Nat, Nat))[]) -> Nat:
  example oneTriple: sumNestedTuples([(1, (2, 3)), (10, (20, 30))]) == 66
  let mut acc : Nat = 0
  for (a, (b, c)) in xs:
    acc += a + b + c
  return acc

fn tupleProjDemo(p: (Nat, (String, Nat))) -> Nat:
  ensures result == p.1 + p.2.2 + p.2.1.length
  example sampleProj: tupleProjDemo((5, ("abc", 7))) == 15
  return p.1 + p.2.2 + p.2.1.length

fn compoundAssignDemo(start: Nat) -> Nat:
  example runAll: compoundAssignDemo(3) == 16
  let mut x : Nat = start
  x *= 4
  x /= 2
  x %= 5
  x <<= 3
  x |= 5
  x &= 15
  x ^= 1
  x >>= 1
  x *= 2 + 1
  x -= 2
  return x

/-- Documented component exercising JSX `elif`/`elif let`, statement `if let`/`elif`, and compound assignments. -/
component ElifAndCompoundComp:
  state mode : Nat = 0
  state sel : String? = none
  state val : Nat = 2
  action step(optA: Nat?, optB: Nat?):
    if let some(a) = optA:
      val *= a
    elif let some(b) = optB:
      val |= b
    elif mode == 1:
      val <<= 1
    else:
      val ^= 3
  view:
    <div>
      {if mode == 0:
        <button onClick={val *= 2}>double</button>
      elif let some(label) = sel:
        <span>{label}</span>
      elif mode == 1:
        <p>one</p>
      else:
        <p>other</p>}
    </div>

/-- Documented private top-level invariant with unbounded `any` quantifier. -/
private invariant existsWitnessInv: any x: Nat: x == 42
  prove:
    exact ⟨42, rfl⟩

/-- Documented private field with inline `example` and `rejects`. -/
private field TagCode : String
  where s => s.length >= 2 and s.length <= 8
  example okTag: "abc"
  rejects tooShort: "x"
  rejects tooLong: "123456789"

/-- Documented private router. -/
private router PrivatePageRoute:
  home = "/"
  item(id: Nat) = "/items/:id"

/-- Documented private mapping. -/
private mapping PrivateShiftMap:
  from x : Nat where x <= 100
  to   y : Nat where y <= 101
  encode(x): return x + 1
  decode(y):
    if y == 0: fail("zero")
    return y - 1

/-- Documented private view invariant. -/
private invariant privateElifHasDiv: hasTag("div") holds_in ElifAndCompoundComp.view

check_decls [exprElifDemo_example_z, exprElifDemo_example_s, exprElifDemo_example_m, exprElifDemo_example_l,
  exprElifLetDemo_example_hitA, exprElifLetDemo_example_hitB, exprElifLetDemo_example_hitFlag, exprElifLetDemo_example_hitElse,
  stmtIfLetElifDemo_example_sA, stmtIfLetElifDemo_example_sB, stmtIfLetElifDemo_example_sF, stmtIfLetElifDemo_example_sE,
  sumTuplePairs_ensures, sumTuplePairs_example_twoPairs, sumNestedTuples_example_oneTriple,
  tupleProjDemo_ensures, tupleProjDemo_example_sampleProj, compoundAssignDemo_example_runAll,
  existsWitnessInv, TagCode.okTag, TagCode.satisfiable, TagCode.rejects_tooShort, TagCode.rejects_tooLong,
  PrivatePageRoute.round_trip, PrivateShiftMap.encode_ok, PrivateShiftMap.roundtrip, privateElifHasDiv]

expect_err "Field `BadExField` example `bad` failed `where` constraint" in
  field BadExField : Nat
    where n => n >= 10
    example bad: 5

expect_err "Field `BadRejField` `rejects bad` failed" in
  field BadRejField : Nat
    where n => n >= 10
    rejects bad: 20

expect_err "any x, x + 1 = 0" in
  invariant badAnyDiag: any x: Nat: x + 1 == 0

/-! ## Grammar Polish: Trailing Commas, Single-Line/Unit `fn`, Quantifier & Lambda Tuples, Record Compound Updates, Component `let ... else` -/

fn oneLineDouble(x: Nat,) -> Nat: return x * 2
fn implicitUnitNoop(_x: Nat): pass
fn implicitUnitEarly(flag: Bool):
  if flag: return
  pass

schema RecUpdBox:
  a : Nat
  b : Nat
  c : Nat

fn recordCompoundUpdate(box: RecUpdBox,) -> RecUpdBox:
  ensures result.a == box.a + 2 and result.b == box.b * 3
  example updOk:
    recordCompoundUpdate({ a = 4, b = 5, c = 2, },) == { a = 6, b = 15, c = 6, }
  return { box with a += 2, b *= 3, c |= 4, }

fn trailingAndTupleQuantDemo(pairs: (Nat, Nat,)[],) -> Nat[]:
  ensures all (k, v) in pairs: k + v >= k
  example mapFilterPairs:
    trailingAndTupleQuantDemo([(1, 2,), (5, 3,), (2, 10,),]) == [3, 12,]
  let ok = all (k, v) in pairs: k + v >= 0
  let hasBig = any (_, v) in pairs: v >= 10
  if not ok and not hasBig: return []
  return pairs.filter(((k, v)) => k < v).map(((k, v): (Nat, Nat)) => k + v)

component GuardLetElseComp:
  state selected : Nat? = none
  state total : Nat = 0
  action addSelected(bonus: Nat,):
    let some(v) = selected else: return
    total += v + bonus
  action clearIfEmpty():
    let some(_) = selected else return
    selected = none
  example guardMiss: .addSelected(5,) -> total == 0
  example guardHit from { selected = some(7,), total = 1, }: .addSelected(3,) -> total == 11
  view: <div><span>{total}</span></div>

check_decls [recordCompoundUpdate_ensures, recordCompoundUpdate_example_updOk,
  trailingAndTupleQuantDemo_ensures, trailingAndTupleQuantDemo_example_mapFilterPairs,
  GuardLetElseComp.guardMiss, GuardLetElseComp.guardHit]

example : oneLineDouble 21 = 42 ∧ implicitUnitNoop 1 = () ∧ implicitUnitEarly true = () := ⟨rfl, rfl, rfl⟩

expect_err "requires a base record" in
  fn badRecCompoundNoBase() -> RecUpdBox:
    return { a += 1, b = 2, c = 3 }

expect_err "guard `let ... = ... else` branch in component action must `return` on all paths" in
  component BadCompLetElse:
    state x : Nat? = none
    state y : Nat = 0
    action go():
      let some(v) = x else:
        y = 1
      y = v
    view: <span>{y}</span>
end SyntaxChecks
