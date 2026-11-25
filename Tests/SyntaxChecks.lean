import Qed
import Tests.CheckHelper
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
structure Row where
  id : Nat
  label : String
inductive ParentMsg | reported (id : Nat) (count : Int)
end LocalNested
def importedHelper (r : LocalNested.Row) : Html LocalNested.ParentMsg :=
  <LocalNested.Widget key={r.id} id={r.id} label={r.label} initial={{ note = r.label }} onReport={LocalNested.ParentMsg.reported(r.id)}/>
component HelperApp:
  state draft : String = ""
  action localEvent(m: LocalNested.ParentMsg): pass
  view: importedHelper({ id = 8, label = draft }).map(.localEvent)
expect_err "`label` is a read-only `prop` and cannot be assigned (`state` fields: `count`)" in
component ReadOnly:
  prop label : String
  state count : Nat = 0
  action change: label = "changed"
  view: <span>{label}</span>
expect_err "duplicate action name `save`" in
component DuplicateAction:
  state count : Nat = 0
  action save: count = 1
  action save: count = 2
  view: <span>{count}</span>
component Owned:
  prop caption : String
  state id : Nat
  state count : Nat
  key id
  action increment: count = count + 1
  view: <button title={caption} onClick={.increment}>{count}</button>
route_enum Section:
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
expect_err "Styling invariant `badVacuousRole` failed in `navView`:\n  • `roleHasOneOf(\"nonexistent\", [navOn, navOff])` does not hold in every state" in
invariant badVacuousRole : roleHasOneOf("nonexistent", [navOn, navOff]) holds_in navView
def bothStylesView (b : Bool) : Html Unit := <button role="btn" {navOn} {navOff if b else navOff}>{"x"}</button>
expect_err "Styling invariant `badDualStyle` failed in `bothStylesView`:\n  • `roleHasOneOf(\"btn\", [navOn, navOff])` does not hold in every state" in
invariant badDualStyle : roleHasOneOf("btn", [navOn, navOff]) holds_in bothStylesView
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
structure PlainNote where
  id : Nat
  text : String
deriving DecidableEq
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
    ModernCounter.init.quantity = 1 ∧ ModernCounter.init.draft = "" := ⟨rfl, rfl, rfl, rfl, rfl⟩
#guard
  let ids := HelperApp.app.locals.map (·.id)
  let ssr := Html.renderWith Counter.regs (<div><style>{".a > .b { content: \"</style>\"; }"}</style><br/>{defaults}</div> : Html Unit)
  let draft : Ticket.Draft := { title := "Fix parser", priority := "2" }
  let jx := Html.render (jsxErgonomicsView #[1, 2] (some "ok") true)
  let jxElseT := Html.render (jsxElseBranchesView (some "hi") true [<span>ex</span>])
  let jxElseF := Html.render (jsxElseBranchesView none false [<span>ex</span>])
  (Html.renderWith Counter.regs defaults).contains "8</button>" &&
  ids.length == 3 && ["SyntaxChecks.HelperApp", "SyntaxChecks.LocalNested.Widget", "SyntaxChecks.LocalNested.Tag"].all ids.contains &&
  (Html.render (<Owned state={{ id = 4, count = 2 }} caption="Live" onMsg={Prod.mk}/> : Html (String × Owned.Msg))).contains "Live" &&
  [".a > .b", "<\\/style>", "8</button>"].all (ssr.contains ·) && !ssr.contains "</br>" &&
  Router.toURL (DocRoute.sec .architecture 2) == "/docs/arch/2" &&
  [("/docs/bench/5", some (DocRoute.sec .benchmarks 5)), ("/docs/unknown/5", none), ("/docs/arch/2?tab=api#top", some (DocRoute.sec .architecture 2)), ("/?utm=1#hero", some DocRoute.home)].all (fun (u, w) => Router.fromURL u == w) &&
  (RoutedDehydrated.app.rehydrate (RoutedDehydrated.app.dehydrate { r := .sec .benchmarks 3 })).map (·.r) == some (.sec .benchmarks 3) &&
  (Html.render (TypedLink.view { target := .sec .architecture 2 } { cur := .home })).contains "href=\"/docs/arch/2\"" &&
  AutoStyled.app.styles.length == 2 && (AutoStyled.app.ssrStep "T" "/qed.js" "/" "").contains navOn.raw &&
  ResetTheme.style.raw.contains ":where(*, *::before) { margin: 0px; }" && typedBorderStyle.raw == "border: 1px solid var(--border-subtle); border-bottom: 2px dashed #333; border-top: none;" &&
  (Html.render (ParentPage.view { route := .sec .architecture 3 })).contains "/docs/arch/1" &&
  Router.toURL (RepoRoute.edit "acme" "qed") == "/orgs/acme/repos/qed/edit" &&
  [("/orgs/acme/repos/qed/edit", some (RepoRoute.edit "acme" "qed")), ("/orgs/acme/repos/qed", some (RepoRoute.blob "acme" "qed")), ("/orgs/acme/issues/3", some (RepoRoute.issues "acme" 3))].all (fun (u, w) => Router.fromURL u == w) &&
  ((Json.parse (Json.render (toJson draft))).bind fromJson).toOption == some draft &&
  ["<p>ok</p>", "<li>3</li><li>4</li>"].all (jx.contains ·) && !(Html.render (jsxErgonomicsView #[] none false)).contains "<em>" &&
  ["<span>yes</span>", "<p>hi</p>", "<span>ex</span><span>ex</span>"].all (jxElseT.contains ·) &&
  ["<span>no</span>", "<p>empty</p>", "<b>f1</b><b>f2</b>", "<i>m1</i><i>m2</i>"].all (jxElseF.contains ·) &&
  (RichAuto.app.rehydrate (RichAuto.app.dehydrate { tab := .tagged "lean", notes := #[{ id := 1, text := "hello" }], pick := some { id := 2, text := "pinned" }, cache := ({} : Cached String).put "k" (.ok "v") "k", child := { count := 42, saved := 0 } })).map
    (fun m => m.tab == .tagged "lean" && m.notes == #[{ id := 1, text := "hello" }] && m.pick == some { id := 2, text := "pinned" } && m.cache.lookup "k" == some "v" && m.child.count == 42) == some true &&
  ((PartialFn.app.rehydrate (PartialFn.app.dehydrate { count := 8, fn := (· * 2) })).map fun m => (m.count, m.fn 5)) == some (8, 15)

-- ── Compile-time rejection checks ──
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
bad_comp_view "Invalid HTML / XSS check failed for this view:\n  • `<div>` cannot be nested inside `<p>` or a heading (`<h1>`–`<h6>`)" BadOpaqueNesting u : Unit = () | <p>{sneakyBlock}</p>
bad_comp_view "Qed.lazy function must not capture state directly" BadLazyCapturesModel m : Nat = 1 | <div>{Qed.lazy((k: Nat) => <span>{k + m}</span>, m / 2)}</div>
expect_err "SSR hydration mismatch: `ephemeral` field affects the rendered view:\n  • view mismatch after rehydration:  \"hi\" = b" in
component BadEphemeralReadByView:
  state a : Nat = 1
  ephemeral b : String = "hi"
  view: <div>{a}{b}</div>

-- ── Sub-components, `Field`, `<Await>`, & fractional CSS checks ──
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
  invariant xPos: 0 <= x := by intro m msg h; cases msg <;> simp_all [update] <;> split <;> simp_all <;> omega
def lazyBadge {msg : Type} (k : Nat) : Html msg := <span>{k}</span>
component FineGrainedCheck:
  state count : Nat = 1
  state items : Nat[] = [1, 2]
  action bump: count += 1
  view: <div><span class="c">{count}</span>{<p>zero</p> if count == 0 else <p>nonzero</p>}{Qed.lazy(lazyBadge, count)}<ul>{for n in items: <li key={n}>{n}</li>}</ul></div>
#guard
  let gl := Html.render (GoodLazy.app.view { m := 7 })
  let cs := Html.render (<Card title="Docs" badge={<span class="badge">v2</span>}><p>First</p><ul><ListChip key="a" text="Alpha"/></ul></Card> : Html Unit)
  let s1 := CompositeDemo.update CompositeDemo.init (._sub_0 (._emit (.set_filter "lean4")))
  let s2 := CompositeDemo.update s1 (._sub_0 (._emit (.onPick "lean4")))
  let s3 := CompositeDemo.update s2 (._sub_1 .toggle)
  gl.contains "href=\"/docs/guide\"" && gl.contains "<span>3</span>" &&
  fracStyle.raw == "text-align: center; padding: 0.35rem 0 0.5rem; margin: 2rem auto; gap: 4px 8px; line-height: 1.5; font-weight: 600; opacity: 0.85; z-index: -1;" &&
  (match (Resource.ok (none : Option Nat)).someOr "missing" with | .failed "missing" => true | _ => false) &&
  (match (Resource.ok (some 42)).someOr "missing" with | .ok 42 => true | _ => false) &&
  (match (({} : Cached Nat).put "a" (.ok 1) "b").state with | .idle => true | _ => false) &&
  ((({} : Cached Nat).put "a" (.ok 1) "b").lookup "a" == some 1) && (match (({} : Cached Nat).put "a" (.ok 7) "a").state with | .ok 7 => true | _ => false) &&
  cs.contains "<h3>Docs</h3><span class=\"badge\">v2</span>" && cs.contains "<li class=\"chip\">Alpha</li>" && !cs.contains "data-qed-local" &&
  s1.query == "lean4" && s2.picked == "lean4" && !(Html.render (CompositeDemo.view CompositeDemo.init)).contains "class=\"panel\"" &&
  (Html.render (CompositeDemo.view s3)).contains "class=\"panel\"" &&
  (CompositeDemo.app.rehydrate (CompositeDemo.app.dehydrate { s3 with clicks := 5, scratch := 0 })).map (fun s => (s.query, s.clicks, s.scratch)) == some ("lean4", 5, 99) &&
  (Html.render (awaitSample .loading)).contains "<p>Wait</p>" && (Html.render (awaitSample (.failed "boom"))).contains "<p class=\"err\">boom</p>" &&
  (EarlyReturnCheck.update { x := 5 } (.step 0)).x == 5 && (EarlyReturnCheck.update { x := 5 } (.step 3)).x == 8 &&
  (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := 5 })).map (·.x) == some 5 && (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := -1 })).isNone &&
  (match FineGrainedCheck.app.template with | .element "div" _ [.element "span" _ [.dyn _], .ifElse _ _ _, .memo _, .keyedList "ul" _ _ _ _ _ _ (some _)] => true | _ => false)
expect_err "Invariant `BadUnguardedDecrease.inRange` failed in `BadUnguardedDecrease.update`:\n  • action `decrease` must satisfy:  1 <= quantity - 1 and quantity - 1 <= 10" in
component BadUnguardedDecrease:
  state quantity = 1
  action decrease: quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  view: <span>{quantity}</span>
bad_comp_act "`qunatity` is not a `state` field of this component (did you mean `quantity`?) (`state` fields: `quantity`)" BadStateFieldTypo quantity : Nat = 1 | inc : qunatity += 1
style safeBtnStyle:
  background-color: #111
style dangerBtnStyle:
  background-color: #999
component StyleLacksGood:
  state ok : Bool = true
  view: <div><button role="submit" {safeBtnStyle}>OK</button><span>safe</span></div>
  invariant noDanger: roleLacks("submit", dangerBtnStyle), tagLacks("span", dangerBtnStyle)
expect_err "Styling invariant `BadRoleLacks.noDanger` failed in `BadRoleLacks.view`:\n  • `roleLacks(\"submit\", dangerBtnStyle)` does not hold in every state" in
component BadRoleLacks:
  state ok : Bool = true
  view: <button role="submit" {dangerBtnStyle}>Bad</button>
  invariant noDanger: roleLacks("submit", dangerBtnStyle)
expect_err "Invariant `BadPropInit.nonNeg` failed on initial state `BadPropInit.init`:\n  • initial state must satisfy:  0 <= -1" in
component BadPropInit:
  prop offset : Int = 0
  state count : Int = -1
  action nop: pass
  invariant nonNeg: 0 <= count
  view: <span>{count}</span>
expect_err "SSR rehydration can violate the component's state invariant:\n  • after rehydration must satisfy:  5 <= shown + 0" in
component BadEphemeralInv:
  state shown : Int = 5
  ephemeral cache : Int = 0
  action shift: shown = 0; cache = 5
  invariant totalMin: 5 <= shown + cache
  view: <span>{shown}</span>

-- ── Self-hosted `<Schema.Form>` & unified syntax checks ──
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
example : MultiParamAndAutoDefaults.update MultiParamAndAutoDefaults.init (.pushBoth 4 "hi") = ({ xs := #[4], x := some 4 }, some (.emitted 4 "hi")) := rfl
bad_comp_view "use `Nat[]` instead of `Array Nat`" BadArrayType xs : Array Nat = [] | <span>{xs.size}</span>
expect_err "use `Nat?` instead of `Option Nat`" in
schema BadOptType:
  val : Option Nat
expect_err "use `jsonOnly(String)` with parentheses instead of `jsonOnly String`" in
schema BadJsonOnly:
  id : jsonOnly String

-- ── Python-esque ergonomics checks ──
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
#guard
  let vd : Ticket.Draft := { title := "Fix bug", priority := "3", kind := "bug" }
  let upd := PythonicShowcase.update PythonicShowcase.init
  SelfHostedFormKeep.init.picked.isNone && SelfHostedFormKeep.init._form_0 == Ticket.Draft.empty &&
  (Html.render (SelfHostedFormKeep.view SelfHostedFormKeep.init)).contains "disabled" &&
  !(Html.render (SelfHostedFormKeep.view { picked := none, _form_0 := vd })).contains "disabled" &&
  (match Ticket.parse vd with | some t => let sK := SelfHostedFormKeep.update { picked := none, _form_0 := vd } (.set_picked (some t)); let sR := SelfHostedFormReset.update { picked := none, _form_0 := vd } ._form_reset_0; sK.picked.map (·.title.val) == some t.title.val && sK._form_0 == vd && sR.picked.map (·.title.val) == some t.title.val && sR._form_0 == Ticket.Draft.empty | none => false) &&
  MultiParamAndAutoDefaults.init.xs == #[] && MultiParamAndAutoDefaults.init.x.isNone &&
  [(.classify 5, "low:5"), (.classify 25, "mid:25"), (.classify 80, "high:80"), (.addTag "qed", "tags:2"), (.usePick, "score=4"), (.describeTab (.tagged "ui"), "tag:ui"),
   (.exprBranches 3 (some 7), "pos:7"), (.exprBranches 0 none, "zero:none")].all (fun (m, want) => (upd m).label == want) &&
  (upd (.addTag "lean")).tags.size == 1 && (Html.render (PythonicShowcase.view PythonicShowcase.init)).contains "has-lean" &&
  Json.pathStr "{\"choices\":[{\"delta\":{\"content\":\"hi\"}}]}" "choices.0.delta.content" == "hi" && Json.pathStr "{\"choices\":[]}" "choices.0.delta.content" == ""
bad_srv1 "`if cond: ...` expression requires `else:` here" BadExprIfNoElse : rpc go() -> Nat: return if true: 1
bad_srv1 "`if let pat = expr: ...` expression requires `else:` here" BadExprIfLetNoElse : rpc go(opt: Nat?) -> Nat: return if let some(v) = opt: v
expect_err "invalid HTML5 nesting: <div> is not allowed inside <p>" in def badElseBranchNesting : Html Unit := <p>{if true: <span>ok</span> else: <div>bad</div>}</p>

-- ── Automated Quantified, Collection-Query, Nonlinear & Extended `for_each` Invariants ──
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

-- ── `enum`, `record`, `schema` Option/Bare-Type Lawfulness & Proto Mapping ──
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

record RoomSnapshotRec:
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

-- Backwards-compatible explicit deriving + custom Inhabited override
deriving instance Repr, DecidableEq for OptSchema
record CustomInhabRec:
  count : Nat
instance : Inhabited CustomInhabRec := ⟨{ count := 42 }⟩

-- Bare field types (no `Codec.Val` wrapper on unrefined schema/record fields)
example (s : OptSchema) : String := s.title
example (s : OptSchema) : Option String := s.note
example : (default : GamePhase) = .lobby := rfl
example : (default : RoomSnapshotRec).phase = .lobby ∧ (default : RoomSnapshotRec).spyCount.val = 1 := ⟨rfl, rfl⟩
example : (default : CustomInhabRec).count = 42 := rfl
example : LawfulJson GamePhase := inferInstance
example : LawfulProto GamePhase := inferInstance
example : LawfulJson (Option GamePhase) := inferInstance
example : LawfulJson RoleCard := inferInstance
example : LawfulProto RoleCard := inferInstance
example : LawfulJson (Option RoleCard) := inferInstance
example : LawfulJson TickEvent := inferInstance
example : LawfulProto TickEvent := inferInstance
example : LawfulJson RoomSnapshotRec := inferInstance
example : LawfulProto RoomSnapshotRec := inferInstance
example : LawfulJson (Option RoomSnapshotRec) := inferInstance
example : LawfulJson OptSchema := inferInstance
example : LawfulProto OptSchema := inferInstance
example : DecidableEq RoomSnapshotRec := inferInstance
example : Repr RoomSnapshotRec := inferInstance
example : DecidableEq RoleCard := inferInstance
example : Repr RoleCard := inferInstance

mapping RoomFrameMap:
  from RoomSnapshotRec
  to String
  encode(v):
    return Proto.encodeHex(Proto.encode(v))
  decode(frame):
    let bytes = Proto.decodeHex(frame)?
    return Proto.decode(bytes)?

#guard
  let r := RoomSnapshotRec.sample
  let tick := TickEvent.tick 7 "go"
  (GamePhase.ofString (toString GamePhase.playing)).toOption == some .playing &&
  (GamePhase.decode (GamePhase.encode .playing)).toOption == some .playing &&
  (GamePhase.decodeBytes (GamePhase.encodeBytes .playing)).toOption == some .playing &&
  (RoleCard.decode (RoleCard.encode (.agent "Pilot" (some "ok")))).toOption == some (.agent "Pilot" (some "ok")) &&
  (RoleCard.decodeBytes (RoleCard.encodeBytes (.agent "Pilot" none))).toOption == some (.agent "Pilot" none) &&
  (TickEvent.decode (TickEvent.encode tick)).toOption == some tick &&
  (TickEvent.decodeBytes (TickEvent.encodeBytes tick)).toOption == some tick &&
  (RoomSnapshotRec.decode (RoomSnapshotRec.encode r)).toOption == some r &&
  (RoomSnapshotRec.decodeBytes (RoomSnapshotRec.encodeBytes r)).toOption == some r &&
  (OptSchema.decode (OptSchema.encode { title := "x", note := some "n", phase := some .playing })).toOption == some { title := "x", note := some "n", phase := some .playing } &&
  (OptSchema.decode (OptSchema.encode { title := "x", note := none, phase := none })).toOption == some { title := "x", note := none, phase := none } &&
  (RoomFrameMap.decode (RoomFrameMap.encode r).val).toOption == some r

expect_err "duplicate variant `a` in `enum DupEnum`" in
enum DupEnum:
  a
  a
expect_err "duplicate field `x` in variant `pair` of `enum DupEnumField`" in
enum DupEnumField:
  pair(x: Nat, x: String)
expect_err "Record `BadRecDefault` default for field `qty` failed `where` constraint" in
record BadRecDefault:
  qty : Nat = 99 where 1 <= qty <= 4
expect_err "Record `UnsatRec` is unsatisfiable: field `qty` has contradictory `where` constraints" in
record UnsatRec:
  qty : Nat where 10 <= qty, qty <= 2

-- Pure `fn` contracts (`requires`, `ensures`, `if`, `blindTo`)
record SecretRoom:
  code           : String
  secretLocation : String
  secretPack     : String
  spyIds         : String[]

record RedactedView:
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
  return {
    code = room.code,
    secretLocation = none if isSpy else some(room.secretLocation),
    secretPack = none if isSpy else some(room.secretPack),
    isSpy = isSpy
  }

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
  if viewerId in room.spyIds:
    blindTo room.secretLocation
  if viewerId in room.spyIds: return none
  return some(room.secretLocation)

example := @projectSecretRoom_ensures_1
example := @projectSecretRoom_ensures_2
example := @projectSecretRoom_blindTo
example := @clampRoundMins_ensures
example := @hideWholeParam_ensures
example := @hideWholeParam_blindTo
example := @redactSingleField_blindTo

expect_err "`blindTo room.secretLocation` failed in `leakyProjection`" in
fn leakyProjection(room: SecretRoom, viewerId: String) -> RedactedView:
  if viewerId in room.spyIds:
    ensures result.secretLocation == none
    blindTo room.secretLocation
  let isSpy = viewerId in room.spyIds
  return {
    code = f"{room.code}:{room.secretLocation}",
    secretLocation = none if isSpy else some(room.secretLocation),
    secretPack = none,
    isSpy = isSpy
  }

expect_err "`ensures` contract failed for `badClamp`" in
fn badClamp(n: Nat) -> Nat:
  ensures result <= 10
  return n

-- Component `fn` (pure + state-mutating), implication invariants, per-action `prove:`, and keyed hoisted sub-components
enum ViewTab:
  home
  room(code: String)

component PureFnBadge:
  prop name : String
  fn label(prefixStr: String) -> String:
    return f"{prefixStr}: {name}"
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

  fn heading(pfx: String) -> String:
    return f"{pfx} {title} ({counter})"

  fn applyRoom(t: String, clearBusy: Bool):
    title = t
    if clearBusy: busy = false

  action openRoom(c: String, t: String):
    tab = .room(c)
    applyRoom(t, true)

  action goHome:
    tab = .home
    title = ""
    busy = false

  action rename(t: String):
    match tab:
      case .home: pass
      case .room(_): applyRoom(t, false)

  action inc:
    counter += 1

  invariant homeClean: isHome() -> title == ""
  invariant nonNeg: counter >= 0
    prove:
      case inc:
        omega

  view: <div><span>{heading("Room")}</span><PureFnBadge name={title}/></div>

example := @CompFnAndProve.homeClean
example := @CompFnAndProve.nonNeg
example := @CompFnAndProve.app_view_eq

expect_err "unknown action/message `noSuchAction` in `prove:` on invariant `BadProveCase.ok`" in
component BadProveCase:
  state n : Nat = 0
  action inc: n += 1
  invariant ok: n >= 0
    prove:
      case noSuchAction:
        omega
  view: <span>{n}</span>

expect_err "`fn reset` has no `-> ReturnType` and mutates component state" in
component BadMutFnInPure:
  prop x : Nat = 0
  fn reset(): pass
  view: <span>{x}</span>

-- Keyed / conditional hoisted sub-components with lifecycle reset, `start`, and lifted `subscribe`
server SubHostSrv:
  channel feed(code: String) -> String:
    on_join -> String:
      return code

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
  let s0 := SubHostShell.init
  let (s1, _) := SubHostShell.update s0 (.openRoom "AAA")
  let (s2, _) := SubHostShell.update s1 (._sub_0 .tick)
  let (s3, _) := SubHostShell.update s2 (.openRoom "BBB")
  let (s4, _) := SubHostShell.update s3 (._sub_0 .tick)
  let (s5, _) := SubHostShell.update s4 .leaveRoom
  s2._sub_0.ticks = 1 ∧ s3._sub_0.ticks = 0 ∧ s4._sub_0.ticks = 1 ∧ s5._sub_0.ticks = 0 ∧
  SubHostShell.subscriptions.length = 1 := by
  decide

-- Pure component forwarding events to pure children, keyed local children, and `bind:` children
component PureLangSelect:
  prop lang : String
  event onSelect(code : String)
  event onReset
  view:
    <div class="lang-select">
      <button class="fr" onClick={onSelect("fr")}>{lang}</button>
      <button class="rst" onClick={onReset}>Reset</button>
    </div>

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

example := @PureForwardHost.app_view_eq
example : Type → Type := PureContentPage.Props
#guard
  let rendered := Html.render (PureForwardHost.view PureForwardHost.init)
  let (_, hs) := renderNode #[] (PureForwardHost.view PureForwardHost.init)
  let s1 := PureForwardHost.update PureForwardHost.init (hs[0]?.getD (.setLang ""))
  let s2 := PureForwardHost.update s1 (hs[1]?.getD (.setLang ""))
  rendered.contains "class=\"lang-select\"" && rendered.contains "data-qed-local=\"SyntaxChecks.KeyedTagPicker@tp\"" &&
  PureForwardHost.app.locals.any (·.id == "SyntaxChecks.KeyedTagPicker") &&
  s1.lang == "fr" && s2.lang == "en"

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

structure NestedFilter where
  page   : Nat := 0
  search : String := ""
  tags   : Array String := #[]
deriving Inhabited, DecidableEq, Repr

instance : ToJson NestedFilter where
  toJson f := .obj [("page", toJson f.page), ("search", toJson f.search), ("tags", toJson f.tags)]
instance : FromJson NestedFilter where
  fromJson j := do
    return { page := ← FromJsonField.fromField j "page", search := ← FromJsonField.fromField j "search", tags := ← FromJsonField.fromField j "tags" }

server PolishRpcSrv:
  rpc listItems(q: String) -> String[]!:
    return [q, "item-a"]
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
    case .account | .tokens:
      visits += 1
    case _:
      pass
  state visits : Nat = 0
  state flt : NestedFilter = { page = 0, search = "", tags = ["a"] }
  state lastSaved : String = ""
  query items = PolishRpcSrv.listItems(flt.search)
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
      case .badInput(e) | .failed(e):
        lastSaved = f"err:{e}"
    lastSaved = f"{label}->{res}"
    items.refetch()
  action saveCurrent:
    doSave(flt.search)
  action bumpNested:
    flt.page += 1
    flt.tags.push("b")
    flt.tags[0] = "z"
  action refreshItems:
    items.invalidate()
  action optimisticAdd(x: String):
    items.update(xs => xs.push(x))
  action replaceItems(xs: String[]):
    items.set(xs)
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

expect_err "duplicate CSS property `padding` in the same style block" in
style BadDupCssProp:
  padding: 4px
  padding: 8px

expect_err "recursive `await` call cycle in component `fn ping`" in
component BadAsyncCycleComp:
  state x : String = ""
  fn ping():
    let _r = await PolishRpcSrv.saveItem("a") catch:
      case _: pass
    pong()
  fn pong():
    ping()
  action go: ping()
  view: <span>{x}</span>

expect_err "cannot use `await` inside pure component `fn pureBad`; remove `-> ReturnType` for an async mutating helper, or perform `await` in the calling `action`" in
component BadPureAwaitComp:
  state x : String = ""
  fn pureBad() -> String:
    let r = await PolishRpcSrv.saveItem("a")
    return r
  view: <span>{x}</span>

expect_err "duplicate wire name `dup` in `enum BadDupWireEnum`" in
enum BadDupWireEnum:
  a = "dup"
  b = "dup"

expect_err "Field `BadImpossibleField` is unsatisfiable" in
field BadImpossibleField : Nat where n => n > 10, n < 5

example := @ShortSlug.satisfiable
example := @ServicePort.satisfiable
example := @SessionParentShell.app_view_eq
example := @MultiStyleSpliceDemo.app_view_eq

#guard
  let s0 := SessionParentShell.init
  let (s1, _) := SessionParentShell.update s0 (._onSession (some "alice"))
  let (s2, _) := SessionParentShell.update s1 (._onRoute .account)
  let (s3, _) := SessionParentShell.update s2 (._onRoute .tokens)
  let (s4, _) := SessionParentShell.update s3 (._onRoute .home)
  let (s5, _) := SessionParentShell.update s4 .bumpNested
  let (s6, _) := SessionParentShell.update s5 (.replaceItems #["one"])
  let (s7, _) := SessionParentShell.update s6 (.optimisticAdd "two")
  let (_, cRef) := SessionParentShell.update s7 .refreshItems
  let rOff := Html.render (MultiStyleSpliceDemo.view MultiStyleSpliceDemo.init)
  let rOn  := Html.render (MultiStyleSpliceDemo.view { active := true })
  let c0 : Cached Nat := ({} : Cached Nat).setKey "k" 10
  let c1 := c0.updateCurrent "k" (· + 5)
  let c2 := c1.map (· * 2)
  let c3 := c2.invalidateKey "k"
  s1._sub_0.user == some "alice" &&
  s2.visits == 1 && s2._sub_0.user == some "alice" &&
  s3.visits == 2 && s3._sub_0.user == some "alice" &&
  s4._sub_0.user == some "alice" &&
  s5.flt.page == 1 && s5.flt.tags == #["z", "b"] &&
  s6.items.getD #[] == #["one"] && s6.items.isOk &&
  s7.items.getD #[] == #["one", "two"] &&
  (match cRef with | .none => false | _ => true) &&
  (SessionParentShell.headInfo s2).1.title == some "Settings" &&
  (SessionParentShell.headInfo s2).1.canonical == some "https://qed.cloud/account" &&
  (SessionParentShell.headInfo s2).1.redirect == some "/" &&
  (SessionParentShell.headInfo s2).2 == 301 &&
  (SessionParentShell.headInfo s4).1.title == some "Home" &&
  (SessionParentShell.headInfo s4).1.canonical == some "/" &&
  (PolishRoute.item "42").toPath == "/items/42" &&
  PolishRoute.fromPath "/items/42" == some (.item "42") &&
  toString (PolishRoute.item "42") == "/items/42" &&
  (PolishRoute.appTab (ShortSlug.make "my-app") .deployLogs).toPath == "/apps/my-app/deploy-logs" &&
  PolishRoute.fromPath "/apps/my-app/database" == some (.appTab (ShortSlug.make "my-app") .db) &&
  ShortSlug.parse? "" == none &&
  ShortSlug.parse? "ok" == some (ShortSlug.make "ok") &&
  (match ShortSlug.parse "" with | .error _ => true | .ok _ => false) &&
  (ServicePort.make 8080).val == 8080 &&
  ServicePort.parse? 0 == none &&
  (BoundedStr.make 16 "hello").val == "hello" &&
  BoundedStr.parse? 4 "too-long" == none &&
  (ServiceFieldForm.parse { slug := "api", port := "8080", tag := "v1" }).isSome &&
  (ServiceFieldForm.parse { slug := "", port := "8080", tag := "v1" }).isNone &&
  (ServiceFieldForm.parse { slug := "api", port := "70000", tag := "v1" }).isNone &&
  (Html.render (ServiceFieldForm.formView { slug := "api", port := "8080", tag := "v1" } id (fun _ => ServiceFieldForm.Draft.empty))).contains "type=\"number\"" &&
  (match Date.mk? 2026 11 25 with
   | some d => (PolishRoute.report d).toPath == "/reports/2026-11-25" && PolishRoute.fromPath "/reports/2026-11-25" == some (.report d)
   | none => false) &&
  (match Date.mk? (-44) 3 15 with
   | some d => d.toString == "-0044-03-15" && Date.parse? d.toString == some d
   | none => false) &&
  LawfulKey.toKey PolishTab.deployLogs == "deploy-logs" &&
  LawfulKey.toKey (ShortSlug.make "my-app") == "my-app" &&
  (PolishEvent.encode (.deployStarted "r1")).contains "\"deploy-started\"" &&
  (match PolishEvent.decode (PolishEvent.encode (.deployFailed "oom")) with | .ok (.deployFailed "oom") => true | _ => false) &&
  rOff.contains spliceBaseBtn.className && !rOff.contains spliceActiveBtn.className &&
  rOn.contains spliceBaseBtn.className && rOn.contains spliceActiveBtn.className &&
  c0.getD 0 == 10 && c1.getD 0 == 15 && c2.getD 0 == 30 && !c3.isOk &&
  Qed.Str.trim "  hi\t\n " == "hi" &&
  Qed.Str.containsCI "Hello Qed" "qed" &&
  Qed.Str.startsWith "foobar" "foo" && Qed.Str.endsWith "foobar" "bar" &&
  Qed.Str.split "a::b::c" "::" == ["a", "b", "c"] &&
  Qed.Str.replace "a-b-c" "-" "_" == "a_b_c" &&
  Qed.Str.truncate "abcdef" 5 == "ab..." &&
  Qed.Str.parseNat? "42" == some 42 && Qed.Str.parseInt? "-7" == some (-7) &&
  Qed.Time.formatIsoUtc 0 == "1970-01-01T00:00:00Z" &&
  Qed.Time.formatDateUtc (11016 * 86400) == "2000-02-29" &&
  Qed.Time.formatUtc 1700000000 == "2023-11-14 22:13 UTC" &&
  Qed.Time.formatDuration 125 == "2m 5s" &&
  Qed.Time.formatRelative 1000 700 == "5m ago"

end SyntaxChecks
