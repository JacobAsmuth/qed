import Qed
open Qed

namespace SyntaxChecks

component Counter:
  prop step : Nat = 1
  state count : Nat = 0
  state saved : Nat = 0
  event emitted(n: Nat)
  action advance(times: Nat):
    if times > 0:
      count = count + step * times
      saved = count
      emitted.emit(count)
  view: <button onClick={.advance(2)}>{count}</button>

example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 2) =
    ({ count := 10, saved := 10 }, some (.emitted 10)) := rfl
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 0) =
    ({ count := 4, saved := 0 }, none) := rfl

def defaults : Html Unit := <Counter initial={{ count = 8 }}/>
#guard (Html.renderWith Counter.regs defaults).contains "8</button>"

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
  view:
    <div>
      <span>{note}</span>
      <Tag key={f"t{id}"} label={label} onToggle={pinned = _}/>
    </div>

structure Row where
  id    : Nat
  label : String

inductive ParentMsg
  | reported (id : Nat) (count : Int)

end LocalNested

def importedHelper (r : LocalNested.Row) : Html LocalNested.ParentMsg :=
  <LocalNested.Widget key={r.id} id={r.id} label={r.label}
    initial={{ note = r.label }} onReport={LocalNested.ParentMsg.reported(r.id)}/>

component HelperApp:
  state draft : String = ""
  action localEvent(m: LocalNested.ParentMsg): pass
  view: importedHelper({ id = 8, label = draft }).map(.localEvent)

#guard (HelperApp.app.locals.map (·.id)).contains "SyntaxChecks.HelperApp"
#guard (HelperApp.app.locals.map (·.id)).contains "SyntaxChecks.LocalNested.Widget"
#guard (HelperApp.app.locals.map (·.id)).contains "SyntaxChecks.LocalNested.Tag"
#guard HelperApp.app.locals.length == 3

/-- error: `label` is a read-only `prop` and cannot be assigned (`state` fields: `count`) -/
#guard_msgs in
component ReadOnly:
  prop label : String
  state count : Nat = 0
  action change: label = "changed"
  view: <span>{label}</span>

/-- error: duplicate action name `save` -/
#guard_msgs in
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

def ownedView : Html (String × Owned.Msg) :=
  <Owned state={{ id = 4, count = 2 }} caption="Live" onMsg={Prod.mk}/>
#guard (Html.render ownedView).contains "Live"
example : (Owned.update { caption := "Live" } { id := 4, count := 2 } .increment).count = 3 := rfl

def ssrEdgeCases : Html Unit :=
  <div>
    <style>{".a > .b { content: \"</style>\"; }"}</style>
    <br/>
    {defaults}
  </div>
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains ".a > .b"
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains "<\\/style>"
#guard !(Html.renderWith Counter.regs ssrEdgeCases).contains "</br>"
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains "8</button>"

route_enum Section:
  overview
  architecture = "arch"
  benchmarks   = "bench"

router DocRoute:
  home = ""
  sec(s: Section, page: Nat) = "docs"

#guard Router.toURL (DocRoute.sec .architecture 2) == "/docs/arch/2"
#guard Router.fromURL "/docs/bench/5" == some (DocRoute.sec .benchmarks 5)
#guard (Router.fromURL "/docs/unknown/5" : Option DocRoute) == none

style navOn:
  font-weight: 700
style navOff:
  font-weight: 400
def navView (s : Section) : Html Unit :=
  <nav>
    <a role="nav-overview" {navOn if s == .overview else navOff}>{"Overview"}</a>
    <a role="nav-arch"     {navOn if s == .architecture else navOff}>{"Arch"}</a>
    <a role="nav-bench"    {navOn if s == .benchmarks else navOff}>{"Bench"}</a>
  </nav>

invariant navExclusive :
  exactlyOneOf(["nav-overview", "nav-arch", "nav-bench"], navOn, navOff) holds_in navView

component RoutedDehydrated:
  route r : DocRoute = .home
  view: <div>{Router.toURL(r)}</div>

#guard (RoutedDehydrated.app.rehydrate (RoutedDehydrated.app.dehydrate { r := .sec .benchmarks 3 })).map (·.r)
  == some (.sec .benchmarks 3)

/-- error: Styling invariant `badVacuousRole` failed in `navView`:
  • `roleHasOneOf("nonexistent", [navOn, navOff])` does not hold in every state

Hint: Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `navView`. -/
#guard_msgs in
invariant badVacuousRole : roleHasOneOf("nonexistent", [navOn, navOff]) holds_in navView

def bothStylesView (b : Bool) : Html Unit :=
  <button role="btn" {navOn} {navOff if b else navOff}>{"x"}</button>

/-- error: Styling invariant `badDualStyle` failed in `bothStylesView`:
  • `roleHasOneOf("btn", [navOn, navOff])` does not hold in every state

Hint: Check that the matching `role`/tag is rendered and receives exactly one allowed style in every branch of `bothStylesView`. -/
#guard_msgs in
invariant badDualStyle : roleHasOneOf("btn", [navOn, navOff]) holds_in bothStylesView

structure AppModel where route : DocRoute deriving DecidableEq
def activeSection : DocRoute → Section | .home => .overview | .sec s _ => s
def compositeNav (m : AppModel) : Html Unit := <div>{navView(activeSection(m.route))}</div>

invariant compositeNavExclusive :
  exactlyOneOf(["nav-overview", "nav-arch", "nav-bench"], navOn, navOff) holds_in compositeNav

def validCountView (n : Nat) : Html Unit :=
  <span role="pos" {navOn if n > 0 else navOff}>{toString(n)}</span>

invariant posStyledFromInv :
  roleHas("pos", navOn) holds_in validCountView assuming (n => n > 0)

component RowItem:
  state id    : Nat = 0
  state count : Nat = 0
  key id
  action inc: count = count + 1
  invariant rowSafeFromInit: 0 <= count
  view: <span>{count}</span>

#guard Router.fromURL "/docs/arch/2?tab=api#top" == some (DocRoute.sec .architecture 2)
#guard Router.fromURL "/?utm=1#hero" == some DocRoute.home

component TypedLink:
  prop target : DocRoute
  state cur : DocRoute = .home
  view: <a href={target} class={"active" if cur == target else ""}>{"Go"}</a>
#guard (Html.render (TypedLink.view { target := .sec .architecture 2 } { cur := .home })).contains "href=\"/docs/arch/2\""

component AutoStyled:
  state route : DocRoute = .home
  action noop: pass
  view: compositeNav({ route = route }).map(_ => .noop)
#guard AutoStyled.app.styles.length == 2
#guard (AutoStyled.app.ssrStep "T" "/qed.js" "/" "").contains navOn.raw

theme ResetTheme:
  color borderSubtle = #ccc
  reset *, *::before:
    margin: 0px

#guard ResetTheme.style.raw.contains ":where(*, *::before) { margin: 0px; }"

style typedBorderStyle:
  border: 1px solid ResetTheme.borderSubtle
  border-bottom: 2px dashed #333
  border-top: none
#guard typedBorderStyle.raw ==
  "border: 1px solid var(--border-subtle); border-bottom: 2px dashed #333; border-top: none;"

component SubBanner:
  prop sec : Section
  view: <header><a href={DocRoute.sec(sec, 1)}>{Router.toURL(DocRoute.sec(sec, 1))}</a></header>

component ParentPage:
  state route : DocRoute = .home
  invariant parentPageHasHeader: hasTag("header")
  view: <div><SubBanner sec={activeSection(route)}/></div>
#guard (Html.render (ParentPage.view { route := .sec .architecture 3 })).contains "/docs/arch/1"

style chipStyle:
  padding-inline: 6px
  margin-top: 2px

component ModernCounter:
  state quantity = 1
  state draft    = ""
  state active   = true
  action increase:
    if quantity < 10:
      let step = 1
      quantity += step
  action decrease:
    if 1 < quantity: quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  invariant qtyStyled: roleHasOneOf("qty", [chipStyle])
  view:
    <div>
      <button onClick={.decrease}>−</button>
      <span role="qty" {chipStyle}>{quantity}</span>
      <button onClick={.increase}>+</button>
      <button onClick={quantity = 5; draft = "five"}>Five</button>
      <input bind={draft}/>
      <input type="checkbox" bind={active}/>
    </div>

example : ModernCounter.init.quantity = 1 ∧ ModernCounter.init.draft = "" := ⟨rfl, rfl⟩

router RepoRoute:
  index = "/"
  blob  = "/orgs/:org/repos/:repo"
  edit  = "/orgs/:org/repos/:repo/edit"
  issues(page: Nat) = "/orgs/:org/issues/:page"

#guard Router.toURL (RepoRoute.edit "acme" "qed") == "/orgs/acme/repos/qed/edit"
#guard Router.fromURL "/orgs/acme/repos/qed/edit" == some (RepoRoute.edit "acme" "qed")
#guard Router.fromURL "/orgs/acme/repos/qed" == some (RepoRoute.blob "acme" "qed")
#guard Router.fromURL "/orgs/acme/issues/3" == some (RepoRoute.issues "acme" 3)

schema Ticket:
  id       : jsonOnly(String)
  title    : String where title.length >= 3
  priority : Nat    where 1 <= priority <= 5
  urgent   : Bool
  kind     : select([("bug", "Bug"), ("feat", "Feature")])

def draftRoundTrip : Ticket.Draft := { title := "Fix parser", priority := "2" }
#guard ((Json.parse (Json.render (toJson draftRoundTrip))).bind fromJson).toOption == some draftRoundTrip

def jsxErgonomicsView (items : Array Nat) (note? : Option String) (highlight : Bool) : Html Unit :=
  <div {chipStyle if highlight} data-tag={"hi" if highlight}>
    <>
      <span>Header</span>
      {<em>!</em> if highlight}
      {if let some(note) = note?: <p>{note}</p>}
    </>
    <ul>
      <li key="head">Top</li>
      {for n in items: <li key={n}>{n}</li>}
      {for n in ([3, 4] : List Nat): <li key={f"l{n}"}>{n}</li>}
    </ul>
  </div>

#guard (Html.render (jsxErgonomicsView #[1, 2] (some "ok") true)).contains "<p>ok</p>"
#guard (Html.render (jsxErgonomicsView #[1, 2] (some "ok") true)).contains "<li>3</li><li>4</li>"
#guard !(Html.render (jsxErgonomicsView #[] none false)).contains "<em>"

inductive FilterTab | all | tagged (tag : String) deriving DecidableEq
structure PlainNote where
  id   : Nat
  text : String
deriving DecidableEq

component RichAuto:
  state tab   : FilterTab = .all
  state notes : PlainNote[]
  state pick  : PlainNote?
  state cache : Cached String = {}
  state child : Counter.State = { count = 0, saved = 0 }
  view: <div>{notes.size}{child.count}</div>

#guard (RichAuto.app.rehydrate (RichAuto.app.dehydrate
  { tab := .tagged "lean", notes := #[{ id := 1, text := "hello" }], pick := some { id := 2, text := "pinned" },
    cache := ({} : Cached String).put "k" (.ok "v") "k", child := { count := 42, saved := 0 } })).map
  (fun m => m.tab == .tagged "lean" && m.notes == #[{ id := 1, text := "hello" }] &&
            m.pick == some { id := 2, text := "pinned" } && m.cache.lookup "k" == some "v" && m.child.count == 42) == some true

component PartialFn:
  state count : Nat = 1
  state fn    : Nat -> Nat = (x => x + 10)
  action bump(d: Nat): count = count + d
  view: <div>{count}</div>
#guard ((PartialFn.app.rehydrate (PartialFn.app.dehydrate { count := 8, fn := (· * 2) })).map fun m => (m.count, m.fn 5)) == some (8, 15)

-- ── Compile-time rejection checks (#guard_msgs) ─────────────────────────

/-- error: URL attribute `href` cannot take raw string literal `"/raw"` (raw strings are disallowed to prevent XSS and broken links).
Pass a typed `Router` route or a compile-time checked literal: `href={url("/raw")}`. -/
#guard_msgs in
def badRawHref : Html Unit := <a href="/raw">bad</a>

/-- error: unsafe URL literal `javascript:alert(1)`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badJsUrl : Url := url("javascript:alert(1)")

/-- error: unsafe URL literal `data:text/html,<script>alert(1)</script>`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badDataUrl : Url := url("data:text/html,<script>alert(1)</script>")

/-- error: unsafe URL literal `//evil.example/x`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badProtocolRelativeUrl : Url := url("//evil.example/x")

/-- error: <script> is forbidden in Qed views (untrusted script/plugin execution sink) -/
#guard_msgs in
def badScriptTag : Html Unit := <script>{"alert(1)"}</script>

/-- error: inline event attribute `onclick` is forbidden; use Qed's typed event handlers (`onClick`, `onInput`, `on "click" …`, …) -/
#guard_msgs in
def badInlineHandler : Html Unit := <div onclick="alert(1)"/>

/-- error: `srcdoc` is forbidden in Qed views (iframe raw-HTML execution sink) -/
#guard_msgs in
def badSrcdoc : Html Unit := <iframe srcdoc="<script>alert(1)</script>"/>

/-- error: invalid HTML5 nesting: <div> is not allowed inside <p> (browsers rewrite this tree during HTML parsing, causing hydration mismatch) -/
#guard_msgs in
def badNestedParagraph : Html Unit := <p><div>bad</div></p>

/-- error: invalid HTML5 nesting: <button> is not allowed inside <button> (browsers rewrite this tree during HTML parsing, causing hydration mismatch) -/
#guard_msgs in
def badNestedInteractive : Html Unit := <button><button>bad</button></button>

/-- error: invalid HTML5 nesting: <span> is not allowed inside <ul> (browsers rewrite this tree during HTML parsing, causing hydration mismatch) -/
#guard_msgs in
def badListChild : Html Unit := <ul><span>bad</span></ul>

def goodSafeUrl : Url := url("/docs/guide")
component GoodLazy:
  state m : Nat = 7
  view: <div><a href={goodSafeUrl}>Docs</a><a href={url("/about")}>About</a>{Qed.lazy((k: Nat) => <span>{k}</span>, m / 2)}</div>
#guard (Html.render (GoodLazy.app.view { m := 7 })).contains "href=\"/docs/guide\""
#guard (Html.render (GoodLazy.app.view { m := 7 })).contains "<span>3</span>"

def sneakyBlock {msg : Type} : Html msg := <div>bad</div>

/-- error: could not synthesize default value for parameter 'hvalid' using tactics
---
error: Invalid HTML / XSS check failed for this view:
  • `<div>` cannot be nested inside `<p>` or a heading (`<h1>`–`<h6>`)
---
error: could not synthesize default value for parameter 'valid_view' using tactics
---
error: Invalid HTML / XSS check failed for this view:
  • `<div>` cannot be nested inside `<p>` or a heading (`<h1>`–`<h6>`) -/
#guard_msgs in
component BadOpaqueNesting:
  state u : Unit = ()
  view: <p>{sneakyBlock}</p>

/-- error: Qed.lazy function must not capture state directly; pass all state dependencies through the `[LawfulKey]` argument so memoization stays sound -/
#guard_msgs in
component BadLazyCapturesModel:
  state m : Nat = 1
  view: <div>{Qed.lazy((k: Nat) => <span>{k + m}</span>, m / 2)}</div>

/-- error: could not synthesize default value for parameter 'hview' using tactics
---
error: SSR hydration mismatch: `ephemeral` field affects the rendered view:
  • view mismatch after rehydration:  "hi" = b

Hint: Do not mark fields read by `view:` as `ephemeral` (rehydration resets them to their initial value). -/
#guard_msgs in
component BadEphemeralReadByView:
  state a : Nat = 1
  ephemeral b : String = "hi"
  view: <div>{a}{b}</div>

-- ── Sub-components, unified `app`, `Field`, `<Await>`, & fractional CSS checks ──

style fracStyle:
  text-align: center
  padding: 0.35rem 0 0.5rem
  margin: 2rem auto
  gap: 4px 8px
  line-height: 1.5
  font-weight: 600
  opacity: 0.85
  z-index: -1

#guard fracStyle.raw ==
  "text-align: center; padding: 0.35rem 0 0.5rem; margin: 2rem auto; gap: 4px 8px; line-height: 1.5; font-weight: 600; opacity: 0.85; z-index: -1;"

#guard (match (Resource.ok (none : Option Nat)).someOr "missing" with | .failed "missing" => true | _ => false)
#guard (match (Resource.ok (some 42)).someOr "missing" with | .ok 42 => true | _ => false)

component Card:
  prop title : String
  prop badge : Html
  view:
    <div class="card">
      <header><h3>{title}</h3>{badge}</header>
      <div class="card-body">{children}</div>
    </div>

component SearchBar:
  bind query : String = ""
  event onClear
  event onSubmitQuery(q: String)
  view:
    <div class="search-bar">
      <input bind={query}/>
      <button class="clear" onClick={onClear}>Clear</button>
      <button class="go" onClick={onSubmitQuery(query)}>Go</button>
    </div>

component ListChip:
  prop text : String
  view: <li class="chip">{text}</li>

def cardSample : Html Unit :=
  <Card title="Docs" badge={<span class="badge">v2</span>}>
    <p>First</p>
    <ul><ListChip key="a" text="Alpha"/></ul>
  </Card>

#guard (Html.render cardSample).contains "<h3>Docs</h3><span class=\"badge\">v2</span>"
#guard (Html.render cardSample).contains "<li class=\"chip\">Alpha</li>"
#guard !(Html.render cardSample).contains "data-qed-local"

/-- error: invalid HTML5 nesting: <Card> (root <div>) is not allowed inside <p> (browsers rewrite this tree during HTML parsing, causing hydration mismatch) -/
#guard_msgs in
def badCardInParagraph : Html Unit := <p><Card title="Nope"><span>x</span></Card></p>

/-- error: invalid HTML5 nesting: <ListChip> (root <li>) is not allowed inside <div> (browsers rewrite this tree during HTML parsing, causing hydration mismatch) -/
#guard_msgs in
def badChipInDiv : Html Unit := <div><ListChip text="Orphan"/></div>

-- Stateful sub-component with implicit `{children}`, `Html` prop, `bind:`, and `event` hoisted into a parent `app`
component Accordion:
  prop heading : String
  prop extra   : Html
  state openPanel = false
  action toggle: openPanel = not openPanel
  view:
    <section class="accordion">
      <header>
        <button class="toggle" onClick={.toggle}>{heading}</button>
        {extra}
      </header>
      {<div class="panel">{children}</div> if openPanel}
    </section>

component PickerBox:
  bind filter : String = ""
  state highlighted = 0
  event onPick(choice: String)
  action next: highlighted += 1
  view:
    <div class="picker">
      <input bind={filter}/>
      <button onClick={onPick(filter)}>Pick</button>
    </div>

component CompositeDemo:
  state query     = "init"
  state picked    = ""
  state clicks    = 1
  ephemeral scratch = 99
  collection rows : RowItem

  action bump: clicks += 1

  invariant clicksPos: 1 <= clicks

  view:
    <div class="demo">
      <SearchBar bind:query={query} onClear={query = ""} onSubmitQuery={picked = _}/>
      <PickerBox bind:filter={query} onPick={picked = _}/>
      <Accordion heading="Details" extra={<span>!</span>}>
        <button class="inner" onClick={.bump}>{clicks}</button>
      </Accordion>
      <div>{for r in rows: <RowItem state={r}/>}</div>
    </div>

-- Verify hoisted stateful sub-component state, two-way `bind:`, and `event` forwarding work synchronously!
def step1 := CompositeDemo.update CompositeDemo.init (._sub_0 (._emit (.set_filter "lean4")))
#guard step1.query == "lean4"
def step2 := CompositeDemo.update step1 (._sub_0 (._emit (.onPick "lean4")))
#guard step2.picked == "lean4"
-- Toggling hoisted `<Accordion>` opens its panel and exposes parent-wired `{children}`
#guard !(Html.render (CompositeDemo.view CompositeDemo.init)).contains "class=\"panel\""
def step3 := CompositeDemo.update step2 (._sub_1 .toggle)
#guard (Html.render (CompositeDemo.view step3)).contains "class=\"panel\""
-- Ephemeral field `scratch` resets to `init` (`99`) across SSR dehydration while `query` and `clicks` round-trip!
#guard (CompositeDemo.app.rehydrate (CompositeDemo.app.dehydrate { step3 with clicks := 5, scratch := 0 })).map
  (fun s => (s.query, s.clicks, s.scratch)) == some ("lean4", 5, 99)

-- `<Await>` JSX tag on `Resource` + `.val`-free `Field` rendering
def awaitSample (r : Resource Ticket) : Html Unit :=
  <Await of={r} as={t} err={e} loading={<p>Wait</p>} failed={<p class="err">{e}</p>}>
    <article><h2>{t.title}</h2><span>{t.priority}</span></article>
  </Await>

#guard (Html.render (awaitSample .loading)).contains "<p>Wait</p>"
#guard (Html.render (awaitSample (.failed "boom"))).contains "<p class=\"err\">boom</p>"

component EarlyReturnCheck:
  state x : Int = 0
  action step(n: Int):
    if n <= 0: return
    x += n
  view: <span>{x}</span>
  invariant xPos: 0 <= x := by
    intro m msg h
    cases msg <;> simp_all [update] <;> split <;> simp_all <;> omega

#guard (EarlyReturnCheck.update { x := 5 } (.step 0)).x == 5
#guard (EarlyReturnCheck.update { x := 5 } (.step 3)).x == 8

-- Verify `component` emits a fine-grained `View` template (`V.el`, `V.dyn`, `V.ifElse`, `V.memo`, `V.forEach`)
def lazyBadge {msg : Type} (k : Nat) : Html msg := <span>{k}</span>

component FineGrainedCheck:
  state count : Nat = 1
  state items : Nat[] = [1, 2]
  action bump: count += 1
  view:
    <div>
      <span class="c">{count}</span>
      {<p>zero</p> if count == 0 else <p>nonzero</p>}
      {Qed.lazy(lazyBadge, count)}
      <ul>{for n in items: <li key={n}>{n}</li>}</ul>
    </div>

#guard match FineGrainedCheck.app.template with
  | .element "div" _ [.element "span" _ [.dyn _], .ifElse _ _ _, .memo _, .keyedList "ul" _ _ _ _ _ _ (some _)] => true
  | _ => false

/-- error: Invariant `BadUnguardedDecrease.inRange` failed in `BadUnguardedDecrease.update`:
  • action `decrease` must satisfy:  1 <= quantity - 1 and quantity - 1 <= 10

Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.
      If the rule does hold, add `using [lemma]` or a manual `:= by` proof. -/
#guard_msgs in
component BadUnguardedDecrease:
  state quantity = 1
  action decrease: quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  view: <span>{quantity}</span>

/-- error: `qunatity` is not a `state` field of this component (did you mean `quantity`?) (`state` fields: `quantity`) -/
#guard_msgs in
component BadStateFieldTypo:
  state quantity = 1
  action inc: qunatity += 1
  view: <span>{quantity}</span>

style safeBtnStyle:
  background-color: #111
style dangerBtnStyle:
  background-color: #999

component StyleLacksGood:
  state ok : Bool = true
  view:
    <div>
      <button role="submit" {safeBtnStyle}>OK</button>
      <span>safe</span>
    </div>
  invariant noDanger: roleLacks("submit", dangerBtnStyle), tagLacks("span", dangerBtnStyle)

#guard !(renderStyleSheet [{ className := "x", raw := Item.renderList [background "red/*evil*/</style"] }]).contains "/*"
#guard !(renderStyleSheet [{ className := "x", raw := Item.renderList [background "red/*evil*/</style"] }]).contains "<"
#guard !(renderStyleSheet [{ className := "x", raw := Item.renderList [background "red/*evil*/</style"] }]).contains "</style"
#guard (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := 5 })).map (·.x) == some 5
#guard (EarlyReturnCheck.app.rehydrate (EarlyReturnCheck.app.dehydrate { x := -1 })).isNone

/-- error: Styling invariant `BadRoleLacks.noDanger` failed in `BadRoleLacks.view`:
  • `roleLacks("submit", dangerBtnStyle)` does not hold in every state

Hint: A matching element in `BadRoleLacks.view` carries a forbidden style class in some branch. Remove that style from the matching element or guard it so it cannot apply there. -/
#guard_msgs in
component BadRoleLacks:
  state ok : Bool = true
  view: <button role="submit" {dangerBtnStyle}>Bad</button>
  invariant noDanger: roleLacks("submit", dangerBtnStyle)

/-- error: Invariant `BadPropInit.nonNeg` failed on initial state `BadPropInit.init`:
  • initial state must satisfy:  0 <= -1

Hint: Update the initial `state` values so `BadPropInit.nonNeg` holds, add `using [lemma]`, or supply a `:= by` proof. -/
#guard_msgs in
component BadPropInit:
  prop offset : Int = 0
  state count : Int = -1
  action nop: pass
  invariant nonNeg: 0 <= count
  view: <span>{count}</span>

/-- error: could not synthesize default value for parameter 'hpres' using tactics
---
error: SSR rehydration can violate the component's state invariant:
  • after rehydration must satisfy:  5 <= shown + 0

Hint: Rehydration resets `ephemeral` fields to their initial value. Remove `ephemeral` from fields constrained by an `invariant`, or weaken the invariant. -/
#guard_msgs (error, drop warning) in
component BadEphemeralInv:
  state shown : Int = 5
  ephemeral cache : Int = 0
  action shift:
    shown = 0
    cache = 5
  invariant totalMin: 5 <= shown + cache
  view: <span>{shown}</span>

-- ── Unified syntax & self-hosted `<Schema.Form>` checks ──
component SelfHostedFormKeep:
  state picked : Ticket?
  view: <Ticket.Form onSubmit={picked = some(_)}/>

component SelfHostedFormReset:
  state picked : Ticket?
  view: <Ticket.Form reset onSubmit={picked = some(_)}/>

def validTicketDraft : Ticket.Draft := { title := "Fix bug", priority := "3", kind := "bug" }
#guard SelfHostedFormKeep.init.picked.isNone && SelfHostedFormKeep.init._form_0 == Ticket.Draft.empty
#guard (Html.render (SelfHostedFormKeep.view SelfHostedFormKeep.init)).contains "disabled" &&
  !(Html.render (SelfHostedFormKeep.view { picked := none, _form_0 := validTicketDraft })).contains "disabled"
#guard match Ticket.parse validTicketDraft with
  | some t =>
      let sK := SelfHostedFormKeep.update { picked := none, _form_0 := validTicketDraft } (.set_picked (some t))
      let sR := SelfHostedFormReset.update { picked := none, _form_0 := validTicketDraft } ._form_reset_0
      sK.picked.map (·.title.val) == some t.title.val && sK._form_0 == validTicketDraft &&
      sR.picked.map (·.title.val) == some t.title.val && sR._form_0 == Ticket.Draft.empty
  | none => false

component MultiParamAndAutoDefaults:
  state xs : Nat[]
  state x  : Nat?
  event emitted(a: Nat, b: String)
  action pushBoth(a: Nat, b: String):
    xs.push(a)
    x = some(a)
    emitted.emit(a, b)
  view: <button onClick={.pushBoth(4, "hi")}>{xs.size}</button>
#guard MultiParamAndAutoDefaults.init.xs == #[] && MultiParamAndAutoDefaults.init.x.isNone
example : MultiParamAndAutoDefaults.update MultiParamAndAutoDefaults.init (.pushBoth 4 "hi") =
    ({ xs := #[4], x := some 4 }, some (.emitted 4 "hi")) := rfl

/-- error: use `Nat[]` instead of `Array Nat` -/
#guard_msgs in
component BadArrayType:
  state xs : Array Nat = []
  view: <span>{xs.size}</span>
/-- error: use `Nat?` instead of `Option Nat` -/
#guard_msgs in
schema BadOptType:
  val : Option Nat
/-- error: use `jsonOnly(String)` with parentheses instead of `jsonOnly String` -/
#guard_msgs in
schema BadJsonOnly:
  id : jsonOnly String

-- ── Unified Python-esque ergonomics checks (elif, match/case, if let, in/not in, f-strings, sequential) ──
component PythonicShowcase:
  state score : Nat = 5
  state tags  : String[] = ["lean"]
  state pick  : Nat? = some(2)
  state label : String = ""

  action classify(n: Nat):
    if 0 <= n <= 100:
      if n < 10:
        label = f"low:{n}"
      elif n < 50:
        label = f"mid:{n}"
      else:
        label = f"high:{n}"

  action addTag(t: String):
    if t in tags: return
    tags.push(t)
    label = f"tags:{tags.size}"

  action usePick:
    if let some(v) = pick:
      if v > 0:
        score = v * 2
        label = f"score={score}"

  action describeTab(tab: FilterTab):
    match tab:
      case .all:
        label = "all"
      case .tagged(t):
        label = f"tag:{t}"

  view:
    <div>
      <span>{label}</span>
      <span>{"has-lean" if "lean" in tags and pick is not none else "none"}</span>
    </div>

#guard (PythonicShowcase.update PythonicShowcase.init (.classify 5)).label == "low:5"
#guard (PythonicShowcase.update PythonicShowcase.init (.classify 25)).label == "mid:25"
#guard (PythonicShowcase.update PythonicShowcase.init (.classify 80)).label == "high:80"
#guard (PythonicShowcase.update PythonicShowcase.init (.addTag "lean")).tags.size == 1
#guard (PythonicShowcase.update PythonicShowcase.init (.addTag "qed")).label == "tags:2"
#guard (PythonicShowcase.update PythonicShowcase.init .usePick).label == "score=4"
#guard (PythonicShowcase.update PythonicShowcase.init (.describeTab (.tagged "ui"))).label == "tag:ui"
#guard (Html.render (PythonicShowcase.view PythonicShowcase.init)).contains "has-lean"
#guard Json.pathStr "{\"choices\":[{\"delta\":{\"content\":\"hi\"}}]}" "choices.0.delta.content" == "hi"
#guard Json.pathStr "{\"choices\":[]}" "choices.0.delta.content" == ""

-- ── Automated Quantified, Collection-Query, Nonlinear & Extended `for_each` Invariants ──

schema LineItem:
  id    : Nat
  price : Nat
  done  : Bool
  ts    : Nat

-- 1 & 2. Quantified IDs, uniqueBy, sumBy, countWhere, and isSortedBy — all proved WITHOUT `:= by`!
component SmartLedger:
  state rows       : LineItem[] = []
  state nextId     : Nat = 0
  state lastTs     : Nat = 0
  state totalCents : Nat = 0
  state doneCount  : Nat = 0

  action addItem(price: Nat, done: Bool):
    let ts = lastTs + 1
    rows.push(LineItem(id=nextId, price=price, done=done, ts=ts))
    nextId += 1
    lastTs = ts
    totalCents += price
    if done:
      doneCount += 1

  action reverseView:
    rows = rows.reverse

  action sortByPrice:
    rows = rows.sortBy((a, b) => a.price <= b.price)

  invariant idsAndUnique:
    (all r in rows: r.id < nextId) and rows.uniqueBy(r => r.id)
  invariant totalSynced:
    rows.sumBy(r => r.price) == totalCents
  invariant doneSynced:
    rows.countWhere(r => r.done) == doneCount and doneCount <= rows.size

  view:
    <div>
      <span>{totalCents}</span>
      <span>{doneCount}</span>
    </div>

component SortedTimeline:
  state events : LineItem[] = []
  state lastTs : Nat = 0

  action append(price: Nat):
    let ts = lastTs + 1
    events.push(LineItem(id=ts, price=price, done=false, ts=ts))
    lastTs = ts

  action dropLast:
    events = events.pop

  action keepExpensive(minPrice: Nat):
    events = events.filter(e => e.price >= minPrice)

  action sortByTs:
    events = events.sortBy((a, b) => decide(a.ts <= b.ts))

  invariant ordered:
    (all e in events: e.ts <= lastTs) and events.isSortedBy(e => e.ts)

  view: <span>{events.size}</span>

-- 3. Nonlinear arithmetic invariants (monotonic mul/div + ring) — proved WITHOUT `:= by`!
component BudgetCalc:
  state price    : Nat = 10
  state qty      : Nat = 2
  state maxPrice : Nat = 100
  state maxQty   : Nat = 50
  state total    : Nat = 200

  action setPrice(p: Nat):
    if p <= maxPrice:
      price = p

  action setQty(q: Nat):
    if q <= maxQty:
      qty = q

  action addTotal(delta: Nat):
    if total + delta <= 1000:
      total += delta

  invariant bounds:
    price <= maxPrice and qty <= maxQty and total <= 1000 and
    price * qty <= maxPrice * maxQty and
    total / 10 <= 100 and
    (qty + 1) * price == qty * price + price

  view: <span>{price * qty}</span>

-- 4. Extended `for_each` array ops (pop, reverse, extract, eraseIdxIfInBounds, swapIfInBounds, setIfInBounds, modify)
component PositiveCard:
  state id    : Nat = 0
  state score : Nat = 1
  key id
  action bump: score += 1
  invariant positive: 1 <= score
  view: <span>{score}</span>

component ExtendedDeck:
  collection cards : PositiveCard
  action addCard(nid: Nat):
    cards.push(PositiveCard.State(id=nid, score=1))
  action popCard:
    cards = cards.pop
  action flipDeck:
    cards = cards.reverse
  action sliceTop:
    cards = cards.extract(0, 5)
  action dropAt(i: Nat):
    cards = cards.eraseIdxIfInBounds(i)
  action swapCards(i: Nat, j: Nat):
    cards = cards.swapIfInBounds(i, j)
  action replaceAt(i: Nat, nid: Nat):
    cards = cards.setIfInBounds(i, PositiveCard.State(id=nid, score=5))
  action boostAt(i: Nat):
    cards = cards.modify(i, c => PositiveCard.State(id=c.id, score=c.score + 1))
  invariant deckSafe: PositiveCard.positive for_each cards
  view:
    <div>{for c in cards: <PositiveCard state={c}/>}</div>

end SyntaxChecks
