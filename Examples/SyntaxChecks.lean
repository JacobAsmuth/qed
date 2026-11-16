import Examples.Local
import Examples.Todo
open Qed

namespace SyntaxChecks

component Counter where
  prop step : Nat := 1
  state count : Nat := 0
  state saved : Nat := 0
  event emitted (n : Nat)
  action advance (times : Nat) when (times > 0) =>
    count := count + step * times
    saved := count
    send (.emitted count)
  view => <button onClick={.advance 2}>{count}</button>

example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 2) =
    ({ count := 10, saved := 4 }, some (.emitted 4)) := rfl
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 0) =
    ({ count := 4, saved := 0 }, none) := rfl

def defaults : Html Unit := <Counter initial={{ count := 8 }}/>
#guard (Html.renderWith Counter.regs defaults).contains "8</button>"

def importedHelper (r : Local.Row) : Html Local.Msg :=
  <Local.Widget key={r.id} id={r.id} label={r.label}
    initial={{ note := r.label }} onReport={Local.Msg.reported r.id}/>

component HelperApp where
  state draft : String := ""
  action localEvent (m : Local.Msg) => ()
  view => (importedHelper { id := 8, label := draft }).map .localEvent

#guard (HelperApp.app.locals.map (·.id)).contains "SyntaxChecks.HelperApp"
#guard (HelperApp.app.locals.map (·.id)).contains "Local.Widget"
#guard (HelperApp.app.locals.map (·.id)).contains "Local.Tag"
#guard HelperApp.app.locals.length == 3

def rows : Array Todo.Row.State :=
  #[{ id := 8, text := "Zulu", done := false }, { id := 2, text := "Alpha", done := false }]
def sorted := Todo.update { rows } .sort
#guard ((Todo.update sorted (.rows "8" .toggle)).rows[1]?.map (·.done)) == some true
#guard ((Todo.update sorted (.rows "8" .toggle)).rows[0]?.map (·.done)) == some false
#guard (Todo.update (Todo.update sorted (.remove 8)) (.rows "8" .toggle)).rows.size == 1
example : (Todo.update { draft := "  " } .add).nextId = 0 := rfl

/-- error: `label`: not a `state` field of this component (fields: [count]) -/
#guard_msgs in
component ReadOnly where
  prop label : String
  state count : Nat := 0
  action change => label := "changed"
  view => <span>{label}</span>

/-- error: duplicate action name `save` -/
#guard_msgs in
component DuplicateAction where
  state count : Nat := 0
  action save => count := 1
  action save => count := 2
  view => <span>{count}</span>

component Owned where
  prop caption : String
  state id : Nat
  state count : Nat
  key id
  action increment => count := count + 1
  view => <button title={caption} onClick={.increment}>{count}</button>

def ownedView : Html (String × Owned.Msg) :=
  <Owned state={{ id := 4, count := 2 }} caption="Live" onMsg={Prod.mk}/>
#guard (Html.render ownedView).contains "Live"
example : (Owned.update { caption := "Live" } { id := 4, count := 2 } .increment).count = 3 := rfl

def counterHelper {msg : Type} : Html msg := <Counter key="helper"/>
/-- Component whose child is supplied by a helper. -/
component Container where
  state unused : Nat := 0
  view => <div>{counterHelper}</div>
#guard (Container.app.locals.map (·.id)).contains "SyntaxChecks.Counter"
#guard (Container.app.renderInitial).contains "0</button>"

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

example : ToJson Counter.Props := Counter.Props.instToJson
example : FromJson Counter.Props := Counter.Props.instFromJson
example : ToJson Counter.State := Counter.State.instToJson
example : FromJson Counter.State := Counter.State.instFromJson
example : ToJson Owned.State := Owned.State.instToJson
example : FromJson Owned.State := Owned.State.instFromJson

route_enum Section where
  overview
  architecture => "arch"
  benchmarks   => "bench"

router DocRoute where
  home => ""
  sec (s : Section) (page : Nat) => "docs"

#guard Router.toURL (DocRoute.sec .architecture 2) == "/docs/arch/2"
#guard Router.fromURL "/docs/bench/5" == some (DocRoute.sec .benchmarks 5)
#guard (Router.fromURL "/docs/unknown/5" : Option DocRoute) == none

def navOn  : Style := css [ fontWeight "700" ]
def navOff : Style := css [ fontWeight "400" ]
def navView (s : Section) : Html Unit :=
  <nav>
    <a role="nav-overview" {if s == .overview then navOn else navOff}>{"Overview"}</a>
    <a role="nav-arch"     {if s == .architecture then navOn else navOff}>{"Arch"}</a>
    <a role="nav-bench"    {if s == .benchmarks then navOn else navOff}>{"Bench"}</a>
  </nav>

invariant navExclusive :
  exactlyOneOf ["nav-overview", "nav-arch", "nav-bench"] navOn navOff holds_in navView

component StepCount where
  state n : Nat := 0
  action step (d : Nat) => n := n + d
  invariant nonNegFromZero : 0 ≤ n
  view => <span>{n}</span>

def docDehydrate : Dehydrate (DocRoute × Resource (Array Qed.Demo.Signup)) :=
  Dehydrate.full

example (x : DocRoute × Resource (Array Qed.Demo.Signup)) :
    docDehydrate.rehydrate (docDehydrate.dehydrate x) = some x :=
  docDehydrate.round_trip x

component RoutedDehydrated where
  route r : DocRoute := .home
  view => <div>{Router.toURL r}</div>

#guard (RoutedDehydrated.app.rehydrate (RoutedDehydrated.app.dehydrate { r := .sec .benchmarks 3 })).map (·.r)
  == some (.sec .benchmarks 3)

/-- error: styling invariant `badVacuousRole` doesn't hold for every model, `roleHasOneOf "nonexistent" [navOn, navOff]` is false for some `navView m`.

Some element the rule constrains isn't carrying one of the required style classes (or no element with that role/tag is rendered). Check that the `role`/tag it matches exists and gets one of the styles passed to `roleHasOneOf`/`tagHasOneOf` in every branch of `navView`. If the view is routed through `App.view`/`View.render` rather than a plain `Model → Html`, prove it with:  invariant badVacuousRole : … holds_in navView := by … -/
#guard_msgs in
invariant badVacuousRole : roleHasOneOf "nonexistent" [navOn, navOff] holds_in navView

def bothStylesView (b : Bool) : Html Unit :=
  <button role="btn" {navOn} {if b then navOff else navOff}>{"x"}</button>

/-- error: styling invariant `badDualStyle` doesn't hold for every model, `roleHasOneOf "btn" [navOn, navOff]` is false for some `bothStylesView m`.

Some element the rule constrains isn't carrying one of the required style classes (or no element with that role/tag is rendered). Check that the `role`/tag it matches exists and gets one of the styles passed to `roleHasOneOf`/`tagHasOneOf` in every branch of `bothStylesView`. If the view is routed through `App.view`/`View.render` rather than a plain `Model → Html`, prove it with:  invariant badDualStyle : … holds_in bothStylesView := by … -/
#guard_msgs in
invariant badDualStyle : roleHasOneOf "btn" [navOn, navOff] holds_in bothStylesView

structure AppModel where route : DocRoute deriving DecidableEq
def activeSection : DocRoute → Section | .home => .overview | .sec s _ => s
def compositeNav (m : AppModel) : Html Unit := <div>{navView (activeSection m.route)}</div>

invariant compositeNavExclusive :
  exactlyOneOf ["nav-overview", "nav-arch", "nav-bench"] navOn navOff holds_in compositeNav

def validCountView (n : Nat) : Html Unit :=
  <span role="pos" {if n > 0 then navOn else navOff}>{toString n}</span>

invariant posStyledFromInv :
  roleHas "pos" navOn holds_in validCountView assuming (fun n : Nat => n > 0)

component RowItem where
  state id    : Nat := 0
  state count : Nat := 0
  key id
  action inc => count := count + 1
  invariant rowSafeFromInit : 0 ≤ count
  view => <span>{count}</span>

#guard Router.fromURL "/docs/arch/2?tab=api#top" == some (DocRoute.sec .architecture 2)
#guard Router.fromURL "/?utm=1#hero" == some DocRoute.home

component TypedLink where
  prop target : DocRoute
  state cur : DocRoute := .home
  view => <a href={target} class={if cur == target then "active" else ""}>{"Go"}</a>
#guard (Html.render (TypedLink.view { target := .sec .architecture 2 } { cur := .home })).contains "href=\"/docs/arch/2\""

component AutoStyled where
  state route : DocRoute := .home
  action noop => ()
  view => (compositeNav { route }).map (fun _ => .noop)
#guard AutoStyled.app.styles.length == 2
#guard (AutoStyled.app.ssrStep "T" "/qed.js" "/" "").contains navOn.raw

#guard (renderTheme [nest "*, *::before" [margin (px 0)]]).contains
  ":where(*, *::before) { margin: 0px; }"

def tokBorder := token "border-subtle"
def typedBorderStyle : Style :=
  css [ border (px 1) .solid tokBorder, borderBottom (px 2) .dashed (hex "333"), borderTop "none" ]
#guard typedBorderStyle.raw ==
  "border: 1px solid var(--border-subtle); border-bottom: 2px dashed #333; border-top: none;"

component SubBanner where
  prop sec : Section
  view => <header><a href={DocRoute.sec sec 1}>{Router.toURL (DocRoute.sec sec 1)}</a></header>

component ParentPage where
  state route : DocRoute := .home
  invariant parentPageHasHeader : hasTag "header"
  view => <div><SubBanner sec={activeSection route}/></div>
#guard (Html.render (ParentPage.view { route := .sec .architecture 3 })).contains "/docs/arch/1"

component SingleChild where
  state count : Nat := 0
  action bump => count := count + 1
  view => <button onClick={.bump}>{count}</button>

inductive ParentMsg | child (m : SingleChild.Msg)
def singleChildJsx (s : SingleChild.State) : Html ParentMsg := <SingleChild state={s} onMsg={.child}/>
#guard (Html.render (singleChildJsx { count := 5 })).contains "5</button>"

def chipStyle : Style := css [ paddingX (px 6), marginTop (px 2) ]

component ModernCounter where
  state quantity := 1
  state draft    := ""
  state active   := true
  action increase when quantity < 10 =>
    let step := 1
    quantity += step
  action decrease when 1 < quantity => quantity -= 1
  invariant 1 ≤ quantity, quantity ≤ 10
  invariant roleHasOneOf "qty" [chipStyle]
  view =>
    <div>
      <button onClick={.decrease}>−</button>
      <span role="qty" {chipStyle}>{quantity}</span>
      <button onClick={.increase}>+</button>
      <button onClick={quantity := 5, draft := "five"}>Five</button>
      <input bind={draft}/>
      <input type="checkbox" bind={active}/>
    </div>

example : ModernCounter.init.quantity = 1 ∧ ModernCounter.init.draft = "" := ⟨rfl, rfl⟩
example := ModernCounter.inv
example := ModernCounter.inv_2

component HostModern where
  state n : Nat := 0
  view => <div data-n={n}><ModernCounter key="mc"/></div>
#guard HostModern.app.styles.any (·.raw == chipStyle.raw)

router RepoRoute where
  index => "/"
  blob  => "/orgs/:org/repos/:repo"
  edit  => "/orgs/:org/repos/:repo/edit"
  issues (page : Nat) => "/orgs/:org/issues/:page"

#guard Router.toURL (RepoRoute.edit "acme" "qed") == "/orgs/acme/repos/qed/edit"
#guard Router.fromURL "/orgs/acme/repos/qed/edit" == some (RepoRoute.edit "acme" "qed")
#guard Router.fromURL "/orgs/acme/repos/qed" == some (RepoRoute.blob "acme" "qed")
#guard Router.fromURL "/orgs/acme/issues/3" == some (RepoRoute.issues "acme" 3)

schema Ticket where
  id       : jsonOnly String
  title    : String where title.length ≥ 3
  priority : Nat    where 1 ≤ priority, priority ≤ 5
  urgent   : Bool
  kind     : select [("bug", "Bug"), ("feat", "Feature")]

def draftRoundTrip : Ticket.Draft := { title := "Fix parser", priority := "2" }
#guard ((Json.parse (Json.render (toJson draftRoundTrip))).bind fromJson).toOption == some draftRoundTrip

def jsxErgonomicsView (items : Array Nat) (note? : Option String) (highlight : Bool) : Html Unit :=
  <div {if highlight then chipStyle} data-tag={if highlight then "hi"}>
    <>
      <span>Header</span>
      {if highlight then <em>!</em>}
      {if let some note := note? then <p>{note}</p>}
    </>
    <ul>
      <li key="head">Top</li>
      {for n in items => <li key={n}>{n}</li>}
    </ul>
  </div>

#guard (Html.render (jsxErgonomicsView #[1, 2] (some "ok") true)).contains "<p>ok</p>"
#guard !(Html.render (jsxErgonomicsView #[] none false)).contains "<em>"

component AutoSliceComp where
  state a : Nat := 1
  state b : String := "hi"
  state ephemeral : Nat := 99
  action bump (d : Nat) => a := a + d
  invariant sliceSafe : 1 ≤ a
  view => <div>{a}{b}</div>

component EphemeralComp where
  state a : Nat := 1
  state b : String := "hi"
  ephemeral ephemeral : Nat := 99
  action bump (d : Nat) => a := a + d
  view => <div>{a}{b}</div>

#guard (AutoSliceComp.app.rehydrate (AutoSliceComp.app.dehydrate { a := 7, b := "yo", ephemeral := 0 })).map
  (fun s => (s.a, s.b, s.ephemeral)) == some (7, "yo", 0)
#guard (EphemeralComp.app.rehydrate (EphemeralComp.app.dehydrate { a := 7, b := "yo", ephemeral := 0 })).map
  (fun s => (s.a, s.b, s.ephemeral)) == some (7, "yo", 99)
#guard (ModernCounter.app.rehydrate (ModernCounter.app.dehydrate { quantity := 6, draft := "six", active := false })).map (·.quantity) == some 6

inductive FilterTab | all | tagged (tag : String) deriving DecidableEq
structure PlainNote where
  id   : Nat
  text : String
deriving DecidableEq

component RichAuto where
  state tab   : FilterTab := .all
  state notes : Array PlainNote := #[]
  state pick  : Option PlainNote := none
  state cache : Cached String := {}
  state child : SingleChild.State := { count := 0 }
  view => <div>{notes.size}{child.count}</div>

#guard (RichAuto.app.rehydrate (RichAuto.app.dehydrate
  { tab := .tagged "lean", notes := #[{ id := 1, text := "hello" }], pick := some { id := 2, text := "pinned" },
    cache := ({} : Cached String).put "k" (.ok "v") "k", child := { count := 42 } })).map
  (fun m => m.tab == .tagged "lean" && m.notes == #[{ id := 1, text := "hello" }] &&
            m.pick == some { id := 2, text := "pinned" } && m.cache.lookup "k" == some "v" && m.child.count == 42) == some true

component PartialFn where
  state count : Nat := 1
  state fn    : Nat → Nat := (· + 10)
  action bump (d : Nat) => count := count + d
  view => <div>{count}</div>
#guard ((PartialFn.app.rehydrate (PartialFn.app.dehydrate { count := 8, fn := (· * 2) })).map fun m => (m.count, m.fn 5)) == some (8, 15)

-- ── Compile-time rejection checks (#guard_msgs) ─────────────────────────

/-- error: failed to synthesize instance of type class
  ToHref String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
def badRawHref : Html Unit := <a href="/raw">bad</a>

/-- error: unsafe URL literal `javascript:alert(1)`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badJsUrl : Url := url% "javascript:alert(1)"

/-- error: unsafe URL literal `data:text/html,<script>alert(1)</script>`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badDataUrl : Url := url% "data:text/html,<script>alert(1)</script>"

/-- error: unsafe URL literal `//evil.example/x`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters -/
#guard_msgs in
def badProtocolRelativeUrl : Url := url% "//evil.example/x"

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

def goodSafeUrl : Url := url% "/docs/guide"
component GoodLazy where
  state m : Nat := 7
  view => <div><a href={goodSafeUrl}>Docs</a>{Qed.lazy (fun (k : Nat) => <span>{k}</span>) (m / 2)}</div>
#guard (Html.render (GoodLazy.app.view { m := 7 })).contains "href=\"/docs/guide\""
#guard (Html.render (GoodLazy.app.view { m := 7 })).contains "<span>3</span>"

def sneakyBlock {msg : Type} : Html msg := <div>bad</div>

/-- error: could not synthesize default value for parameter 'hvalid' using tactics
---
error: HTML5 / XSS validity check (`Html.valid`) failed for this view.
  • unsolved HTML5 / attribute validity obligation: False

Common causes:
• Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<button>`/`<a>`, non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)
• Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount
• Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute
• Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`
• Unescaped dynamic text inside `<style>` (wrap with `escapeRawText` or `theme`)
---
error: could not synthesize default value for parameter 'valid_view' using tactics
---
error: HTML5 / XSS validity check (`Html.valid`) failed for this view.
  • unsolved HTML5 / attribute validity obligation: False

Common causes:
• Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<button>`/`<a>`, non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)
• Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount
• Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute
• Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`
• Unescaped dynamic text inside `<style>` (wrap with `escapeRawText` or `theme`) -/
#guard_msgs in
component BadOpaqueNesting where
  state u : Unit := ()
  view => <p>{sneakyBlock}</p>

/-- error: Qed.lazy function must not capture state directly; pass all state dependencies through the `[LawfulKey]` argument so memoization stays sound -/
#guard_msgs in
component BadLazyCapturesModel where
  state m : Nat := 1
  view => <div>{Qed.lazy (fun (k : Nat) => <span>{k + m}</span>) (m / 2)}</div>

/-- error: could not synthesize default value for parameter 'hview' using tactics
---
error: SSR `dehydrate` slice does not preserve the rendered view: rehydrating a model can render different HTML on the client than SSR rendered on the server.
  • view mismatch after rehydration: "hi" = _qed_m.b

Do not mark model fields read by the view as `ephemeral` (so rehydration preserves the rendered view). -/
#guard_msgs in
component BadEphemeralReadByView where
  state a : Nat := 1
  ephemeral b : String := "hi"
  view => <div>{a}{b}</div>

-- ── Sub-components, unified `app`, `Field`, `<Await>`, & fractional CSS checks ──

def fracStyle : Style := css [
  padding (rem 0.75) (rem 1.5),
  margin (rem 2) .auto,
  gap (px 4) (px 8),
  lineHeight 1.5,
  fontWeight 600,
  opacity 0.85,
  zIndex (-1) ]

#guard fracStyle.raw ==
  "padding: 0.75rem 1.5rem; margin: 2rem auto; gap: 4px 8px; line-height: 1.5; font-weight: 600; opacity: 0.85; z-index: -1;"

#guard (match (Resource.ok (none : Option Nat)).someOr "missing" with | .failed "missing" => true | _ => false)
#guard (match (Resource.ok (some 42)).someOr "missing" with | .ok 42 => true | _ => false)

component Card where
  prop title : String
  slot badge
  children
  view =>
    <div class="card">
      <header><h3>{title}</h3>{badge}</header>
      <div class="card-body">{children}</div>
    </div>

component SearchBar where
  bind query : String := ""
  event onClear
  event onSubmitQuery (q : String)
  view =>
    <div class="search-bar">
      <input bind={query}/>
      <button class="clear" onClick={onClear}>Clear</button>
      <button class="go" onClick={onSubmitQuery query}>Go</button>
    </div>

component ListChip where
  prop text : String
  view => <li class="chip">{text}</li>

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

-- Stateful sub-component with `children`, `slot`, `bind:`, and `event` hoisted into a parent `app`
component Accordion where
  prop heading : String
  slot extra
  state openPanel := false
  action toggle => openPanel := !openPanel
  children
  view =>
    <section class="accordion">
      <header>
        <button class="toggle" onClick={.toggle}>{heading}</button>
        {extra}
      </header>
      {if openPanel then <div class="panel">{children}</div>}
    </section>

component PickerBox where
  bind filter : String := ""
  state highlighted := 0
  event onPick (choice : String)
  action next => highlighted += 1
  view =>
    <div class="picker">
      <input bind={filter}/>
      <button onClick={onPick filter}>Pick</button>
    </div>

component CompositeDemo where
  state query     := "init"
  state picked    := ""
  state clicks    := 1
  ephemeral scratch := 99
  collection rows : RowItem

  action bump => clicks += 1

  invariant clicksPos : 1 ≤ clicks

  view =>
    <div class="demo">
      <SearchBar bind:query={query} onClear={query := ""} onSubmitQuery={picked := ·}/>
      <PickerBox bind:filter={query} onPick={picked := ·}/>
      <Accordion heading="Details" extra={<span>!</span>}>
        <button class="inner" onClick={.bump}>{clicks}</button>
      </Accordion>
      <div>{for r in rows => <RowItem state={r}/>}</div>
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

-- `<Schema.Form>` JSX tag, `{for ... => ...}`, inline `for_each`, early `return`, & scoped manual `invariant` proof
component TicketFormHost where
  state draft := Ticket.Draft.empty
  state saved : Option Ticket := none
  action submit => saved := Ticket.parse draft
  view =>
    <div class="host">
      <Ticket.Form bind={draft} onSubmit={.submit}/>
    </div>

#guard (Html.render (TicketFormHost.view TicketFormHost.init)).contains "class=\"qed-form\""

def forLoopHtml : Html Unit :=
  <ul>
    {for n in (#[1, 2] : Array Nat) => <li key={n}>{n}</li>}
    {for n in ([3, 4] : List Nat) => <li key={n}>{n}</li>}
  </ul>

#guard (Html.render forLoopHtml).contains "<li>1</li><li>2</li><li>3</li><li>4</li>"

component InlineForEachParent where
  collection rows : RowItem
  invariant rowsSafe : RowItem.rowSafeFromInit for_each rows
  view => <ul>{for r in rows => <li><RowItem state={r}/></li>}</ul>

example := InlineForEachParent.rowsSafe

component EarlyReturnCheck where
  state x : Int := 0
  action step (n : Int) =>
    if n ≤ 0 then return
    x += n
  view => <span>{x}</span>
  invariant xPos : 0 ≤ x := by
    intro m msg h
    cases msg <;> simp_all [update] <;> split <;> simp_all <;> omega

#guard (EarlyReturnCheck.update { x := 5 } (.step 0)).x == 5
#guard (EarlyReturnCheck.update { x := 5 } (.step 3)).x == 8

-- Verify `component` emits a fine-grained `View` template (`V.el`, `V.dyn`, `V.ifElse`, `V.memo`, `V.forEach`)
def lazyBadge {msg : Type} (k : Nat) : Html msg := <span>{k}</span>

component FineGrainedCheck where
  state count : Nat := 1
  state items : Array Nat := #[1, 2]
  action bump => count += 1
  view =>
    <div>
      <span class="c">{count}</span>
      {if count == 0 then <p>zero</p> else <p>nonzero</p>}
      {Qed.lazy lazyBadge count}
      <ul>{for n in items => <li key={n}>{n}</li>}</ul>
    </div>

#guard match FineGrainedCheck.app.template with
  | .element "div" _ [.element "span" _ [.dyn _], .ifElse _ _ _, .memo _, .keyedList "ul" _ _ _ _ _] => true
  | _ => false

/-- error: Unknown identifier `mkApp` -/
#guard_msgs in
#check mkApp

/-- error: Unknown identifier `mkRoutedApp` -/
#guard_msgs in
#check mkRoutedApp

/-- error: Unknown identifier `ui` -/
#guard_msgs in
#check ui

/-- error: Unknown identifier `SingleChild.mount` -/
#guard_msgs in
#check SingleChild.mount

/-- error: Unknown identifier `SingleChild.toComponent` -/
#guard_msgs in
#check SingleChild.toComponent

/-- error: Unknown identifier `view` -/
#guard_msgs in
example : View Nat Unit := view% (fun (n : Nat) => <div>{n}</div>)

end SyntaxChecks
