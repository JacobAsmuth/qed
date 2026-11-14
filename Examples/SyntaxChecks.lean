import Examples.Local
import Examples.Todo
open Qed

namespace SyntaxChecks

component Counter where
  prop step : Nat := 1
  state count : Nat := 0
  state saved : Nat := 0
  emits Nat
  action advance (times : Nat) when (times > 0) =>
    set count (count + step * times), set saved count, send count
  view => <button onClick={.advance 2}>{count}</button>

example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 2) =
    ({ count := 10, saved := 4 }, some 4) := rfl
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 0) =
    ({ count := 4, saved := 0 }, none) := rfl

def defaults : Html Unit := <Counter initial={{ count := 8 }}/>
#guard (Html.renderWith Counter.regs defaults).contains "8</button>"

def importedHelper (r : Local.Row) : Html Local.Msg := Local.widgetView r

def helperApp : App Local.Model Local.Msg := ui Local.init Local.update fun m =>
  importedHelper { id := 8, label := m.draft }

#guard (helperApp.locals.map (·.id)).contains "Local.Widget"
#guard (helperApp.locals.map (·.id)).contains "Local.Tag"
#guard helperApp.locals.length == 2

def rows : Array Todo.Row.State :=
  #[{ id := 8, text := "Zulu", done := false }, { id := 2, text := "Alpha", done := false }]
def sorted := Todo.Board.update { rows } .sort
#guard ((Todo.Board.update sorted (.rows "8" .toggle)).rows[1]?.map (·.done)) == some true
#guard ((Todo.Board.update sorted (.rows "8" .toggle)).rows[0]?.map (·.done)) == some false
#guard (Todo.Board.update (Todo.Board.update sorted (.remove 8)) (.rows "8" .toggle)).rows.size == 1
example : (Todo.Board.update { draft := "  " } .add).nextId = 0 := rfl

/-- error: `set label`: not a `state` field of this component (fields: [count]) -/
#guard_msgs in
component ReadOnly where
  prop label : String
  state count : Nat := 0
  action change => set label "changed"
  view => <span>{label}</span>

/-- error: duplicate action name `save` -/
#guard_msgs in
component DuplicateAction where
  state count : Nat := 0
  action save => set count 1
  action save => set count 2
  view => <span>{count}</span>

component Owned where
  prop caption : String
  state id : Nat
  state count : Nat
  key id
  action increment => set count (count + 1)
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
#guard (Container.regs.map (·.id)).contains "SyntaxChecks.Counter"
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

def stepCount (n : Nat) (d : Nat) : Nat := n + d
invariant nonNegFromZero : (fun n : Nat => 0 ≤ n) from (0 : Nat) preserved_by stepCount

def docDehydrate : Dehydrate (DocRoute × Resource (Array Qed.Demo.Signup)) :=
  Dehydrate.full

example (x : DocRoute × Resource (Array Qed.Demo.Signup)) :
    docDehydrate.rehydrate (docDehydrate.dehydrate x) = some x :=
  docDehydrate.round_trip x

def routedDehydratedApp : App DocRoute DocRoute :=
  ui DocRoute.home (fun _ r => r) (onRoute := id) (dehydrate := Dehydrate.full) fun r =>
    <div>{Router.toURL r}</div>

#guard routedDehydratedApp.rehydrate (routedDehydratedApp.dehydrate (.sec .benchmarks 3))
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
  action inc => set count (count + 1)
  view => <span>{count}</span>

invariant rowSafeFromInit :
  (fun r : RowItem.State => 0 ≤ r.count) from RowItem.init preserved_by RowItem.update

structure RowList where rows : Array RowItem.State
inductive RowListMsg | row (k : String) (m : RowItem.Msg)
def updateRowList (m : RowList) : RowListMsg → RowList
  | .row k cm => { rows := RowItem.updateKeyed m.rows k cm }

invariant listSafeFromInit : rowSafeFromInit for_each rows preserved_by updateRowList

#guard Router.fromURL "/docs/arch/2?tab=api#top" == some (DocRoute.sec .architecture 2)
#guard Router.fromURL "/?utm=1#hero" == some DocRoute.home

def typedLinkView (r : DocRoute) : View DocRoute DocRoute :=
  view% fun cur => <a href={r} class={if cur == r then "active" else ""}>{"Go"}</a>
#guard (Html.render (typedLinkView (.sec .architecture 2) .home)).contains "href=\"/docs/arch/2\""

def routeDehydrate : Dehydrate AppModel :=
  Dehydrate.fromRoute { route := .home } (fun _ r => ({ route := r } : AppModel)) id (·.route)
#guard routeDehydrate.rehydrate (routeDehydrate.dehydrate { route := .sec .benchmarks 7 })
  == some { route := .sec .benchmarks 7 }

def autoStyledApp : App AppModel Unit := ui { route := .home } (fun m _ => m) fun m => compositeNav m
#guard autoStyledApp.styles.length == 2
#guard (autoStyledApp.ssrStep "T" "/qed.js" "/" "").contains navOn.raw

#guard (renderTheme [nest "*, *::before" [margin (px 0)]]).contains
  ":where(*, *::before) { margin: 0px; }"

def tokBorder := token "border-subtle"
def typedBorderStyle : Style :=
  css [ border (px 1) .solid tokBorder, borderBottom (px 2) .dashed (hex "333"), borderTop "none" ]
#guard typedBorderStyle.raw ==
  "border: 1px solid var(--border-subtle); border-bottom: 2px dashed #333; border-top: none;"

def subBanner : View Section DocRoute :=
  view% fun s => <header><a href={DocRoute.sec s 1}>{Router.toURL (DocRoute.sec s 1)}</a></header>
def parentPage : View AppModel DocRoute :=
  view% fun m => <div>{subBanner (activeSection m.route)}</div>
#guard (Html.render (parentPage { route := .sec .architecture 3 })).contains "/docs/arch/1"
invariant parentPageHasHeader : hasTag "header" holds_in parentPage

component SingleChild where
  state count : Nat := 0
  action bump => set count (count + 1)
  view => <button onClick={.bump}>{count}</button>

inductive ParentMsg | child (m : SingleChild.Msg)
def singleChildJsx (s : SingleChild.State) : Html ParentMsg := <SingleChild state={s} onMsg={.child}/>
def singleChildDirect (s : SingleChild.State) : Html ParentMsg := SingleChild.render ParentMsg.child s
#guard Html.render (singleChildJsx { count := 5 }) == Html.render (singleChildDirect { count := 5 })
example : Component SingleChild.State SingleChild.Msg := SingleChild.toComponent

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

def hostModernApp : App Nat Unit := ui 0 (fun n _ => n) fun n =>
  <div data-n={n}><ModernCounter key="mc"/></div>
#guard hostModernApp.styles.any (·.raw == chipStyle.raw)

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
      {items.map fun (n : Nat) => <li key={n}>{n}</li>}
    </ul>
  </div>

#guard (Html.render (jsxErgonomicsView #[1, 2] (some "ok") true)).contains "<p>ok</p>"
#guard !(Html.render (jsxErgonomicsView #[] none false)).contains "<em>"

structure SliceModel where
  a : Nat
  b : String
  ephemeral : Nat
deriving DecidableEq

def sliceInit : SliceModel := { a := 1, b := "hi", ephemeral := 99 }
def sliceApp : App SliceModel Nat :=
  ui sliceInit (fun m d => { m with a := m.a + d }) (dehydrate := [a, b]) fun m =>
    <div>{m.a}{m.b}</div>

#guard sliceApp.rehydrate (sliceApp.dehydrate { a := 7, b := "yo", ephemeral := 0 })
  == some { a := 7, b := "yo", ephemeral := 99 }

invariant (m) on sliceApp : 1 ≤ m.a

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
def goodLazyView : View Nat Unit :=
  view% fun m => <div><a href={goodSafeUrl}>Docs</a>{Qed.lazy (fun (k : Nat) => <span>{k}</span>) (m / 2)}</div>
#guard (Html.render (goodLazyView 7)).contains "href=\"/docs/guide\""
#guard (Html.render (goodLazyView 7)).contains "<span>3</span>"

def sneakyBlock : Html Unit := <div>bad</div>

/-- error: could not synthesize default value for parameter 'valid_view' using tactics
---
error: HTML5 / XSS validity check (`Html.valid`) failed for this view.
  • unsolved HTML5 / attribute validity obligation: False

Common causes:
• Invalid HTML5 tag nesting (e.g. `<div>` inside `<p>`, `<button>` inside `<button>`/`<a>`, non-`<li>` inside `<ul>`/`<ol>`, non-`<tr>` inside `<tbody>`, non-`<option>` inside `<select>`)
• Non-empty children on a void element (`<input>`, `<img>`, `<br>`, …) or local component mount
• Forbidden tag (`<script>`, `<base>`, `<applet>`, `<object>`, `<embed>`) or raw `on*`/`srcdoc` attribute
• Dynamic URL-bearing attribute (`href`, `src`, `action`, …) not routed through `Router` or `Url`
• Unescaped dynamic text inside `<style>` (wrap with `escapeRawText` or `theme`/`styleSheet`) -/
#guard_msgs in
def badOpaqueNestingApp : App Unit Unit :=
  ui () (fun m _ => m) fun u => <p>{sneakyBlock}</p>

/-- error: Qed.lazy function must not capture model variable `m` directly; pass all model dependencies through the `[LawfulKey]` argument so memoization stays sound -/
#guard_msgs in
def badLazyCapturesModel : View Nat Unit :=
  view% fun m => <div>{Qed.lazy (fun (k : Nat) => <span>{k + m}</span>) (m / 2)}</div>

/-- error: could not synthesize default value for parameter 'hview' using tactics
---
error: SSR `dehydrate` slice does not preserve the rendered view: rehydrating a model can render different HTML on the client than SSR rendered on the server.
  • view mismatch after rehydration: "hi" = _qed_m.b

Include every model field read by the view in `(dehydrate := […])`, use `(dehydrate := Dehydrate.full)`, or supply a proof to `App.withDehydrate`. -/
#guard_msgs in
def badIncompleteDehydrate : App SliceModel Nat :=
  ui sliceInit (fun m d => { m with a := m.a + d }) (dehydrate := [a]) fun m =>
    <div>{m.a}{m.b}</div>

end SyntaxChecks
