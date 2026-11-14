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
    <div {Attr.rawHtml "<em>raw</em>"}/>
    {defaults}
  </div>
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains ".a > .b"
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains "<\\/style>"
#guard !(Html.renderWith Counter.regs ssrEdgeCases).contains "</br>"
#guard (Html.renderWith Counter.regs ssrEdgeCases).contains "<em>raw</em>"
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

end SyntaxChecks
