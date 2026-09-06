/- Compile-time regressions for the authored component API. -/
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

-- Assignments and outputs share the pre-update state. A failed guard emits nothing.
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 2) =
    ({ count := 10, saved := 4 }, some 4) := rfl
example : Counter.update { step := 3 } { count := 4, saved := 0 } (.advance 0) =
    ({ count := 4, saved := 0 }, none) := rfl

-- Defaults are usable at mount sites, while explicit initial values seed only state.
def defaults : Html Unit := <Counter initial={{ count := 8 }}/>
#guard (Html.renderWith Counter.regs defaults).contains "8</button>"

-- Registration follows imported helpers and their nested components.
def importedHelper (r : Local.Row) : Html Local.Msg := Local.widgetView r

def helperApp : App Local.Model Local.Msg := ui Local.init Local.update fun m =>
  importedHelper { id := 8, label := m.draft }

#guard (helperApp.locals.map (·.id)).contains "Local.Widget"
#guard (helperApp.locals.map (·.id)).contains "Local.Tag"
#guard helperApp.locals.length == 2

-- Keyed messages address identity after sorting, and become no-ops after deletion.
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

/-- A parent-owned component may receive props without storing them in its state. -/
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

-- A helper inside a component is included even when rendering through Name.regs.
def counterHelper {msg : Type} : Html msg := <Counter key="helper"/>
/-- A component whose child is supplied by a helper. -/
component Container where
  state unused : Nat := 0
  view => <div>{counterHelper}</div>
#guard (Container.regs.map (·.id)).contains "SyntaxChecks.Counter"
#guard (Container.app.renderInitial).contains "0</button>"

end SyntaxChecks
