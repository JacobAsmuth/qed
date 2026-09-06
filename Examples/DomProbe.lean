/- Browser differential oracle: exercise the real driver with Lean-built trees and templates.
   The test compares incremental updates with fresh DOM and the pure Html renderer. -/
import Qed
import Qed.Driver

open Qed
namespace DomProbe

def row (seed id : Nat) : Html Nat :=
  .element (if (seed + id) % 5 == 0 then "p" else "div")
    ([.key (toString id), .attr "data-id" (toString id)] ++
      if seed % 2 == 0 then [.cls "active", .attr "title" "present"] else [])
    [.text s!"row {id}: {seed % 7}",
     .element "button" (if seed % 3 == 0 then [] else [.on "click" (seed + id)]) [.text "select"],
     .element "input" ([.attr "type" "checkbox"] ++
       if seed % 2 == 0 then [.flag "checked" true, .attr "value" (toString seed)] else []) []]

def ids (seed : Nat) : List Nat :=
  match seed % 8 with
  | 0 => [] | 1 => [0] | 2 => [0, 1, 2] | 3 => [2, 0, 1]
  | 4 => [2, 3] | 5 => [1, 1, 2] | 6 => [2, 1, 1] | _ => [3, 2, 1, 0]

def tree (seed : Nat) : Html Nat :=
  if seed % 13 == 12 then .text s!"text root {seed}"
  else .element "section" [] [
    .element "article" [] ((ids seed).map (row seed)),
    .lazy (toString (seed / 3)) (.element "aside" [] [.text s!"memo {seed / 3}"]),
    .element "svg" [] [.element "use"
      (if seed % 2 == 0 then [.attr "xlink:href" "#icon"] else []) []]]

def handlers : IO (Handlers Nat) := do
  return { click := (← IO.mkRef #[]), input := (← IO.mkRef #[]),
           mountLocal := fun _ _ _ _ _ _ => pure () }

initialize liveHandlers : IO.Ref (Option (Handlers Nat)) ← IO.mkRef none
initialize oldTree : IO.Ref (Html Nat) ← IO.mkRef (.text "")
initialize parentRef : IO.Ref Dom.Node ← IO.mkRef 0

def mount (seed : Nat) : IO Dom.Node := do
  let h ← handlers
  liveHandlers.set (some h)
  let parent ← Dom.createElement "" "main"
  Dom.appendChild parent (← buildDom h "" (tree seed))
  oldTree.set (tree seed)
  parentRef.set parent
  return parent

def advance (seed : Nat) : IO Unit := do
  if let some h ← liveHandlers.get then
    let parent ← parentRef.get
    applyToDom h parent 0 (← Dom.childAt parent 0) (diff (← oldTree.get) (tree seed))
    oldTree.set (tree seed)

def fresh (seed : Nat) : IO Dom.Node := do
  buildDom (← handlers) "" (tree seed)

def expected (seed : Nat) : String := Html.render (tree seed)

def handlerValue (id : Nat) : IO Nat := do
  if let some h ← liveHandlers.get then return (← h.click.get).getD id 999999
  return 999999

-- Unique rows exercise the signal path, keyed moves, and conditional structure.
def structuredRows : View Nat Nat :=
  V.forEach "article" (fun seed => ((ids seed).eraseDups).toArray.map (fun id => (id, seed)))
    (fun r => toString r.1)
    (.element "div" [] [
      .dyn (fun r => s!"row {r.1}: {r.2}"),
      .ifElse (fun r => r.2 % 2 == 0) (.text "even") (.text "odd"),
      .showIf (fun r => r.2 % 3 != 0)
        (.element "em" [.dynVal "title" (fun r => s!"title {r.2}")] [
          .dyn (fun r => s!"shown {r.2}"),
          V.showIf (fun r => r.2 % 2 == 0) (.dyn (fun r => s!"nested {r.2}"))]),
      .dyn (fun r => s!"after {r.2}")])
    [.bind (fun seed => if seed % 2 == 0 then .cls "even" else .attr "title" "odd")]

-- Exercise both opaque-row reconciliation and the signal-only list fast path.
def template : View Nat Nat :=
  .element "section" [] [structuredRows,
    V.forEach "aside" (fun seed => ((ids seed).eraseDups).toArray.map (fun id => (id, seed)))
      (fun r => toString r.1)
      (.element "p" [.dynVal "title" (fun r => s!"signal {r.2}")]
        [.dyn (fun r => s!"{r.1}:{r.2}")])]

initialize templateState : IO.Ref (Option (VState Nat Nat)) ← IO.mkRef none
initialize cells : CondCells Nat Nat ← IO.mkRef (#[], #[])

def mountTemplate (seed : Nat) : IO Dom.Node := do
  let h ← handlers
  liveHandlers.set (some h)
  cells.set (#[], #[])
  let parent ← Dom.createElement "" "main"
  let (node, state) ← buildView h cells "" template seed
  Dom.appendChild parent node
  parentRef.set parent
  templateState.set (some state)
  return parent

def advanceTemplate (seed : Nat) : IO Unit := do
  if let some h ← liveHandlers.get then
    if let some st ← templateState.get then
      patchView h cells (← parentRef.get) 0 template seed st

def expectedTemplate (seed : Nat) : String := Html.render (View.render template seed)

def duplicateTemplate : View Nat Nat :=
  V.forEach "div" (fun seed => if seed == 0 then #[0, 1] else #[1, 1])
    toString (.dyn toString)

def duplicateBuild : IO Dom.Node := do
  return (← buildView (← handlers) cells "" duplicateTemplate 1).1

def duplicateUpdate : IO Unit := do
  let h ← handlers
  let (node, state) ← buildView h cells "" duplicateTemplate 0
  patchView h cells node 0 duplicateTemplate 1 state

def duplicateHydrate : IO Unit := do
  let h ← handlers
  let (node, _) ← buildView h cells "" duplicateTemplate 0
  discard <| hydrateView h cells duplicateTemplate 1 node

end DomProbe
