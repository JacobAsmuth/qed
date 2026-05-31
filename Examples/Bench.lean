/-
  Performance benchmarks for the rebuild + diff pipeline — the cost *upstream* of the
  DOM patch, which keyed reconciliation does not address. For a large list it measures,
  per edit:

    • rebuild — `view newModel`, allocating the whole `Html` tree afresh
    • diff    — `diff oldTree newTree`, walking the whole tree to compute the patch
    • patch-ops — the size of the resulting patch (how much the driver must apply)

  under four edits: update one element, remove one, add one, reorder all (ascending →
  descending). Everything here is pure Lean, so this runs natively: `lake exe bench`.
  Re-run after `Html.lazy` lands to see rebuild/diff/patch-ops collapse to O(changed).

  Distinct edits are pre-built per benchmark so the optimizer can't hoist a constant
  `view`/`diff` out of the timing loop; `treeNodes`/`patchNodes` force full evaluation.
-/
import Qed
open Qed

namespace Bench

structure Row where
  id    : Nat
  label : String
  n     : Nat

def mkRows (count : Nat) : Array Row :=
  (Array.range count).map fun i => { id := i, label := s!"item {i}", n := i }

def rowView (r : Row) : Html Unit :=
  li [key (toString r.id), cls "row"] [
    span [cls "label"] [r.label],
    span [cls "count"] [toString r.n]
  ]

def view (rows : Array Row) : Html Unit :=
  ul [cls "list"] (rows.map rowView).toList

-- Force a tree / patch to a number, so the work can't be dead-code-eliminated.
mutual
  def treeNodes : Html msg → Nat
    | .text _         => 1
    | .element _ _ cs => 1 + listNodes cs
  def listNodes : List (Html msg) → Nat
    | []      => 0
    | c :: cs => treeNodes c + listNodes cs
end

mutual
  def patchNodes : Patch msg → Nat
    | .replace _          => 1
    | .setText _          => 1
    | .patchElement _ k   => 1 + childNodes k
    | .patchKeyed _ steps => 1 + stepNodes steps
  def childNodes : ChildPatch msg → Nat
    | .patch p rest => patchNodes p + childNodes rest
    | .append _     => 1
    | .drop         => 1
  def stepNodes : List (KeyedStep msg) → Nat
    | []                 => 0
    | .reuse _ p :: rest => patchNodes p + stepNodes rest
    | .create _ :: rest  => 1 + stepNodes rest
end

def ms (ns : Nat) : String :=
  let hundredths := (ns + 5000) / 10000   -- ns → ms with 2 decimals, rounded
  s!"{hundredths / 100}.{let r := hundredths % 100; if r < 10 then s!"0{r}" else s!"{r}"} ms"

/-- Time processing a set of distinct edits against `base`: rebuild each, diff it, force
    both, and report the per-edit average plus the patch size. -/
def bench (label : String) (base : Array Row) (edits : Array (Array Row)) : IO Unit := do
  let oldTree := view base
  let mut warm := treeNodes oldTree
  let mut rebuild : Nat := 0
  let mut diffT   : Nat := 0
  let mut ops     : Nat := 0
  for e in edits do
    let t0 ← IO.monoNanosNow
    let nt := view e
    let c  := treeNodes nt           -- force the rebuild
    let t1 ← IO.monoNanosNow
    let p  := diff oldTree nt
    let po := patchNodes p           -- force the diff
    let t2 ← IO.monoNanosNow
    rebuild := rebuild + (t1 - t0)
    diffT   := diffT + (t2 - t1)
    ops     := po
    warm    := warm + c
  let k := max 1 edits.size
  IO.println s!"  {label}:  rebuild {ms (rebuild / k)}   diff {ms (diffT / k)}   patch-ops {ops}   [csum {warm % 7}]"

def main : IO Unit := do
  let n := 20000
  let base := mkRows n
  let spots := (Array.range 10).map (· * (n / 10))   -- 0, 2000, …, 18000 (distinct positions)
  IO.println s!"▸ rebuild + diff over a {n}-row keyed list — no lazy (current model)\n"
  bench "update one" base (spots.map fun i => base.modify i (fun r => { r with n := r.n + 1 }))
  bench "remove one" base (spots.map fun i => base.extract 0 i ++ base.extract (i + 1) base.size)
  bench "add one"    base (spots.map fun i =>
    base.extract 0 i ++ #[({ id := n + i, label := "new", n := 0 } : Row)] ++ base.extract i base.size)
  bench "reorder all" base #[base.reverse]
  IO.println ""

end Bench

def main : IO Unit := Bench.main
