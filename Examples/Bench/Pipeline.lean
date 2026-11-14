import Qed
open Qed

namespace Bench

structure Row where
  id    : Nat
  label : String
  n     : Nat

def mkRows (count : Nat) : Array Row :=
  (Array.range count).map fun i => { id := i, label := s!"item {i}", n := i }

def rowBody (r : Row) : Html Unit :=
  <div class="row-body">
    <span class="label">{r.label}</span>
    <div class="meta">
      <span class="id">{toString r.id}</span>
      <span class="count">{toString r.n}</span>
      <span class="tag">{if r.n % 2 == 0 then "even" else "odd"}</span>
    </div>
    <div class="controls"><span>▲</span><span>▼</span><span>✕</span></div>
  </div>

def rowView     (r : Row) : Html Unit := <li key={toString r.id} class="row">{rowBody r}</li>
def rowViewLazy (r : Row) : Html Unit := <li key={toString r.id} class="row">{lazy s!"{r.id}-{r.n}" (rowBody r)}</li>

def view     (rows : Array Row) : Html Unit := <ul class="list">{rows.map rowView}</ul>
def viewLazy (rows : Array Row) : Html Unit := <ul class="list">{rows.map rowViewLazy}</ul>

mutual
  def treeNodes : Html msg → Nat
    | .text _         => 1
    | .lazy _ s       => 1 + treeNodes s
    | .element _ _ cs => 1 + listNodes cs
  def listNodes : List (Html msg) → Nat
    | []      => 0
    | c :: cs => treeNodes c + listNodes cs
end

mutual
  def patchNodes : Patch msg → Nat
    | .replace _            => 1
    | .setText _            => 1
    | .lazyReuse _ _        => 1
    | .lazyPatch _ p        => 1 + patchNodes p
    | .patchElement _ steps => 1 + stepNodes steps
  def stepNodes : List (KeyedStep msg) → Nat
    | []                 => 0
    | .reuse _ p :: rest => patchNodes p + stepNodes rest
    | .create _ :: rest  => 1 + stepNodes rest
end

def ms (ns : Nat) : String :=
  let h := (ns + 5000) / 10000
  s!"{h / 100}.{let r := h % 100; if r < 10 then s!"0{r}" else s!"{r}"} ms"

def bench (label : String) (viewFn : Array Row → Html Unit)
    (base : Array Row) (edits : Array (Array Row)) : IO Unit := do
  let oldTree := viewFn base
  let mut warm := treeNodes oldTree
  let mut rebuild : Nat := 0
  let mut diffT   : Nat := 0
  let mut ops     : Nat := 0
  for e in edits do
    let t0 ← IO.monoNanosNow
    let nt := viewFn e
    let c  := treeNodes nt
    let t1 ← IO.monoNanosNow
    let p  := diff oldTree nt
    let po := patchNodes p
    let t2 ← IO.monoNanosNow
    rebuild := rebuild + (t1 - t0); diffT := diffT + (t2 - t1); ops := po; warm := warm + c
  let k := max 1 edits.size
  IO.println s!"  {label}  rebuild {ms (rebuild / k)}   diff {ms (diffT / k)}   patch-ops {ops}   [csum {warm % 7}]"

def main : IO Unit := do
  let n := 20000
  let base := mkRows n
  let spots := (Array.range 10).map (· * (n / 10))
  let updates := spots.map fun i => base.modify i (fun r => { r with n := r.n + 1 })
  let removes := spots.map fun i => base.extract 0 i ++ base.extract (i + 1) base.size
  let adds    := spots.map fun i =>
    base.extract 0 i ++ #[({ id := n + i, label := "new", n := 0 } : Row)] ++ base.extract i base.size
  let run (lbl : String) (v : Array Row → Html Unit) : IO Unit := do
    IO.println lbl
    bench "update one " v base updates
    bench "remove one " v base removes
    bench "add one    " v base adds
    bench "reorder all" v base #[base.reverse]
  IO.println s!"▸ rebuild + diff over a {n}-row keyed list (~12 nodes/row)\n"
  run "  plain view:" view
  IO.println ""
  run "  Html.lazy (memo key = the row's mutable field):" viewLazy
  IO.println ""

end Bench

def main : IO Unit := Bench.main
