import Qed.Diff
import Qed.Notation
open Qed

namespace Bench

structure Row where
  id    : Nat
  label : String
  n     : Nat
deriving BEq, DecidableEq

instance : LawfulKey Row where
  toKey r := toString r.id ++ (":" ++ (toString r.n ++ (":" ++ r.label)))
  injective := fun ⟨i1, l1, n1⟩ ⟨i2, l2, n2⟩ h => by
    have hcolon : ':' < '0' ∨ '9' < ':' := .inr (by decide)
    have ⟨hi, hr⟩ := Qed.Str.str_split_sep_inj (d := ':') rfl (Qed.Str.nat_toString_not_mem hcolon i1) (Qed.Str.nat_toString_not_mem hcolon i2) h
    have ⟨hn, hl⟩ := Qed.Str.str_split_sep_inj (d := ':') rfl (Qed.Str.nat_toString_not_mem hcolon n1) (Qed.Str.nat_toString_not_mem hcolon n2) hr
    cases Qed.Str.nat_toString_injective hi; cases Qed.Str.nat_toString_injective hn; cases hl; rfl

def mkRows (count : Nat) : Array Row :=
  (Array.range count).map fun i => { id := i, label := s!"item {i}", n := i }

def rowBody (r : Row) : Html Unit :=
  el "div" [cls "row-body"] [
    el "span" [cls "label"] [.text r.label],
    el "div" [cls "meta"] [
      el "span" [cls "id"] [.text (toString r.id)],
      el "span" [cls "count"] [.text (toString r.n)],
      el "span" [cls "tag"] [.text (if r.n % 2 == 0 then "even" else "odd")]],
    el "div" [cls "controls"] [el "span" [] [.text "▲"], el "span" [] [.text "▼"], el "span" [] [.text "✕"]]]

def rowView     (r : Row) : Html Unit := el "li" [key (toString r.id), cls "row"] [rowBody r]
def rowViewLazy (r : Row) : Html Unit := el "li" [key (toString r.id), cls "row"] [lazy rowBody r]

def view     (rows : Array Row) : Html Unit := el "ul" [cls "list"] (rows.map rowView).toList
def viewLazy (rows : Array Row) : Html Unit := el "ul" [cls "list"] (rows.map rowViewLazy).toList

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
    | .replace _            => 1
    | .setText _            => 1
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
