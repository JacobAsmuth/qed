/-
  Qed.Invariant — automatic state-machine invariant proofs.

  You state a property of the model and which transition should preserve it; the
  framework *generates and discharges* the preservation theorem for every message,
  with no hand-written proof. If the automation cannot close a goal this fails to
  compile — we never emit `sorry`, because an honest "you must prove this" beats a
  fake guarantee.

      invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update

  expands to a machine-checked

      theorem counterSafe : ∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count

  This is the property that survives *every* reachable sequence of events — not the
  cases a test happened to cover. The claim itself is small and readable; the proof
  that the code obeys it is the machine's job.

  ## Pure or effectful — same syntax

  `preserved_by` works whether the transition is pure (`Model → Msg → Model`) or
  effectful (`Model → Msg → Model × Cmd Msg`). The next model is projected out of
  the result either way (`InvTarget.proj`), so `update` and `transition` both work:

      invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size)
        preserved_by transition

  ## When the automation can't close it

  The default discharger handles arithmetic, boolean and `Option` reasoning, and the
  `still`/`also` effect wrappers (`omega`, `simp`, case splits, `decide`). For an
  invariant that needs a lemma it can't guess — typically one quantified over your
  own collections — supply the proof after `:=`. The goal is the generated theorem
  `∀ m msg, pred m → pred (next m msg)`, so a proof opens with `intro m msg h`:

      invariant idsBelowNext : (fun m => ∀ r ∈ m.rows, r.id < m.nextId)
        preserved_by update := by
          intro m msg h
          cases msg <;> simp_all [update] <;> omega

  On failure the unsolved goal is labelled with the offending message constructor
  (Lean's `case` tag), so the error points at exactly the transition arm that breaks
  the property — the signal you (or an agent) act on: fix the update, or weaken the
  claim to what the code actually guarantees.

  Note: this file deliberately does *not* `import Lean`. `syntax`/`macro_rules` are
  core features, so the macro carries zero runtime footprint — apps that use it never
  link the Lean elaborator into their WASM binary. The only import is `Qed.Runtime`,
  for the `still`/`also` effect wrappers the discharger unfolds; it too is `Lean`-free.
-/
import Qed.Runtime

namespace Qed

/-- Projects the next *model* out of whatever a transition returns — the model itself
    for a pure `update`, or the first component for an effectful `transition` that
    returns `Model × Cmd Msg`. This is what lets one `invariant` syntax cover both
    shapes; it is erased from the statement by `simp` before any real proof work. -/
class InvTarget (α : Type) (Model : outParam Type) where
  proj : α → Model

instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩

@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) :
    InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) :
    InvTarget.proj p = p.1 := rfl

/-- `invariant name : pred preserved_by upd` — see the module docs. The optional
    `:= proof` supplies a proof for the cases the default automation can't close. -/
syntax (name := invariantCmd)
  "invariant " ident " : " term " preserved_by " ident (" := " term)? : command

macro_rules
  | `(invariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        intro m msg h
        cases msg <;>
          -- Unfold the transition / effect wrappers / model projection, split every
          -- `if`/`match` the arm introduces, then close each leaf. Each alternative is
          -- all-or-nothing (`<;> done`), and the whole finisher is wrapped in `try` so an
          -- arm the automation can't close is left as an *unsolved goal* labelled with its
          -- message constructor — which fails to compile, rather than slipping through.
          (try simp_all only [$upd:ident, Qed.still, Qed.also,
                              InvTarget.proj_id, InvTarget.proj_fst]) <;>
          (try ((repeat' split) <;>
                 (first | rfl | omega | assumption | (simp_all <;> done) | trivial))))

end Qed
