/-
  Qed.Invariant — automatic state-machine invariant proofs (dream-API #3).

  A developer states a property of the model and which transition function should
  preserve it; the framework *generates and discharges* the preservation theorem
  for every message, with no hand-written proof. If the automation cannot close
  the goal, this fails to compile — we never emit `sorry`, because an honest "you
  must prove this" beats a fake guarantee.

      invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update

  expands to a machine-checked

      theorem counterSafe : ∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count

  This is pure surface syntax: it produces an ordinary Lean `theorem`, so the
  proof obligation is checked by the kernel like any other.

  Note: this file deliberately does *not* `import Lean`. `syntax`/`macro_rules`
  are core features, so the macro carries zero runtime footprint — apps that use
  it never link the Lean elaborator into their WASM binary.
-/
namespace Qed

/-- `invariant name : pred preserved_by upd` — see module docs. -/
syntax (name := invariantCmd)
  "invariant " ident " : " term " preserved_by " ident : command

macro_rules
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) ($upd m msg) := by
        intro m msg h
        cases msg <;>
          simp_all only [$upd:ident] <;>
          first
            | omega
            | (split <;> omega)
            | simp_all)

end Qed
