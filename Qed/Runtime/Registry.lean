import Qed.Runtime.App
import Lean

namespace Qed.Internal

open Lean Elab Term Meta in
private def discoverAssets (value : Expr) : TermElabM (Expr × Expr) := do
  let env ← getEnv
  let mut pending := value.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut regs : Array Expr := #[]
  let mut styles : Array Expr := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      let reg := n.getPrefix ++ `regs
      let isMount := match n with
        | .str _ s => s == "_qed_mount" || s == "_qed_mountWithOpt"
        | _ => false
      if isMount && env.contains reg then
        regs := regs.push (Lean.mkConst reg)
        let compView := n.getPrefix ++ `view
        if env.contains compView then
          pending := compView :: pending
      else if let some (.defnInfo d) := env.find? n then
        if d.type.isConstOf ``Qed.Style then
          styles := styles.push (Lean.mkConst n)
        else
          pending := d.value.getUsedConstants.toList ++ pending
  let mut locals := Lean.mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``LocalDef)
  for reg in regs do
    locals ← mkAppM ``List.append #[locals, reg]
  return (← mkAppM ``LocalDef.dedupe #[locals], ← mkListLit (Lean.mkConst ``Qed.Style) styles.toList)

syntax (name := registrationsTerm) "qedInternalLocalRegistrations% " term:max : term
syntax (name := stylesTerm) "qedInternalStyles% " term:max : term

open Lean Elab Term in
@[term_elab registrationsTerm] def elabRegistrations : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return (← discoverAssets (← instantiateMVars value)).1

open Lean Elab Term in
@[term_elab stylesTerm] def elabStyles : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return (← discoverAssets (← instantiateMVars value)).2

end Qed.Internal
