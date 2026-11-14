import Qed.Runtime.App
import Qed.Style
import Lean

namespace Qed

class InvTarget (α : Type) (Model : outParam Type) where
  proj : α → Model

instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩

@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) :
    InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) :
    InvTarget.proj p = p.1 := rfl

syntax (name := invariantCmd)
  "invariant " ident " : " term (" from " term)? " preserved_by " ident
    (" using " "[" term,* "]")? (" := " term)? : command

open Lean Elab Tactic

private def qedLooksGenerated (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s =>
       ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion",
        "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg",
        "toJson", "fromJson"].contains s
         || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "inst"
   | _ => false)

def qedIsHelper (env : Environment) (n : Name) : Bool :=
  let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i]! | none => n
  ![`Init, `Std, `Lean, `Qed].contains mod.getRoot
    && (match env.find? n with | some (.defnInfo d) => !d.type.isConstOf ``Qed.Style | _ => false)
    && !qedLooksGenerated n

private def qedBoundaryLemmas : Array Name :=
  #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
    ``Array.size_map, ``Array.size_append,
    ``List.length_cons, ``List.length_append, ``List.length_map]

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => do
  let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let fixedNames := #[``Qed.ToStep.toStep_model, ``Qed.ToStep.toStep_pair,
                      ``InvTarget.proj_id, ``InvTarget.proj_fst] ++ qedBoundaryLemmas
  let fixedL := (← fixedNames.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ (← extra.getElems.mapM toLemma)
  for _ in [0:12] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let goal ← instantiateMVars (← getMainTarget)
    let present ← (goal.getUsedConstants.filter (qedIsHelper env)).filterM
      (fun n => return (← getProjectionFnInfo? n).isNone)
    if present.isEmpty then return
    -- Splice a single combined array; comma-separated `$[…],*` splices fail when one is empty.
    let lemmas := (← present.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ fixedL
    let ok ← try
        evalTactic (← `(tactic| simp_all only [$[$lemmas],*]))
        pure true
      catch _ => pure false
    unless ok do return

syntax "qedDischargePreserved " "[" term,* "]" ident ident term:max (" from " term)? : tactic

elab_rules : tactic
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    let pred := match pred with | `(($p)) => p | p => p
    let predI : Ident := ⟨pred.raw⟩
    let unfoldPred ← if pred.raw.isIdent
      then `(tactic| try simp only [$predI:ident] at *)
      else `(tactic| skip)
    let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      `(Lean.Parser.Tactic.simpLemma| $t:term)
    let closerL := (← qedBoundaryLemmas.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩))
                     ++ (← usingL.mapM toLemma)
    let stepTac ← `(tactic|
      (intro m msg h;
       $unfoldPred:tactic;
       cases msg <;>
         (try simp_all only [$upd:ident, Qed.ToStep.toStep_model, Qed.ToStep.toStep_pair,
                             InvTarget.proj_id, InvTarget.proj_fst]) <;>
         qedUnfoldPresent [$[$usingL],*] <;>
         (try ((repeat' split) <;>
                (first | rfl | omega | assumption
                       | (simp_all [$[$closerL],*] <;> omega)
                       | (simp_all [$[$closerL],*] <;> done) | trivial)))))
    match init with
    | some initT =>
        let initI : Ident := ⟨initT.raw⟩
        let unfoldInit ← if initT.raw.isIdent
          then `(tactic| try simp only [$initI:ident] at *)
          else `(tactic| skip)
        evalTactic (← `(tactic|
          (refine And.intro ?init ?step;
           case init =>
             $unfoldPred:tactic
             $unfoldInit:tactic
             qedUnfoldPresent [$[$usingL],*]
             try ((repeat' split) <;>
                    (first | rfl | decide | omega | assumption
                           | (simp_all [$[$closerL],*] <;> omega)
                           | (simp_all [$[$closerL],*] <;> decide)
                           | (simp_all [$[$closerL],*] <;> done) | trivial));
           case step => $stepTac:tactic)))
    | none =>
        evalTactic stepTac
    let goals ← getUnsolvedGoals
    unless goals.isEmpty do
      let mut body : MessageData := m!""
      for g in goals do
        body := body ++ (← g.withContext do
          let tag ← g.getTag
          let ty ← instantiateMVars (← g.getType)
          let tgt := (← Meta.ppExpr ty).pretty.replace "✝" ""
          let env ← getEnv
          let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM
            (fun n => return (← getProjectionFnInfo? n).isNone)
          let involves := if present.isEmpty then m!"" else m!"\n    (still involves: {present.toList})"
          pure m!"\n  • case `{tag}` still needs:  {tgt}{involves}")
      throwErrorAt nm m!"invariant `{nm.getId}` isn't preserved by `{upd.getId}`, the automation \
        couldn't close every message.\n{body}\n\nIf the property is true here, the prover is likely \
        missing a fact: supply it with `… preserved_by {upd.getId} using [yourLemma]`, or prove the \
        case with `:= by`. If a branch can actually violate the property, fix that branch of \
        `{upd.getId}`, or weaken the property to what it guarantees."

macro_rules
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred) from $init)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred) from $init)
  | `(invariant $name:ident : $pred preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred))
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred))

open Lean Elab Command Term Meta Lean.PrettyPrinter in
def extractInvPred (id : Ident) : TermElabM (TSyntax `term) := do
  let cTy := (← getConstInfo (← realizeGlobalConstNoOverload id)).type
  let stepTy := if cTy.isAppOfArity ``And 2 then cTy.appArg! else cTy
  forallTelescope stepTy fun args _ => do
    if args.size < 2 then throwErrorAt id
      "`{id}` doesn't look like a `… preserved_by …` invariant, so its predicate can't \
       be inferred, write it explicitly (`<pred> for_each … preserved_by … using {id}`)."
    delab (← mkLambdaFVars #[args[0]!] (← inferType args[args.size - 1]!)).eta

end Qed
