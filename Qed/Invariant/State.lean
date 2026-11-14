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

private def qedBoundaryLemmas : Array Name :=
  #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
    ``Array.size_map, ``Array.size_append,
    ``List.length_cons, ``List.length_append, ``List.length_map]

private def qedAppLemmas (env : Environment) : Array Name :=
  let base := #[``Qed.ToStep.toStep_model, ``Qed.ToStep.toStep_pair, ``Qed.ToStep.toStep_listPair,
                ``InvTarget.proj_id, ``InvTarget.proj_fst,
                ``Qed.mkApp_init, ``Qed.mkApp_update,
                ``Qed.mkRoutedApp_init, ``Qed.mkRoutedApp_update,
                ``Qed.App.addLocals_init, ``Qed.App.addLocals_update,
                ``Qed.App.withDehydrate_init, ``Qed.App.withDehydrate_update]
  let opt := #[`Qed.App.withQueries_init, `Qed.App.withQueries_update,
               `Qed.Query.wrap, `Qed.Resource.query].filter env.contains
  base ++ opt

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s     =>
      let p' := stripStepPrefix p
      if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => do
  let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let env0 ← getEnv
  let fixedNames := qedAppLemmas env0 ++ qedBoundaryLemmas
  let fixedL := (← fixedNames.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ (← extra.getElems.mapM toLemma)
  for _ in [0:12] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let goal ← instantiateMVars (← getMainTarget)
    let present ← (goal.getUsedConstants.filter (qedIsHelper env)).filterM
      (fun n => return (← getProjectionFnInfo? n).isNone)
    if present.isEmpty then
      let _ ← try evalTactic (← `(tactic| simp_all only [$[$fixedL],*])) catch _ => pure ()
      return
    -- Splice a single combined array; comma-separated `$[…],*` splices fail when one is empty.
    let lemmas := (← present.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ fixedL
    let ok ← try
        evalTactic (← `(tactic| simp_all only [$[$lemmas],*]))
        pure true
      catch _ => pure false
    unless ok do return

syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? : tactic

elab_rules : tactic
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    let pred := match pred with | `(($p)) => p | p => p
    let predI : Ident := ⟨pred.raw⟩
    let unfoldPred ← if pred.raw.isIdent
      then `(tactic| try simp only [$predI:ident] at *)
      else `(tactic| skip)
    let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      `(Lean.Parser.Tactic.simpLemma| $t:term)
    let env0 ← getEnv
    let appL ← (qedAppLemmas env0).mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)
    let updL ← if upd.raw.isIdent
      then pure (#[← toLemma ⟨upd.raw⟩] ++ appL)
      else match upd with
        | `((($a:ident).update)) => pure (#[← toLemma ⟨a.raw⟩] ++ appL)
        | `(($a:ident).update)   => pure (#[← toLemma ⟨a.raw⟩] ++ appL)
        | `(($fn:ident $_:term*)) => pure (#[← toLemma ⟨fn.raw⟩] ++ appL)
        | _ => pure appL
    let closerL := (← qedBoundaryLemmas.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩))
                     ++ (← usingL.mapM toLemma)
    let stepTac ← `(tactic|
      (intro m msg h;
       $unfoldPred:tactic;
       try dsimp only at *;
       cases msg <;>
         (try simp_all only [$[$updL],*]) <;>
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
        let initTac ← `(tactic|
          ($unfoldPred:tactic;
           try dsimp only at *;
           $unfoldInit:tactic;
           qedUnfoldPresent [$[$usingL],*];
           try ((repeat' split) <;>
                  (first | rfl | decide | omega | assumption
                         | (simp_all [$[$closerL],*] <;> omega)
                         | (simp_all [$[$closerL],*] <;> decide)
                         | (simp_all [$[$closerL],*] <;> done) | trivial))))
        let g0 ← getMainGoal
        let gs ← g0.apply (mkConst ``And.intro)
        match gs with
        | [gInit, gStep] =>
            gInit.setTag `init
            gStep.setTag `step
            setGoals [gInit]
            evalTactic initTac
            let remInit ← getUnsolvedGoals
            setGoals [gStep]
            evalTactic stepTac
            let remStep ← getUnsolvedGoals
            setGoals (remInit ++ remStep)
        | _ => throwError "internal error splitting invariant init/step goals"
    | none =>
        evalTactic stepTac
    let goals ← getUnsolvedGoals
    unless goals.isEmpty do
      let mut body : MessageData := m!""
      for g in goals do
        body := body ++ (← g.withContext do
          let tag := stripStepPrefix (← g.getTag)
          let ty ← instantiateMVars (← g.getType)
          let tgt := (← Meta.ppExpr ty).pretty.replace "✝" ""
          let env ← getEnv
          let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM
            (fun n => return (← getProjectionFnInfo? n).isNone)
          let involves := if present.isEmpty then m!"" else m!"\n    (still involves: {present.toList})"
          pure m!"\n  • case `{tag}` still needs:  {tgt}{involves}")
      let updName := if upd.raw.isIdent then toString upd.raw.getId
        else (upd.raw.reprint.getD (toString upd.raw)).trimmed
      throwErrorAt nm m!"invariant `{nm.getId}` isn't preserved by `{updName}`, the automation \
        couldn't close every message.\n{body}\n\nIf the property is true here, the prover is likely \
        missing a fact: supply it with `… preserved_by {updName} using [yourLemma]`, or prove the \
        case with `:= by`. If a branch can actually violate the property, fix that branch of \
        `{updName}`, or weaken the property to what it guarantees."

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

open Lean Parser in
def invBinder : Parser := leading_parser
  "(" >> ident >> optional (" : " >> termParser) >> ")"

open Lean Parser in
def invOptName : Parser := leading_parser
  notFollowedBy (identEq `on) "on" >> ident

open Lean Parser in
@[command_parser] def invariantBinderCmd : Parser := leading_parser
  "invariant " >> ident >> invBinder >> " : " >> sepBy1 termParser "," >>
  optional (" from " >> termParser) >> " preserved_by " >> ident >>
  optional (" using " >> "[" >> sepBy termParser "," >> "]") >>
  optional (" := " >> termParser)

open Lean Parser in
@[command_parser] def invariantOnCmd : Parser := leading_parser
  "invariant " >> optional (atomic invOptName) >> optional invBinder >>
  atomic (identEq `on) >> termParser maxPrec >> " : " >>
  sepBy1 termParser "," >>
  optional (" using " >> "[" >> sepBy termParser "," >> "]") >>
  optional (" := " >> termParser)

open Lean Elab Command in
def mkConjBody (clauses : Array Term) : CommandElabM Term := do
  let props ← clauses.mapM fun c => `(($c : Prop))
  match props.toList with
  | []      => `(True)
  | p :: ps => ps.foldlM (init := p) fun acc x => `($acc ∧ $x)

open Lean Elab Command in
private def mkBinderPred (bNode : Syntax) (clauses : Array Term) : CommandElabM Term := do
  let bId : Ident := ⟨bNode[1]⟩
  let conj ← mkConjBody clauses
  if bNode[2].getNumArgs == 2 then
    let bTy : Term := ⟨bNode[2][1]⟩
    `(fun ($bId : $bTy) => $conj)
  else
    `(fun $bId => $conj)

open Lean Elab Command in
private def freshInvIdent (ref : Syntax) (stem : String) : CommandElabM Ident := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let mut idx := 1
  let mut cand := Name.mkSimple s!"{stem}_inv_{idx}"
  while env.contains (ns ++ cand) do
    idx := idx + 1
    cand := Name.mkSimple s!"{stem}_inv_{idx}"
  return mkIdentFrom ref cand

open Lean Elab Command in
@[command_elab invariantBinderCmd] def elabInvariantBinderCmd : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let clauses : Array Term := stx[4].getSepArgs.map (⟨·⟩)
  let pred ← mkBinderPred stx[2] clauses
  let init? : Option Term := if stx[5].getNumArgs == 2 then some ⟨stx[5][1]⟩ else none
  let upd : Ident := ⟨stx[7]⟩
  let using? : Option (Array Term) :=
    if stx[8].getNumArgs == 4 then some (stx[8][2].getSepArgs.map (⟨·⟩)) else none
  let pf? : Option Term := if stx[9].getNumArgs == 2 then some ⟨stx[9][1]⟩ else none
  let cmd ← match init?, using?, pf? with
    | some i, some ls, some pf => `(invariant $name : $pred from $i preserved_by $upd using [$[$ls],*] := $pf)
    | some i, none,    some pf => `(invariant $name : $pred from $i preserved_by $upd := $pf)
    | some i, some ls, none    => `(invariant $name : $pred from $i preserved_by $upd using [$[$ls],*])
    | some i, none,    none    => `(invariant $name : $pred from $i preserved_by $upd)
    | none,   some ls, some pf => `(invariant $name : $pred preserved_by $upd using [$[$ls],*] := $pf)
    | none,   none,    some pf => `(invariant $name : $pred preserved_by $upd := $pf)
    | none,   some ls, none    => `(invariant $name : $pred preserved_by $upd using [$[$ls],*])
    | none,   none,    none    => `(invariant $name : $pred preserved_by $upd)
  elabCommand cmd

open Lean Elab Command in
@[command_elab invariantOnCmd] def elabInvariantOnCmd : CommandElab := fun stx => do
  let app : Term := ⟨stx[4]⟩
  let stem := if app.raw.isIdent then app.raw.getId.getString! else "app"
  let name ← match stx[1].find? (·.isIdent) with
    | some idStx => pure (⟨idStx⟩ : Ident)
    | none       => freshInvIdent stx stem
  let clauses : Array Term := stx[6].getSepArgs.map (⟨·⟩)
  let pred : Term ←
    if stx[2].getNumArgs == 1 then
      mkBinderPred stx[2][0] clauses
    else if clauses.size == 1 then
      pure clauses[0]!
    else
      throwErrorAt stx[6] "comma-separated invariant clauses need a model binder, e.g. `invariant (m) on app : ...`"
  let usingL : Array Term :=
    if stx[7].getNumArgs == 4 then stx[7][2].getSepArgs.map (⟨·⟩) else #[]
  let pf? : Option Term := if stx[8].getNumArgs == 2 then some ⟨stx[8][1]⟩ else none
  let prop ← `(($pred) (InvTarget.proj (($app).init)) ∧
               ∀ m msg, ($pred) m → ($pred) (InvTarget.proj (($app).update m msg)))
  match pf? with
  | some pf => elabCommand (← `(theorem $name:ident : $prop := $pf))
  | none    => elabCommand (← `(theorem $name:ident : $prop := by
      qedDischargePreserved [$[$usingL],*] (($app).update) $name ($pred) from (InvTarget.proj (($app).init))))

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
