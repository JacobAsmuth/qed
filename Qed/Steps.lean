import Qed.Runtime
import Lean

namespace Qed

namespace Steps
open Lean

partial def rewriteArm (stx : TSyntax `term) : MacroM (TSyntax `term) := do
  match stx with
  | `(($_:term, $_:term)) => pure stx
  | `(if $c then $t else $e) => do
      let t' ← rewriteArm t; let e' ← rewriteArm e
      `(if $c then $t' else $e')
  | `(if $h : $c then $t else $e) => do
      let t' ← rewriteArm t; let e' ← rewriteArm e
      `(if $h : $c then $t' else $e')
  | `(($e:term)) => do `(($(← rewriteArm e)))
  | _ =>
    let k := stx.raw.getKind
    if k == ``Lean.Parser.Term.match || k == ``Lean.Parser.Term.let then
      -- Match alts and let bodies both sit in `stx`'s last argument; rewrite in place to preserve binders/positions.
      let last := stx.raw.getArgs.size - 1
      let tail := stx.raw[last]
      let tail' : Syntax ←
        if k == ``Lean.Parser.Term.match then do
          let alts ← tail[0].getArgs.mapM fun alt => do
            let rhs ← rewriteArm ⟨alt[3]⟩
            pure (alt.setArg 3 rhs.raw)
          pure (tail.setArg 0 (mkNullNode alts))
        else do
          let body ← rewriteArm ⟨tail⟩
          pure body.raw
      return ⟨stx.raw.setArg last tail'⟩
    else
      `(Qed.ToStep.toStep $stx)

end Steps

open Lean Parser Term in
@[term_parser] def stepsParser := leading_parser:maxPrec
  nonReservedSymbol "steps" (includeIdent := true) >> matchAlts

open Lean in
@[macro stepsParser] def expandSteps : Macro := fun stx => do
  let alts := stx[1]
  let alts' ← alts[0].getArgs.mapM fun alt => do
    return alt.setArg 3 (← Steps.rewriteArm ⟨alt[3]⟩).raw
  let altsStx : TSyntax ``Lean.Parser.Term.matchAlts := ⟨alts.setArg 0 (mkNullNode alts')⟩
  `(fun msg => match msg with $altsStx:matchAlts)

end Qed
