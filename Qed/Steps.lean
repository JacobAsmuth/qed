/-
  Qed.Steps: the `steps` builder for effectful transitions.

  An effectful `update` returns `Model × Cmd Msg`, but most of its arms request no
  effect. Written as a plain `match`, every pure arm would have to wrap its model in
  the pair by hand. `steps` removes that tax: each arm is either a bare model (an
  effect-free arm) or a `(model, cmd)` pair, and the macro normalises arm by arm
  through `ToStep` (the same class that lets `ui` accept a pure or effectful update):

      def update (m : Model) : Msg → Model × Cmd Msg := steps
        | .edit s => { m with draft := s }
        | .submit => ({ m with pending := true }, Cmd.postJson url body .ok .err)

  The rewrite is syntax-directed and recursive: a tuple literal is left alone (it is
  already a step, and its `Cmd`'s message type elaborates against the expected pair),
  while `match`/`if`/`let` bodies recurse so a nested branch can mix pure and
  effectful results. Everything else is a leaf, wrapped in `ToStep.toStep`.

  The `steps` word is a non-reserved symbol, so apps can still use `steps` as an
  ordinary name (a model field, a variable); only `steps` followed by `| … => …`
  match alternatives parses as the builder.

  `import Lean` here is build-time only: macros run during elaboration and are
  erased from the app bundle (the transpiler tree-shakes compile-time code).
-/
import Qed.Runtime
import Lean

namespace Qed

namespace Steps
open Lean

/-- Rewrite one transition arm. A tuple literal `(model, cmd)` is already a step;
    `if`/`match`/`let`/parens recurse, so a nested branch can mix pure and effectful
    results; any other leaf normalises through `ToStep.toStep`, turning a bare model
    into `(model, Cmd.none)`. -/
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
      -- For a `match`, rewrite every alternative's right-hand side; for a `let`, the
      -- body. Both sit in the node's last argument, patched in place so binders,
      -- discriminants, and source positions survive untouched.
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
/-- `steps | pat => arm | …` builds an effectful transition `Msg → Model × Cmd Msg`
    from arms that are bare models (no effect) or `(model, cmd)` pairs. See the
    module docstring for the shape, and `Qed.ToStep` for the normalisation. -/
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
