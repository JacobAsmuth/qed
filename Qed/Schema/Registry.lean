import Lean
import Qed.Diag
import Qed.Proto

namespace Qed

structure SchemaFormInfo where
  fullName     : Lean.Name
  formViewName : Lean.Name
  ctxBinders   : Array Lean.Name
deriving Inhabited

initialize schemaFormRegistry :
    Lean.SimplePersistentEnvExtension SchemaFormInfo (Lean.NameMap SchemaFormInfo) ←
  Qed.Diag.mkNameMapExt (·.fullName)

open Lean in
def lookupSchemaForm? (cName : Name) : CoreM (Option SchemaFormInfo) := do
  let env ← getEnv
  let reg := schemaFormRegistry.getState env
  let ns ← getCurrNamespace
  if let some info := reg.find? (ns ++ cName) then return some info
  if let some info := reg.find? cName then return some info
  if cName.getString! == "Form" then
    for (fullView, _) in ResolveName.resolveGlobalName env {} ns (← getOpenDecls) (cName.getPrefix ++ `formView) do
      if let some info := reg.find? (fullView.getPrefix ++ `Form) then return some info
  return none

def resolveSchemaCtxArgs (ref : Lean.Syntax) (tag : String) (ctxBinders : Array Lean.Name)
    (props : Array (Lean.Syntax × String × Lean.Term)) (checkUnknown := true) : Lean.MacroM (Array Lean.Term) := do
  let mut ctxVals : Std.HashMap Lean.Name Lean.Term := {}
  let mut ctxArg? : Option Lean.Term := none
  for (attrRef, nm, v) in props do
    if nm == "ctx" && ctxBinders.size == 1 then ctxArg? := some v
    else if ctxBinders.contains (.mkSimple nm) then ctxVals := ctxVals.insert (.mkSimple nm) v
    else if checkUnknown then
      let valid := ["bind", "onSubmit", "key", "reset"] ++ ctxBinders.toList.map toString ++
        (if ctxBinders.size == 1 then ["ctx"] else [])
      let hint := Qed.Diag.didYouMean nm valid
      Lean.Macro.throwErrorAt attrRef s!"<{tag}>: unknown attribute `{nm}`{hint} (valid: {String.intercalate ", " valid})"
  ctxBinders.mapM fun b => do
    if let some v := ctxVals[b]? <|> ctxArg? then pure v
    else Lean.Macro.throwErrorAt ref s!"<{tag}> requires context attribute `{b}=\{…}`{if ctxBinders.size == 1 then " (or `ctx={…}`)" else ""}"

/-! ## Shared Protobuf Struct Derivation (`ToProto` / `FromProto` / `LawfulProto`) -/

section ProtoDerive
open Lean Elab Command Term

/-- Builds the tag-ordered `toProtoFields` body, positive-tag proof, and per-field
    `decodeProtoField` roundtrip `have` tactics for a struct's fields (`1..N`). -/
def mkProtoFieldSkeleton
    (reads : Array (TSyntax `term))
    (fieldValTy : Nat → CommandElabM (TSyntax `term))
    (wrapFieldEq : Nat → TSyntax `term → TSyntax `term → CommandElabM (TSyntax `term) := fun _ _ e => pure e) :
    CommandElabM (TSyntax `term × TSyntax `term × Array Ident × Array (TSyntax `tactic)) := do
  let nFields := reads.size
  let emptyList ← `(term| ([] : List (Nat × Qed.Proto.WireVal)))
  let mut tails : Array (TSyntax `term) := Array.replicate (nFields + 1) emptyList
  let mut tagsPosPf ← `(term| (fun (_ : Nat × Qed.Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  for revIdx in [0:nFields] do
    let i := nFields - 1 - revIdx
    let iLit := Syntax.mkNumLit (toString i)
    let kLit := Syntax.mkNumLit (toString (i + 1))
    tails := tails.set! i (← `(term| Qed.ToProtoField.encodeProtoField $kLit $(reads[i]!) ++ $(tails[i + 1]!)))
    tagsPosPf ← `(term| Qed.Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $iLit) $(reads[i]!) $tagsPosPf)
  let body := tails[0]!
  let mut pIdents : Array Ident := #[]
  let mut pHaveTacs : Array (TSyntax `tactic) := #[]
  for i in [0:nFields] do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let valTy ← fieldValTy i
    let mut gtPf ← `(term| Qed.Proto.allTagsGt_nil $kLit)
    for revAfter in [0 : nFields - 1 - i] do
      let j := nFields - 1 - revAfter
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (j - i - 1))
      gtPf ← `(term| Qed.Proto.allTagsGt_encodeAppend (Nat.lt_of_sub_eq_succ (rfl : $jLit - $kLit = Nat.succ $diffPredLit)) $(reads[j]!) $gtPf)
    let mut rawEq ← `(term| Qed.Proto.decodeProtoField_hit $kLit $(reads[i]!) $(tails[i + 1]!) $gtPf)
    for revBefore in [0:i] do
      let j := i - 1 - revBefore
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (i - j - 1))
      rawEq ← `(term| Eq.trans (Qed.Proto.decodeProtoField_skip (α := $valTy) (Nat.ne_of_lt (Nat.lt_of_sub_eq_succ (rfl : $kLit - $jLit = Nat.succ $diffPredLit))) $(reads[j]!) $(tails[j + 1]!)) $rawEq)
    let fullEq ← wrapFieldEq i body rawEq
    let hId := mkIdent (Name.mkSimple s!"_hp{i}")
    pIdents := pIdents.push hId
    pHaveTacs := pHaveTacs.push (← `(tactic| have $hId:ident := $fullEq))
  return (body, tagsPosPf, pIdents, pHaveTacs)

/-- Emits `ToProto`, `FromProto`, and (when `allLawfulProto`) `_fromProto_toProto` + `LawfulProto`
    instances for a struct `t` with field encoder/decoder `toId`/`fromId`. -/
def mkStructProtoInsts (t toId fromId xId : Ident)
    (tagsPosPf : TSyntax `term) (pIdents : Array Ident) (pHaveTacs : Array (TSyntax `tactic))
    (allLawfulProto : Bool := true) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let instBase : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : Qed.ToProto $t := .ofFields $toId),
    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : Qed.FromProto $t := .ofFields $fromId) ]
  if !allLawfulProto then return instBase
  let fromProtoThmId := mkIdent (tId ++ `_fromProto_toProto)
  let lawCmds : Array (TSyntax `command) := #[
    ← `(command| private theorem $fromProtoThmId ($xId:ident : $t) : $fromId ($toId $xId) = Except.ok $xId := by
          $[$pHaveTacs:tactic]*
          unfold $fromId $toId
          simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : Qed.LawfulProto $t :=
          .ofFields $toId $fromId (fun $xId => $tagsPosPf) $fromProtoThmId) ]
  return instBase ++ lawCmds

end ProtoDerive

end Qed
