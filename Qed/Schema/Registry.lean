import Lean
import Qed.Diag
import Qed.Lang
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
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  if let some info := Qed.Diag.lookupNameMapExt? schemaFormRegistry env ns openDecls cName then
    return some info
  if cName.getString! == "Form" then
    let reg := schemaFormRegistry.getState env
    for (fullView, _) in ResolveName.resolveGlobalName env {} ns openDecls (cName.getPrefix ++ `formView) do
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

theorem structMaxLeMax {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

structure StructFieldSpec where
  ident          : Ident
  wireKey        : String
  valTy          : Term
  isRefinedField : Bool := false
  codecTerm?     : Option Term := none
deriving Inhabited

structure StructJsonOpts where
  ctxBinders      : Array (Ident × Term) := #[]
  emitNamedDefs   : Bool := true
  emitStringCodec : Bool := false
  emitNonNull     : Bool := true
  emitLawful      : Bool := true
  fixedDepthBound : Option Nat := none

private def mkStructCodecCtx (t : Ident) (fields : Array StructFieldSpec)
    (ctxBinders : Array (Ident × Term)) :
    CommandElabM (Array Ident × Array Term × Ident × Term × (Term → CommandElabM Term) × Array Ident × Array Term) := do
  let cbns := ctxBinders.map (·.1)
  let cbts := ctxBinders.map (·.2)
  let xId : Ident := mkIdent `x
  let appTo (head : Term) : CommandElabM Term := Qed.Lang.mkAppTerms head (cbns.map (⟨·.raw⟩))
  let tApp ← appTo ⟨t.raw⟩
  let fs := fields.map (·.ident)
  let reads ← fields.mapM fun f => do
    let fId := f.ident
    if f.isRefinedField then `(($xId.$fId:ident).val) else `($xId.$fId:ident)
  return (cbns, cbts, xId, tApp, appTo, fs, reads)

/-- Emits JSON serialization/deserialization definitions and instances (`ToJson`, `FromJson`,
    and optionally `NonNullJson`, `LawfulJson`, `encode`, `decode`) for a struct. -/
def mkStructJsonCmds (t : Ident) (fields : Array StructFieldSpec)
    (opts : StructJsonOpts := {}) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let jId : Ident := mkIdent `j
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let jsonPairs ← (fields.zip reads).mapM fun (f, rd) =>
    `(($(Syntax.mkStrLit f.wireKey), Qed.ToJson.toJson $rd))
  let jsonDecodes ← fields.mapM fun f => do
    let kLit := Syntax.mkStrLit f.wireKey
    match f.isRefinedField, f.codecTerm? with
    | true, some inp => `(($inp).fromJsonField $jId $kLit)
    | _, _           => `(Qed.FromJsonField.fromField (α := $(f.valTy)) $jId $kLit)
  let toBody ← `(Qed.Json.obj [$[$jsonPairs:term],*])
  let fromBody ← `(do
    $[let $fs:ident ← $jsonDecodes:term]*
    return { $[$fs:ident],* })
  if !opts.emitNamedDefs then
    return #[
      ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨fun $xId:ident => $toBody⟩),
      ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨fun $jId:ident => $fromBody⟩) ]
  let toJsonId   := mkIdent (tId ++ `toJson)
  let fromJsonId := mkIdent (tId ++ `fromJson)
  let toJsonApp   ← appTo ⟨toJsonId.raw⟩
  let fromJsonApp ← appTo ⟨fromJsonId.raw⟩
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toJsonId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Json := $toBody),
    ← `(command| def $fromJsonId $[($cbns:ident : $cbts:term)]* ($jId:ident : Qed.Json) : Except String $tApp := $fromBody) ]
  if opts.emitStringCodec then
    let decodeId := mkIdent (tId ++ `decode)
    let encodeId := mkIdent (tId ++ `encode)
    cmds := cmds ++ #[
      ← `(command| def $decodeId $[($cbns:ident : $cbts:term)]* (s : String) (maxDepth : Nat := 64) :
            Except String $tApp := (Qed.Json.parse s maxDepth).bind ($fromJsonApp)),
      ← `(command| def $encodeId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : String :=
            Qed.Json.render ($toJsonApp $xId)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨$toJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨$fromJsonId⟩) ]
  if opts.emitNonNull then
    cmds := cmds.push (← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : Qed.NonNullJson $t := ⟨fun _ => nofun⟩))
  if !opts.emitLawful then return cmds
  let depthBoundExpr : Term ← match opts.fixedDepthBound with
    | some d => `(term| $(Syntax.mkNumLit (toString d)))
    | none => do
        let maxD ← fields.foldrM (init := ← `(term| (0 : Nat))) fun f acc =>
          `(term| Nat.max (Qed.LawfulJson.depthBound $(f.valTy)) $acc)
        `(term| 1 + $maxD)
  let depthProofExpr ← reads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc =>
    `(term| Qed.structMaxLeMax (Qed.LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← fields.mapM fun f => do
    let kLit := Syntax.mkStrLit f.wireKey
    let fId := f.ident
    match f.isRefinedField, f.codecTerm? with
    | true, some inp =>
        let lemmaId := mkIdent `Qed.Codec.fromJsonField_of_field
        `(term| $lemmaId $inp ($toJsonId $xId) $kLit ($xId.$fId:ident) rfl)
    | _, _ =>
        `(term| Qed.LawfulJson.fromField_of_field ($toJsonId $xId) $kLit ($xId.$fId:ident) rfl)
  let fromJsonThmId := mkIdent (tId ++ `_fromJson_toJson)
  return cmds ++ #[
    ← `(command|
      private theorem $fromJsonThmId ($xId:ident : $t) : $fromJsonId ($toJsonId $xId) = .ok $xId := by
        unfold $fromJsonId
        simp only [$[$fieldEqs:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command|
      instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
        depthBound := $depthBoundExpr
        depth_toJson := fun $xId:ident => Nat.add_le_add_left $depthProofExpr 1
        fromJson_toJson := $fromJsonThmId) ]

structure StructProtoOpts where
  ctxBinders     : Array (Ident × Term) := #[]
  emitBytesCodec : Bool := false
  emitLawful     : Bool := true

/-- Emits Protobuf field codecs (`toProtoFields`, `fromProtoFields`), optional `encodeBytes`/
    `decodeBytes`, and `ToProto`/`FromProto`/`LawfulProto` instances for a struct. -/
def mkStructProtoCmds (t : Ident) (fields : Array StructFieldSpec)
    (opts : StructProtoOpts := {}) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let fsId : Ident := mkIdent `fs
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let toId   := mkIdent (tId ++ `toProtoFields)
  let fromId := mkIdent (tId ++ `fromProtoFields)
  let toApp   ← appTo ⟨toId.raw⟩
  let fromApp ← appTo ⟨fromId.raw⟩
  let protoDecodes ← (List.range fields.size).toArray.mapM fun i => do
    let f := fields[i]!
    let kLit := Syntax.mkNumLit (toString (i + 1))
    match f.isRefinedField, f.codecTerm? with
    | true, some inp => `(($inp).fromProtoField $kLit $fsId)
    | _, _           => `(Qed.FromProtoField.decodeProtoField (α := $(f.valTy)) $kLit $fsId)
  let (protoBody, tagsPosPf, pIdents, pHaveTacs) ← mkProtoFieldSkeleton reads
    (fun i => pure fields[i]!.valTy)
    (fun i body rawEq => do
      let f := fields[i]!
      match f.isRefinedField, f.codecTerm? with
      | true, some inp =>
          let kLit := Syntax.mkNumLit (toString (i + 1))
          let fId := f.ident
          let lemmaId := mkIdent `Qed.Codec.fromProtoField_of_field
          `(term| $lemmaId $inp $kLit $body ($xId.$fId:ident) $rawEq)
      | _, _ => pure rawEq)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : List (Nat × Qed.Proto.WireVal) := $protoBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $tApp := do
          $[let $fs:ident ← $protoDecodes:term]*
          return { $[$fs:ident],* }) ]
  if opts.emitBytesCodec then
    let encodeBytesId := mkIdent (tId ++ `encodeBytes)
    let decodeBytesId := mkIdent (tId ++ `decodeBytes)
    cmds := cmds ++ #[
      ← `(command| def $encodeBytesId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Bytes :=
            Qed.Proto.encodeFieldsSpec ($toApp $xId)),
      ← `(command| def $decodeBytesId $[($cbns:ident : $cbts:term)]* (b : Qed.Bytes) : Except String $tApp :=
            (Qed.Proto.decodeFieldsSpec b).bind ($fromApp)) ]
  if !cbns.isEmpty then return cmds
  let instCmds ← mkStructProtoInsts t toId fromId xId tagsPosPf pIdents pHaveTacs opts.emitLawful
  return cmds ++ instCmds

end ProtoDerive

end Qed
