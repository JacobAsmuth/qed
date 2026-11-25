import Lean
import Qed.Diag
import Qed.Lang
import Qed.Proto

namespace Qed

structure SchemaFormInfo where mk :: (fullName formViewName : Lean.Name) (ctxBinders : Array Lean.Name) deriving Inhabited

initialize schemaFormRegistry : Lean.SimplePersistentEnvExtension SchemaFormInfo (Lean.NameMap SchemaFormInfo) ← Qed.Diag.mkNameMapExt (·.fullName)

structure UnitEnumInfo where
  fullName : Lean.Name
  variants : Array String
deriving Inhabited, Repr

initialize unitEnumRegistry : Lean.SimplePersistentEnvExtension UnitEnumInfo (Lean.NameMap UnitEnumInfo) ← Qed.Diag.mkNameMapExt (·.fullName)

def lookupUnitEnum? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (tyName : Lean.Name) : Option UnitEnumInfo :=
  Qed.Diag.lookupNameMapExt? unitEnumRegistry env currNs openDecls tyName

open Lean in
def lookupSchemaForm? (cName : Name) : CoreM (Option SchemaFormInfo) := do
  let (env, ns, openDecls) := (← getEnv, ← getCurrNamespace, ← getOpenDecls)
  if let some info := Qed.Diag.lookupNameMapExt? schemaFormRegistry env ns openDecls cName then return some info
  if cName.getString! == "Form" then
    let reg := schemaFormRegistry.getState env
    return (ResolveName.resolveGlobalName env {} ns openDecls (cName.getPrefix ++ `formView)).findSome? fun (fullView, _) => reg.find? (fullView.getPrefix ++ `Form)
  return none

def resolveSchemaCtxArgs (ref : Lean.Syntax) (tag : String) (ctxBinders : Array Lean.Name)
    (props : Array (Lean.Syntax × String × Lean.Term)) (checkUnknown := true) : Lean.MacroM (Array Lean.Term) := do
  let mut ctxVals : Std.HashMap Lean.Name Lean.Term := {}; let mut ctxArg? : Option Lean.Term := none
  for (attrRef, nm, v) in props do
    if nm == "ctx" && ctxBinders.size == 1 then ctxArg? := some v
    else if ctxBinders.contains (.mkSimple nm) then ctxVals := ctxVals.insert (.mkSimple nm) v
    else if checkUnknown then
      let valid := ["bind", "onSubmit", "key", "reset"] ++ ctxBinders.toList.map toString ++ (if ctxBinders.size == 1 then ["ctx"] else [])
      Lean.Macro.throwErrorAt attrRef s!"<{tag}>: unknown attribute `{nm}`{Qed.Diag.didYouMean nm valid} (valid: {String.intercalate ", " valid})"
  ctxBinders.mapM fun b => (ctxVals[b]? <|> ctxArg?).getDM <|
    Lean.Macro.throwErrorAt ref s!"<{tag}> requires context attribute `{b}=\{…}`{if ctxBinders.size == 1 then " (or `ctx={…}`)" else ""}"

/-! ## Shared JSON & Protobuf Struct Derivation -/

theorem structMaxLeMax {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

section CodecDerive
open Lean Elab Command Term

structure StructFieldSpec where mk :: (ident : Ident) (wireKey : String) (valTy : Term) (codecTerm? : Option Term := none) deriving Inhabited
structure StructJsonOpts where mk ::
  (ctxBinders : Array (Ident × Term) := #[]) (emitNamedDefs : Bool := true) (emitStringCodec : Bool := false)
  (emitNonNull emitLawful : Bool := true) (fixedDepthBound : Option Nat := none)
structure StructProtoOpts where mk :: (ctxBinders : Array (Ident × Term) := #[]) (emitBytesCodec : Bool := false) (emitLawful : Bool := true)

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

private def mkStructCodecCtx (t : Ident) (fields : Array StructFieldSpec) (ctxBinders : Array (Ident × Term)) :
    CommandElabM (Array Ident × Array Term × Ident × Term × (Term → CommandElabM Term) × Array Ident × Array Term) := do
  let (cbns, cbts, xId) := (ctxBinders.map (·.1), ctxBinders.map (·.2), mkIdent `x)
  let appTo (head : Term) : CommandElabM Term := Qed.Lang.mkAppTerms head (cbns.map (⟨·.raw⟩))
  let reads ← fields.mapM fun f => let fId := f.ident; if f.codecTerm?.isSome then `(($xId.$fId:ident).val) else `($xId.$fId:ident)
  return (cbns, cbts, xId, ← appTo ⟨t.raw⟩, appTo, fields.map (·.ident), reads)

def mkStructJsonCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructJsonOpts := {}) : CommandElabM (Array (TSyntax `command)) := do
  let (tId, jId) := (t.getId, mkIdent `j)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let jsonPairs ← (fields.zip reads).mapM fun (f, rd) => `(($(Syntax.mkStrLit f.wireKey), Qed.ToJson.toJson $rd))
  let jsonDecodes ← fields.mapM fun f => let kLit := Syntax.mkStrLit f.wireKey; match f.codecTerm? with
    | some inp => `(($inp).fromJsonField $jId $kLit) | none => `(Qed.FromJsonField.fromField (α := $(f.valTy)) $jId $kLit)
  let toBody ← `(Qed.Json.obj [$[$jsonPairs:term],*])
  let fromBody ← `(do
    $[let $fs:ident ← $jsonDecodes:term]*
    return { $[$fs:ident],* })
  if !opts.emitNamedDefs then return #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨fun $xId:ident => $toBody⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨fun $jId:ident => $fromBody⟩) ]
  let (toId, fromId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Json := $toBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($jId:ident : Qed.Json) : Except String $tApp := $fromBody) ]
  if opts.emitStringCodec then cmds := cmds ++ #[
    ← `(command| def $(mkIdent (tId ++ `decode)) $[($cbns:ident : $cbts:term)]* (s : String) (maxDepth : Nat := 64) : Except String $tApp := (Qed.Json.parse s maxDepth).bind ($fromApp)),
    ← `(command| def $(mkIdent (tId ++ `encode)) $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : String := Qed.Json.render ($toApp $xId)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨$toId⟩),
                    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨$fromId⟩)]
  if opts.emitNonNull then cmds := cmds.push (← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : Qed.NonNullJson $t := ⟨fun _ => nofun⟩))
  if !opts.emitLawful then return cmds
  let depthBoundExpr : Term ← match opts.fixedDepthBound with
    | some d => `(term| $(numLit d))
    | none   => `(term| 1 + $(← fields.foldrM (init := ← `(term| (0 : Nat))) fun f acc => `(term| Nat.max (Qed.LawfulJson.depthBound $(f.valTy)) $acc)))
  let depthProofExpr ← reads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc => `(term| Qed.structMaxLeMax (Qed.LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← fields.mapM fun f => let (kLit, fId) := (Syntax.mkStrLit f.wireKey, f.ident); match f.codecTerm? with
    | some inp => `(term| $(mkIdent `Qed.Codec.fromJsonField_of_field) $inp ($toId $xId) $kLit ($xId.$fId:ident) rfl)
    | none     => `(term| Qed.LawfulJson.fromField_of_field ($toId $xId) $kLit ($xId.$fId:ident) rfl)
  let thmId := mkIdent (tId ++ `_fromJson_toJson)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = .ok $xId := by unfold $fromId; simp only [$[$fieldEqs:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
          depthBound := $depthBoundExpr; depth_toJson := fun $xId:ident => Nat.add_le_add_left $depthProofExpr 1; fromJson_toJson := $thmId) ]

def mkProtoFieldTailsAndTags (reads : Array Term) (needTagsPf : Bool) : CommandElabM (Array Term × Term) := do
  let n := reads.size
  let mut tails := Array.replicate (n + 1) (← `(term| ([] : List (Nat × Qed.Proto.WireVal))))
  let mut tagsPosPf ← `(term| (fun (_ : Nat × Qed.Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  for i in (Array.range n).reverse do
    tails := tails.set! i (← `(term| Qed.ToProtoField.encodeProtoField $(numLit (i + 1)) $(reads[i]!) ++ $(tails[i + 1]!)))
    if needTagsPf then tagsPosPf ← `(term| Qed.Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $(numLit i)) $(reads[i]!) $tagsPosPf)
  return (tails, tagsPosPf)

def mkProtoFieldRoundtripTacs (fields : Array StructFieldSpec) (reads tails : Array Term) (xId? : Option Ident := none) :
    CommandElabM (Array Ident × Array (TSyntax `tactic)) := do
  let n := fields.size; let protoBody := tails[0]!
  let mut pIdents : Array Ident := #[]; let mut pHaveTacs : Array (TSyntax `tactic) := #[]
  for i in [0:n] do
    let kLit := numLit (i + 1); let f := fields[i]!
    let mut gtPf ← `(term| Qed.Proto.allTagsGt_nil $kLit)
    for j in (Array.range n).extract (i + 1) n |>.reverse do
      gtPf ← `(term| Qed.Proto.allTagsGt_encodeAppend (Nat.lt_of_sub_eq_succ (rfl : $(numLit (j + 1)) - $kLit = Nat.succ $(numLit (j - i - 1)))) $(reads[j]!) $gtPf)
    let mut rawEq ← `(term| Qed.Proto.decodeProtoField_hit $kLit $(reads[i]!) $(tails[i + 1]!) $gtPf)
    for j in (Array.range i).reverse do
      rawEq ← `(term| Eq.trans (Qed.Proto.decodeProtoField_skip (α := $(f.valTy)) (Nat.ne_of_lt (Nat.lt_of_sub_eq_succ (rfl : $kLit - $(numLit (j + 1)) = Nat.succ $(numLit (i - j - 1))))) $(reads[j]!) $(tails[j + 1]!)) $rawEq)
    let wrappedEq ← match f.codecTerm?, xId? with
      | some inp, some xId => let fId := f.ident; `(term| $(mkIdent `Qed.Codec.fromProtoField_of_field) $inp $kLit $protoBody ($xId.$fId:ident) $rawEq)
      | _, _ => pure rawEq
    let hId := mkIdent (Name.mkSimple s!"_hp{i}"); pIdents := pIdents.push hId; pHaveTacs := pHaveTacs.push (← `(tactic| have $hId:ident := $wrappedEq))
  return (pIdents, pHaveTacs)

def mkStructProtoCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructProtoOpts := {}) : CommandElabM (Array (TSyntax `command)) := do
  let (tId, fsId) := (t.getId, mkIdent `fs)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let (toId, fromId) := (mkIdent (tId ++ `toProtoFields), mkIdent (tId ++ `fromProtoFields))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let (tails, tagsPosPf) ← mkProtoFieldTailsAndTags reads (cbns.isEmpty && opts.emitLawful)
  let protoBody := tails[0]!
  let protoDecodes ← fields.zipIdx.mapM fun (f, i) => let kLit := numLit (i + 1); match f.codecTerm? with
    | some inp => `(($inp).fromProtoField $kLit $fsId) | none => `(Qed.FromProtoField.decodeProtoField (α := $(f.valTy)) $kLit $fsId)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : List (Nat × Qed.Proto.WireVal) := $protoBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $tApp := do
          $[let $fs:ident ← $protoDecodes:term]*
          return { $[$fs:ident],* }) ]
  if opts.emitBytesCodec then cmds := cmds ++ #[
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Bytes := Qed.Proto.encodeFieldsSpec ($toApp $xId)),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) $[($cbns:ident : $cbts:term)]* (b : Qed.Bytes) : Except String $tApp := (Qed.Proto.decodeFieldsSpec b).bind ($fromApp)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : Qed.ToProto $t := .ofFields $toId),
                    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : Qed.FromProto $t := .ofFields $fromId)]
  if !opts.emitLawful then return cmds
  let (pIdents, pHaveTacs) ← mkProtoFieldRoundtripTacs fields reads tails (some xId)
  let thmId := mkIdent (tId ++ `_fromProto_toProto)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = Except.ok $xId := by
          $[$pHaveTacs:tactic]*; unfold $fromId $toId; simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : Qed.LawfulProto $t := .ofFields $toId $fromId (fun $xId => $tagsPosPf) $thmId) ]

end CodecDerive
end Qed
