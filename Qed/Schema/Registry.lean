import Lean
import Qed.Diag
import Qed.Lang
import Qed.Proto.Lawful

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

/-- Linear `Except.bind` reduction helper avoiding `O(2^N)` kernel `isDefEq` blowup in `simp`-generated roundtrip proofs. -/
theorem exceptBind_eq {ε α β : Type} {a : Except ε α} {v : α}
    {k : α → Except ε β} {r : Except ε β}
    (ha : a = .ok v) (hk : k v = r) : (a >>= k) = r := by
  subst ha; exact hk

theorem optionBind_pure_isSome_iff {α β : Type} (o : Option α) (f : α → β) :
    (o >>= fun a => pure (f a)).isSome = true ↔ o.isSome = true := by
  cases o <;> rfl

theorem optionBind_isSome_iff {α β : Type} (o : Option α) (f : α → Option β) {Q : Prop}
    (hf : ∀ a, (f a).isSome = true ↔ Q) : (o >>= f).isSome = true ↔ (o.isSome = true ∧ Q) := by
  cases o with
  | none => simp [bind, Option.bind]
  | some a => simpa [bind, Option.bind] using hf a

section CodecDerive
open Lean Elab Command Term

@[run_parser_attribute_hooks]
def schemaCtxParamP : Lean.Parser.Parser :=
  Lean.Parser.group (Lean.Parser.ident >> ":" >> Lean.Parser.withPosition (Lean.Parser.categoryParser `qedType 0))

def parseCtxBinders (ctxStx : Syntax) : CommandElabM (Array Ident × Array Term) := do
  let rawCtx := if ctxStx.getNumArgs == 3 then (ctxStx.getArg 1).getSepArgs else #[]
  let cbns : Array Ident := rawCtx.map (⟨·.getArg 0⟩)
  let cbts ← rawCtx.mapM fun cp => liftMacroM (return (← Qed.Lang.lowerQedType (cp.getArg 2) false).1)
  return (cbns, cbts)

def fmtWhereLabel (rawWheres : Array Syntax) (fallback : String := "constraint") : String :=
  String.intercalate ", " (rawWheres.toList.map fun w => let s := Qed.Lang.stxSnippet w; if s.isEmpty then fallback else s)

structure StructFieldSpec where mk :: (ident : Ident) (wireKey : String) (valTy : Term) (codecTerm? : Option Term := none) deriving Inhabited
structure StructJsonOpts where mk ::
  (ctxBinders : Array (Ident × Term) := #[]) (emitNamedDefs : Bool := true) (emitStringCodec : Bool := false)
  (emitNonNull emitLawful : Bool := true) (fixedDepthBound : Option Nat := none)
  (invCheck? : Option (Term × String) := none)
structure StructProtoOpts where mk ::
  (ctxBinders : Array (Ident × Term) := #[]) (emitBytesCodec : Bool := false) (emitLawful : Bool := true)
  (invCheck? : Option (Term × String) := none)

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

@[noinline] private def mkStructCodecCtx (t : Ident) (fields : Array StructFieldSpec) (ctxBinders : Array (Ident × Term)) :
    PureQuotM (Array Ident × Array Term × Ident × Term × (Term → PureQuotM Term) × Array Ident × Array Term) := do
  let (cbns, cbts, xId) := (ctxBinders.map (·.1), ctxBinders.map (·.2), mkIdent `x)
  let appTo (head : Term) : PureQuotM Term := Qed.Lang.mkAppTerms head (cbns.map (⟨·.raw⟩))
  let reads ← fields.mapM fun f => let fId := f.ident; if f.codecTerm?.isSome then `(($xId.$fId:ident).val) else `($xId.$fId:ident)
  return (cbns, cbts, xId, ← appTo ⟨t.raw⟩, appTo, fields.map (·.ident), reads)

@[noinline] private def mkFieldBindChain (fs : Array Ident) (decodes : Array Term) (retExpr : Term)
    (invCheck? : Option (Ident × Term × String) := none) : PureQuotM Term :=
  match invCheck? with
  | none =>
      if fs.isEmpty then `(Except.ok $retExpr)
      else `(do $[let $fs:ident ← $decodes:term]* return $retExpr)
  | some (hInvId, invTerm, errMsg) =>
      `(do $[let $fs:ident ← $decodes:term]*
           if $hInvId:ident : $invTerm then return $retExpr else Except.error $(Syntax.mkStrLit errMsg))

@[noinline] private def mkStructFromBody (fs : Array Ident) (decodes : Array Term) (invCheck? : Option (Term × String)) : PureQuotM Term := do
  match invCheck? with
  | none => mkFieldBindChain fs decodes (← `({ $[$fs:ident],* })) none
  | some (invTerm, errMsg) =>
      let hInvId := mkIdent `_hInv
      mkFieldBindChain fs decodes (← `({ $[$fs:ident],*, _inv := $hInvId:ident })) (some (hInvId, invTerm, errMsg))

@[noinline] private def mkStructLeafPf (xId : Ident) (invCheck? : Option (Term × String)) : PureQuotM Term :=
  match invCheck? with | none => `(term| rfl) | some _ => `(term| dite_eq_left ($xId:ident)._inv)

@[noinline] private def emitJsonCodecWrappers (t toId fromId : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp toApp fromApp : Term) (emitStringCodec emitNonNull : Bool) (nonNullPf : Term) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId; let xId := mkIdent `x
  let mut cmds : Array (TSyntax `command) := #[]
  if emitStringCodec then cmds := cmds ++ #[
    ← `(command| def $(mkIdent (tId ++ `decode)) $[($cbns:ident : $cbts:term)]* (s : String) (maxDepth : Nat := 64) : Except String $tApp := (Qed.Json.parse s maxDepth).bind ($fromApp)),
    ← `(command| def $(mkIdent (tId ++ `encode)) $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : String := Qed.Json.render ($toApp $xId)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨$toId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨$fromId⟩) ]
  if emitNonNull then cmds := cmds.push (← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : Qed.NonNullJson $t := ⟨$nonNullPf⟩))
  return cmds

@[noinline] def mkStructJsonCmdsPure (t : Ident) (fields : Array StructFieldSpec) (opts : StructJsonOpts := {}) : PureQuotM (Array (TSyntax `command)) := do
  let (tId, jId) := (t.getId, mkIdent `j)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let jsonPairs ← (fields.zip reads).mapM fun (f, rd) => `(($(Syntax.mkStrLit f.wireKey), Qed.ToJson.toJson $rd))
  let jsonDecodes ← fields.mapM fun f => let kLit := Syntax.mkStrLit f.wireKey; match f.codecTerm? with
    | some inp => `(($inp).fromJsonField $jId $kLit) | none => `(Qed.FromJsonField.fromField (α := $(f.valTy)) $jId $kLit)
  let toBody ← `(Qed.Json.obj [$[$jsonPairs:term],*])
  let fromBody ← mkStructFromBody fs jsonDecodes opts.invCheck?
  if !opts.emitNamedDefs then return #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨fun $xId:ident => $toBody⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨fun $jId:ident => $fromBody⟩) ]
  let (toId, fromId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Json := $toBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($jId:ident : Qed.Json) : Except String $tApp := $fromBody) ]
  cmds := cmds ++ (← emitJsonCodecWrappers t toId fromId cbns cbts tApp toApp fromApp opts.emitStringCodec opts.emitNonNull (← `(fun _ => nofun)))
  if !cbns.isEmpty || !opts.emitLawful then return cmds
  let depthBoundExpr : Term ← match opts.fixedDepthBound with
    | some d => `(term| $(numLit d))
    | none   => `(term| 1 + $(← fields.foldrM (init := ← `(term| (0 : Nat))) fun f acc => `(term| Nat.max (Qed.LawfulJson.depthBound $(f.valTy)) $acc)))
  let depthProofExpr ← reads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc => `(term| Qed.structMaxLeMax (Qed.LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← fields.mapM fun f => let (kLit, fId) := (Syntax.mkStrLit f.wireKey, f.ident); match f.codecTerm? with
    | some inp => `(term| $(mkIdent `Qed.Codec.fromJsonField_of_field) $inp ($toId $xId) $kLit ($xId.$fId:ident) rfl)
    | none     => `(term| Qed.LawfulJson.fromField_of_field ($toId $xId) $kLit ($xId.$fId:ident) rfl)
  let roundtripPf ← fieldEqs.foldrM (init := ← mkStructLeafPf xId opts.invCheck?) fun eqPf acc => `(term| Qed.exceptBind_eq $eqPf $acc)
  let thmId := mkIdent (tId ++ `_fromJson_toJson)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = .ok $xId := by unfold $fromId; exact $roundtripPf),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
          depthBound := $depthBoundExpr; depth_toJson := fun $xId:ident => Nat.add_le_add_left $depthProofExpr 1; fromJson_toJson := $thmId) ]

@[noinline] def mkStructJsonCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructJsonOpts := {}) : CommandElabM (Array (TSyntax `command)) :=
  runPureQuot (mkStructJsonCmdsPure t fields opts)

@[noinline] def mkProtoFieldTailsAndTagsPure (reads : Array Term) (needTagsPf : Bool) : PureQuotM (Array Term × Term) := do
  let n := reads.size
  let mut protoBody ← `(term| ([] : List (Nat × Qed.Proto.WireVal)))
  let mut tagsPosPf ← `(term| (fun (_ : Nat × Qed.Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  for i in (Array.range n).reverse do
    protoBody ← `(term| Qed.ToProtoField.encodeProtoField $(numLit (i + 1)) $(reads[i]!) ++ $protoBody)
    if needTagsPf then tagsPosPf ← `(term| Qed.Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $(numLit i)) $(reads[i]!) $tagsPosPf)
  return (#[protoBody], tagsPosPf)

@[noinline] def mkProtoFieldTailsAndTags (reads : Array Term) (needTagsPf : Bool) : CommandElabM (Array Term × Term) :=
  runPureQuot (mkProtoFieldTailsAndTagsPure reads needTagsPf)

@[noinline] private def mkProtoRoundtripStep (n i : Nat) (f : StructFieldSpec) (rd : Term)
    (tailIds gtIds : Array Ident) (xId? : Option Ident) : PureQuotM (Ident × Array (TSyntax `tactic)) := do
  let kLit := numLit (i + 1)
  let rawEq ←
    if i == 0 then `(term| Qed.Proto.decodeProtoField_hit 1 $rd $(tailIds[1]!) $(gtIds[1]!))
    else
      let heqId := mkIdent (Name.mkSimple s!"_heq{i}"); let hleId := mkIdent (Name.mkSimple s!"_hle{i}")
      `(term| Qed.Proto.decodeProtoField_mid $rd $heqId $hleId $(gtIds[i + 1]!))
  let wrappedEq ← match f.codecTerm?, xId? with
    | some inp, some xId => let fId := f.ident; `(term| $(mkIdent `Qed.Codec.fromProtoField_of_field) $inp $kLit $(tailIds[0]!) ($xId.$fId:ident) $rawEq)
    | _, _ => pure rawEq
  let hId := mkIdent (Name.mkSimple s!"_hp{i}")
  let mut tacs : Array (TSyntax `tactic) := #[← `(tactic| have $hId:ident := $wrappedEq)]
  if i + 1 < n then
    let ppNext := mkIdent (Name.mkSimple s!"_pp{i + 1}")
    let heqNext := mkIdent (Name.mkSimple s!"_heq{i + 1}")
    let hleNext := mkIdent (Name.mkSimple s!"_hle{i + 1}")
    if i == 0 then
      tacs := tacs ++ #[
        ← `(tactic| let $ppNext:ident := Qed.ToProtoField.encodeProtoField 1 $rd),
        ← `(tactic| have $heqNext:ident : $(tailIds[0]!) = $ppNext ++ $(tailIds[1]!) := rfl),
        ← `(tactic| have $hleNext:ident := Qed.Proto.allTagsLe_single 1 $rd) ]
    else
      let ppPrev := mkIdent (Name.mkSimple s!"_pp{i}")
      let heqPrev := mkIdent (Name.mkSimple s!"_heq{i}")
      let hlePrev := mkIdent (Name.mkSimple s!"_hle{i}")
      tacs := tacs ++ #[
        ← `(tactic| let $ppNext:ident := $ppPrev ++ Qed.ToProtoField.encodeProtoField $kLit $rd),
        ← `(tactic| have $heqNext:ident : $(tailIds[0]!) = $ppNext ++ $(tailIds[i + 1]!) := Qed.Proto.split_step $kLit $rd $heqPrev),
        ← `(tactic| have $hleNext:ident := Qed.Proto.allTagsLe_append_step $hlePrev $rd) ]
  return (hId, tacs)

@[noinline] def mkProtoFieldRoundtripTacsPure (fields : Array StructFieldSpec) (reads _tails : Array Term) (xId? : Option Ident := none) :
    PureQuotM (Array Ident × Array (TSyntax `tactic)) := do
  let n := fields.size
  if n == 0 then return (#[], #[])
  let tailIds : Array Ident := (Array.range (n + 1)).map fun i => mkIdent (Name.mkSimple s!"_pt{i}")
  let gtIds : Array Ident := (Array.range (n + 1)).map fun i => mkIdent (Name.mkSimple s!"_hgt{i}")
  let mut pHaveTacs : Array (TSyntax `tactic) := #[← `(tactic| let $(tailIds[n]!):ident : List (Nat × Qed.Proto.WireVal) := [])]
  for i in (Array.range n).reverse do
    pHaveTacs := pHaveTacs.push (← `(tactic| let $(tailIds[i]!):ident := Qed.ToProtoField.encodeProtoField $(numLit (i + 1)) $(reads[i]!) ++ $(tailIds[i + 1]!)))
  pHaveTacs := pHaveTacs.push (← `(tactic| have $(gtIds[n]!):ident : Qed.Proto.AllTagsGt $(numLit n) $(tailIds[n]!) := Qed.Proto.allTagsGt_nil $(numLit n)))
  for j in (Array.range n).extract 1 n |>.reverse do
    pHaveTacs := pHaveTacs.push (← `(tactic| have $(gtIds[j]!):ident : Qed.Proto.AllTagsGt $(numLit j) $(tailIds[j]!) := Qed.Proto.allTagsGt_step $(reads[j]!) $(gtIds[j + 1]!)))
  let mut pIdents : Array Ident := #[]
  for i in [0:n] do
    let (hId, stepTacs) ← mkProtoRoundtripStep n i fields[i]! reads[i]! tailIds gtIds xId?
    pIdents := pIdents.push hId; pHaveTacs := pHaveTacs ++ stepTacs
  return (pIdents, pHaveTacs)

@[noinline] def mkProtoFieldRoundtripTacs (fields : Array StructFieldSpec) (reads tails : Array Term) (xId? : Option Ident := none) :
    CommandElabM (Array Ident × Array (TSyntax `tactic)) :=
  runPureQuot (mkProtoFieldRoundtripTacsPure fields reads tails xId?)

@[noinline] def mkStructProtoCmdsPure (t : Ident) (fields : Array StructFieldSpec) (opts : StructProtoOpts := {}) : PureQuotM (Array (TSyntax `command)) := do
  let (tId, fsId) := (t.getId, mkIdent `fs)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let (toId, fromId) := (mkIdent (tId ++ `toProtoFields), mkIdent (tId ++ `fromProtoFields))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let (tails, tagsPosPf) ← mkProtoFieldTailsAndTagsPure reads (cbns.isEmpty && opts.emitLawful)
  let protoBody := tails[0]!
  let protoDecodes ← fields.zipIdx.mapM fun (f, i) => let kLit := numLit (i + 1); match f.codecTerm? with
    | some inp => `(($inp).fromProtoField $kLit $fsId) | none => `(Qed.FromProtoField.decodeProtoField (α := $(f.valTy)) $kLit $fsId)
  let protoFromBody ← mkStructFromBody fs protoDecodes opts.invCheck?
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : List (Nat × Qed.Proto.WireVal) := $protoBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $tApp := $protoFromBody) ]
  if opts.emitBytesCodec then cmds := cmds ++ #[
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Bytes := Qed.Proto.encodeFieldsSpec ($toApp $xId)),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) $[($cbns:ident : $cbts:term)]* (b : Qed.Bytes) : Except String $tApp := (Qed.Proto.decodeFieldsSpec b).bind ($fromApp)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : Qed.ToProto $t := .ofFields $toId),
                    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : Qed.FromProto $t := .ofFields $fromId)]
  if !opts.emitLawful then return cmds
  let (pIdents, pHaveTacs) ← mkProtoFieldRoundtripTacsPure fields reads tails (some xId)
  let roundtripPf ← pIdents.foldrM (init := ← mkStructLeafPf xId opts.invCheck?) fun hp acc => `(term| Qed.exceptBind_eq $hp $acc)
  let thmId := mkIdent (tId ++ `_fromProto_toProto)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = Except.ok $xId := by
          $[$pHaveTacs:tactic]*; unfold $fromId $toId; exact $roundtripPf),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : Qed.LawfulProto $t := .ofFields $toId $fromId (fun $xId => $tagsPosPf) $thmId) ]

@[noinline] def mkStructProtoCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructProtoOpts := {}) : CommandElabM (Array (TSyntax `command)) :=
  runPureQuot (mkStructProtoCmdsPure t fields opts)

structure TaggedVariantSpec where mk ::
  (ctorName : Name) (wireTag : String) (fields : Array (Ident × String × Term))
deriving Inhabited

structure TaggedJsonOpts where mk ::
  (tagKey : String := "t")
  (emitNamedDefs : Bool := true)
  (emitStringCodec : Bool := false)
  (emitNonNull emitLawful : Bool := false)
  (unknownTagStatic? : Option String := none)

@[noinline] private def mkLeMaxProof (idx total : Nat) : PureQuotM Term := do
  let mut pf ← `(term| Nat.le_max_left _ _)
  for _ in [0:idx] do pf ← `(term| Nat.le_trans $pf (Nat.le_max_right _ _))
  if total == 0 then `(term| Nat.le_refl _) else pure pf

@[noinline] private def mkTaggedVariantDepthAlt (tId : Name) (totalParams flatIdx : Nat) (v : TaggedVariantSpec) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr × Nat) := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pTerms : Array Term := v.fields.map fun (p, _, _) => ⟨p.raw⟩
  let mut idx := flatIdx; let mut paramPfs : Array Term := #[]
  for (pId, _, _) in v.fields do
    let leMax ← mkLeMaxProof idx totalParams
    paramPfs := paramPfs.push (← `(term| Nat.le_trans (Qed.LawfulJson.depth_toJson $pId:ident) $leMax))
    idx := idx + 1
  let bodyPf ← paramPfs.foldrM (init := ← `(term| Nat.zero_le _)) fun hp acc => `(term| Nat.max_le.2 ⟨$hp, $acc⟩)
  let fullPf ← `(term| Nat.add_le_add_left (Nat.max_le.2 ⟨Nat.zero_le _, $bodyPf⟩) 1)
  return (← `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => $fullPf), idx)

@[noinline] private def mkTaggedVariantRtCase (tId : Name) (toId fromId : Ident) (tagKeyLit : StrLit)
    (variants : Array TaggedVariantSpec) (vi : Nat) : PureQuotM (TSyntax ``Lean.Parser.Tactic.inductionAlt) := do
  let v := variants[vi]!
  let vName := v.ctorName; let vLit := Syntax.mkStrLit v.wireTag; let pIds := v.fields.map (·.1)
  let ctorVal ← Qed.Lang.mkAppTerms (mkIdent (tId ++ vName)) (pIds.map (⟨·.raw⟩))
  let hTagId := mkIdent `_htag
  let mut hIdents : Array Ident := #[hTagId]
  let mut hTacs : Array (TSyntax `tactic) := #[← `(tactic| have $hTagId:ident := Qed.LawfulJson.fromField_of_field ($toId $ctorVal) $tagKeyLit $vLit rfl)]
  for ((pId, wKey, _), pi) in v.fields.zipIdx do
    let hfId := mkIdent (Name.mkSimple s!"_hf{pi}"); hIdents := hIdents.push hfId
    hTacs := hTacs.push (← `(tactic| have $hfId:ident := Qed.LawfulJson.fromField_of_field ($toId $ctorVal) $(Syntax.mkStrLit wKey) $pId:ident rfl))
  for prevIdx in [0:vi] do
    let prevLit := Syntax.mkStrLit variants[prevIdx]!.wireTag
    let hneId := mkIdent (Name.mkSimple s!"_hne{prevIdx}"); hIdents := hIdents.push hneId
    hTacs := hTacs.push (← `(tactic| have $hneId:ident : ($vLit == $prevLit) = false := rfl))
  `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* =>
    $[$hTacs:tactic]*; unfold $fromId; simp only [$[$hIdents:term],*, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure])

@[noinline] private def mkTaggedUnionLawfulJsonCmdsPure (t toId fromId : Ident) (tagKeyLit : StrLit)
    (variants : Array TaggedVariantSpec) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId
  let allParamTys := variants.flatMap fun v => v.fields.map (·.2.2)
  let maxDepthExpr ← allParamTys.foldrM (init := ← `(term| (0 : Nat))) fun ty acc => `(term| Nat.max (Qed.LawfulJson.depthBound $ty) $acc)
  let mut flatIdx := 0; let mut depthAlts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  for v in variants do
    let (alt, nextIdx) ← mkTaggedVariantDepthAlt tId allParamTys.size flatIdx v
    depthAlts := depthAlts.push alt; flatIdx := nextIdx
  let rtCases ← (Array.range variants.size).mapM (mkTaggedVariantRtCase tId toId fromId tagKeyLit variants)
  let thmId := mkIdent (tId ++ `_fromJson_toJson)
  return #[
    ← `(command| private theorem $thmId (x : $t) : $fromId ($toId x) = Except.ok x := by cases x with $[$rtCases:inductionAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
          depthBound := 1 + $maxDepthExpr; depth_toJson $[$depthAlts:matchAlt]*; fromJson_toJson := $thmId)]

@[noinline] private def mkTaggedVariantToAlt (tId : Name) (tagKeyLit : StrLit) (v : TaggedVariantSpec) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pTerms : Array Term := v.fields.map fun (p, _, _) => ⟨p.raw⟩
  let pairs := #[← `(($tagKeyLit, Qed.ToJson.toJson $(Syntax.mkStrLit v.wireTag)))] ++
    (← v.fields.mapM fun (pId, wKey, _) => `(($(Syntax.mkStrLit wKey), Qed.ToJson.toJson $pId:ident)))
  `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => Qed.Json.obj [$[$pairs:term],*])

@[noinline] private def mkTaggedVariantFromArm (tId : Name) (jId tagId : Ident) (v : TaggedVariantSpec) (acc : Term) : PureQuotM Term := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pIds := v.fields.map (·.1)
  let decs ← v.fields.mapM fun (_, wKey, pTy) => `(Qed.FromJsonField.fromField (α := $pTy) $jId $(Syntax.mkStrLit wKey))
  let ctorApp ← Qed.Lang.mkAppTerms ctorId (pIds.map (⟨·.raw⟩))
  let okBr ← mkFieldBindChain pIds decs ctorApp
  `(if $tagId == $(Syntax.mkStrLit v.wireTag) then $okBr else $acc)

@[noinline] def mkTaggedUnionJsonCmdsPure (t : Ident) (variants : Array TaggedVariantSpec) (opts : TaggedJsonOpts := {}) :
    PureQuotM (Array (TSyntax `command)) := do
  let (tId, jId, tagId) := (t.getId, mkIdent `j, mkIdent `_tag)
  let tagKeyLit := Syntax.mkStrLit opts.tagKey
  let toAlts ← variants.mapM (mkTaggedVariantToAlt tId tagKeyLit)
  let unknownErr ← match opts.unknownTagStatic? with
    | some msg => `(Except.error $(Syntax.mkStrLit msg))
    | none => `(Except.error ($(Syntax.mkStrLit s!"unknown {tId} variant '") ++ $tagId ++ "'"))
  let fromChain ← variants.foldrM (init := unknownErr) (mkTaggedVariantFromArm tId jId tagId)
  if !opts.emitNamedDefs then return #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨fun _x => match _x with $[$toAlts:matchAlt]*⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨fun $jId:ident => do let $tagId:ident ← Qed.FromJsonField.fromField (α := String) $jId $tagKeyLit; $fromChain:term⟩) ]
  let (toId, fromId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId : $t → Qed.Json $[$toAlts:matchAlt]*),
    ← `(command| def $fromId ($jId:ident : Qed.Json) : Except String $t := do let $tagId:ident ← Qed.FromJsonField.fromField (α := String) $jId $tagKeyLit; $fromChain:term) ]
  cmds := cmds ++ (← emitJsonCodecWrappers t toId fromId #[] #[] ⟨t.raw⟩ ⟨toId.raw⟩ ⟨fromId.raw⟩ opts.emitStringCodec opts.emitNonNull (← `(fun x => by cases x <;> nofun)))
  if !opts.emitLawful then return cmds
  return cmds ++ (← mkTaggedUnionLawfulJsonCmdsPure t toId fromId tagKeyLit variants)

@[noinline] def mkTaggedUnionJsonCmds (t : Ident) (variants : Array TaggedVariantSpec) (opts : TaggedJsonOpts := {}) :
    CommandElabM (Array (TSyntax `command)) :=
  runPureQuot (mkTaggedUnionJsonCmdsPure t variants opts)

private def unitEnumInstSpecs : Array (Name × Name) := #[
  (`instToString, ``ToString), (`instStringEnum, ``Qed.StringEnum),
  (`instRouteParam, `Qed.RouteParam), (`instLawfulKey, `Qed.LawfulKey),
  (`instToJson, ``Qed.ToJson), (`instFromJson, ``Qed.FromJson),
  (`instNonNullJson, ``Qed.NonNullJson), (`instLawfulJson, ``Qed.LawfulJson),
  (`instToProto, ``Qed.ToProto), (`instFromProto, ``Qed.FromProto), (`instLawfulProto, ``Qed.LawfulProto)]

@[noinline] def mkUnitEnumCodecCmdsPure (t : Ident) (variants : Array (Name × String)) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId
  let toStrAlts ← variants.mapM fun (vNm, wire) =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ vNm)) => $(Syntax.mkStrLit wire))
  let ofStrAlts := (← variants.mapM fun (vNm, wire) =>
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit wire) => Except.ok $(mkIdent (tId ++ vNm)))).push
    (← `(Lean.Parser.Term.matchAltExpr| | other => Except.error ($(Syntax.mkStrLit s!"invalid {tId} '") ++ other ++ "'")))
  let toTagAlts ← variants.zipIdx.mapM fun ((vNm, _), i) =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ vNm)) => $(numLit i))
  let ofTagAlts := (← variants.zipIdx.mapM fun ((vNm, _), i) =>
    `(Lean.Parser.Term.matchAltExpr| | $(numLit i) => Except.ok $(mkIdent (tId ++ vNm)))).push
    (← `(Lean.Parser.Term.matchAltExpr| | n => Except.error ($(Syntax.mkStrLit s!"protobuf: invalid {tId} tag ") ++ toString n)))
  let (toStrId, ofStrId, codecId) := (mkIdent (tId ++ `toString), mkIdent (tId ++ `ofString), mkIdent (tId ++ `_codec))
  let instCmds ← unitEnumInstSpecs.mapM fun (leaf, cls) =>
    `(command| instance $(mkIdent (tId ++ leaf)):ident : $(mkCIdent cls) $t := ($codecId).$(mkIdent leaf):ident)
  return #[
    ← `(command| def $toStrId : $t → String $[$toStrAlts:matchAlt]*),
    ← `(command| def $ofStrId : String → Except String $t $[$ofStrAlts:matchAlt]*),
    ← `(command| def $codecId : $(mkCIdent `Qed.UnitEnumCodec) $t where
          typeName := $(Syntax.mkStrLit tId.toString)
          toStr := $toStrId
          ofStr := $ofStrId
          rtStr := fun x => by cases x <;> rfl
          toTag $[$toTagAlts:matchAlt]*
          ofTag $[$ofTagAlts:matchAlt]*
          rtTag := fun x => by cases x <;> rfl),
    ← `(command| @[simp] theorem $(mkIdent (tId ++ `ofString_toString)) (x : $t) : $ofStrId ($toStrId x) = Except.ok x := ($codecId).rtStr x),
    ← `(command| def $(mkIdent (tId ++ `toJson)) (x : $t) : Qed.Json := ($codecId).toJson x),
    ← `(command| def $(mkIdent (tId ++ `fromJson)) (j : Qed.Json) : Except String $t := ($codecId).fromJson j),
    ← `(command| def $(mkIdent (tId ++ `encode)) (x : $t) : String := ($codecId).encode x),
    ← `(command| def $(mkIdent (tId ++ `decode)) (s : String) (maxDepth : Nat := 64) : Except String $t := ($codecId).decode s maxDepth),
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) (x : $t) : Qed.Bytes := ($codecId).encodeBytes x),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) (b : Qed.Bytes) : Except String $t := ($codecId).decodeBytes b) ] ++ instCmds

@[noinline] def mkUnitEnumCodecCmds (t : Ident) (variants : Array (Name × String)) : CommandElabM (Array (TSyntax `command)) :=
  runPureQuot (mkUnitEnumCodecCmdsPure t variants)

end CodecDerive
end Qed
