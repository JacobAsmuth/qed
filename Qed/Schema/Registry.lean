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
deriving Inhabited

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
  let rec collect : Nat → Std.HashMap Lean.Name Lean.Term → Option Lean.Term → Lean.MacroM (Std.HashMap Lean.Name Lean.Term × Option Lean.Term)
    | 0, m, ca => pure (m, ca)
    | r + 1, m, ca => do
        let i := props.size - (r + 1)
        if h : i < props.size then
          let (attrRef, nm, v) := props[i]
          if nm == "ctx" && ctxBinders.size == 1 then collect r m (some v)
          else if ctxBinders.contains (.mkSimple nm) then collect r (m.insert (.mkSimple nm) v) ca
          else if checkUnknown then
            let valid := ["bind", "onSubmit", "key", "reset"] ++ ctxBinders.toList.map toString ++ (if ctxBinders.size == 1 then ["ctx"] else [])
            Lean.Macro.throwErrorAt attrRef s!"<{tag}>: unknown attribute `{nm}`{Qed.Diag.didYouMean nm valid} (valid: {String.intercalate ", " valid})"
          else collect r m ca
        else pure (m, ca)
  let (ctxVals, ctxArg?) ← collect props.size {} none
  let rec resolve : Nat → Array Lean.Term → Lean.MacroM (Array Lean.Term)
    | 0, acc => pure acc
    | r + 1, acc => do
        let i := ctxBinders.size - (r + 1)
        if h : i < ctxBinders.size then
          let b := ctxBinders[i]
          match ctxVals[b]? <|> ctxArg? with
          | some v => resolve r (acc.push v)
          | none => Lean.Macro.throwErrorAt ref s!"<{tag}> requires context attribute `{b}=\{…}`{if ctxBinders.size == 1 then " (or `ctx={…}`)" else ""}"
        else pure acc
  resolve ctxBinders.size (Array.mkEmpty ctxBinders.size)

/-! ## Shared JSON & Protobuf Struct Derivation -/

theorem structMaxLeMax {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

/-- Linear `Except.bind` reduction helper avoiding `O(2^N)` kernel `isDefEq` blowup in `simp`-generated roundtrip proofs. -/
theorem exceptBind_eq {ε α β : Type} {a : Except ε α} {v : α}
    {k : α → Except ε β} {r : Except ε β} (ha : a = .ok v) (hk : k v = r) : (a >>= k) = r := by
  subst ha; exact hk

theorem optionBind_pure_isSome_iff {α β : Type} (o : Option α) (f : α → β) :
    (o >>= fun a => pure (f a)).isSome = true ↔ o.isSome = true := by cases o <;> rfl

theorem optionBind_isSome_iff {α β : Type} (o : Option α) (f : α → Option β) {Q : Prop}
    (hf : ∀ a, (f a).isSome = true ↔ Q) : (o >>= f).isSome = true ↔ (o.isSome = true ∧ Q) := by
  cases o with | none => simp [bind, Option.bind] | some a => simpa [bind, Option.bind] using hf a

section CodecDerive
open Lean Elab Command Term

@[run_parser_attribute_hooks]
def schemaCtxParamP : Lean.Parser.Parser :=
  Qed.Lang.opaqueP (Lean.Parser.group (Lean.Parser.ident >> ":" >> Lean.Parser.withPosition (Lean.Parser.categoryParser `qedType 0)))

def parseCtxBinders (ctxStx : Syntax) : CommandElabM (Array Ident × Array Term) := do
  let rawCtx := if ctxStx.getNumArgs == 3 then (ctxStx.getArg 1).getSepArgs else #[]
  let qctx ← Qed.Lang.getPureQuotCtxCmd
  let cbts ← Lang.mapCmd rawCtx fun cp => match Lang.lowerQedTypePure qctx (cp.getArg 2) false with
    | .ok (t, _) => pure t | .error (ref, msg) => throwErrorAt ref msg
  return (rawCtx.map (⟨·.getArg 0⟩), cbts)

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
private def mkIdxId (pfx : String) (i : Nat) : Ident := mkIdent (Name.mkSimple s!"{pfx}{i}")

@[noinline] private def mkInstCmd (tId leaf cls : Name) (t : Ident) (rhs : Term) : PureQuotM (TSyntax `command) :=
  `(command| instance $(mkIdent (tId ++ leaf)):ident : $(mkCIdent cls) $t := $rhs)
@[noinline] private def mkMatchAlt1 (pat rhs : Term) : PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr) :=
  `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs)
@[noinline] private def mkHaveTac (id : Ident) (ty? : Option Term) (pf : Term) : PureQuotM (TSyntax `tactic) :=
  match ty? with | some ty => `(tactic| have $id:ident : $ty := $pf) | none => `(tactic| have $id:ident := $pf)
@[noinline] private def mkLetTac (id : Ident) (ty? : Option Term) (rhs : Term) : PureQuotM (TSyntax `tactic) :=
  match ty? with | some ty => `(tactic| let $id:ident : $ty := $rhs) | none => `(tactic| let $id:ident := $rhs)
@[noinline] private def mkMatchDef (id : Ident) (inTy outTy : Term) (alts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) : PureQuotM (TSyntax `command) :=
  `(command| def $id : $inTy → $outTy $[$alts:matchAlt]*)

@[noinline] private def mkStructCodecCtx (t : Ident) (fields : Array StructFieldSpec) (ctxBinders : Array (Ident × Term)) :
    PureQuotM (Array Ident × Array Term × Ident × Term × (Term → PureQuotM Term) × Array Ident × Array Term) := do
  let (cbns, cbts, xId) := (ctxBinders.map (·.1), ctxBinders.map (·.2), mkIdent `x)
  let appTo (head : Term) : PureQuotM Term := Qed.Lang.mkAppTermsPure head (cbns.map (⟨·.raw⟩))
  let reads ← Lang.mapPQ fields fun f => let fId := f.ident; if f.codecTerm?.isSome then `(($xId.$fId:ident).val) else `($xId.$fId:ident)
  return (cbns, cbts, xId, ← appTo ⟨t.raw⟩, appTo, fields.map (·.ident), reads)

@[noinline] private def mkFieldBindChain (fs : Array Ident) (decodes : Array Term) (retExpr : Term)
    (invCheck? : Option (Ident × Term × String) := none) : PureQuotM Term :=
  match invCheck? with
  | none => if fs.isEmpty then `(Except.ok $retExpr) else `(do $[let $fs:ident ← $decodes:term]* return $retExpr)
  | some (hInvId, invTerm, errMsg) =>
      `(do $[let $fs:ident ← $decodes:term]* if $hInvId:ident : $invTerm then return $retExpr else Except.error $(Syntax.mkStrLit errMsg))

@[noinline] private def mkStructFromBody (fs : Array Ident) (decodes : Array Term) (invCheck? : Option (Term × String)) : PureQuotM Term := do
  match invCheck? with
  | none => mkFieldBindChain fs decodes (← `({ $[$fs:ident],* })) none
  | some (invTerm, errMsg) => let hInvId := mkIdent `_hInv; mkFieldBindChain fs decodes (← `({ $[$fs:ident],*, _inv := $hInvId:ident })) (some (hInvId, invTerm, errMsg))

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
  cmds := cmds ++ #[← mkInstCmd tId `instToJson ``Qed.ToJson t (← `(⟨$toId⟩)), ← mkInstCmd tId `instFromJson ``Qed.FromJson t (← `(⟨$fromId⟩))]
  if emitNonNull then cmds := cmds.push (← mkInstCmd tId `instNonNullJson ``Qed.NonNullJson t (← `(⟨$nonNullPf⟩)))
  return cmds

@[noinline] def mkStructJsonCmdsPure (t : Ident) (fields : Array StructFieldSpec) (opts : StructJsonOpts := {}) : PureQuotM (Array (TSyntax `command)) := do
  let (tId, jId) := (t.getId, mkIdent `j)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let jsonPairs ← Lang.mapPQ (fields.zip reads) fun (f, rd) => `(($(Syntax.mkStrLit f.wireKey), Qed.ToJson.toJson $rd))
  let jsonDecodes ← Lang.mapPQ fields fun f => let kLit := Syntax.mkStrLit f.wireKey; match f.codecTerm? with
    | some inp => `(($inp).fromJsonField $jId $kLit) | none => `(Qed.FromJsonField.fromField (α := $(f.valTy)) $jId $kLit)
  let toBody ← `(Qed.Json.obj [$[$jsonPairs:term],*]); let fromBody ← mkStructFromBody fs jsonDecodes opts.invCheck?
  if !opts.emitNamedDefs then return #[
    ← mkInstCmd tId `instToJson ``Qed.ToJson t (← `(⟨fun $xId:ident => $toBody⟩)),
    ← mkInstCmd tId `instFromJson ``Qed.FromJson t (← `(⟨fun $jId:ident => $fromBody⟩)) ]
  let (toId, fromId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Json := $toBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($jId:ident : Qed.Json) : Except String $tApp := $fromBody) ]
  cmds := cmds ++ (← emitJsonCodecWrappers t toId fromId cbns cbts tApp toApp fromApp opts.emitStringCodec opts.emitNonNull (← `(fun _ => nofun)))
  if !cbns.isEmpty || !opts.emitLawful then return cmds
  let depthBoundExpr : Term ← match opts.fixedDepthBound with
    | some d => `(term| $(numLit d))
    | none   => `(term| 1 + $(← Lang.foldrPQ fields (← `(term| (0 : Nat))) fun f acc => `(term| Nat.max (Qed.LawfulJson.depthBound $(f.valTy)) $acc)))
  let depthProofExpr ← Lang.foldrPQ reads (← `(term| Nat.le_refl 0)) fun rd acc => `(term| Qed.structMaxLeMax (Qed.LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← Lang.mapPQ fields fun f => let (kLit, fId) := (Syntax.mkStrLit f.wireKey, f.ident); match f.codecTerm? with
    | some inp => `(term| $(mkIdent `Qed.Codec.fromJsonField_of_field) $inp ($toId $xId) $kLit ($xId.$fId:ident) rfl)
    | none     => `(term| Qed.LawfulJson.fromField_of_field ($toId $xId) $kLit ($xId.$fId:ident) rfl)
  let roundtripPf ← Lang.foldrPQ fieldEqs (← mkStructLeafPf xId opts.invCheck?) fun eqPf acc => `(term| Qed.exceptBind_eq $eqPf $acc)
  let thmId := mkIdent (tId ++ `_fromJson_toJson)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = .ok $xId := by unfold $fromId; exact $roundtripPf),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
          depthBound := $depthBoundExpr; depth_toJson := fun $xId:ident => Nat.add_le_add_left $depthProofExpr 1; fromJson_toJson := $thmId) ]

@[noinline] def mkStructJsonCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructJsonOpts := {}) : CommandElabM (Array (TSyntax `command)) :=
  Lang.runPQ (mkStructJsonCmdsPure t fields opts)

@[noinline] def mkProtoFieldTailsAndTagsPure (reads : Array Term) (needTagsPf : Bool) : PureQuotM (Array Term × Term) := do
  let initBody ← `(term| ([] : List (Nat × Qed.Proto.WireVal)))
  let initTags ← `(term| (fun (_ : Nat × Qed.Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  let (protoBody, tagsPosPf) ← Lang.foldrPQ reads.zipIdx (initBody, initTags) fun (rd, i) (body, tags) => do
    let body' ← `(term| Qed.ToProtoField.encodeProtoField $(numLit (i + 1)) $rd ++ $body)
    let tags' ← if needTagsPf then `(term| Qed.Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $(numLit i)) $rd $tags) else pure tags
    return (body', tags')
  return (#[protoBody], tagsPosPf)

@[noinline] private def mkProtoRoundtripStep (n i : Nat) (f : StructFieldSpec) (rd : Term)
    (tailIds gtIds : Array Ident) (xId? : Option Ident) : PureQuotM (Ident × Array (TSyntax `tactic)) := do
  let kLit := numLit (i + 1)
  let rawEq ← if i == 0 then `(term| Qed.Proto.decodeProtoField_hit 1 $rd $(tailIds[1]!) $(gtIds[1]!))
    else `(term| Qed.Proto.decodeProtoField_mid $rd $(mkIdxId "_heq" i) $(mkIdxId "_hle" i) $(gtIds[i + 1]!))
  let wrappedEq ← match f.codecTerm?, xId? with
    | some inp, some xId => let fId := f.ident; `(term| $(mkIdent `Qed.Codec.fromProtoField_of_field) $inp $kLit $(tailIds[0]!) ($xId.$fId:ident) $rawEq)
    | _, _ => pure rawEq
  let hId := mkIdxId "_hp" i; let hTac ← mkHaveTac hId none wrappedEq
  if i + 1 >= n then return (hId, #[hTac])
  let (ppNext, heqNext, hleNext) := (mkIdxId "_pp" (i + 1), mkIdxId "_heq" (i + 1), mkIdxId "_hle" (i + 1))
  let (ppRhs, eqPf, lePf) ← if i == 0 then
      pure (← `(term| Qed.ToProtoField.encodeProtoField 1 $rd), ← `(term| rfl), ← `(term| Qed.Proto.allTagsLe_single 1 $rd))
    else
      pure (← `(term| $(mkIdxId "_pp" i) ++ Qed.ToProtoField.encodeProtoField $kLit $rd),
            ← `(term| Qed.Proto.split_step $kLit $rd $(mkIdxId "_heq" i)),
            ← `(term| Qed.Proto.allTagsLe_append_step $(mkIdxId "_hle" i) $rd))
  return (hId, #[hTac, ← mkLetTac ppNext none ppRhs,
    ← mkHaveTac heqNext (some (← `(term| $(tailIds[0]!) = $ppNext ++ $(tailIds[i + 1]!)))) eqPf,
    ← mkHaveTac hleNext none lePf])

@[noinline] def mkProtoFieldRoundtripTacsPure (fields : Array StructFieldSpec) (reads _tails : Array Term) (xId? : Option Ident := none) :
    PureQuotM (Array Ident × Array (TSyntax `tactic)) := do
  let n := fields.size
  if n == 0 then return (#[], #[])
  let tailIds := (Array.range (n + 1)).map (mkIdxId "_pt"); let gtIds := (Array.range (n + 1)).map (mkIdxId "_hgt")
  let t0 := #[← mkLetTac tailIds[n]! (some (← `(term| List (Nat × Qed.Proto.WireVal)))) (← `(term| []))]
  let t1 ← Lang.foldrPQ reads.zipIdx t0 fun (rd, i) acc => do
    return acc.push (← mkLetTac tailIds[i]! none (← `(term| Qed.ToProtoField.encodeProtoField $(numLit (i + 1)) $rd ++ $(tailIds[i + 1]!))))
  let t2 := t1.push (← mkHaveTac gtIds[n]! (some (← `(term| Qed.Proto.AllTagsGt $(numLit n) $(tailIds[n]!)))) (← `(term| Qed.Proto.allTagsGt_nil $(numLit n))))
  let t3 ← Lang.foldrPQ ((Array.range n).extract 1 n) t2 fun j acc => do
    return acc.push (← mkHaveTac gtIds[j]! (some (← `(term| Qed.Proto.AllTagsGt $(numLit j) $(tailIds[j]!)))) (← `(term| Qed.Proto.allTagsGt_step $(reads[j]!) $(gtIds[j + 1]!))))
  Lang.foldlPQ (Array.range n) (#[], t3) fun (pIdents, tacs) i => do
    let (hId, stepTacs) ← mkProtoRoundtripStep n i fields[i]! reads[i]! tailIds gtIds xId?
    return (pIdents.push hId, tacs ++ stepTacs)

@[noinline] def mkStructProtoCmdsPure (t : Ident) (fields : Array StructFieldSpec) (opts : StructProtoOpts := {}) : PureQuotM (Array (TSyntax `command)) := do
  let (tId, fsId) := (t.getId, mkIdent `fs)
  let (cbns, cbts, xId, tApp, appTo, fs, reads) ← mkStructCodecCtx t fields opts.ctxBinders
  let (toId, fromId) := (mkIdent (tId ++ `toProtoFields), mkIdent (tId ++ `fromProtoFields))
  let (toApp, fromApp) := (← appTo ⟨toId.raw⟩, ← appTo ⟨fromId.raw⟩)
  let (tails, tagsPosPf) ← mkProtoFieldTailsAndTagsPure reads (cbns.isEmpty && opts.emitLawful)
  let protoBody := tails[0]!
  let protoDecodes ← Lang.mapIdxPQ fields fun f i => let kLit := numLit (i + 1); match f.codecTerm? with
    | some inp => `(($inp).fromProtoField $kLit $fsId) | none => `(Qed.FromProtoField.decodeProtoField (α := $(f.valTy)) $kLit $fsId)
  let protoFromBody ← mkStructFromBody fs protoDecodes opts.invCheck?
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : List (Nat × Qed.Proto.WireVal) := $protoBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $tApp := $protoFromBody) ]
  if opts.emitBytesCodec then cmds := cmds ++ #[
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) $[($cbns:ident : $cbts:term)]* ($xId:ident : $tApp) : Qed.Bytes := Qed.Proto.encodeFieldsSpec ($toApp $xId)),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) $[($cbns:ident : $cbts:term)]* (b : Qed.Bytes) : Except String $tApp := (Qed.Proto.decodeFieldsSpec b).bind ($fromApp)) ]
  if !cbns.isEmpty then return cmds
  cmds := cmds ++ #[← mkInstCmd tId `instToProto ``Qed.ToProto t (← `(.ofFields $toId)), ← mkInstCmd tId `instFromProto ``Qed.FromProto t (← `(.ofFields $fromId))]
  if !opts.emitLawful then return cmds
  let (pIdents, pHaveTacs) ← mkProtoFieldRoundtripTacsPure fields reads tails (some xId)
  let roundtripPf ← Lang.foldrPQ pIdents (← mkStructLeafPf xId opts.invCheck?) fun hp acc => `(term| Qed.exceptBind_eq $hp $acc)
  let thmId := mkIdent (tId ++ `_fromProto_toProto)
  return cmds ++ #[
    ← `(command| private theorem $thmId ($xId:ident : $t) : $fromId ($toId $xId) = Except.ok $xId := by $[$pHaveTacs:tactic]*; unfold $fromId $toId; exact $roundtripPf),
    ← mkInstCmd tId `instLawfulProto ``Qed.LawfulProto t (← `(.ofFields $toId $fromId (fun $xId => $tagsPosPf) $thmId)) ]

@[noinline] def mkStructProtoCmds (t : Ident) (fields : Array StructFieldSpec) (opts : StructProtoOpts := {}) : CommandElabM (Array (TSyntax `command)) :=
  Lang.runPQ (mkStructProtoCmdsPure t fields opts)

structure TaggedVariantSpec where mk :: (ctorName : Name) (wireTag : String) (fields : Array (Ident × String × Term)) deriving Inhabited
structure TaggedJsonOpts where mk ::
  (tagKey : String := "t") (emitNamedDefs : Bool := true) (emitStringCodec : Bool := false)
  (emitNonNull emitLawful : Bool := false) (unknownTagStatic? : Option String := none)

@[noinline] private def mkLeMaxProof (idx total : Nat) : PureQuotM Term :=
  if total == 0 then `(term| Nat.le_refl _)
  else
    let rec go : Nat → PureQuotM Term | 0 => `(term| Nat.le_max_left _ _) | k + 1 => do `(term| Nat.le_trans $(← go k) (Nat.le_max_right _ _))
    go idx

@[noinline] private def mkTaggedVariantDepthAlt (tId : Name) (totalParams flatIdx : Nat) (v : TaggedVariantSpec) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr × Nat) := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pTerms : Array Term := v.fields.map fun (p, _, _) => ⟨p.raw⟩
  let (idx, paramPfs) ← Lang.foldlPQ v.fields (flatIdx, Array.mkEmpty v.fields.size) fun (idx, acc) (pId, _, _) => do
    return (idx + 1, acc.push (← `(term| Nat.le_trans (Qed.LawfulJson.depth_toJson $pId:ident) $(← mkLeMaxProof idx totalParams))))
  let bodyPf ← Lang.foldrPQ paramPfs (← `(term| Nat.zero_le _)) fun hp acc => `(term| Nat.max_le.2 ⟨$hp, $acc⟩)
  return (← `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => Nat.add_le_add_left (Nat.max_le.2 ⟨Nat.zero_le _, $bodyPf⟩) 1), idx)

@[noinline] private def mkTaggedVariantRtCase (tId : Name) (toId fromId : Ident) (tagKeyLit : StrLit)
    (variants : Array TaggedVariantSpec) (vi : Nat) : PureQuotM (TSyntax ``Lean.Parser.Tactic.inductionAlt) := do
  let v := variants[vi]!; let vName := v.ctorName; let vLit := Syntax.mkStrLit v.wireTag; let pIds := v.fields.map (·.1)
  let ctorVal ← Qed.Lang.mkAppTermsPure (mkIdent (tId ++ vName)) (pIds.map (⟨·.raw⟩))
  let hTagId := mkIdent `_htag
  let initTacs := #[← mkHaveTac hTagId none (← `(term| Qed.LawfulJson.fromField_of_field ($toId $ctorVal) $tagKeyLit $vLit rfl))]
  let (hIdents1, hTacs1) ← Lang.foldlPQ v.fields.zipIdx (#[hTagId], initTacs) fun (ids, tacs) ((pId, wKey, _), pi) => do
    let hfId := mkIdxId "_hf" pi
    return (ids.push hfId, tacs.push (← mkHaveTac hfId none (← `(term| Qed.LawfulJson.fromField_of_field ($toId $ctorVal) $(Syntax.mkStrLit wKey) $pId:ident rfl))))
  let (hIdents, hTacs) ← Lang.foldlPQ (Array.range vi) (hIdents1, hTacs1) fun (ids, tacs) prevIdx => do
    let hneId := mkIdxId "_hne" prevIdx
    return (ids.push hneId, tacs.push (← mkHaveTac hneId (some (← `(term| ($vLit == $(Syntax.mkStrLit variants[prevIdx]!.wireTag)) = false))) (← `(term| rfl))))
  `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* =>
    $[$hTacs:tactic]*; unfold $fromId; simp only [$[$hIdents:term],*, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure])

@[noinline] private def mkTaggedUnionLawfulJsonCmdsPure (t toId fromId : Ident) (tagKeyLit : StrLit)
    (variants : Array TaggedVariantSpec) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId; let allParamTys := variants.flatMap fun v => v.fields.map (·.2.2)
  let maxDepthExpr ← Lang.foldrPQ allParamTys (← `(term| (0 : Nat))) fun ty acc => `(term| Nat.max (Qed.LawfulJson.depthBound $ty) $acc)
  let (_, depthAlts) ← Lang.foldlPQ variants (0, Array.mkEmpty variants.size) fun (flatIdx, alts) v => do
    let (alt, nextIdx) ← mkTaggedVariantDepthAlt tId allParamTys.size flatIdx v; return (nextIdx, alts.push alt)
  let rtCases ← Lang.mapPQ (Array.range variants.size) (mkTaggedVariantRtCase tId toId fromId tagKeyLit variants)
  let thmId := mkIdent (tId ++ `_fromJson_toJson)
  return #[
    ← `(command| private theorem $thmId (x : $t) : $fromId ($toId x) = Except.ok x := by cases x with $[$rtCases:inductionAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where
          depthBound := 1 + $maxDepthExpr; depth_toJson $[$depthAlts:matchAlt]*; fromJson_toJson := $thmId)]

@[noinline] private def mkTaggedVariantToAlt (tId : Name) (tagKeyLit : StrLit) (v : TaggedVariantSpec) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pTerms : Array Term := v.fields.map fun (p, _, _) => ⟨p.raw⟩
  let pairs := #[← `(($tagKeyLit, Qed.ToJson.toJson $(Syntax.mkStrLit v.wireTag)))] ++
    (← Lang.mapPQ v.fields fun (pId, wKey, _) => `(($(Syntax.mkStrLit wKey), Qed.ToJson.toJson $pId:ident)))
  `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => Qed.Json.obj [$[$pairs:term],*])

@[noinline] private def mkTaggedVariantFromArm (tId : Name) (jId tagId : Ident) (v : TaggedVariantSpec) (acc : Term) : PureQuotM Term := do
  let ctorId := mkIdent (tId ++ v.ctorName); let pIds := v.fields.map (·.1)
  let decs ← Lang.mapPQ v.fields fun (_, wKey, pTy) => `(Qed.FromJsonField.fromField (α := $pTy) $jId $(Syntax.mkStrLit wKey))
  let okBr ← mkFieldBindChain pIds decs (← Qed.Lang.mkAppTermsPure ctorId (pIds.map (⟨·.raw⟩)))
  `(if $tagId == $(Syntax.mkStrLit v.wireTag) then $okBr else $acc)

@[noinline] def mkTaggedUnionJsonCmdsPure (t : Ident) (variants : Array TaggedVariantSpec) (opts : TaggedJsonOpts := {}) :
    PureQuotM (Array (TSyntax `command)) := do
  let (tId, jId, tagId) := (t.getId, mkIdent `j, mkIdent `_tag); let tagKeyLit := Syntax.mkStrLit opts.tagKey
  let toAlts ← Lang.mapPQ variants (mkTaggedVariantToAlt tId tagKeyLit)
  let unknownErr ← match opts.unknownTagStatic? with
    | some msg => `(Except.error $(Syntax.mkStrLit msg))
    | none => `(Except.error ($(Syntax.mkStrLit s!"unknown {tId} variant '") ++ $tagId ++ "'"))
  let fromChain ← Lang.foldrPQ variants unknownErr (mkTaggedVariantFromArm tId jId tagId)
  if !opts.emitNamedDefs then return #[
    ← mkInstCmd tId `instToJson ``Qed.ToJson t (← `(⟨fun _x => match _x with $[$toAlts:matchAlt]*⟩)),
    ← mkInstCmd tId `instFromJson ``Qed.FromJson t (← `(⟨fun $jId:ident => do let $tagId:ident ← Qed.FromJsonField.fromField (α := String) $jId $tagKeyLit; $fromChain:term⟩)) ]
  let (toId, fromId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  let mut cmds : Array (TSyntax `command) := #[
    ← mkMatchDef toId ⟨t.raw⟩ (mkCIdent `Qed.Json) toAlts,
    ← `(command| def $fromId ($jId:ident : Qed.Json) : Except String $t := do let $tagId:ident ← Qed.FromJsonField.fromField (α := String) $jId $tagKeyLit; $fromChain:term) ]
  cmds := cmds ++ (← emitJsonCodecWrappers t toId fromId #[] #[] ⟨t.raw⟩ ⟨toId.raw⟩ ⟨fromId.raw⟩ opts.emitStringCodec opts.emitNonNull (← `(fun x => by cases x <;> nofun)))
  if !opts.emitLawful then return cmds
  return cmds ++ (← mkTaggedUnionLawfulJsonCmdsPure t toId fromId tagKeyLit variants)

private def unitEnumInstSpecs : Array (Name × Name) := #[
  (`instToString, ``ToString), (`instStringEnum, ``Qed.StringEnum), (`instRouteParam, `Qed.RouteParam),
  (`instLawfulKey, `Qed.LawfulKey), (`instToJson, ``Qed.ToJson), (`instFromJson, ``Qed.FromJson),
  (`instNonNullJson, ``Qed.NonNullJson), (`instLawfulJson, ``Qed.LawfulJson),
  (`instToProto, ``Qed.ToProto), (`instFromProto, ``Qed.FromProto), (`instLawfulProto, ``Qed.LawfulProto)]

@[noinline] def mkUnitEnumCodecCmdsPure (t : Ident) (variants : Array (Name × String)) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId
  let (toStrAlts, ofStr0, toTagAlts, ofTag0) ← Lang.foldlPQ variants.zipIdx (#[], #[], #[], #[]) fun (ts, os, tt, ot) ((vNm, wire), i) => do
    let ctor : Term := mkIdent (tId ++ vNm); let wLit : Term := Syntax.mkStrLit wire; let iLit : Term := numLit i
    let okCtor ← `(Except.ok $ctor)
    return (ts.push (← mkMatchAlt1 ctor wLit), os.push (← mkMatchAlt1 wLit okCtor), tt.push (← mkMatchAlt1 ctor iLit), ot.push (← mkMatchAlt1 iLit okCtor))
  let (otherId, nId) := (mkIdent `other, mkIdent `n)
  let ofStrAlts := ofStr0.push (← mkMatchAlt1 otherId (← `(Except.error ($(Syntax.mkStrLit s!"invalid {tId} '") ++ $otherId ++ "'"))))
  let ofTagAlts := ofTag0.push (← mkMatchAlt1 nId (← `(Except.error ($(Syntax.mkStrLit s!"protobuf: invalid {tId} tag ") ++ toString $nId))))
  let (toStrId, ofStrId, codecId) := (mkIdent (tId ++ `toString), mkIdent (tId ++ `ofString), mkIdent (tId ++ `_codec))
  let tTerm : Term := ⟨t.raw⟩; let strT : Term := mkCIdent `String; let jsonT : Term := mkCIdent `Qed.Json; let bytesT : Term := mkCIdent `Qed.Bytes
  let excT ← `(Except String $tTerm)
  let wrapperSpecs : Array (Name × Term × Term) := #[(`toJson, tTerm, jsonT), (`fromJson, jsonT, excT), (`encode, tTerm, strT), (`encodeBytes, tTerm, bytesT), (`decodeBytes, bytesT, excT)]
  let wrapCmds ← Lang.mapPQ wrapperSpecs fun (nm, inTy, outTy) => `(command| def $(mkIdent (tId ++ nm)) (v : $inTy) : $outTy := ($codecId).$(mkIdent nm):ident v)
  let instCmds ← Lang.mapPQ unitEnumInstSpecs fun (leaf, cls) => do mkInstCmd tId leaf cls t (← `(($codecId).$(mkIdent leaf):ident))
  return #[
    ← mkMatchDef toStrId tTerm strT toStrAlts,
    ← mkMatchDef ofStrId strT excT ofStrAlts,
    ← `(command| def $codecId : $(mkCIdent `Qed.UnitEnumCodec) $t where
          typeName := $(Syntax.mkStrLit tId.toString)
          toStr := $toStrId
          ofStr := $ofStrId
          rtStr := fun x => by cases x <;> rfl
          toTag $[$toTagAlts:matchAlt]*
          ofTag $[$ofTagAlts:matchAlt]*
          rtTag := fun x => by cases x <;> rfl),
    ← `(command| @[simp] theorem $(mkIdent (tId ++ `ofString_toString)) (x : $t) : $ofStrId ($toStrId x) = Except.ok x := ($codecId).rtStr x),
    ← `(command| def $(mkIdent (tId ++ `decode)) (s : String) (maxDepth : Nat := 64) : Except String $t := ($codecId).decode s maxDepth)
  ] ++ wrapCmds ++ instCmds

end CodecDerive
end Qed
