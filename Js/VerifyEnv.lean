import Lean

open Lean

namespace Js

def allowedKernelAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
@[inline] def isToolchainModule (modName : Name) : Bool := let r := modName.getRoot; r == `Init || r == `Std || r == `Lean || r == `Lake
@[inline] def definingModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous | none => Name.anonymous
@[inline] def isFrameworkModule (modName : Name) : Bool := let r := modName.getRoot; r == `Qed || r == `Js || r == `Cli
@[inline] private def withPriv (p : Name → Bool) (n : Name) : Bool := p n || (Lean.isPrivateName n && p (Lean.privateToUserName n))
@[specialize] private def hasNamePrefix (p : Name → Bool) : Name → Bool
  | .anonymous => false | .num parent _ => hasNamePrefix p parent | n@(.str parent _) => p n || hasNamePrefix p parent
@[inline] private def exprHasConst (p : Name → Bool) (e : Expr) : Bool := e.foldConsts false fun c acc => acc || p c
private def rootTwoAux : Name → Option String → Option (String × Option String)
  | .str .anonymous r, second => some (r, second) | .str p s, _ => rootTwoAux p (some s) | .num p _, _ => rootTwoAux p none | .anonymous, _ => none
private def metaLeanPrefixes : Array String := #["Syntax", "TSyntax", "Macro", "Elab", "Meta", "Parser", "PrettyPrinter", "Environment", "IR"]
private def isMetaNamespaceConst (env : Environment) (n : Name) : Bool :=
  match rootTwoAux n none with | some ("Lean", some s) => metaLeanPrefixes.any (s.startsWith ·) && isToolchainModule (definingModule env n) | _ => false

@[noinline] private def mkNameSet (s : String) : Std.HashSet Name :=
  ((s.replace "\n" " ").splitOn " ").foldl (init := {}) fun acc w =>
    if w.isEmpty then acc else acc.insert ((w.splitOn ".").foldl Name.mkStr .anonymous)

private def forbiddenRuntimeLoopExact : Std.HashSet Name := mkNameSet "
  IO.iterate repeatM runST runEST IO.FS.Stream.mk IO.FS.Stream.readToEnd IO.FS.Stream.readBinToEnd
  IO.FS.Stream.readBinToEndInto IO.FS.Stream.lines Std.Stream.forIn Std.instForInOfMonadOfStream
  Std.Rci.iter Std.Roi.iter Std.Rii.iter Std.Rcc.iter Std.Rco.iter Std.Roc.iter Std.Roo.iter
  Std.Ric.iter Std.Rio.iter Std.Rxi.Iterator Std.Rxi.instIteratorIteratorIdOfUpwardEnumerable
  Std.Rxc.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE
  Std.Rxo.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT
  Std.Rxi.Iterator.instIteratorLoop.loop Std.Rxc.Iterator.instIteratorLoop.loop
  Std.Rxo.Iterator.instIteratorLoop.loop Std.IterM.DefaultConsumers.forIn' Std.Iter.atIdxSlow?
  Std.IterM.toArray.go Std.IterM.toListRev.go Std.Iterator.mk Std.IteratorLoop.mk Std.Stream.mk
  Std.PRange.UpwardEnumerable.mk String.Slice.Pattern.ForwardPattern.mk String.Slice.Pattern.BackwardPattern.mk
  Std.Iter.repeat Std.IterM.repeat Std.Iterators.Types.RepeatIterator Std.Iter.allowNontermination
  Std.IterM.allowNontermination Std.Iter.Partial Std.IterM.Partial Std.IteratorLoop.defaultImplementation
  Std.Internal.Parsec.manyCore Std.Internal.Parsec.manyCharsCore Std.Internal.Parsec.many
  Std.Internal.Parsec.many1 Std.Internal.Parsec.manyChars Std.Internal.Parsec.many1Chars
  Std.Broadcast.Receiver.forAsync Std.Bounded.Receiver.forAsync Std.Broadcast.Sync.Receiver.forIn
  Std.Broadcast.Sync.Receiver.instForInOfInhabitedOfMonadOfMonadLiftTBaseIO
  Std.Channel.forAsync Std.CloseableChannel.forAsync Std.Channel.Sync.forIn Std.CloseableChannel.Sync.forIn
  Std.Channel.Sync.instForInOfInhabitedOfMonadOfMonadLiftTBaseIO
  Std.CloseableChannel.Sync.instForInOfMonadOfMonadLiftTBaseIO
  Std.Async.EAsync.forIn Std.Async.EAsync.instForInLoopUnit
  Std.Async.ContextAsync.forIn Std.Async.ContextAsync.instForInLoopUnit
  Std.Http.Body.Stream.forIn Std.Http.Body.Stream.forIn' Std.Http.Body.Stream.readAll
  Std.Http.Body.Stream.drain Std.Http.Body.instForInAsyncStreamChunk Std.Http.Body.instForInContextAsyncStreamChunk"
private def forbiddenRuntimeLoopDottedSubstrs : Array String := #[
  "IO.iterate", "repeatM.erased", "repeatM.impl", "IterM.Partial", "Lean.Loop.forIn", "Lean.Order.fix",
  "Std.Stream.forIn", "IteratorLoop.defaultImplementation", "Parsec.manyCore", "Parsec.manyCharsCore"]
private def wfOpaqueLeaves : Array String := #["opaqueFix", "opaqueFix₂", "opaqueFix₃"]
private def wfExtrinsicLeaves : Array String := #[
  "extrinsicFix", "extrinsicFix₂", "extrinsicFix₃", "partialExtrinsicFix", "partialExtrinsicFix₂", "partialExtrinsicFix₃"]
private def parsecLoopLeaves : Array String := #["manyCore", "manyCharsCore", "many", "many1", "manyChars", "many1Chars"]

private def isRuntimeLoopHit : Name → Bool
  | n@(.str _ s) =>
      forbiddenRuntimeLoopExact.contains n ||
      (s.length >= 10 &&
        ((s.length >= 14 && (s.contains "RepeatIterator" || s.contains "allowNontermination")) ||
         (s.contains '.' && forbiddenRuntimeLoopDottedSubstrs.any (s.contains ·)))) ||
      match n with
      | .str (.str (.str _ r) "Order") "fix" => r.endsWith "Lean"
      | .str (.str _ r) leaf =>
          (r.endsWith "Lean" && (leaf == "Loop" || leaf.startsWith "instForInLoop")) ||
          (r == "IO" && leaf == "iterate") || (r == "IterM" && leaf == "Partial") ||
          (r == "Stream" && leaf == "forIn") || (r == "IteratorLoop" && leaf == "defaultImplementation") ||
          (r == "WellFounded" && wfExtrinsicLeaves.contains leaf) || (r == "Parsec" && parsecLoopLeaves.contains leaf)
      | _ => false
  | _ => false

private def isWfFixLeaf (inclExt : Bool) : Name → Bool
  | .str (.str _ "WellFounded") leaf => wfOpaqueLeaves.contains leaf || (inclExt && wfExtrinsicLeaves.contains leaf)
  | _ => false
private def isRuntimeLoopConst (n : Name) : Bool := withPriv (hasNamePrefix isRuntimeLoopHit) n || withPriv (isWfFixLeaf false) n
private def isWhileLoopConst (n : Name) : Bool := isRuntimeLoopConst n || hasNamePrefix (isWfFixLeaf true) n

private def forbiddenUserMutableRefExact : Std.HashSet Name := mkNameSet "
  ST.mkRef ST.Prim.mkRef IO.mkRef ST.Ref.set ST.Prim.Ref.set ST.Ref.modify ST.Ref.modifyGet
  ST.Prim.Ref.modifyGet IO.Ref.set IO.Ref.modify IO.Ref.modifyGet ST.Ref.swap ST.Prim.Ref.swap
  IO.Ref.swap ST.Ref.take ST.Prim.Ref.take IO.Ref.take IO.Promise.new IO.Promise.resolve
  IO.Promise.result? IO.Promise.result! IO.Promise.resultD Std.BaseMutex.new Std.BaseRecursiveMutex.new
  Std.BaseSharedMutex.new Std.Condvar.new Std.Barrier.new Std.Notify.new Std.Semaphore.new
  Std.CancellationContext.new Std.CancellationToken.new Std.Mutex.new Std.Mutex.atomically
  Std.Mutex.tryAtomically Std.Mutex.atomicallyOnce Std.RecursiveMutex.new Std.RecursiveMutex.atomically
  Std.RecursiveMutex.tryAtomically Std.SharedMutex.new Std.SharedMutex.atomically Std.SharedMutex.tryAtomically
  Std.SharedMutex.atomicallyRead Std.SharedMutex.tryAtomicallyRead StateRefT'.run StateRefT'.run'
  StateRefT'.set StateRefT'.modifyGet StateRefT'.instMonadStateOfOfMonadLiftTST Std.Channel.new
  Std.Channel.Sync.new Std.CloseableChannel.new Std.CloseableChannel.Sync.new Std.Broadcast.new
  Std.Broadcast.Sync.new Std.Bounded.new Qed.Server.Prim.mkStateBox Qed.Server.Prim.atomicRead
  Qed.Server.Prim.atomicModify Qed.Server.Native.withStateBox Qed.Handlers.mkNew Qed.registerHandler
  Qed.dispatchStrWithRows Qed.localRerender Qed.localRun"

private def isMutableRefConst (n : Name) : Bool := withPriv (hasNamePrefix forbiddenUserMutableRefExact.contains) n
private def hasRegBuiltin (n : Name) : Bool := hasNamePrefix (fun | .str _ s => s.contains "_regBuiltin" | _ => false) n
private def isRecCombinatorConst (c : Name) : Bool :=
  c == ``WellFounded.fix || c == `WellFounded.Nat.fix || match c with | .str _ s => s == "_f" || s.startsWith "brecOn" || s.startsWith "_unary" || s.startsWith "_mutual" | _ => false
private def isUnsafeRecName : Name → Bool | .str _ "_unsafe_rec" => true | _ => false
private def isProofApp (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.consumeMData with | .const c _ => (match env.find? c with | some (.thmInfo _) => true | _ => false) | _ => false

private def exprEqUpToProofs (env : Environment) (allowProof : Bool) (e1 e2 : Expr) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      let e1 := e1.consumeMData; let e2 := e2.consumeMData
      if allowProof && isProofApp env e2 then !exprHasConst isUnsafeRecName e1
      else match e1, e2 with
      | .bvar i, .bvar j => i == j | .fvar a, .fvar b => a == b | .mvar a, .mvar b => a == b | .sort u, .sort v => u == v | .lit a, .lit b => a == b
      | .const c1 l1, .const c2 l2 => (match c1 with | .str p "_unsafe_rec" => p | c => c) == c2 && l1 == l2
      | .app f1 a1, .app f2 a2 => exprEqUpToProofs env allowProof f1 f2 fuel && exprEqUpToProofs env true a1 a2 fuel
      | .lam _ t1 b1 _, .lam _ t2 b2 _ | .forallE _ t1 b1 _, .forallE _ t2 b2 _ => exprEqUpToProofs env true t1 t2 fuel && exprEqUpToProofs env allowProof b1 b2 fuel
      | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ => exprEqUpToProofs env true t1 t2 fuel && exprEqUpToProofs env true v1 v2 fuel && exprEqUpToProofs env allowProof b1 b2 fuel
      | .proj n1 i1 s1, .proj n2 i2 s2 => n1 == n2 && i1 == i2 && exprEqUpToProofs env false s1 s2 fuel | _, _ => false

def isTotalCompilerAux (env : Environment) (declName : Name) : Bool :=
  match declName with
  | .str root "_unsafe_rec" =>
      (Lean.declRangeExt.find? env declName).isNone && (Compiler.getImplementedBy? env root).isNone && env.getModuleIdxFor? declName == env.getModuleIdxFor? root &&
      match env.find? declName, env.find? root with
      | some (.defnInfo dv), some (.defnInfo rdv) =>
          dv.safety == .partial && rdv.safety == .safe && dv.type == rdv.type && dv.levelParams == rdv.levelParams &&
          exprHasConst isRecCombinatorConst rdv.value && exprHasConst isUnsafeRecName dv.value &&
          match (Lean.Elab.WF.eqnInfoExt.find? env root).map (·.value) |>.orElse fun _ => (Lean.Elab.Structural.eqnInfoExt.find? env root).map (·.value) with
          | some eqVal => !isProofApp env eqVal && exprEqUpToProofs env false dv.value eqVal 100000 | none => false
      | _, _ => false
  | _ => false

def isAllowedExternMod (modName : Name) : Bool := modName == `Qed.Dom || modName == `Qed.Server.Prim
def isLegitOpaque (env : Environment) (modName declName : Name) : Bool :=
  (isAllowedExternMod modName && Lean.isExtern env declName) ||
  (modName == `Qed.Server.Prim && (declName == `Qed.Server.Prim.StateBoxPointed || declName == `Qed.Server.Prim.StaticDirPointed)) ||
  (isFrameworkModule modName && (Lean.getInitFnNameFor? env declName).isSome && (Compiler.getImplementedBy? env declName).isNone)
def isCompileTimeMetaDecl (env : Environment) (declName : Name) (ci : ConstantInfo) : Bool :=
  exprHasConst (isMetaNamespaceConst env) ci.type ||
  ((Lean.declRangeExt.find? env declName).isNone && (hasRegBuiltin declName ||
    match declName with
    | .str parent leaf => (leaf == "_unsafe_rec" || leaf.startsWith "match_" || leaf.startsWith "_cstage") && (env.find? parent).any fun pci => exprHasConst (isMetaNamespaceConst env) pci.type
    | _ => false))

@[inline] private def pushUnseen (clean : Std.HashSet Name) (stack : Array Name) (n : Name) : Array Name := if clean.contains n then stack else stack.push n
private def pushExprDeps (e : Expr) (clean : Std.HashSet Name) (stack : Array Name) : Array Name := e.foldConsts stack fun c acc => if clean.contains c then acc else acc.push c
private def pushConstDeps (ci : ConstantInfo) (clean : Std.HashSet Name) (stack : Array Name) (withRecAll : Bool := true) : Array Name :=
  let s := pushExprDeps ci.type clean stack
  match ci with
  | .defnInfo v | .thmInfo v | .opaqueInfo v => pushExprDeps v.value clean s | .inductInfo v => v.ctors.foldl (pushUnseen clean) s
  | .ctorInfo v => if withRecAll then pushUnseen clean s v.name else s | .recInfo v => if withRecAll then v.all.foldl (pushUnseen clean) s else s | _ => s
private def pushValAndImplDeps (env : Environment) (n : Name) (ci? : Option ConstantInfo) (clean : Std.HashSet Name) (stack : Array Name) : Array Name :=
  let s := (Compiler.getImplementedBy? env n).elim stack (pushUnseen clean stack)
  match ci? with | some (.defnInfo v) | some (.opaqueInfo v) => pushExprDeps v.value clean s | _ => s

private def isAllowedToolchainPartialBase (c : Name) : Bool :=
  let base := match c with | .str p "_unsafe_rec" => p | n => n
  base == `Nat.toSubDigitsAux || base == `Nat.toSuperDigitsAux || base == `Lean.Name.needsNoEscapeAsciiRest || isWfFixLeaf false base
def isForbiddenToolchainPartial (env : Environment) (c : Name) : Bool :=
  isToolchainModule (definingModule env c) && !withPriv isAllowedToolchainPartialBase c &&
  match env.find? c with
  | some (.opaqueInfo _) => !Lean.isExtern env c && env.contains (Name.str c "_unsafe_rec")
  | some (.defnInfo dv) => dv.safety == .partial && !isTotalCompilerAux env c | _ => false
private def forbiddenCustomClass (c : Name) : Bool := c == `Std.Iterator || c == `Std.IteratorLoop || c == `Std.Stream || c == `Std.PRange.UpwardEnumerable
private def metaAliasAllowlist : Std.HashSet Name := mkNameSet "
  Lean.MacroM Lean.Macro Lean.CoreM Lean.Meta.MetaM Lean.Elab.Command.CommandElabM Lean.Elab.Command.CommandElab
  Lean.Elab.Term.TermElabM Lean.Elab.Term.TermElab Lean.Elab.Tactic.TacticM Lean.Elab.Tactic.Tactic
  Lean.PrettyPrinter.Formatter Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Unexpander Lean.PrettyPrinter.Delaborator.Delab"
private def stripTypeBinders : Expr → Expr | .forallE _ _ b _ | .lam _ _ b _ | .mdata _ b => stripTypeBinders b | e => e
private def unfoldReturnHead (env : Environment) (stop : Name → Bool) (e : Expr) (fuel : Nat := 16) : Except String (Option Name) :=
  let e0 := stripTypeBinders ((stripTypeBinders e).headBeta)
  match e0 with
  | .letE _ _ v b _ => match fuel with | 0 => .error "type alias unfolding exceeded depth limit in `let` binder" | f + 1 => unfoldReturnHead env stop (b.instantiate1 v) f
  | _ => match e0.getAppFn.consumeMData with
    | .const c _ =>
        if stop c then .ok (some c)
        else match env.find? c with
        | some (.defnInfo dv) => match fuel with | 0 => .error s!"type alias unfolding exceeded depth limit at `{c}`" | f + 1 => unfoldReturnHead env stop (dv.value.beta e0.getAppArgs) f
        | _ => .ok (some c)
    | _ => .ok none
private def hasMetaReturnType (env : Environment) (e : Expr) : Bool :=
  match unfoldReturnHead env (fun c => isMetaNamespaceConst env c && metaAliasAllowlist.contains c) e with | .ok (some c) => isMetaNamespaceConst env c | _ => false
private def csimpErr (declName modName : Name) : String := s!"kernel gate: `@[csimp]` declaration `{declName}` in `{modName}` is forbidden outside framework modules"

private def collectCSimpData (env : Environment) : Option (Name × Name) × Std.HashMap Name (Array Name) :=
  let step (modName : Name) (e : Lean.Compiler.CSimp.Entry) (acc : Option (Name × Name) × Std.HashMap Name (Array Name)) :=
    let bad := acc.1.orElse fun _ => if !isToolchainModule modName && !isFrameworkModule modName then some (modName, e.thmName) else none
    let cur := acc.2.getD e.fromDeclName #[]; (bad, if cur.contains e.toDeclName then acc.2 else acc.2.insert e.fromDeclName (cur.push e.toDeclName))
  let acc := env.header.moduleNames.size.fold (init := (none, {})) fun modIdx _ acc =>
    (Lean.Compiler.CSimp.ext.ext.getModuleEntries env modIdx).foldl (init := acc) fun a sc =>
      step env.header.moduleNames[modIdx]! (match sc with | .global e | .scoped _ e => e) a
  (Lean.Compiler.CSimp.ext.getState env).map.toList.foldl (init := acc) fun a (_, e) => step (definingModule env e.thmName) e a
private def verifyCSimpClean (env : Environment) : Except String (Std.HashMap Name (Array Name)) :=
  let (bad?, repls) := collectCSimpData env; bad?.elim (.ok repls) fun (modName, declName) => .error (csimpErr declName modName)
private def owningKernelConst? (env : Environment) : Name → Option Name
  | .anonymous => none | n => if env.contains n then some n else match n with | .str p _ | .num p _ => owningKernelConst? env p | .anonymous => none

mutual
def callees : Lean.IR.FnBody → Array Name → Array Name
  | .vdecl _ _ e b, acc => callees b (match e with | .fap c _ | .pap c _ => acc.push c | _ => acc)
  | .jdecl _ _ v b, acc => callees b (callees v acc)
  | .case _ _ _ alts, acc => calleesAlts alts.toList acc
  | .set _ _ _ b, acc | .setTag _ _ b, acc | .uset _ _ _ b, acc | .sset _ _ _ _ _ b, acc
  | .inc _ _ _ _ b, acc | .dec _ _ _ _ b, acc | .del _ b, acc => callees b acc
  | .ret _, acc | .jmp _ _, acc | .unreachable, acc => acc

def calleesAlts : List Lean.IR.Alt → Array Name → Array Name
  | [], acc => acc | .ctor _ b :: rest, acc | .default b :: rest, acc => calleesAlts rest (callees b acc)
end

@[inline] private def hasOwnerMarker (env : Environment) (owner marker : Name) : Bool := !owner.isAnonymous && env.contains (owner ++ marker)

private def forbiddenServerRlsExact : Std.HashSet Name := mkNameSet "
  Qed.Server.AuthToken.mk Qed.Server.AuthToken.ofRaw Qed.Server.AuthToken.ofUser Qed.Server.AuthToken.ofPrincipal
  Qed.Server.RequestCtx.withAuth Qed.Server.RequestCtx.forUser Qed.Server.RequestCtx.forPrincipal
  Qed.Server.Eval.setUser Qed.Server.Eval.setRole Qed.Server.Eval.setSession Qed.Server.Eval.setPrincipal
  Qed.Server.ServerJob.mk Qed.Server.VerifiedJob.mk Qed.Server.ServerJob.runM Qed.Server.ServerJob.runWorkM?
  Qed.Server.ServerJob.toIoJob Qed.Server.IoJob.runOnce Qed.Server.IoJob.runWorkOnce
  Qed.Server.runServerJobs Qed.Server.spawnServerJobs
  Qed.Server.MonadServer.exec Qed.Server.MonadServer.dbExec Qed.Server.MonadServer.dbTxBegin
  Qed.Server.MonadServer.dbTxExec Qed.Server.MonadServer.dbTxCommit Qed.Server.MonadServer.dbTxRollback
  Qed.Server.ServerEffect.dbExec Qed.Server.ServerEffect.dbTxBegin Qed.Server.ServerEffect.dbTxExec
  Qed.Server.ServerEffect.dbTxCommit Qed.Server.ServerEffect.dbTxRollback
  Qed.Server.Db.execDbMaybeTx Qed.Server.Db.DbConfig.forPostgresUrl Qed.Server.Db.PgHandle.mk
  Qed.Server.Native.mkNativeServerInst Qed.Server.Native.mkNativeServerInstWith
  Qed.Server.Native.instMonadServerIO Qed.Server.Native.migrateDatabase
  Qed.Server.Native.execRawOnTransport Qed.Server.Native.execDdlOnTransport Qed.Server.Native.execPgTxBegin"

private def isNsPrefix (pfx : Name) : Name → Bool
  | .anonymous => false
  | n => if n == pfx then true else match n with | .str p _ | .num p _ => isNsPrefix pfx p | .anonymous => false

private def isServerEffectMatchSplitter (env : Environment) (n : Name) (val : Expr) : Bool :=
  (Lean.declRangeExt.find? env n).isNone && Lean.isPrivateName n &&
  let u := Lean.privateToUserName n
  isNsPrefix `Qed.Server.ServerEffect u && (u.toString.contains "splitter" || u.toString.contains "_sparseCasesOn_") &&
  !exprHasConst (fun c => c == `Qed.Server.MonadServer.exec || isNsPrefix `Qed.Server.Prim c || isNsPrefix `Qed.Server.Db.PgWire c) val
private def isDbExecDdlName (n : Name) : Bool :=
  n == `Qed.Server.MonadServer.dbExecDdl || n == `Qed.Server.ServerEffect.dbExecDdl

private def isDbEnsureSchemaDecl (env : Environment) : Name → Bool
  | .str dbOwner "ensureSchema" => hasOwnerMarker env dbOwner `_qed_database_marker
  | _ => false

private def isServerRlsForbiddenBase (env : Environment) (ownerDecl : Name) (transitive : Bool) (c : Name) : Bool :=
  let check1 (n : Name) : Bool :=
    forbiddenServerRlsExact.contains n ||
    isNsPrefix `Qed.Server.Prim n ||
    isNsPrefix `Qed.Server.Db.PgWire n ||
    (isDbExecDdlName n && (transitive || !isDbEnsureSchemaDecl env ownerDecl))
  withPriv (hasNamePrefix check1) c

private def dbVerifiedOpNames : Std.HashSet Name := mkNameSet "
  Qed.Server.Db.dbRunRows Qed.Server.Db.dbRunOneRow Qed.Server.Db.dbSelectProj Qed.Server.Db.dbFindOneProj
  Qed.Server.Db.dbCount Qed.Server.Db.dbSumNat Qed.Server.Db.dbSumInt Qed.Server.Db.dbAggOpt
  Qed.Server.Db.dbDelete Qed.Server.Db.dbInsert Qed.Server.Db.dbInsertOrIgnore
  Qed.Server.Db.dbUpsert Qed.Server.Db.dbJoinSelect"

private def restrictedServerExact : Std.HashSet Name := mkNameSet "
  Qed.Server.Db.dbRunChecked Qed.Server.Db.dbRun Qed.Server.Db.DbConfig.mk Qed.Server.dbRunTx
  Qed.Server.ServerJob.mkSystem Qed.Server.VerifiedJob.mkSystem Qed.Server.verifyRouteAuth"

@[inline] private def isDbVerifiedOpName (c : Name) : Bool := dbVerifiedOpNames.contains c
@[inline] private def isRestrictedServerConst (c : Name) : Bool :=
  restrictedServerExact.contains c || dbVerifiedOpNames.contains c || isNsPrefix `Qed.Server.RouteAuthSpec c

private def peelValWrap (e : Expr) (fuel : Nat := 16) : Expr :=
  match fuel with
  | 0 => e.consumeMData
  | f + 1 =>
      let e := e.consumeMData
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      match fn with
      | .const `Qed.Lang.QedVal.val _ => if args.size == 4 then peelValWrap args[3]! f else e
      | .const ``id _ => if args.size == 2 then peelValWrap args[1]! f else e
      | .const `Qed.Lang.QedSeqLit.ofList _ => if args.size == 4 then peelValWrap args[3]! f else e
      | _ => e

private def extractStrLit? (e : Expr) : Option String :=
  match (peelValWrap e).consumeMData with | .lit (.strVal s) => some s | _ => none

private def extractSqlIdent? (e : Expr) : Option String :=
  let e := e.consumeMData
  if e.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlIdent.mk && e.getAppArgs.size >= 1 then
    extractStrLit? e.getAppArgs[0]!
  else none

private def extractBoolLit? (e : Expr) : Option Bool :=
  match (peelValWrap e).consumeMData with
  | .const ``Bool.true _ => some true | .const ``Bool.false _ => some false | _ => none

private def extractNatLit? (e : Expr) (fuel : Nat := 16) : Option Nat :=
  match fuel with
  | 0 => none
  | f + 1 =>
      let e := (peelValWrap e).consumeMData
      match e with
      | .lit (.natVal n) => some n
      | .const ``Nat.zero _ => some 0
      | _ =>
          let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
          if fn.isConstOf ``OfNat.ofNat && args.size >= 2 then extractNatLit? args[1]! f
          else if fn.isConstOf ``Nat.succ && args.size == 1 then (extractNatLit? args[0]! f).map (· + 1)
          else none

private def extractListElems? (e : Expr) (fuel : Nat := 1024) : Option (Array Expr) :=
  let rec go (cur : Expr) (acc : Array Expr) : Nat → Option (Array Expr)
    | 0 => none
    | f + 1 =>
        let cur := (peelValWrap cur).consumeMData
        let fn := cur.getAppFn.consumeMData; let args := cur.getAppArgs
        if fn.isConstOf ``List.nil then some acc
        else if fn.isConstOf ``List.cons && args.size == 3 then go args[2]! (acc.push args[1]!) f
        else none
  go e #[] fuel

private def extractOpt? (e : Expr) : Option (Option Expr) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf ``Option.none then some none
  else if fn.isConstOf ``Option.some && args.size == 2 then some (some args[1]!)
  else none

private def extractPair? (e : Expr) : Option (Expr × Expr) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf ``Prod.mk && args.size == 4 then some (args[2]!, args[3]!) else none

private def extractStrListFromConst? (env : Environment) (c : Name) : Option (Array String) :=
  match env.find? c with
  | some (.defnInfo dv) => (extractListElems? dv.value).bind fun xs => xs.mapM extractStrLit?
  | _ => none

private def extractAuthCtx? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  match e with
  | .proj `Qed.Server.RequestCtx 3 ctx => some ctx.consumeMData
  | _ =>
      let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
      if fn.isConstOf `Qed.Server.RequestCtx.auth && args.size == 1 then some args[0]!.consumeMData else none

private def extractDbConfigOwner? (env : Environment) (e : Expr) : Option Name :=
  match e.consumeMData with
  | .const (.str dbOwner "config") _ => if hasOwnerMarker env dbOwner `_qed_database_marker then some dbOwner else none
  | _ => none

private def fieldProjName? (env : Environment) (e : Expr) : Option (Expr × String) :=
  let e := (peelValWrap e).consumeMData
  match e with
  | .proj structName idx base =>
      ((Lean.getStructureFields env structName)[idx]?).map fun fld => (base.consumeMData, fld.toString)
  | _ =>
      let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
      match fn with
      | .const (.str structName fld) _ =>
          if args.size == 1 && Lean.isStructure env structName && (Lean.getStructureFields env structName).contains (Name.mkSimple fld) then
            some (args[0]!.consumeMData, fld)
          else none
      | _ => none

private def isHardcodedSecretExpr (e : Expr) (fuel : Nat := 12) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
      let e := (peelValWrap e).consumeMData
      match e with
      | .lit (.strVal _) => true
      | _ =>
          let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
          if fn.isConstOf `Qed.Server.ToSecretStr.toSecretStr && args.size >= 3 then isHardcodedSecretExpr args[2]! f
          else if fn.isConstOf `Qed.Secret.expose && args.size == 1 then isHardcodedSecretExpr args[0]! f
          else if fn.isConstOf `Qed.Secret.ofString && args.size == 1 then isHardcodedSecretExpr args[0]! f
          else false

private structure SqlMatchCtx where
  env        : Environment
  sqlDepth   : Nat := 0
  leanDepth  : Nat := 0
  sqlToLean  : Array (Option Nat) := #[]
  rowScopes  : Array (Option String × Nat) := #[]
  snapLevel? : Option Nat := none

private def SqlMatchCtx.pushSharedBinder (c : SqlMatchCtx) : SqlMatchCtx :=
  { c with sqlDepth := c.sqlDepth + 1, leanDepth := c.leanDepth + 1, sqlToLean := c.sqlToLean.push (some c.leanDepth) }

private def SqlMatchCtx.pushRowScope (c : SqlMatchCtx) (qual? : Option String) : SqlMatchCtx :=
  { c with leanDepth := c.leanDepth + 1, rowScopes := c.rowScopes.push (qual?, c.leanDepth) }

private def SqlMatchCtx.pushLeanBinder (c : SqlMatchCtx) : SqlMatchCtx :=
  { c with leanDepth := c.leanDepth + 1 }

private def outerExprEq (c : SqlMatchCtx) (localD : Nat) (eSql eLean : Expr) : Nat → Bool
  | 0 => false
  | f + 1 =>
      let eSql := (peelValWrap eSql).consumeMData
      let eLean := (peelValWrap eLean).consumeMData
      match eSql, eLean with
      | .bvar i, .bvar j =>
          if i < localD then j == i
          else
            let si := i - localD
            if si < c.sqlDepth then
              let sqlLvl := c.sqlDepth - 1 - si
              match c.sqlToLean[sqlLvl]? with
              | some (some lLvl) => j >= localD && j - localD < c.leanDepth && c.leanDepth - 1 - (j - localD) == lLvl
              | _ => false
            else
              let outerIdx := si - c.sqlDepth
              j >= localD + c.leanDepth && j - localD - c.leanDepth == outerIdx
      | .fvar a, .fvar b => a == b
      | .mvar a, .mvar b => a == b
      | .sort u, .sort v => u == v
      | .lit a, .lit b => a == b
      | .const c1 _, .const c2 _ => c1 == c2
      | .app f1 a1, .app f2 a2 => outerExprEq c localD f1 f2 f && outerExprEq c localD a1 a2 f
      | .lam _ t1 b1 _, .lam _ t2 b2 _ | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
          outerExprEq c localD t1 t2 f && outerExprEq c (localD + 1) b1 b2 f
      | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
          outerExprEq c localD t1 t2 f && outerExprEq c localD v1 v2 f && outerExprEq c (localD + 1) b1 b2 f
      | .proj n1 i1 s1, .proj n2 i2 s2 => n1 == n2 && i1 == i2 && outerExprEq c localD s1 s2 f
      | _, _ =>
          match fieldProjName? c.env eSql, fieldProjName? c.env eLean with
          | some (b1, fld1), some (b2, fld2) => fld1 == fld2 && outerExprEq c localD b1 b2 f
          | _, _ => false

private def unwrapSqlParamVal? (e : Expr) : Option Expr :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf `Qed.Server.Db.ToSql.toSql && args.size == 3 then some args[2]!
  else if fn.isConstOf `Qed.Server.Db.toSqlLike && args.size == 5 then some args[4]!
  else if fn.isConstOf `Qed.Server.Db.SqlVal.text && args.size == 1 then some args[0]!
  else if fn.isConstOf `Qed.Server.Db.SqlVal.bool && args.size == 1 then some args[0]!
  else if fn.isConstOf `Qed.Server.Db.SqlVal.int && args.size == 1 then some args[0]!
  else if fn.isConstOf `Qed.Server.Db.SqlVal.bytes && args.size == 1 then some args[0]!
  else none

private def unwrapToSqlList? (e : Expr) : Option Expr :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf `Qed.Server.Db.ToSqlList.toSqlList && args.size == 3 then some args[2]! else none

private def unwrapOptSome? (e : Expr) : Option Expr :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf ``Option.some && args.size == 2 then some args[1]! else none

private def isOptNoneExpr (e : Expr) : Bool :=
  (peelValWrap e).consumeMData.getAppFn.consumeMData.isConstOf ``Option.none

private def extractDecideInner? (e : Expr) : Option Expr :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if (fn.isConstOf ``decide || fn.isConstOf ``Decidable.decide) && args.size >= 1 then some args[0]! else none

private def extractBoolIte? (e : Expr) : Option (Expr × Expr × Expr × Bool) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  let unwrapEqTrue (condP : Expr) : Expr :=
    let condP := condP.consumeMData
    if condP.getAppFn.consumeMData.isConstOf ``Eq && condP.getAppArgs.size == 3 && extractBoolLit? condP.getAppArgs[2]! == some true then
      condP.getAppArgs[1]!
    else condP
  if fn.isConstOf ``ite && args.size == 5 then some (unwrapEqTrue args[1]!, args[3]!, args[4]!, false)
  else if fn.isConstOf ``dite && args.size == 5 then some (unwrapEqTrue args[1]!, args[3]!, args[4]!, true)
  else if fn.isConstOf ``cond && args.size == 4 then some (args[1]!, args[2]!, args[3]!, false)
  else none

private def unwrapPropNotEq? (e : Expr) : Option (Expr × Expr) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf ``Ne && args.size == 3 then some (args[1]!, args[2]!)
  else if fn.isConstOf ``Not && args.size == 1 then
    let inner := args[0]!.consumeMData
    if inner.getAppFn.consumeMData.isConstOf ``Eq && inner.getAppArgs.size == 3 then some (inner.getAppArgs[1]!, inner.getAppArgs[2]!)
    else none
  else none

private def outerCondEq (c : SqlMatchCtx) (sc lc : Expr) : Nat → Bool
  | 0 => false
  | f + 1 =>
      let sc := (peelValWrap sc).consumeMData
      let lc := (peelValWrap lc).consumeMData
      if outerExprEq c 0 sc lc 512 then true
      else
        let sFn := sc.getAppFn.consumeMData; let sArgs := sc.getAppArgs
        let lFn := lc.getAppFn.consumeMData; let lArgs := lc.getAppArgs
        if sFn.isConstOf ``Bool.and && sArgs.size == 2 && lFn.isConstOf ``And && lArgs.size == 2 then
          outerCondEq c sArgs[0]! lArgs[0]! f && outerCondEq c sArgs[1]! lArgs[1]! f
        else if sFn.isConstOf ``Bool.or && sArgs.size == 2 && lFn.isConstOf ``Or && lArgs.size == 2 then
          outerCondEq c sArgs[0]! lArgs[0]! f && outerCondEq c sArgs[1]! lArgs[1]! f
        else if sFn.isConstOf ``Bool.not && sArgs.size == 1 && lFn.isConstOf ``Not && lArgs.size == 1 then
          outerCondEq c sArgs[0]! lArgs[0]! f
        else if sFn.isConstOf ``BEq.beq && sArgs.size == 4 && lFn.isConstOf ``Eq && lArgs.size == 3 then
          outerExprEq c 0 sArgs[2]! lArgs[1]! 512 && outerExprEq c 0 sArgs[3]! lArgs[2]! 512
        else if sFn.isConstOf ``bne && sArgs.size == 4 then
          match unwrapPropNotEq? lc with
          | some (a, b) => outerExprEq c 0 sArgs[2]! a 512 && outerExprEq c 0 sArgs[3]! b 512
          | none => false
        else if let some p := extractDecideInner? sc then
          outerExprEq c 0 p lc 512
        else false

private def extractSnapTableList? (c : SqlMatchCtx) (e : Expr) : Option String :=
  match c.snapLevel? with
  | none => none
  | some sLvl =>
      match fieldProjName? c.env e with
      | some (.bvar j, tbl) => if j < c.leanDepth && c.leanDepth - 1 - j == sLvl then some tbl else none
      | _ => none

private def matchRowCol (c : SqlMatchCtx) (qual? : Option String) (col : String) (eLean : Expr) : Bool :=
  match fieldProjName? c.env eLean with
  | some (.bvar j, fld) =>
      fld == col && j < c.leanDepth &&
      let lvl := c.leanDepth - 1 - j
      c.rowScopes.any fun (q?, rLvl) => rLvl == lvl && (qual?.isNone || q? == qual?)
  | _ => false

private def extractLeanBinCmp? (e : Expr) (fuel : Nat := 4) : Option (Name × Expr × Expr) :=
  match fuel with
  | 0 => none
  | f + 1 =>
      let e := (peelValWrap e).consumeMData
      let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
      if fn.isConstOf ``BEq.beq && args.size == 4 then some (`eq, args[2]!, args[3]!)
      else if fn.isConstOf ``bne && args.size == 4 then some (`ne, args[2]!, args[3]!)
      else if fn.isConstOf ``Bool.not && args.size == 1 then
        match extractLeanBinCmp? args[0]! f with
        | some (`eq, a, b) => some (`ne, a, b)
        | _ => none
      else if let some p := extractDecideInner? e then
        let p := p.consumeMData; let pfn := p.getAppFn.consumeMData; let pargs := p.getAppArgs
        if pfn.isConstOf ``Eq && pargs.size == 3 then some (`eq, pargs[1]!, pargs[2]!)
        else if pfn.isConstOf ``Ne && pargs.size == 3 then some (`ne, pargs[1]!, pargs[2]!)
        else if pfn.isConstOf ``LT.lt && pargs.size == 4 then some (`lt, pargs[2]!, pargs[3]!)
        else if pfn.isConstOf ``LE.le && pargs.size == 4 then some (`le, pargs[2]!, pargs[3]!)
        else if pfn.isConstOf ``GT.gt && pargs.size == 4 then some (`gt, pargs[2]!, pargs[3]!)
        else if pfn.isConstOf ``GE.ge && pargs.size == 4 then some (`ge, pargs[2]!, pargs[3]!)
        else none
      else none

private def extractLeanArith? (e : Expr) : Option (Name × Expr × Expr) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  if fn.isConstOf ``HAdd.hAdd && args.size == 6 then some (`add, args[4]!, args[5]!)
  else if fn.isConstOf ``HSub.hSub && args.size == 6 then some (`sub, args[4]!, args[5]!)
  else if fn.isConstOf ``HMul.hMul && args.size == 6 then some (`mul, args[4]!, args[5]!)
  else if (fn.isConstOf ``Nat.add || fn.isConstOf ``Int.add) && args.size == 2 then some (`add, args[0]!, args[1]!)
  else if (fn.isConstOf ``Nat.sub || fn.isConstOf ``Int.sub) && args.size == 2 then some (`sub, args[0]!, args[1]!)
  else if (fn.isConstOf ``Nat.mul || fn.isConstOf ``Int.mul) && args.size == 2 then some (`mul, args[0]!, args[1]!)
  else none

private def isCasesOrMatchName : Name → Bool
  | .str _ s => s == "casesOn" || s.startsWith "match_"
  | _ => false

private def findTrailingLamsStart (args : Array Expr) : Nat → Nat
  | 0 => 0
  | i + 1 => if args[i]!.consumeMData.isLambda then findTrailingLamsStart args i else i + 1

private def extractCasesCall? (e : Expr) : Option (Expr × Array Expr) :=
  let e := (peelValWrap e).consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  match fn with
  | .const nm _ =>
      if !isCasesOrMatchName nm then none
      else if nm == ``Option.casesOn && args.size == 5 then some (args[2]!, #[args[3]!, args[4]!])
      else if args.size >= 3 then
        let i := findTrailingLamsStart args args.size
        if i >= 1 && i < args.size then some (args[i - 1]!, args.extract i args.size) else none
      else none
  | _ => none

private def peelSharedLams (c : SqlMatchCtx) (a b : Expr) : Nat → SqlMatchCtx × Expr × Expr
  | 0 => (c, a, b)
  | r + 1 => match a.consumeMData, b.consumeMData with
      | .lam _ _ ab _, .lam _ _ bb _ => peelSharedLams c.pushSharedBinder ab bb r
      | a', b' => (c, a', b')

private def extractStrPred2? (qedNm leanNm : Name) (lFn : Expr) (lArgs : Array Expr) : Option (Expr × Expr) :=
  if lFn.isConstOf qedNm && lArgs.size == 2 then some (lArgs[0]!, lArgs[1]!)
  else if lFn.isConstOf leanNm && lArgs.size >= 3 then some (lArgs[lArgs.size - 3]!, lArgs[lArgs.size - 2]!)
  else if lFn.isConstOf leanNm && lArgs.size == 2 then some (lArgs[0]!, lArgs[1]!)
  else none

private def sqlOrdBinOp? : Name → Option (Name × Name)
  | `Qed.Server.Db.SqlBinOp.lt => some (`lt, `gt) | `Qed.Server.Db.SqlBinOp.le => some (`le, `ge)
  | `Qed.Server.Db.SqlBinOp.gt => some (`gt, `lt) | `Qed.Server.Db.SqlBinOp.ge => some (`ge, `le)
  | _ => none

private def sqlArithBinOp? : Name → Option Name
  | `Qed.Server.Db.SqlBinOp.add => some `add | `Qed.Server.Db.SqlBinOp.sub => some `sub | `Qed.Server.Db.SqlBinOp.mul => some `mul | _ => none

private def sqlExprMatchesLean (c : SqlMatchCtx) (sqlE leanE : Expr) : Nat → Bool
  | 0 => false
  | f + 1 =>
      let sqlE := sqlE.consumeMData.headBeta
      let leanE := (peelValWrap leanE).consumeMData.headBeta
      if let .letE _ _ v b _ := sqlE then
        sqlExprMatchesLean c (b.instantiate1 v) leanE f
      else if let .letE _ _ v b _ := leanE then
        sqlExprMatchesLean c sqlE (b.instantiate1 v) f
      else
        let sFn := sqlE.getAppFn.consumeMData; let sArgs := sqlE.getAppArgs
        let lFn := leanE.getAppFn.consumeMData; let lArgs := leanE.getAppArgs
        match sFn with
        | .const `Qed.Server.Db.SqlExpr.litTrue _ => extractBoolLit? leanE == some true
        | .const `Qed.Server.Db.SqlExpr.litFalse _ => extractBoolLit? leanE == some false
        | .const `Qed.Server.Db.SqlExpr.col _ =>
            sArgs.size == 1 && (extractSqlIdent? sArgs[0]!).any (matchRowCol c none · leanE)
        | .const `Qed.Server.Db.SqlExpr.qualCol _ =>
            sArgs.size == 2 && match extractSqlIdent? sArgs[0]!, extractSqlIdent? sArgs[1]! with
              | some q, some col => matchRowCol c (some q) col leanE | _, _ => false
        | .const `Qed.Server.Db.SqlExpr.strLen _ =>
            sArgs.size == 1 && lArgs.size == 1 &&
            (lFn.isConstOf ``String.length || lFn.isConstOf ``ByteArray.size || lFn.isConstOf ``String.utf8ByteSize) &&
            sqlExprMatchesLean c sArgs[0]! lArgs[0]! f
        | .const `Qed.Server.Db.SqlExpr.param _ =>
            sArgs.size == 1 && (unwrapSqlParamVal? sArgs[0]!).any fun v => outerExprEq c 0 v leanE 512
        | .const `Qed.Server.Db.SqlExpr.not _ =>
            sArgs.size == 1 && lArgs.size == 1 && (lFn.isConstOf ``Bool.not || lFn.isConstOf ``not) &&
            sqlExprMatchesLean c sArgs[0]! lArgs[0]! f
        | .const `Qed.Server.Db.SqlExpr.isNull _ =>
            sArgs.size == 1 &&
            ((lFn.isConstOf ``Option.isNone && lArgs.size == 2 && sqlExprMatchesLean c sArgs[0]! lArgs[1]! f) ||
             match extractLeanBinCmp? leanE with
             | some (`eq, a, b) =>
                 (isOptNoneExpr b && sqlExprMatchesLean c sArgs[0]! a f) ||
                 (isOptNoneExpr a && sqlExprMatchesLean c sArgs[0]! b f)
             | _ => false)
        | .const `Qed.Server.Db.SqlExpr.isNotNull _ =>
            sArgs.size == 1 &&
            ((lFn.isConstOf ``Option.isSome && lArgs.size == 2 && sqlExprMatchesLean c sArgs[0]! lArgs[1]! f) ||
             match extractLeanBinCmp? leanE with
             | some (`ne, a, b) =>
                 (isOptNoneExpr b && sqlExprMatchesLean c sArgs[0]! a f) ||
                 (isOptNoneExpr a && sqlExprMatchesLean c sArgs[0]! b f)
             | _ => false)
        | .const `Qed.Server.Db.SqlExpr.startsWith _ =>
            sArgs.size == 2 && (extractStrPred2? `Qed.Str.startsWith ``String.startsWith lFn lArgs).any fun (a, b) =>
              sqlExprMatchesLean c sArgs[0]! a f && sqlExprMatchesLean c sArgs[1]! b f
        | .const `Qed.Server.Db.SqlExpr.contains _ =>
            sArgs.size == 2 && (extractStrPred2? `Qed.Str.contains `String.contains lFn lArgs).any fun (a, b) =>
              sqlExprMatchesLean c sArgs[0]! a f && sqlExprMatchesLean c sArgs[1]! b f
        | .const `Qed.Server.Db.SqlExpr.like _ =>
            sArgs.size == 2 &&
            match extractStrPred2? `Qed.Str.endsWith ``String.endsWith lFn lArgs with
            | some (a, b) =>
                let p := sArgs[1]!.consumeMData
                p.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.param && p.getAppArgs.size == 1 &&
                let ew := p.getAppArgs[0]!.consumeMData
                ew.getAppFn.consumeMData.isConstOf `Qed.Server.Db.endsWithLikeVal && ew.getAppArgs.size == 1 &&
                sqlExprMatchesLean c sArgs[0]! a f && outerExprEq c 0 ew.getAppArgs[0]! b 512
            | none => lFn.isConstOf `Qed.Str.like && lArgs.size == 2 && sqlExprMatchesLean c sArgs[0]! lArgs[0]! f && sqlExprMatchesLean c sArgs[1]! lArgs[1]! f
        | .const `Qed.Server.Db.SqlExpr.inList _ =>
            sArgs.size == 2 && (unwrapToSqlList? sArgs[1]!).any fun sqlXs =>
              let checkPair (elem xs : Expr) : Bool := sqlExprMatchesLean c sArgs[0]! elem f && outerExprEq c 0 sqlXs xs 512
              if lFn.isConstOf `Qed.Lang.qedInList && lArgs.size == 4 then checkPair lArgs[2]! lArgs[3]!
              else if lFn.isConstOf `Qed.Lang.QedMem.mem && lArgs.size == 5 then checkPair lArgs[3]! lArgs[4]!
              else if (lFn.isConstOf ``List.contains || lFn.isConstOf ``Array.contains || lFn.isConstOf ``List.elem || lFn.isConstOf ``Array.elem) && lArgs.size >= 4 then
                checkPair lArgs[lArgs.size - 1]! lArgs[lArgs.size - 2]!
              else false
        | .const `Qed.Server.Db.SqlExpr.existsSubquery _ =>
            sArgs.size == 3 && lFn.isConstOf ``List.any && lArgs.size == 3 &&
            match extractSqlIdent? sArgs[0]!, extractSqlIdent? sArgs[1]!, extractSnapTableList? c lArgs[1]!, lArgs[2]!.consumeMData with
            | some subTbl, some al, some leanTbl, .lam _ _ lBody _ =>
                subTbl == leanTbl && sqlExprMatchesLean (c.pushRowScope (some al)) sArgs[2]! lBody f
            | _, _, _, _ => false
        | .const `Qed.Server.Db.sqlEqSome _ =>
            sArgs.size == 5 &&
            let (inSql, optVal, isNe?) := (sArgs[2]!, sArgs[3]!, extractBoolLit? sArgs[4]!)
            match isNe?, extractLeanBinCmp? leanE with
            | some false, some (`eq, a, b) | some true, some (`ne, a, b) =>
                ((unwrapOptSome? a).any (sqlExprMatchesLean c inSql · f) && outerExprEq c 0 optVal b 512) ||
                ((unwrapOptSome? b).any (sqlExprMatchesLean c inSql · f) && outerExprEq c 0 optVal a 512)
            | _, _ => false
        | .const `Qed.Server.Db.SqlExpr.binOp _ =>
            if sArgs.size != 3 then false
            else
              let opNm := sArgs[0]!.consumeMData.constName?
              let (sl, sr) := (sArgs[1]!, sArgs[2]!)
              match opNm with
              | some `Qed.Server.Db.SqlBinOp.and =>
                  lFn.isConstOf ``Bool.and && lArgs.size == 2 &&
                  sqlExprMatchesLean c sl lArgs[0]! f && sqlExprMatchesLean c sr lArgs[1]! f
              | some `Qed.Server.Db.SqlBinOp.or =>
                  if lFn.isConstOf ``Bool.or && lArgs.size == 2 then
                    sqlExprMatchesLean c sl lArgs[0]! f && sqlExprMatchesLean c sr lArgs[1]! f
                  else if let some (lc, lt, le, isDep) := extractBoolIte? leanE then
                    -- Row-dependent `if c then t else e` lowers to `(c AND t) OR (NOT c AND e)`
                    let slF := sl.consumeMData; let srF := sr.consumeMData
                    let checkBranch (sB lB : Expr) : Bool :=
                      if !isDep then sqlExprMatchesLean c sB lB f
                      else match lB.consumeMData with | .lam _ _ b _ => sqlExprMatchesLean c.pushLeanBinder sB b f | _ => false
                    slF.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.binOp && slF.getAppArgs.size == 3 &&
                    slF.getAppArgs[0]!.consumeMData.isConstOf `Qed.Server.Db.SqlBinOp.and &&
                    srF.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.binOp && srF.getAppArgs.size == 3 &&
                    srF.getAppArgs[0]!.consumeMData.isConstOf `Qed.Server.Db.SqlBinOp.and &&
                    let nCond := srF.getAppArgs[1]!.consumeMData
                    nCond.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.not && nCond.getAppArgs.size == 1 &&
                    sqlExprMatchesLean c slF.getAppArgs[1]! lc f &&
                    sqlExprMatchesLean c nCond.getAppArgs[0]! lc f &&
                    checkBranch slF.getAppArgs[2]! lt &&
                    checkBranch srF.getAppArgs[2]! le
                  else if let some (`ne, a, b) := extractLeanBinCmp? leanE then
                    -- Row-dependent `some(a) != b` lowers to `isNull b OR (a != b)`
                    let slF := sl.consumeMData; let srF := sr.consumeMData
                    slF.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.isNull && slF.getAppArgs.size == 1 &&
                    srF.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.binOp && srF.getAppArgs.size == 3 &&
                    srF.getAppArgs[0]!.consumeMData.isConstOf `Qed.Server.Db.SqlBinOp.ne &&
                    (((unwrapOptSome? a).any (sqlExprMatchesLean c srF.getAppArgs[1]! · f) &&
                      sqlExprMatchesLean c srF.getAppArgs[2]! b f && sqlExprMatchesLean c slF.getAppArgs[0]! b f) ||
                     ((unwrapOptSome? b).any (sqlExprMatchesLean c srF.getAppArgs[2]! · f) &&
                      sqlExprMatchesLean c srF.getAppArgs[1]! a f && sqlExprMatchesLean c slF.getAppArgs[0]! a f))
                  else false
              | some `Qed.Server.Db.SqlBinOp.eq =>
                  match extractLeanBinCmp? leanE with
                  | some (`eq, a, b) =>
                      let matchSide (s x : Expr) := sqlExprMatchesLean c s x f || (unwrapOptSome? x).any (sqlExprMatchesLean c s · f)
                      matchSide sl a && matchSide sr b
                  | _ => false
              | some `Qed.Server.Db.SqlBinOp.ne =>
                  match extractLeanBinCmp? leanE with
                  | some (`ne, a, b) => sqlExprMatchesLean c sl a f && sqlExprMatchesLean c sr b f
                  | _ => false
              | some op =>
                  if let some (sameOp, flipOp) := sqlOrdBinOp? op then
                    match extractLeanBinCmp? leanE with
                    | some (lop, a, b) =>
                        (lop == sameOp && sqlExprMatchesLean c sl a f && sqlExprMatchesLean c sr b f) ||
                        (lop == flipOp && sqlExprMatchesLean c sl b f && sqlExprMatchesLean c sr a f)
                    | none => false
                  else if let some arithOp := sqlArithBinOp? op then
                    match extractLeanArith? leanE with
                    | some (lop, a, b) => lop == arithOp && sqlExprMatchesLean c sl a f && sqlExprMatchesLean c sr b f
                    | none => false
                  else false
              | none => false
        | _ =>
            if let some (sc, st, se, sDep) := extractBoolIte? sqlE then
              match extractBoolIte? leanE with
              | some (lc, lt, le, lDep) =>
                  let matchBr (sb lb : Expr) : Bool :=
                    match sDep, lDep with
                    | false, false => sqlExprMatchesLean c sb lb f
                    | false, true => match lb.consumeMData with | .lam _ _ b _ => sqlExprMatchesLean c.pushLeanBinder sb b f | _ => false
                    | true, true =>
                        match sb.consumeMData, lb.consumeMData with
                        | .lam _ _ sb' _, .lam _ _ lb' _ => sqlExprMatchesLean c.pushSharedBinder sb' lb' f | _, _ => false
                    | true, false => false
                  outerCondEq c sc lc 16 && matchBr st lt && matchBr se le
              | none => false
            else if let some (sScrut, sAlts) := extractCasesCall? sqlE then
              match extractCasesCall? leanE with
              | some (lScrut, lAlts) =>
                  sAlts.size == lAlts.size && outerExprEq c 0 sScrut lScrut 512 &&
                  (sAlts.zip lAlts).all fun (sa, la) =>
                    let (cc, a', b') := peelSharedLams c sa la 32
                    sqlExprMatchesLean cc a' b' f
              | none => false
            else false

private def extractRowPredGoal? (dbOwner : Name) (tblName : String) (pExpr : Expr) :
    Option (Bool × Expr × Expr × Nat) :=
  let tblPrefix := dbOwner ++ Name.mkSimple tblName
  let rowInvConst := tblPrefix ++ `RowInv
  let checkInner (isCross : Bool) (depth : Nat) (e : Expr) : Option (Bool × Expr × Expr × Nat) :=
    match e.consumeMData with
    | .forallE _ rowInvTy (.forallE _ predEqTy concl _) _ =>
        let rFn := rowInvTy.consumeMData.getAppFn.consumeMData
        let rArgs := rowInvTy.consumeMData.getAppArgs
        let pEq := predEqTy.consumeMData
        if rFn.isConstOf rowInvConst && rArgs.size == 1 && rArgs[0]!.consumeMData == .bvar 0 &&
           pEq.getAppFn.consumeMData.isConstOf ``Eq && pEq.getAppArgs.size == 3 &&
           extractBoolLit? pEq.getAppArgs[2]! == some true then
          some (isCross, pEq.getAppArgs[1]!.headBeta, concl.consumeMData, depth + 2)
        else none
    | _ => none
  match pExpr.consumeMData with
  | .forallE _ ty1 (.forallE _ ty2 rest _) _ =>
      if ty1.consumeMData.isConstOf (dbOwner ++ `Snap) && ty2.consumeMData.isConstOf tblPrefix then
        checkInner true 2 rest
      else if ty1.consumeMData.isConstOf tblPrefix then
        checkInner false 1 (.forallE `_ ty2 rest .default)
      else none
  | _ => none

private def checkPolicyApp (tblPrefix : Name) (allowedLeaves : Array String) (isCross : Bool)
    (expectedCtx : Expr) (conclDepth : Nat) (expectedRow : Expr) (e : Expr) : Option String :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
  let liftedCtx := expectedCtx.liftLooseBVars 0 conclDepth
  match fn with
  | .const (.str parent leaf) _ =>
      if parent != tblPrefix || !allowedLeaves.contains leaf then none
      else if args.size == 2 && args[0]!.consumeMData == liftedCtx && args[1]!.headBeta.consumeMData == expectedRow then some leaf
      else if isCross && args.size == 3 && args[0]!.consumeMData == .bvar (conclDepth - 1) &&
              args[1]!.consumeMData == liftedCtx && args[2]!.headBeta.consumeMData == expectedRow then some leaf
      else none
  | _ => none

private def collectColReadOrChain (tblPrefix : Name) (isCross : Bool) (expectedCtx : Expr) (conclDepth : Nat)
    (expectedRow : Expr) (e : Expr) : Nat → Option (Array String)
  | 0 => none
  | f + 1 =>
      let e := e.consumeMData
      let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
      if fn.isConstOf ``Or && args.size == 2 then
        match collectColReadOrChain tblPrefix isCross expectedCtx conclDepth expectedRow args[0]! f,
              collectColReadOrChain tblPrefix isCross expectedCtx conclDepth expectedRow args[1]! f with
        | some a, some b => some (a ++ b)
        | _, _ => none
      else
        match fn with
        | .const (.str parent leaf) _ =>
            if parent == tblPrefix && (leaf == "ReadPolicy" || leaf.startsWith "ColReadPolicy_") then
              (checkPolicyApp tblPrefix #[leaf] isCross expectedCtx conclDepth expectedRow e).map (#[·])
            else none
        | _ => none

private def sqlWhereHasTopEqCol (col : String) (sqlW : Expr) : Nat → Bool
  | 0 => false
  | f + 1 =>
      let e := sqlW.consumeMData
      let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
      if fn.isConstOf `Qed.Server.Db.SqlExpr.binOp && args.size == 3 then
        match args[0]!.consumeMData.constName? with
        | some `Qed.Server.Db.SqlBinOp.and => sqlWhereHasTopEqCol col args[1]! f || sqlWhereHasTopEqCol col args[2]! f
        | some `Qed.Server.Db.SqlBinOp.eq =>
            let isTargetCol (x : Expr) :=
              let x := x.consumeMData
              x.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.col && x.getAppArgs.size == 1 && extractSqlIdent? x.getAppArgs[0]! == some col
            let isParam (x : Expr) := x.consumeMData.getAppFn.consumeMData.isConstOf `Qed.Server.Db.SqlExpr.param
            (isTargetCol args[1]! && isParam args[2]!) || (isTargetCol args[2]! && isParam args[1]!)
        | _ => false
      else false

private def mkWhereMatchCtx (env : Environment) (tblName : String) (isCross : Bool) : SqlMatchCtx :=
  if isCross then
    { env, sqlDepth := 0, leanDepth := 3, sqlToLean := #[], rowScopes := #[(some tblName, 1), (none, 1)], snapLevel? := some 0 }
  else
    { env, sqlDepth := 0, leanDepth := 2, sqlToLean := #[], rowScopes := #[(some tblName, 0), (none, 0)], snapLevel? := none }

private def verifyRowInsertPairs (env : Environment) (tblPrefix : Name) (newRow pairsExpr : Expr) : Bool :=
  let fields := Lean.getStructureFields env tblPrefix
  match extractListElems? pairsExpr with
  | none => false
  | some elems =>
      if elems.size != fields.size then false
      else
        let rec go (i : Nat) : Bool :=
          if h : i < elems.size then
            match extractPair? elems[i] with
            | some (colE, valE) =>
                let expectedFld := fields[i]!.toString
                let valOk := match unwrapSqlParamVal? valE with
                  | some v =>
                      match fieldProjName? env v with
                      | some (base, fld) => fld == expectedFld && base == newRow.consumeMData
                      | none => false
                  | none => false
                extractSqlIdent? colE == some expectedFld && valOk && go (i + 1)
            | none => false
          else true
        go 0

private def verifyUpdateSetsMatchNewRow (env : Environment) (tblPrefix : Name) (tblName : String) (isCross : Bool)
    (conclDepth : Nat) (sqlSetsExpr newRowExpr : Expr) : Bool :=
  let fields := Lean.getStructureFields env tblPrefix
  let newRowExpr := newRowExpr.headBeta.consumeMData
  let ctorFn := newRowExpr.getAppFn.consumeMData; let ctorArgs := newRowExpr.getAppArgs
  if !ctorFn.isConstOf (tblPrefix ++ `mk) || ctorArgs.size != fields.size then false
  else
    match extractListElems? sqlSetsExpr with
    | none => false
    | some setElems =>
        let rowBvarIdx := conclDepth - (if isCross then 2 else 1)
        let rowLvl := if isCross then 1 else 0
        let mCtx : SqlMatchCtx := { env, sqlDepth := 0, leanDepth := conclDepth, sqlToLean := #[], rowScopes := #[(some tblName, rowLvl), (none, rowLvl)], snapLevel? := if isCross then some 0 else none }
        let setMap? : Option (Std.HashMap String Expr) := setElems.foldlM (init := {}) fun m se => do
          let (colE, rhsE) ← extractPair? se
          let col ← extractSqlIdent? colE
          return m.insert col rhsE
        match setMap? with
        | none => false
        | some setMap =>
          if setMap.size != setElems.size then false
          else
            let rec checkField (i : Nat) : Bool :=
              if h : i < fields.size then
                let fld := fields[i]!.toString
                let arg := ctorArgs[i]!
                let ok := match setMap[fld]? with
                  | some rhsSql => sqlExprMatchesLean mCtx rhsSql arg 256
                  | none =>
                      match fieldProjName? env arg with
                      | some (.bvar j, f2) => f2 == fld && j == rowBvarIdx
                      | _ => false
                ok && checkField (i + 1)
              else true
            checkField 0

private def verifyDbVerifiedCall (env : Environment) (declName modName fnName : Name) (args : Array Expr) : Except String Unit := do
  let err {α : Type} (msg : String) : Except String α := throw s!"rls gate: invalid `{fnName}` call in `{declName}` ({modName}): {msg}"
  let requireCfg (cfgE : Expr) : Except String Name :=
    match extractDbConfigOwner? env cfgE with
    | some dbOwner => .ok dbOwner
    | none => err "`cfg` must be `<Db>.config` from a verified `database`"
  let requireAuthCtx (authE : Expr) : Except String Expr :=
    match extractAuthCtx? authE with
    | some ctxE => .ok ctxE
    | none => err "`auth` must be `ctx.auth` from an authentic `RequestCtx`"
  let checkSimpleSelectPolicy (dbOwner : Name) (tblName : String) (sqlW pExpr ctxE : Expr) (allowedPols : Array String) : Except String Unit := do
    let tblPrefix := dbOwner ++ Name.mkSimple tblName
    let some (isCross, predBody, concl, conclDepth) := extractRowPredGoal? dbOwner tblName pExpr
      | err s!"policy proof obligation for `{tblName}` does not match verified `RowInv → where → Policy` shape"
    let rowBvar := Expr.bvar (conclDepth - (if isCross then 2 else 1))
    unless (checkPolicyApp tblPrefix allowedPols isCross ctxE conclDepth rowBvar concl).isSome do
      err s!"policy proof for `{tblName}` must conclude one of {allowedPols.toList} for the same `ctx` as `auth`"
    unless sqlExprMatchesLean (mkWhereMatchCtx env tblName isCross) sqlW predBody 512 do
      err s!"SQL `WHERE` predicate on `{tblName}` does not match the Lean policy proof predicate"
  let checkSimpleQueryOp (expArity pIdx cfgIdx qIdx authIdx : Nat) (qCtor : Name) (qArity tblIdx whereIdx : Nat) (allowedPols : Array String) : Except String Unit := do
    if args.size != expArity then err s!"expected {expArity} arguments, got {args.size}"
    let dbOwner ← requireCfg args[cfgIdx]!
    let ctxE ← requireAuthCtx args[authIdx]!
    let q := args[qIdx]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
    unless qFn.isConstOf qCtor && qArgs.size == qArity do err s!"expected `{qCtor}`"
    let some tblName := extractSqlIdent? qArgs[tblIdx]! | err "expected static table identifier"
    checkSimpleSelectPolicy dbOwner tblName qArgs[whereIdx]! args[pIdx]! ctxE allowedPols
  match fnName with
  | `Qed.Server.Db.dbRunRows | `Qed.Server.Db.dbRunOneRow =>
      if args.size != 18 then err s!"expected 18 arguments, got {args.size}"
      let dbOwner ← requireCfg args[5]!
      let ctxE ← requireAuthCtx args[17]!
      let q := args[6]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
      if qFn.isConstOf `Qed.Server.Db.SqlQuery.select && qArgs.size == 6 then
        let some tblName := extractSqlIdent? qArgs[0]! | err "expected static table identifier in `SqlQuery.select`"
        checkSimpleSelectPolicy dbOwner tblName qArgs[2]! args[4]! ctxE #["ReadPolicy"]
      else if qFn.isConstOf `Qed.Server.Db.SqlQuery.update && qArgs.size == 4 then
        let some tblName := extractSqlIdent? qArgs[0]! | err "expected static table identifier in `SqlQuery.update`"
        let tblPrefix := dbOwner ++ Name.mkSimple tblName
        let pAll := args[4]!.consumeMData
        unless pAll.getAppFn.consumeMData.isConstOf ``And && pAll.getAppArgs.size == 2 do
          err s!"update policy obligation on `{tblName}` must bundle policy, RowInv, and TransInv proofs"
        let (polP, restP) := (pAll.getAppArgs[0]!.consumeMData, pAll.getAppArgs[1]!.consumeMData)
        unless restP.getAppFn.consumeMData.isConstOf ``And && restP.getAppArgs.size == 2 do
          err s!"update obligation on `{tblName}` missing RowInv/TransInv proofs"
        let (invP, transP) := (restP.getAppArgs[0]!.consumeMData, restP.getAppArgs[1]!.consumeMData)
        let some (isCross, invPred, invConcl, invDepth) := extractRowPredGoal? dbOwner tblName invP
          | err s!"update RowInv obligation on `{tblName}` malformed"
        unless invConcl.getAppFn.consumeMData.isConstOf (tblPrefix ++ `RowInv) && invConcl.getAppArgs.size == 1 do
          err s!"update RowInv obligation on `{tblName}` must conclude `{tblPrefix}.RowInv`"
        let newRowE := invConcl.getAppArgs[0]!.headBeta
        unless sqlExprMatchesLean (mkWhereMatchCtx env tblName isCross) qArgs[2]! invPred 512 do
          err s!"SQL `WHERE` predicate on `update {tblName}` does not match Lean proof predicate"
        unless verifyUpdateSetsMatchNewRow env tblPrefix tblName isCross invDepth qArgs[1]! newRowE do
          err s!"SQL `SET` assignments on `update {tblName}` do not match verified post-update row expression"
        let rowBvar := Expr.bvar (invDepth - (if isCross then 2 else 1))
        let some (tCross, tPred, tConcl, tDepth) := extractRowPredGoal? dbOwner tblName transP
          | err s!"update TransInv obligation on `{tblName}` malformed"
        unless tCross == isCross && tDepth == invDepth && tPred == invPred &&
               tConcl.getAppFn.consumeMData.isConstOf (tblPrefix ++ `TransInv) && tConcl.getAppArgs.size == 2 &&
               tConcl.getAppArgs[0]!.consumeMData == rowBvar && tConcl.getAppArgs[1]!.headBeta == newRowE do
          err s!"update TransInv obligation on `{tblName}` does not match row/set expression"
        if polP.getAppFn.consumeMData.isConstOf ``And && polP.getAppArgs.size == 2 then
          -- Single-state update policy: both old row and new row satisfy UpdatePolicy
          let some (c1, p1, k1, d1) := extractRowPredGoal? dbOwner tblName polP.getAppArgs[0]!
            | err s!"single-state update old-row policy obligation on `{tblName}` malformed"
          let some (c2, p2, k2, d2) := extractRowPredGoal? dbOwner tblName polP.getAppArgs[1]!
            | err s!"single-state update new-row policy obligation on `{tblName}` malformed"
          unless c1 == isCross && c2 == isCross && d1 == invDepth && d2 == invDepth && p1 == invPred && p2 == invPred &&
                 (checkPolicyApp tblPrefix #["UpdatePolicy"] isCross ctxE invDepth rowBvar k1).isSome &&
                 (checkPolicyApp tblPrefix #["UpdatePolicy"] isCross ctxE invDepth newRowE k2.headBeta).isSome do
            err s!"single-state update policy on `{tblName}` must prove `UpdatePolicy` for both old and new rows with matching `ctx`"
        else
          -- Two-state update policy: UpdatePolicy [snap] ctx oldRow newRow
          let some (c1, p1, k1, d1) := extractRowPredGoal? dbOwner tblName polP
            | err s!"two-state update policy obligation on `{tblName}` malformed"
          let liftedCtx := ctxE.liftLooseBVars 0 invDepth
          let kFn := k1.getAppFn.consumeMData; let kArgs := k1.getAppArgs
          let okTwo := c1 == isCross && d1 == invDepth && p1 == invPred && kFn.isConstOf (tblPrefix ++ `UpdatePolicy) &&
            ((!isCross && kArgs.size == 3 && kArgs[0]!.consumeMData == liftedCtx && kArgs[1]!.consumeMData == rowBvar && kArgs[2]!.headBeta == newRowE) ||
             (isCross && kArgs.size == 4 && kArgs[0]!.consumeMData == .bvar (invDepth - 1) && kArgs[1]!.consumeMData == liftedCtx && kArgs[2]!.consumeMData == rowBvar && kArgs[3]!.headBeta == newRowE))
          unless okTwo do err s!"two-state update policy on `{tblName}` must prove `UpdatePolicy` for `(oldRow, newRow)` with matching `ctx`"
      else err "expected `SqlQuery.select` or `SqlQuery.update`"
  | `Qed.Server.Db.dbSelectProj | `Qed.Server.Db.dbFindOneProj =>
      if args.size != 12 then err s!"expected 12 arguments, got {args.size}"
      let dbOwner ← requireCfg args[5]!
      let ctxE ← requireAuthCtx args[11]!
      let q := args[6]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
      unless qFn.isConstOf `Qed.Server.Db.SqlQuery.select && qArgs.size == 6 do err "expected `SqlQuery.select`"
      let some tblName := extractSqlIdent? qArgs[0]! | err "expected static table identifier"
      let tblPrefix := dbOwner ++ Name.mkSimple tblName
      let some (isCross, predBody, concl, conclDepth) := extractRowPredGoal? dbOwner tblName args[4]!
        | err s!"projected select policy obligation on `{tblName}` malformed"
      unless sqlExprMatchesLean (mkWhereMatchCtx env tblName isCross) qArgs[2]! predBody 512 do
        err s!"SQL `WHERE` predicate on projected select `{tblName}` does not match Lean proof predicate"
      let rowBvar := Expr.bvar (conclDepth - (if isCross then 2 else 1))
      if (checkPolicyApp tblPrefix #["ReadPolicy"] isCross ctxE conclDepth rowBvar concl).isSome then
        pure ()
      else if (checkPolicyApp tblPrefix #["ReadMetaPolicy"] isCross ctxE conclDepth rowBvar concl).isSome then
        unless qArgs[1]!.consumeMData.isConstOf (tblPrefix ++ `metaColumns) do
          err s!"`ReadMetaPolicy` on `{tblName}` may only select `{tblPrefix}.metaColumns`"
      else
        let some polLeaves := collectColReadOrChain tblPrefix isCross ctxE conclDepth rowBvar concl 32
          | err s!"projected select on `{tblName}` must prove `ReadPolicy`, `ReadMetaPolicy`, or a verified `ColReadPolicy`"
        let some colExprs := extractListElems? qArgs[1]! | err "expected static column list in projected select"
        let some colNames := colExprs.mapM extractSqlIdent? | err "expected static column identifiers in projected select"
        for leaf in polLeaves do
          if leaf != "ReadPolicy" then
            let some allowedCols := extractStrListFromConst? env (tblPrefix ++ Name.mkSimple s!"{leaf}_cols")
              | err s!"missing column metadata for `{tblPrefix}.{leaf}`"
            for cn in colNames do
              unless allowedCols.contains cn do
                err s!"column `{cn}` is not authorized by `{tblPrefix}.{leaf}`"
            let byCols := (extractStrListFromConst? env (tblPrefix ++ Name.mkSimple s!"{leaf}_byCols")).getD #[]
            if !byCols.isEmpty then
              unless fnName == `Qed.Server.Db.dbFindOneProj &&
                     (extractOpt? qArgs[4]!).any (fun lim? => lim?.any (fun l => extractNatLit? l == some 1)) do
                err s!"`{tblPrefix}.{leaf}` with `by` columns requires `findOne` (`limit = some 1`)"
              for bc in byCols do
                unless sqlWhereHasTopEqCol bc qArgs[2]! 64 do
                  err s!"`{tblPrefix}.{leaf}` requires top-level equality filter on `{bc}`"
  | `Qed.Server.Db.dbCount =>
      checkSimpleQueryOp 9 3 4 5 8 `Qed.Server.Db.SqlQuery.count 2 0 1 #["CountPolicy", "ReadPolicy"]
  | `Qed.Server.Db.dbSumNat | `Qed.Server.Db.dbSumInt =>
      checkSimpleQueryOp 9 3 4 5 8 `Qed.Server.Db.SqlQuery.aggregate 4 1 3 #["ReadPolicy"]
  | `Qed.Server.Db.dbAggOpt =>
      checkSimpleQueryOp 13 6 7 8 12 `Qed.Server.Db.SqlQuery.aggregate 4 1 3 #["ReadPolicy"]
  | `Qed.Server.Db.dbDelete =>
      checkSimpleQueryOp 9 3 4 5 8 `Qed.Server.Db.SqlQuery.delete 3 0 1 #["DeletePolicy"]
  | `Qed.Server.Db.dbInsert | `Qed.Server.Db.dbInsertOrIgnore =>
      let isIgn := fnName == `Qed.Server.Db.dbInsertOrIgnore
      let expArity := if isIgn then 14 else 15
      if args.size != expArity then err s!"expected {expArity} arguments, got {args.size}"
      let dbOwner ← requireCfg args[5]!
      let ctxE ← requireAuthCtx args[expArity - 1]!
      let q := args[6]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
      let (tblName, pairsE, guardOptE) ←
        if !isIgn && qFn.isConstOf `Qed.Server.Db.SqlQuery.insert && qArgs.size == 5 then
          let some tn := extractSqlIdent? qArgs[0]! | err "expected static table identifier in `SqlQuery.insert`"
          pure (tn, qArgs[1]!, qArgs[3]!)
        else if isIgn && qFn.isConstOf `Qed.Server.Db.SqlQuery.insertOrIgnore && qArgs.size == 6 then
          let some tn := extractSqlIdent? qArgs[0]! | err "expected static table identifier in `SqlQuery.insertOrIgnore`"
          pure (tn, qArgs[1]!, qArgs[4]!)
        else err "unexpected `SqlQuery` constructor for insert"
      let tblPrefix := dbOwner ++ Name.mkSimple tblName
      let newRowE := args[7]!.consumeMData
      unless args[8]!.consumeMData.isConstOf (tblPrefix ++ `RowInv) do
        err s!"insert `RowInv` must be `{tblPrefix}.RowInv`"
      unless verifyRowInsertPairs env tblPrefix newRowE pairsE do
        err s!"SQL insert column pairs on `{tblName}` do not match verified `newRow`"
      let some guard? := extractOpt? guardOptE | err "expected static `Option` insert guard"
      let pExpr := args[4]!.consumeMData
      match guard? with
      | none =>
          let okDirect :=
            (checkPolicyApp tblPrefix #["InsertPolicy"] false ctxE 0 newRowE pExpr).isSome ||
            match pExpr with
            | .forallE _ ty body _ =>
                ty.consumeMData.isConstOf (dbOwner ++ `Snap) &&
                (checkPolicyApp tblPrefix #["InsertPolicy"] true ctxE 1 (newRowE.liftLooseBVars 0 1) body).isSome
            | _ => false
          unless okDirect do err s!"unguarded insert on `{tblName}` must directly prove `{tblPrefix}.InsertPolicy` for `ctx` and `newRow`"
      | some guardSql =>
          if !isIgn then
            unless extractBoolLit? args[13]! == some true do
              err s!"guarded `dbInsert` on `{tblName}` must set `requireReturning := true`"
          let checkGuarded (isCross : Bool) (depth : Nat) (e : Expr) : Except String Unit := do
            match e.consumeMData with
            | .forallE _ rowInvTy (.forallE _ predEqTy concl _) _ =>
                let liftedRow := newRowE.liftLooseBVars 0 depth
                let rFn := rowInvTy.consumeMData.getAppFn.consumeMData; let rArgs := rowInvTy.consumeMData.getAppArgs
                let pEq := predEqTy.consumeMData
                unless rFn.isConstOf (tblPrefix ++ `RowInv) && rArgs.size == 1 && rArgs[0]!.consumeMData == liftedRow &&
                       pEq.getAppFn.consumeMData.isConstOf ``Eq && pEq.getAppArgs.size == 3 &&
                       extractBoolLit? pEq.getAppArgs[2]! == some true do
                  err s!"guarded insert proof shape on `{tblName}` malformed"
                let conclDepth := depth + 2
                unless (checkPolicyApp tblPrefix #["InsertPolicy"] isCross ctxE conclDepth (newRowE.liftLooseBVars 0 conclDepth) concl).isSome do
                  err s!"guarded insert on `{tblName}` must conclude `{tblPrefix}.InsertPolicy` for matching `ctx` and `newRow`"
                let mCtx : SqlMatchCtx := { env, sqlDepth := 0, leanDepth := depth + 1, sqlToLean := #[], rowScopes := #[], snapLevel? := if isCross then some 0 else none }
                unless sqlExprMatchesLean mCtx guardSql pEq.getAppArgs[1]!.headBeta 512 do
                  err s!"SQL insert guard on `{tblName}` does not match Lean proof predicate"
            | _ => err s!"guarded insert proof shape on `{tblName}` malformed"
          match pExpr with
          | .forallE _ ty body _ =>
              if ty.consumeMData.isConstOf (dbOwner ++ `Snap) then checkGuarded true 1 body
              else checkGuarded false 0 pExpr
          | _ => err s!"guarded insert proof shape on `{tblName}` malformed"
  | `Qed.Server.Db.dbUpsert =>
      if args.size != 24 then err s!"expected 24 arguments, got {args.size}"
      let dbOwner ← requireCfg args[4]!
      let q := args[5]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
      unless qFn.isConstOf `Qed.Server.Db.SqlQuery.upsert && qArgs.size == 6 do err "expected `SqlQuery.upsert`"
      let some tblName := extractSqlIdent? qArgs[0]! | err "expected static table identifier in `SqlQuery.upsert`"
      let tblPrefix := dbOwner ++ Name.mkSimple tblName
      unless args[8]!.consumeMData.isConstOf (tblPrefix ++ `RowInv) && args[11]!.consumeMData.isConstOf (tblPrefix ++ `TransInv) do
        err s!"upsert `RowInv`/`TransInv` must match `{tblPrefix}`"
      let insArg := args[13]!.consumeMData
      let okInsPol := insArg.isConstOf (tblPrefix ++ `InsertPolicy) ||
        match insArg with
        | .lam _ _ (.lam _ _ (.forallE _ snapTy body _) _) _ =>
            snapTy.consumeMData.isConstOf (dbOwner ++ `Snap) &&
            body.consumeMData.getAppFn.consumeMData.isConstOf (tblPrefix ++ `InsertPolicy) &&
            body.consumeMData.getAppArgs == #[.bvar 0, .bvar 2, .bvar 1]
        | _ => false
      unless okInsPol && args[14]!.consumeMData.isConstOf (tblPrefix ++ `UpdatePolicy) do
        err s!"upsert policies must be `{tblPrefix}.InsertPolicy` and `{tblPrefix}.UpdatePolicy`"
      unless verifyRowInsertPairs env tblPrefix args[6]! qArgs[1]! do
        err s!"upsert SQL insert pairs on `{tblName}` do not match verified `newRow`"
      let some cwOpt := extractOpt? qArgs[4]! | err "expected static `Option` conflictWhere in `SqlQuery.upsert`"
      let cwSql := cwOpt.getD (mkConst `Qed.Server.Db.SqlExpr.litTrue)
      match args[12]!.consumeMData with
      | .lam _ _ predBody _ =>
          let mCtx : SqlMatchCtx := { env, sqlDepth := 0, leanDepth := 1, sqlToLean := #[], rowScopes := #[(some tblName, 0), (none, 0)], snapLevel? := none }
          unless sqlExprMatchesLean mCtx cwSql predBody 512 do
            err s!"upsert SQL `conflictWhere` on `{tblName}` does not match Lean `conflictPred`"
      | _ => err s!"upsert `conflictPred` on `{tblName}` must be a row lambda"
  | `Qed.Server.Db.dbJoinSelect =>
      if args.size != 29 then err s!"expected 29 arguments, got {args.size}"
      let dbOwner ← requireCfg args[7]!
      let q := args[8]!.consumeMData; let qFn := q.getAppFn.consumeMData; let qArgs := q.getAppArgs
      unless qFn.isConstOf `Qed.Server.Db.SqlQuery.joinSelect && qArgs.size == 11 do err "expected `SqlQuery.joinSelect`"
      let some tblL := extractSqlIdent? qArgs[0]! | err "expected static left table identifier in `SqlQuery.joinSelect`"
      let some tblR := extractSqlIdent? qArgs[1]! | err "expected static right table identifier in `SqlQuery.joinSelect`"
      let pfxL := dbOwner ++ Name.mkSimple tblL; let pfxR := dbOwner ++ Name.mkSimple tblR
      unless args[12]!.consumeMData.isConstOf (pfxL ++ `RowInv) && args[15]!.consumeMData.isConstOf (pfxR ++ `RowInv) &&
             args[22]!.consumeMData.isConstOf (pfxL ++ `ReadPolicy) && args[23]!.consumeMData.isConstOf (pfxR ++ `ReadPolicy) do
        err s!"joinSelect RowInv/ReadPolicy arguments do not match `{tblL}` and `{tblR}`"
      match args[18]!.consumeMData, args[19]!.consumeMData with
      | .lam _ _ lPredBody _, .lam _ _ rPredBody _ =>
          let mL : SqlMatchCtx := { env, sqlDepth := 0, leanDepth := 1, sqlToLean := #[], rowScopes := #[(some tblL, 0), (none, 0)] }
          let mR : SqlMatchCtx := { env, sqlDepth := 0, leanDepth := 1, sqlToLean := #[], rowScopes := #[(some tblR, 0), (none, 0)] }
          unless sqlExprMatchesLean mL qArgs[6]! lPredBody 512 do err s!"joinSelect left `WHERE` on `{tblL}` does not match Lean `wherePredL`"
          unless sqlExprMatchesLean mR qArgs[7]! rPredBody 512 do err s!"joinSelect right `WHERE` on `{tblR}` does not match Lean `wherePredR`"
      | _, _ => err "joinSelect `wherePredL` and `wherePredR` must be row lambdas"
  | _ => err "unsupported database runner"

private def verifyServerRlsExpr (env : Environment) (declName modName : Name) (root : Expr) : Except String Unit :=
  let rec go (e : Expr) : Nat → Except String Unit
    | 0 => throw s!"rls gate: expression walk exceeded fuel limit in `{declName}` ({modName})"
    | f + 1 => do
        let e := e.consumeMData
        match e with
        | .const c _ =>
            if isServerRlsForbiddenBase env declName false c then
              throw s!"rls gate: forbidden server/DB/auth primitive `{c}` inside `{declName}` ({modName})"
            if isRestrictedServerConst c then
              throw s!"rls gate: unapplied or partially-applied security primitive `{c}` inside `{declName}` ({modName})"
        | .app _ _ =>
            let fn := e.getAppFn.consumeMData; let args := e.getAppArgs
            match fn with
            | .const c _ =>
                if isServerRlsForbiddenBase env declName false c then
                  throw s!"rls gate: forbidden server/DB/auth primitive `{c}` inside `{declName}` ({modName})"
                if c == `Qed.Server.Db.dbRunChecked || c == `Qed.Server.Db.dbRun then
                  throw s!"rls gate: direct call to `{c}` inside `{declName}` ({modName}) is forbidden outside verified database queries"
                else if c == `Qed.Server.Db.DbConfig.mk then
                  match declName with
                  | .str dbOwner "config" =>
                      unless hasOwnerMarker env dbOwner `_qed_database_marker && env.contains (dbOwner ++ `tables) &&
                             args.size == 8 && extractBoolLit? args[7]! == some false do
                        throw s!"rls gate: `DbConfig.mk` in `{declName}` ({modName}) must be an authentic `database` config"
                  | _ => throw s!"rls gate: `DbConfig.mk` is forbidden outside `<Db>.config` (found in `{declName}` in `{modName}`)"
                else if c == `Qed.Server.ServerJob.mkSystem || c == `Qed.Server.VerifiedJob.mkSystem then
                  let isVer := c == `Qed.Server.VerifiedJob.mkSystem
                  let expectedLeaf := if isVer then "verifiedJobs" else "jobs"
                  let srvNameIdx := if isVer then 2 else 1
                  match declName with
                  | .str srvOwner@(.str _ srvLeaf) leaf =>
                      if leaf != expectedLeaf then
                        throw s!"rls gate: `{c}` is forbidden outside `<Server>.{expectedLeaf}` (found in `{declName}` in `{modName}`)"
                      else unless hasOwnerMarker env srvOwner `_qed_server_marker &&
                             args.size > srvNameIdx && extractStrLit? args[srvNameIdx]! == some srvLeaf do
                        throw s!"rls gate: `{c}` in `{declName}` ({modName}) must match owning server `{srvLeaf}`"
                  | _ => throw s!"rls gate: `{c}` is forbidden outside `<Server>.{expectedLeaf}` (found in `{declName}` in `{modName}`)"
                else if c == `Qed.Server.verifyRouteAuth || isNsPrefix `Qed.Server.RouteAuthSpec c then
                  match declName with
                  | .str srvOwner "httpDispatchM" =>
                      unless hasOwnerMarker env srvOwner `_qed_server_marker do
                        throw s!"rls gate: `{c}` in `{declName}` ({modName}) requires a verified `server`"
                      if isNsPrefix `Qed.Server.RouteAuthSpec c then
                        let secIdx? := match c with
                          | `Qed.Server.RouteAuthSpec.hmacSha256 | `Qed.Server.RouteAuthSpec.stripe => some 2
                          | `Qed.Server.RouteAuthSpec.headerSecret => some 1
                          | `Qed.Server.RouteAuthSpec.bearerSecret => some 0
                          | _ => none
                        match secIdx? with
                        | some idx =>
                            if args.size <= idx || isHardcodedSecretExpr args[idx]! then
                              throw s!"rls gate: `{c}` in `{declName}` ({modName}) forbids hardcoded string literal secrets"
                        | none => pure ()
                  | _ => throw s!"rls gate: `{c}` is forbidden outside `<Server>.httpDispatchM` (found in `{declName}` in `{modName}`)"
                else if c == `Qed.Server.dbRunTx then
                  if args.size != 9 then
                    throw s!"rls gate: partially applied `dbRunTx` in `{declName}` ({modName})"
                  if (extractDbConfigOwner? env args[6]!).isNone then
                    throw s!"rls gate: `dbRunTx` in `{declName}` ({modName}) requires `<Db>.config` from a verified `database`"
                  if (extractAuthCtx? args[8]!).isNone then
                    throw s!"rls gate: `dbRunTx` in `{declName}` ({modName}) requires `ctx.auth` from an authentic `RequestCtx`"
                else if isDbVerifiedOpName c then
                  verifyDbVerifiedCall env declName modName c args
            | _ => go fn f
            for a in args do go a f
        | .lam _ t b _ | .forallE _ t b _ => go t f; go b f
        | .letE _ t v b _ => go t f; go v f; go b f
        | .proj _ _ s => go s f
        | _ => pure ()
  go root 1000000

private def irCallSite (irName modName : Name) (transitive : Bool) : String :=
  s!"{if transitive then "transitively called in IR" else "called"} by `{irName}` in `{modName}`"

private def checkIrCallee (env : Environment) (checkNonFw checkTcPartials : Bool)
    (irName modName : Name) (transitive : Bool) (c : Name) : Except String Unit := do
  if isRuntimeLoopConst c then
    throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop (`{c}`) is {irCallSite irName modName transitive}"
  if checkNonFw && isMutableRefConst c then
    throw s!"kernel gate: mutable reference primitive (`{c}`, Landin's knot) is {irCallSite irName modName transitive} outside framework modules"
  if checkNonFw && checkTcPartials then
    let irOwner := (owningKernelConst? env irName).getD irName
    if isServerRlsForbiddenBase env irOwner transitive c then
      throw s!"rls gate: forbidden server/DB/auth primitive (`{c}`) is {irCallSite irName modName transitive} outside framework modules"
  if checkTcPartials then
    let owner := (owningKernelConst? env c).getD c
    if isForbiddenToolchainPartial env owner then
      throw s!"kernel gate: non-total toolchain `partial` declaration `{owner}` (via `{c}`) is {irCallSite irName modName transitive}"

private def isCompilerCtorIdxImpl (env : Environment) (n : Name) : Bool :=
  match n with
  | .str (.str ind "ctorIdx") "_impl" =>
      match env.find? ind, env.find? n, Compiler.getImplementedBy? env (Name.str ind "ctorIdx") with
      | some (.inductInfo _), some (.defnInfo dv), some impl =>
          let rec peel : Expr → Expr | .lam _ _ b _ => peel b | e => e
          impl == n && match peel dv.value with
            | .app (.app (.const ``getObjTagNat _) ty) (.bvar 0) => match ty.getAppFn with | .const c _ => c == ind | _ => false
            | _ => false
      | _, _, _ => false
  | _ => false

private def verifyUserDecl (env : Environment) (modName n : Name) (ci? : Option ConstantInfo) (checkIr : Bool := true) : Except String Unit := do
  let ownerMod := if !modName.isAnonymous then modName else definingModule env ((owningKernelConst? env n).getD n)
  let isNonFw := !isFrameworkModule ownerMod
  let gate (msg : String) := s!"kernel gate: {msg}"
  if isNonFw && (Lean.isIOUnitInitFn env n || Lean.isIOUnitBuiltinInitFn env n ||
      (Lean.getInitFnNameFor? env n).isSome || (Lean.builtinInitAttr.getParam? env n).isSome) then
    throw (gate s!"`initialize`/`@[init]` declaration `{n}` in `{modName}` is forbidden outside framework modules")
  if (Lean.getExportNameFor? env n).isSome && ownerMod != `Qed.Driver.Runtime then
    throw (gate s!"`@[export]` declaration `{n}` in `{modName}` is forbidden outside `Qed.Driver.Runtime`")
  if let some impl := Compiler.getImplementedBy? env n then
    if !(impl == Name.str n "_impl" && isCompilerCtorIdxImpl env impl) then
      throw (gate s!"`@[implemented_by {impl}]` or `partial def` on `{n}` in `{modName}` is forbidden")
  if let some ci := ci? then
    let isCtorIdxImpl := isCompilerCtorIdxImpl env n
    if ci.isUnsafe && !isCtorIdxImpl then throw (gate s!"`unsafe` declaration `{n}` in `{modName}` is forbidden")
    let isBadClass (c : Name) := forbiddenCustomClass c || (isNonFw && (c == `Qed.Server.MonadServer || c == `Qed.Server.MonadAtomic))
    match unfoldReturnHead env isBadClass ci.type with
    | .error err => throw (gate s!"`{n}` in `{modName}` failed return-type check ({err})")
    | .ok (some rtHead) => if isBadClass rtHead then throw (gate s!"custom `{rtHead}` instance `{n}` in `{modName}` is forbidden")
    | .ok none => pure ()
    let opaqueErr (nm : Name) := gate s!"`partial` or `opaque` declaration `{nm}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"
    match ci with
    | .opaqueInfo _ => if !isLegitOpaque env modName n then throw (opaqueErr n)
    | .defnInfo dv =>
        if dv.safety != .safe && !isTotalCompilerAux env n && !isCtorIdxImpl then
          let opaqueRoot? := match n with | .str root "_unsafe_rec" => if (env.find? root).any (· matches ConstantInfo.opaqueInfo _) then some root else none | _ => none
          throw (opaqueRoot?.elim (gate s!"`partial` or non-safe definition `{n}` in `{modName}` is forbidden") opaqueErr)
        let bad : UInt8 := dv.value.foldConsts 0 fun c acc =>
          if acc == 1 || isWhileLoopConst c then 1 else if isNonFw && acc == 0 && isMutableRefConst c then 2 else acc
        if bad == 1 then throw (gate s!"unbounded `while`/`repeat`/`partial_fixpoint` loop inside `{n}` in `{modName}` is forbidden")
        if bad == 2 then throw (gate s!"mutable reference primitive (Landin's knot) inside `{n}` in `{modName}` is forbidden outside framework modules")
        if isNonFw && !hasMetaReturnType env ci.type && !isServerEffectMatchSplitter env n dv.value then
          verifyServerRlsExpr env n modName dv.value
    | _ => pure ()
  if checkIr then
    let checkTcPartials := isNonFw && !ci?.any (hasMetaReturnType env ·.type)
    for irName in #[n, Name.str n "_redArg"] do
      if let some (.fdecl (body := b) ..) := Lean.IR.findEnvDecl env irName then
        for c in callees b #[] do checkIrCallee env isNonFw checkTcPartials n modName false c
  if Lean.isExtern env n && !isAllowedExternMod modName then
    throw (gate s!"unverified `@[extern]` `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`")

private def isServerOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && (hasOwnerMarker env owner `_qed_server_marker || (env.find? (owner ++ `dispatchM)).any (exprHasConst (· == `Qed.Server.RequestCtx) ·.type))

private def collectExprStrLits : Expr → Std.HashSet String → Std.HashSet String
  | .lit (.strVal s), acc => acc.insert s
  | .app f a, acc | .lam _ f a _, acc | .forallE _ f a _, acc => collectExprStrLits a (collectExprStrLits f acc)
  | .letE _ t v b _, acc => collectExprStrLits b (collectExprStrLits v (collectExprStrLits t acc))
  | .mdata _ e, acc | .proj _ _ e, acc => collectExprStrLits e acc
  | _, acc => acc

private def externalHasSecrets (env : Environment) (owner : Name) : Bool :=
  hasOwnerMarker env owner `_qed_external_marker && match env.find? (owner ++ `secrets) with
    | some (.defnInfo dv) => !(collectExprStrLits dv.value {}).isEmpty | _ => false

private def isBenignEmptyCseThunk (env : Environment) (n : Name) : Bool :=
  match Lean.IR.findEnvDecl env n with
  | some (.fdecl _ xs _ (.vdecl v1 _ (.lit (.num 0)) (.vdecl v2 _ (.fap fn args) (.ret (.var v2')))) _) =>
      xs.isEmpty && v2 == v2' && (fn == `Array.mkEmpty || fn == `ByteArray.emptyWithCapacity) &&
      match args with | #[.erased, .var v1'] | #[.var v1'] => v1 == v1' | _ => false
  | _ => false

private def serverOnlyLeaves : Array String := #[
  "dispatchM", "wsDispatchM", "wsProject", "httpDispatchM", "authHookM", "initState", "runServer",
  "jobs", "verifiedJobs", "jobNames", "readOnlyMethods", "methods", "channels"]
private def dbOnlyLeaves : Array String := #["config", "ensureSchema", "ddl", "rlsDdl", "instSafeIOEnsureSchema", "Snap"]
private def dbMetaLeaves : Array String := #["schema", "decodeRow", "decodeMetaRow", "metaColumns"]
private def secretOwnerMarkers : Array Name := #[`_qed_external_marker, `_qed_service_marker, `_qed_database_marker, `_qed_auth_marker]

def isServerOnlyDeclName (env : Environment) : Name → Bool
  | .anonymous => false | .num p _ => isServerOnlyDeclName env p
  | .str owner s =>
      if s.startsWith "_closed_" then isServerOnlyDeclName env owner && !isBenignEmptyCseThunk env (.str owner s)
      else ((serverOnlyLeaves.contains s || s.endsWith "_step" || s.endsWith "_handler" || s.endsWith "_project") && isServerOwner env owner) ||
        (dbOnlyLeaves.contains s && hasOwnerMarker env owner `_qed_database_marker) ||
        ((dbMetaLeaves.contains s || s.startsWith "ColReadPolicy_") && (hasOwnerMarker env owner `_qed_database_marker || hasOwnerMarker env owner.getPrefix `_qed_database_marker)) ||
        (s == "config" && hasOwnerMarker env owner `_qed_auth_marker) || (s == "spec" && hasOwnerMarker env owner `_qed_deploy_marker) ||
        (s == "baseUrl" && externalHasSecrets env owner) ||
        (s == "secrets" && (isServerOwner env owner || secretOwnerMarkers.any (hasOwnerMarker env owner ·))) ||
        isServerOnlyDeclName env owner

private def serverOnlyModules : Std.HashSet Name := mkNameSet "
  Qed.Server.Prim Qed.Server.Native Qed.Server.Http Qed.Server.Net Qed.Server.Db.PgWire
  Qed.Auth.Oidc Qed.Deploy Qed.Cloud.Compile Qed.Cloud.Proofs Qed.Cloud.GcpApi Qed.Cloud.Executor"
private def serverOnlyDecls : Std.HashSet Name := mkNameSet "
  Qed.Server.ServerEffect Qed.Server.execExternalRaw Qed.Server.MonadServer.exec Qed.Server.MonadServer.httpCall
  Qed.Server.MonadServer.dbExec Qed.Server.MonadServer.dbExecDdl Qed.Server.MonadServer.dbTxBegin
  Qed.Server.MonadServer.dbTxExec Qed.Server.MonadServer.dbTxCommit Qed.Server.MonadServer.dbTxRollback
  Qed.Server.MonadServer.setCookie Qed.Server.MonadServer.sendSse Qed.Server.MonadServer.readEnv
  Qed.Server.MonadServer.nowMs Qed.Server.MonadServer.randomHex Qed.Server.MonadServer.randomBytes
  Qed.Server.MonadServer.hmacSha256 Qed.Server.MonadServer.sha256 Qed.Server.MonadServer.constEq
  Qed.Server.MonadServer.aeadEncrypt Qed.Server.MonadServer.aeadDecrypt Qed.Server.MonadServer.wsBroadcast
  Qed.Server.flushWsEmits Qed.Server.MonadAtomic.runAtomic Qed.Server.MonadAtomic.runAtomicRead
  Qed.Server.Webhook.postJson Qed.Server.Webhook.postBytes Qed.Crypto.hmacSha256 Qed.Crypto.hmacSha256Hex
  Qed.Crypto.constEq Qed.Crypto.sha256 Qed.Crypto.sha256Hex Qed.Time.nowMs Qed.Time.nowSec
  Qed.Random.hex Qed.Random.bytes Qed.Random.uuid"

def clientLeakReason? (env : Environment) (n : Name) : Option String :=
  let modName := definingModule env n
  if serverOnlyModules.contains modName then some s!"client bundle leak gate: server runtime primitive `{n}` (`{modName}`) cannot be bundled into client JavaScript"
  else if serverOnlyDecls.contains n || n.getPrefix == `Qed.Server.ServerEffect then some s!"client bundle leak gate: server I/O or state primitive `{n}` cannot be bundled into client JavaScript"
  else if isServerOnlyDeclName env n then some s!"client bundle leak gate: server secret/state/handler `{n}` cannot be bundled into client JavaScript"
  else none

def verifyNoServerLeakInClient (env : Environment) (reachable : Array Name) : Except String Unit := do
  for n in reachable do if let some err := clientLeakReason? env n then throw err

private inductive DfsMode where
  | partials (declName : Name) | mutRefs (declName : Name) | axioms (declName : Name)
  | kernel (csimpRepls : Std.HashMap Name (Array Name)) (checkLeak : Bool)

private def envDfsAux (mode : DfsMode) (env : Environment) :
    Nat → Std.HashSet Name → Array Name → Option ConstantInfo → Std.HashSet String → Except String (Std.HashSet Name × Std.HashSet String)
  | fuel, visited, stack, firstCi?, strLits =>
      if stack.isEmpty then .ok (visited, strLits)
      else
        let n := stack.back!; let stack := stack.pop
        match fuel with
        | 0 =>
            let pfx := match mode with
              | .partials d => s!"kernel gate: toolchain totality check for `{d}`" | .mutRefs d => s!"kernel gate: mutable-reference check for `{d}`"
              | .axioms d => s!"kernel gate: axiom check for `{d}`" | .kernel _ lk => if lk then "client bundle leak gate: kernel expression check" else "kernel gate: reachability closure"
            .error s!"{pfx} exceeded fuel limit while inspecting `{n}`"
        | fuel + 1 =>
            if firstCi?.isNone && visited.contains n then envDfsAux mode env fuel visited stack none strLits
            else
              let ci? := firstCi?.orElse fun _ => env.find? n
              match mode with
              | .partials d =>
                  if isForbiddenToolchainPartial env n then .error s!"kernel gate: `{d}` depends on non-total toolchain `partial` declaration `{n}`"
                  else let visited := visited.insert n; envDfsAux mode env fuel visited (pushValAndImplDeps env n ci? visited stack) none strLits
              | .mutRefs d =>
                  if isMutableRefConst n then .error s!"kernel gate: `{d}` transitively uses mutable reference primitive `{n}` (Landin's knot) outside framework modules"
                  else let visited := visited.insert n; envDfsAux mode env fuel visited (if isFrameworkModule (definingModule env n) then stack else pushValAndImplDeps env n ci? visited stack) none strLits
              | .axioms d =>
                  let visited := visited.insert n
                  match ci? with
                  | some (.axiomInfo ax) =>
                      if allowedKernelAxioms.contains ax.name && !ax.isUnsafe then envDfsAux mode env fuel visited stack none strLits
                      else .error s!"kernel gate: `{d}` depends on disallowed axiom `{ax.name}` (only {allowedKernelAxioms} are permitted)"
                  | some ci => envDfsAux mode env fuel visited (pushConstDeps ci visited stack) none strLits
                  | none => envDfsAux mode env fuel visited stack none strLits
              | .kernel csimpRepls checkLeak =>
                  match if checkLeak then clientLeakReason? env n else none with
                  | some err => .error err
                  | none =>
                      let isTc := isToolchainModule (definingModule env n)
                      let visited := if checkLeak || !isTc then visited.insert n else visited
                      if isTc then envDfsAux mode env fuel visited stack none strLits
                      else
                        let stack := (Lean.getInitFnNameFor? env n).elim stack (pushUnseen visited stack)
                        let stack := (Compiler.getImplementedBy? env n).elim stack (pushUnseen visited stack)
                        let stack := let u := Name.str n "_unsafe_rec"; if env.contains u then pushUnseen visited stack u else stack
                        let stack := (csimpRepls.getD n #[]).foldl (pushUnseen visited) stack
                        let (stack, strLits) := ci?.elim (stack, strLits) fun ci =>
                          (pushConstDeps ci visited stack (withRecAll := false),
                           if checkLeak then match ci with | .defnInfo v | .opaqueInfo v => collectExprStrLits v.value strLits | _ => strLits else strLits)
                        envDfsAux mode env fuel visited stack none strLits

private def dfsClean (mode : DfsMode) (env : Environment) (declName : Name) (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) :=
  if clean.contains declName then .ok clean else (envDfsAux mode env 2000000 clean #[declName] initCi? {}).map Prod.fst
private def walkKernelClosure (env : Environment) (csimpRepls : Std.HashMap Name (Array Name)) (checkLeak : Bool) (seeds : Array Name) (initVisited : Std.HashSet Name) (initStrLits : Std.HashSet String := {}) : Except String (Std.HashSet Name × Std.HashSet String) :=
  envDfsAux (.kernel csimpRepls checkLeak) env 1000000 initVisited seeds none initStrLits

private def isCompilerNumSuffix (pfx s : String) : Bool := s.startsWith pfx && let tail := s.toList.drop pfx.length; !tail.isEmpty && tail.all fun c => '0' ≤ c && c ≤ '9'
private def hasStrictSharedIrAuxSuffix : Name → Bool
  | .str p s => isCompilerNumSuffix "_closed_" s || isCompilerNumSuffix "_lam_" s || ((s == "_redArg" || s == "_boxed" || isCompilerNumSuffix "_boxed_const_" s) && hasStrictSharedIrAuxSuffix p) | _ => false
private def closedIrStrLit? (env : Environment) (n : Name) : Option String :=
  match Lean.IR.findEnvDecl env n with | some (.fdecl _ xs _ (.vdecl v1 _ (.lit (.str s)) (.ret (.var v2))) _) => if xs.isEmpty && v1 == v2 then some s else none | _ => none
private def isRuntimeDbgPrim (n : Name) : Bool := n == ``dbgTrace || n == ``dbgTraceIfShared || n == ``dbgSleep || n == ``panicCore || n == ``dbgStackTrace

@[noinline] private def checkClientLeakSeed (env : Environment) (exprVis exprMods : Std.HashSet Name)
    (exprStrLits : Std.HashSet String) (extraSeeds : Array Name) (n : Name) : Except String (Array Name) := do
  let err (what wh : String) := s!"client bundle leak gate: IR-reachable {what} is absent from {wh} (possible `@[local csimp]` rewrite)"
  if isRuntimeDbgPrim n && !exprVis.contains n then throw (err s!"`{n}`" "kernel dependencies of client entrypoints")
  let base := (owningKernelConst? env n).getD n; let baseMod := definingModule env base
  let isSharedAux := !env.contains n && hasStrictSharedIrAuxSuffix n
  let missingUserBase := !exprVis.contains base && env.contains base && !isToolchainModule baseMod && !isFrameworkModule baseMod
  if !isSharedAux then
    if missingUserBase then throw (err s!"`{n}` (owner `{base}`)" "kernel dependencies of client entrypoints")
    return if base != n then extraSeeds.push base else extraSeeds
  else if missingUserBase then
    if !exprMods.contains baseMod then throw (err s!"`{n}` (owner `{base}` in `{baseMod}`)" "client entrypoint modules")
    return if !isBenignEmptyCseThunk env n && !((closedIrStrLit? env n).any exprStrLits.contains) then extraSeeds.push base else extraSeeds
  else return extraSeeds

def verifyNoServerLeakInClientExprs (env : Environment) (roots : List Name) (irReachable : Array Name := #[]) : Except String Unit := do
  let (_, csimpRepls) := collectCSimpData env
  let (exprVis, exprStrLits) ← walkKernelClosure env csimpRepls true roots.toArray
    (Std.HashSet.emptyWithCapacity 4096) (Std.HashSet.emptyWithCapacity 1024)
  let exprMods := exprVis.fold (init := ({} : Std.HashSet Name)) fun acc c =>
    let m := definingModule env c; if !m.isAnonymous && !isToolchainModule m then acc.insert m else acc
  let extraSeeds ← irReachable.foldlM (checkClientLeakSeed env exprVis exprMods exprStrLits) irReachable
  discard <| walkKernelClosure env csimpRepls true extraSeeds exprVis exprStrLits

private structure VerifyCache where
  axioms   : Std.HashSet Name
  partials : Std.HashSet Name
  mutRefs  : Std.HashSet Name
  irNodes  : Std.HashSet Name := {}

@[noinline] private def checkDeclCache (env : Environment) (n : Name) (ci? : Option ConstantInfo)
    (doAx doPart doRef : Bool) (c : VerifyCache) : Except String VerifyCache := do
  let { axioms, partials, mutRefs, irNodes } := c
  let axioms ← if doAx then dfsClean (.axioms n) env n axioms ci? else pure axioms
  let partials ← if doPart then dfsClean (.partials n) env n partials ci? else pure partials
  let mutRefs ← if doRef then dfsClean (.mutRefs n) env n mutRefs ci? else pure mutRefs
  return { axioms, partials, mutRefs, irNodes }

@[noinline] private def verifyReachableEntry (env : Environment) (st : Std.HashSet Name × Array Name) (n : Name) :
    Except String (Std.HashSet Name × Array Name) := do
  if isRuntimeLoopConst n then throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop (`{n}`) is reachable at runtime"
  let (clean, seeds) := st; let clean ← dfsClean (.axioms n) env n clean
  let modName := definingModule env n; if !isToolchainModule modName then verifyUserDecl env modName n (env.find? n)
  let owner := (owningKernelConst? env n).getD n
  if isForbiddenToolchainPartial env owner then throw s!"kernel gate: non-total toolchain `partial` declaration `{owner}` (via `{n}`) is reachable at runtime"
  return (clean, if !isToolchainModule (definingModule env owner) && env.contains owner then seeds.push owner else seeds)

@[noinline] private def verifyReachableKernelEntry (env : Environment) (c : VerifyCache) (k : Name) : Except String VerifyCache := do
  let modName := definingModule env k; if isToolchainModule modName then return c
  let ci? := env.find? k; verifyUserDecl env modName k ci?
  checkDeclCache env k ci? true (!(isFrameworkModule modName && ci?.any (isCompileTimeMetaDecl env k ·))) (!isFrameworkModule modName) c

def verifyReachable (env : Environment) (reachable : Array Name) (roots : List Name := []) : Except String Unit := do
  let csimpRepls ← verifyCSimpClean env
  let (clean, kernelSeeds) ← reachable.foldlM (verifyReachableEntry env) (Std.HashSet.emptyWithCapacity 4096, roots.toArray)
  let (kernelClosure, _) ← walkKernelClosure env csimpRepls false kernelSeeds (Std.HashSet.emptyWithCapacity 4096)
  discard <| kernelClosure.foldM (verifyReachableKernelEntry env)
    { axioms := clean, partials := Std.HashSet.emptyWithCapacity 4096, mutRefs := Std.HashSet.emptyWithCapacity 4096 }

private def irSpecTarget? (env : Environment) (n : Name) : Option Name :=
  let rec parts : Name → List (Sum String Nat) → List (Sum String Nat)
    | .anonymous, acc => acc | .str p s, acc => parts p (.inl s :: acc) | .num p k, acc => parts p (.inr k :: acc)
  let rec find : List (Sum String Nat) → Option Name
    | [] => none
    | .inl "_at_" :: rest =>
        let cand := rest.foldl (init := Name.anonymous) fun a => fun | .inl s => .str a s | .inr k => .num a k
        match owningKernelConst? env cand with
        | some o => if !isToolchainModule (definingModule env o) then some o else find rest | none => find rest
    | _ :: rest => find rest
  find (parts n [])

private def resolveIrTarget (env : Environment) (n : Name) : Name :=
  match owningKernelConst? env n with
  | some o => if isToolchainModule (definingModule env o) then (irSpecTarget? env n).getD o else o
  | none   => (irSpecTarget? env n).getD n

@[inline] private def checkNonFwPartRefs (env : Environment) (n : Name) (c : VerifyCache) : Except String VerifyCache :=
  if isFrameworkModule (definingModule env n) then .ok c else checkDeclCache env n none false true true c

private def checkTransitiveIr (env : Environment) (modIrMap : Std.HashMap Name Lean.IR.FnBody)
    (irName modName : Name) : Nat → Array Name → VerifyCache → Except String VerifyCache
  | fuel, irStack, cache =>
      if irStack.isEmpty then .ok cache
      else match fuel with
        | 0 => .error s!"kernel gate: transitive IR callee check for `{irName}` in `{modName}` exceeded fuel limit"
        | fuel + 1 => do
            let c := irStack.back!; let irStack := irStack.pop
            if cache.irNodes.contains c then checkTransitiveIr env modIrMap irName modName fuel irStack cache
            else
              let { axioms, partials, mutRefs, irNodes } := cache
              let mut cache : VerifyCache := { axioms, partials, mutRefs, irNodes := irNodes.insert c }
              checkIrCallee env true true irName modName true c
              let cOwner := (owningKernelConst? env c).getD c; let cTarget := resolveIrTarget env c
              cache ← checkNonFwPartRefs env cOwner cache
              if cTarget != cOwner then cache ← checkNonFwPartRefs env cTarget cache
              let cTargetMod := definingModule env cTarget
              let cb? := (modIrMap.get? c).orElse fun _ =>
                if !isToolchainModule cTargetMod && !isFrameworkModule cTargetMod then
                  match Lean.IR.findEnvDecl env c with | some (.fdecl (body := cb) ..) => some cb | _ => none
                else none
              checkTransitiveIr env modIrMap irName modName fuel (cb?.elim irStack (callees · irStack)) cache

@[noinline] private def verifyConstEntry (env : Environment) (modName : Name) (isNonFw : Bool)
    (csimpThms : SSet Name) (c : VerifyCache) (ci : ConstantInfo) : Except String VerifyCache := do
  let n := ci.name
  if isNonFw && csimpThms.contains n then throw (csimpErr n modName)
  match ci with
  | .axiomInfo _ => throw s!"kernel gate: custom `axiom {n}` declared in `{modName}` is forbidden"
  | .thmInfo _   => checkDeclCache env n (some ci) true false false c
  | _ =>
      if !isNonFw && isCompileTimeMetaDecl env n ci then return c
      verifyUserDecl env modName n (some ci) (checkIr := false)
      let chk := isNonFw && !hasMetaReturnType env ci.type
      checkDeclCache env n (some ci) true chk chk c

@[noinline] private def verifyIrDeclEntry (env : Environment) (modIrMap : Std.HashMap Name Lean.IR.FnBody)
    (modName : Name) (isNonFw : Bool) (c : VerifyCache) (d : Lean.IR.Decl) : Except String VerifyCache := do
  let .fdecl (f := irName) (body := b) .. := d | return c
  let owner := resolveIrTarget env irName; let ownerCi? := env.find? owner
  if !isNonFw && ownerCi?.elim (hasRegBuiltin irName) (isCompileTimeMetaDecl env owner ·) then return c
  let checkTcPartials := isNonFw && !ownerCi?.any (hasMetaReturnType env ·.type)
  let irCallees := callees b #[]
  for callee in irCallees do checkIrCallee env isNonFw checkTcPartials irName modName false callee
  if checkTcPartials && !c.irNodes.contains irName then
    let { axioms, partials, mutRefs, irNodes } := c
    checkTransitiveIr env modIrMap irName modName 200000 irCallees { axioms, partials, mutRefs, irNodes := irNodes.insert irName }
  else return c

private def verifyModuleIndices (env : Environment) (idxs : Array Nat) (initCap : Nat) : Except String Nat := do
  let mk (_ : Unit) := Std.HashSet.emptyWithCapacity initCap
  let mut c : VerifyCache := { axioms := mk (), partials := mk (), mutRefs := mk (), irNodes := mk () }
  let mut checkedCount : Nat := 0
  let (modNames, modData) := (env.header.moduleNames, env.header.moduleData)
  let csimpThms := (Lean.Compiler.CSimp.ext.getState env).thmNames
  for i in idxs do
    let modName := modNames[i]!; let isNonFw := !isFrameworkModule modName
    let consts := modData[i]!.constants; checkedCount := checkedCount + consts.size
    c ← consts.foldlM (verifyConstEntry env modName isNonFw csimpThms) c
    let irEntries := Lean.IR.declMapExt.getModuleEntries env i
    let modIrMap := if !isNonFw then {} else irEntries.foldl (init := ({} : Std.HashMap Name Lean.IR.FnBody)) fun m d =>
      match d with | .fdecl (f := irName) (body := b) .. => m.insert irName b | _ => m
    c ← irEntries.foldlM (verifyIrDeclEntry env modIrMap modName isNonFw) c
  return checkedCount

def verifyProjectEnv (env : Environment) (skipFramework : Bool := false) : Except String Nat := do
  discard <| verifyCSimpClean env
  let (modNames, modData) := (env.header.moduleNames, env.header.moduleData)
  let (active, totalDecls) := (min modNames.size modData.size).fold (init := (#[], 0)) fun i _ (acc, tot) =>
    let m := modNames[i]!
    if !isToolchainModule m && !(skipFramework && isFrameworkModule m) then
      let sz := modData[i]!.constants.size
      if sz > 0 then (acc.push (i, sz), tot + sz) else (acc, tot)
    else (acc, tot)
  if totalDecls < 4000 || active.size < 4 then return ← verifyModuleIndices env (active.map Prod.fst) (max 4096 (totalDecls * 2))
  let nWorkers := min 8 active.size
  let (buckets, _) := (active.qsort (·.2 > ·.2)).foldl (init := (Array.replicate nWorkers #[], Array.replicate nWorkers 0))
    fun (bs, ls) (idx, sz) =>
      let bestW := nWorkers.fold (init := 0) fun w _ best => if ls[w]! < ls[best]! then w else best
      (bs.set! bestW (bs[bestW]!.push idx), ls.set! bestW (ls[bestW]! + sz))
  let tasks := buckets.map fun b => Task.spawn fun _ => verifyModuleIndices env b 16384
  tasks.foldlM (init := 0) fun acc t => return acc + (← t.get)

end Js
