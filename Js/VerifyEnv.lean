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

private def forbiddenRuntimeLoopExact : Std.HashSet Name := Std.HashSet.ofList [
  `IO.iterate, `repeatM, `runST, `runEST, `IO.FS.Stream.mk, `IO.FS.Stream.readToEnd, `IO.FS.Stream.readBinToEnd,
  `IO.FS.Stream.readBinToEndInto, `IO.FS.Stream.lines, `Std.Stream.forIn, `Std.instForInOfMonadOfStream,
  `Std.Rci.iter, `Std.Roi.iter, `Std.Rii.iter, `Std.Rcc.iter, `Std.Rco.iter, `Std.Roc.iter, `Std.Roo.iter,
  `Std.Ric.iter, `Std.Rio.iter, `Std.Rxi.Iterator, `Std.Rxi.instIteratorIteratorIdOfUpwardEnumerable,
  `Std.Rxc.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE,
  `Std.Rxo.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT,
  `Std.Rxi.Iterator.instIteratorLoop.loop, `Std.Rxc.Iterator.instIteratorLoop.loop,
  `Std.Rxo.Iterator.instIteratorLoop.loop, `Std.IterM.DefaultConsumers.forIn', `Std.Iter.atIdxSlow?,
  `Std.IterM.toArray.go, `Std.IterM.toListRev.go, `Std.Iterator.mk, `Std.IteratorLoop.mk, `Std.Stream.mk,
  `Std.PRange.UpwardEnumerable.mk, `String.Slice.Pattern.ForwardPattern.mk, `String.Slice.Pattern.BackwardPattern.mk,
  `Std.Iter.repeat, `Std.IterM.repeat, `Std.Iterators.Types.RepeatIterator, `Std.Iter.allowNontermination,
  `Std.IterM.allowNontermination, `Std.Iter.Partial, `Std.IterM.Partial, `Std.IteratorLoop.defaultImplementation,
  `Std.Internal.Parsec.manyCore, `Std.Internal.Parsec.manyCharsCore, `Std.Internal.Parsec.many,
  `Std.Internal.Parsec.many1, `Std.Internal.Parsec.manyChars, `Std.Internal.Parsec.many1Chars,
  `Std.Broadcast.Receiver.forAsync, `Std.Bounded.Receiver.forAsync, `Std.Broadcast.Sync.Receiver.forIn,
  `Std.Broadcast.Sync.Receiver.instForInOfInhabitedOfMonadOfMonadLiftTBaseIO,
  `Std.Channel.forAsync, `Std.CloseableChannel.forAsync, `Std.Channel.Sync.forIn, `Std.CloseableChannel.Sync.forIn,
  `Std.Channel.Sync.instForInOfInhabitedOfMonadOfMonadLiftTBaseIO,
  `Std.CloseableChannel.Sync.instForInOfMonadOfMonadLiftTBaseIO,
  `Std.Async.EAsync.forIn, `Std.Async.EAsync.instForInLoopUnit,
  `Std.Async.ContextAsync.forIn, `Std.Async.ContextAsync.instForInLoopUnit,
  `Std.Http.Body.Stream.forIn, `Std.Http.Body.Stream.forIn', `Std.Http.Body.Stream.readAll,
  `Std.Http.Body.Stream.drain,
  `Std.Http.Body.instForInAsyncStreamChunk, `Std.Http.Body.instForInContextAsyncStreamChunk
]
private def forbiddenRuntimeLoopDottedSubstrs : Array String := #[
  "IO.iterate", "repeatM.erased", "repeatM.impl", "IterM.Partial", "Lean.Loop.forIn", "Lean.Order.fix",
  "Std.Stream.forIn", "IteratorLoop.defaultImplementation", "Parsec.manyCore", "Parsec.manyCharsCore"
]
private def wfOpaqueLeaves : Array String := #["opaqueFix", "opaqueFix₂", "opaqueFix₃"]
private def wfExtrinsicLeaves : Array String := #[
  "extrinsicFix", "extrinsicFix₂", "extrinsicFix₃", "partialExtrinsicFix", "partialExtrinsicFix₂", "partialExtrinsicFix₃"
]
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

private def isRuntimeLoopConst (n : Name) : Bool :=
  withPriv (hasNamePrefix isRuntimeLoopHit) n || withPriv (isWfFixLeaf false) n

private def isWhileLoopConst (n : Name) : Bool := isRuntimeLoopConst n || hasNamePrefix (isWfFixLeaf true) n

private def forbiddenUserMutableRefExact : Std.HashSet Name := Std.HashSet.ofList [
  `ST.mkRef, `ST.Prim.mkRef, `IO.mkRef, `ST.Ref.set, `ST.Prim.Ref.set, `ST.Ref.modify, `ST.Ref.modifyGet,
  `ST.Prim.Ref.modifyGet, `IO.Ref.set, `IO.Ref.modify, `IO.Ref.modifyGet, `ST.Ref.swap, `ST.Prim.Ref.swap,
  `IO.Ref.swap, `ST.Ref.take, `ST.Prim.Ref.take, `IO.Ref.take, `IO.Promise.new, `IO.Promise.resolve,
  `IO.Promise.result?, `IO.Promise.result!, `IO.Promise.resultD, `Std.BaseMutex.new, `Std.BaseRecursiveMutex.new,
  `Std.BaseSharedMutex.new, `Std.Condvar.new, `Std.Barrier.new, `Std.Notify.new, `Std.Semaphore.new,
  `Std.CancellationContext.new, `Std.CancellationToken.new,
  `Std.Mutex.new, `Std.Mutex.atomically, `Std.Mutex.tryAtomically, `Std.Mutex.atomicallyOnce,
  `Std.RecursiveMutex.new, `Std.RecursiveMutex.atomically, `Std.RecursiveMutex.tryAtomically,
  `Std.SharedMutex.new, `Std.SharedMutex.atomically, `Std.SharedMutex.tryAtomically,
  `Std.SharedMutex.atomicallyRead, `Std.SharedMutex.tryAtomicallyRead,
  `StateRefT'.run, `StateRefT'.run', `StateRefT'.set, `StateRefT'.modifyGet,
  `StateRefT'.instMonadStateOfOfMonadLiftTST, `Std.Channel.new, `Std.Channel.Sync.new,
  `Std.CloseableChannel.new, `Std.CloseableChannel.Sync.new, `Std.Broadcast.new, `Std.Broadcast.Sync.new,
  `Std.Bounded.new, `Qed.Server.Prim.mkStateBox, `Qed.Server.Prim.atomicRead, `Qed.Server.Prim.atomicModify,
  `Qed.Server.Native.withStateBox, `Qed.Handlers.mkNew, `Qed.registerHandler, `Qed.dispatchStrWithRows,
  `Qed.localRerender, `Qed.localRun
]

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
private def metaAliasAllowlist : Array Name := #[
  `Lean.MacroM, `Lean.Macro, `Lean.CoreM, `Lean.Meta.MetaM, `Lean.Elab.Command.CommandElabM, `Lean.Elab.Command.CommandElab,
  `Lean.Elab.Term.TermElabM, `Lean.Elab.Term.TermElab, `Lean.Elab.Tactic.TacticM, `Lean.Elab.Tactic.Tactic,
  `Lean.PrettyPrinter.Formatter, `Lean.PrettyPrinter.Parenthesizer, `Lean.PrettyPrinter.Unexpander, `Lean.PrettyPrinter.Delaborator.Delab
]
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

private def irCallSite (irName modName : Name) (transitive : Bool) : String :=
  s!"{if transitive then "transitively called in IR" else "called"} by `{irName}` in `{modName}`"

private def checkIrCallee (env : Environment) (checkNonFw checkTcPartials : Bool)
    (irName modName : Name) (transitive : Bool) (c : Name) : Except String Unit := do
  if isRuntimeLoopConst c then
    throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop (`{c}`) is {irCallSite irName modName transitive}"
  if checkNonFw && isMutableRefConst c then
    throw s!"kernel gate: mutable reference primitive (`{c}`, Landin's knot) is {irCallSite irName modName transitive} outside framework modules"
  if checkTcPartials then
    let owner := (owningKernelConst? env c).getD c
    if isForbiddenToolchainPartial env owner then
      throw s!"kernel gate: non-total toolchain `partial` declaration `{owner}` (via `{c}`) is {irCallSite irName modName transitive}"

private def isCompilerCtorIdxImpl (env : Environment) (n : Name) : Bool :=
  match n with
  | .str (.str ind "ctorIdx") "_impl" =>
      match env.find? ind, env.find? n, Compiler.getImplementedBy? env (Name.str ind "ctorIdx") with
      | some (.inductInfo _), some (.defnInfo dv), some impl =>
          if impl != n then false
          else
            let rec peel : Expr → Expr | .lam _ _ b _ => peel b | e => e
            match peel dv.value with
            | .app (.app (.const ``getObjTagNat _) ty) (.bvar 0) =>
                match ty.getAppFn with | .const c _ => c == ind | _ => false
            | _ => false
      | _, _, _ => false
  | _ => false

private def verifyUserDecl (env : Environment) (modName n : Name) (ci? : Option ConstantInfo) (checkIr : Bool := true) : Except String Unit := do
  let ownerMod := if !modName.isAnonymous then modName else definingModule env ((owningKernelConst? env n).getD n)
  let isNonFw := !isFrameworkModule ownerMod
  if isNonFw && (Lean.isIOUnitInitFn env n || Lean.isIOUnitBuiltinInitFn env n ||
      (Lean.getInitFnNameFor? env n).isSome || (Lean.builtinInitAttr.getParam? env n).isSome) then
    throw s!"kernel gate: `initialize`/`@[init]` declaration `{n}` in `{modName}` is forbidden outside framework modules"
  if (Lean.getExportNameFor? env n).isSome && ownerMod != `Qed.Driver.Runtime then
    throw s!"kernel gate: `@[export]` declaration `{n}` in `{modName}` is forbidden outside `Qed.Driver.Runtime`"
  if let some impl := Compiler.getImplementedBy? env n then
    if !(impl == Name.str n "_impl" && isCompilerCtorIdxImpl env impl) then
      throw s!"kernel gate: `@[implemented_by {impl}]` or `partial def` on `{n}` in `{modName}` is forbidden"
  if let some ci := ci? then
    let isCtorIdxImpl := isCompilerCtorIdxImpl env n
    if ci.isUnsafe && !isCtorIdxImpl then throw s!"kernel gate: `unsafe` declaration `{n}` in `{modName}` is forbidden"
    match unfoldReturnHead env forbiddenCustomClass ci.type with
    | .error err => throw s!"kernel gate: `{n}` in `{modName}` failed return-type check ({err})"
    | .ok (some rtHead) => if forbiddenCustomClass rtHead then throw s!"kernel gate: custom `{rtHead}` instance `{n}` in `{modName}` is forbidden"
    | .ok none => pure ()
    let opaqueErr (nm : Name) := s!"kernel gate: `partial` or `opaque` declaration `{nm}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"
    match ci with
    | .opaqueInfo _ => if !isLegitOpaque env modName n then throw (opaqueErr n)
    | .defnInfo dv =>
        if dv.safety != .safe && !isTotalCompilerAux env n && !isCtorIdxImpl then
          if let .str root "_unsafe_rec" := n then
            if let some (.opaqueInfo _) := env.find? root then throw (opaqueErr root)
          throw s!"kernel gate: `partial` or non-safe definition `{n}` in `{modName}` is forbidden"
        let bad : UInt8 := dv.value.foldConsts 0 fun c acc =>
          if acc == 1 then 1 else if isWhileLoopConst c then 1 else if isNonFw && acc == 0 && isMutableRefConst c then 2 else acc
        if bad == 1 then throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop inside `{n}` in `{modName}` is forbidden"
        if bad == 2 then throw s!"kernel gate: mutable reference primitive (Landin's knot) inside `{n}` in `{modName}` is forbidden outside framework modules"
    | _ => pure ()
  if checkIr then
    let checkTcPartials := isNonFw && !ci?.any (hasMetaReturnType env ·.type)
    for irName in #[n, Name.str n "_redArg"] do
      if let some (.fdecl (body := b) ..) := Lean.IR.findEnvDecl env irName then
        for c in callees b #[] do checkIrCallee env isNonFw checkTcPartials n modName false c
  if Lean.isExtern env n && !isAllowedExternMod modName then
    throw s!"kernel gate: unverified `@[extern]` `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"

@[inline] private def hasOwnerMarker (env : Environment) (owner marker : Name) : Bool :=
  !owner.isAnonymous && env.contains (owner ++ marker)

def isServerOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && (hasOwnerMarker env owner `_qed_server_marker ||
    (env.find? (owner ++ `dispatchM)).any (exprHasConst (· == `Qed.Server.RequestCtx) ·.type))
def isExternalOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_external_marker
def isServiceOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_service_marker
def isDatabaseOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_database_marker
def isAuthOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_auth_marker
def isDeployOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_deploy_marker

private def collectExprStrLits : Expr → Std.HashSet String → Std.HashSet String
  | .lit (.strVal s), acc => acc.insert s
  | .app f a, acc | .lam _ f a _, acc | .forallE _ f a _, acc => collectExprStrLits a (collectExprStrLits f acc)
  | .letE _ t v b _, acc => collectExprStrLits b (collectExprStrLits v (collectExprStrLits t acc))
  | .mdata _ e, acc | .proj _ _ e, acc => collectExprStrLits e acc
  | _, acc => acc

def externalHasSecrets (env : Environment) (owner : Name) : Bool :=
  isExternalOwner env owner && match env.find? (owner ++ `secrets) with
    | some (.defnInfo dv) => !(collectExprStrLits dv.value {}).isEmpty | _ => false

private def isBenignEmptyCseThunk (env : Environment) (n : Name) : Bool :=
  match Lean.IR.findEnvDecl env n with
  | some (.fdecl _ xs _ (.vdecl v1 _ (.lit (.num 0)) (.vdecl v2 _ (.fap fn args) (.ret (.var v2')))) _) =>
      xs.isEmpty && v2 == v2' && (fn == `Array.mkEmpty || fn == `ByteArray.emptyWithCapacity) &&
      match args with | #[.erased, .var v1'] | #[.var v1'] => v1 == v1' | _ => false
  | _ => false

private def serverOnlyLeaves : Array String := #[
  "dispatchM", "wsDispatchM", "wsProject", "httpDispatchM", "authHookM", "initState", "runServer",
  "jobs", "verifiedJobs", "jobNames", "readOnlyMethods", "methods", "channels"
]
private def dbOnlyLeaves : Array String := #["config", "ensureSchema", "ddl", "rlsDdl", "instSafeIOEnsureSchema", "Snap"]

def isServerOnlyDeclName (env : Environment) : Name → Bool
  | .anonymous => false | .num p _ => isServerOnlyDeclName env p
  | .str owner s =>
      if s.startsWith "_closed_" then isServerOnlyDeclName env owner && !isBenignEmptyCseThunk env (.str owner s)
      else ((serverOnlyLeaves.contains s || s.endsWith "_step" || s.endsWith "_handler" || s.endsWith "_project") && isServerOwner env owner) ||
        (dbOnlyLeaves.contains s && isDatabaseOwner env owner) ||
        ((s == "schema" || s == "decodeRow" || s == "decodeMetaRow" || s == "metaColumns") && (isDatabaseOwner env owner || isDatabaseOwner env owner.getPrefix)) ||
        (s == "config" && isAuthOwner env owner) || (s == "spec" && isDeployOwner env owner) ||
        (s == "baseUrl" && externalHasSecrets env owner) ||
        (s == "secrets" && (isServerOwner env owner || isExternalOwner env owner || isServiceOwner env owner || isDatabaseOwner env owner || isAuthOwner env owner)) ||
        isServerOnlyDeclName env owner

private def serverOnlyModules : Std.HashSet Name := Std.HashSet.ofList [
  `Qed.Server.Prim, `Qed.Server.Native, `Qed.Server.Http, `Qed.Server.Net, `Qed.Server.Db.PgWire,
  `Qed.Auth.Oidc, `Qed.Deploy, `Qed.Cloud.Compile, `Qed.Cloud.Proofs,
  `Qed.Cloud.GcpApi, `Qed.Cloud.Executor
]
private def serverOnlyDecls : Std.HashSet Name := Std.HashSet.ofList [
  `Qed.Server.ServerEffect, `Qed.Server.execExternalRaw, `Qed.Server.MonadServer.exec, `Qed.Server.MonadServer.httpCall,
  `Qed.Server.MonadServer.dbExec, `Qed.Server.MonadServer.dbExecDdl, `Qed.Server.MonadServer.dbTxBegin,
  `Qed.Server.MonadServer.dbTxExec, `Qed.Server.MonadServer.dbTxCommit, `Qed.Server.MonadServer.dbTxRollback,
  `Qed.Server.MonadServer.setCookie, `Qed.Server.MonadServer.sendSse, `Qed.Server.MonadServer.readEnv,
  `Qed.Server.MonadServer.nowMs, `Qed.Server.MonadServer.randomHex, `Qed.Server.MonadServer.randomBytes,
  `Qed.Server.MonadServer.hmacSha256, `Qed.Server.MonadServer.sha256, `Qed.Server.MonadServer.constEq,
  `Qed.Server.MonadServer.aeadEncrypt, `Qed.Server.MonadServer.aeadDecrypt,
  `Qed.Server.MonadServer.wsBroadcast, `Qed.Server.flushWsEmits, `Qed.Server.MonadAtomic.runAtomic,
  `Qed.Server.MonadAtomic.runAtomicRead, `Qed.Server.Webhook.postJson, `Qed.Server.Webhook.postBytes,
  `Qed.Crypto.hmacSha256, `Qed.Crypto.hmacSha256Hex, `Qed.Crypto.constEq, `Qed.Crypto.sha256, `Qed.Crypto.sha256Hex,
  `Qed.Time.nowMs, `Qed.Time.nowSec, `Qed.Random.hex, `Qed.Random.bytes, `Qed.Random.uuid
]

def clientLeakReason? (env : Environment) (n : Name) : Option String :=
  let modName := definingModule env n
  if serverOnlyModules.contains modName then
    some s!"client bundle leak gate: server runtime primitive `{n}` (`{modName}`) cannot be bundled into client JavaScript"
  else if serverOnlyDecls.contains n || n.getPrefix == `Qed.Server.ServerEffect || withPriv (hasNamePrefix (· == `Qed.Server.Db.HttpSql)) n then
    some s!"client bundle leak gate: server I/O or state primitive `{n}` cannot be bundled into client JavaScript"
  else if isServerOnlyDeclName env n then
    some s!"client bundle leak gate: server secret/state/handler `{n}` cannot be bundled into client JavaScript"
  else none

def verifyNoServerLeakInClient (env : Environment) (reachable : Array Name) : Except String Unit := do
  for n in reachable do
    if let some err := clientLeakReason? env n then
      throw err

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
              | .partials declName =>
                  if isForbiddenToolchainPartial env n then .error s!"kernel gate: `{declName}` depends on non-total toolchain `partial` declaration `{n}`"
                  else let visited := visited.insert n; envDfsAux mode env fuel visited (pushValAndImplDeps env n ci? visited stack) none strLits
              | .mutRefs declName =>
                  if isMutableRefConst n then .error s!"kernel gate: `{declName}` transitively uses mutable reference primitive `{n}` (Landin's knot) outside framework modules"
                  else let visited := visited.insert n; envDfsAux mode env fuel visited (if isFrameworkModule (definingModule env n) then stack else pushValAndImplDeps env n ci? visited stack) none strLits
              | .axioms declName => match ci? with
                  | none => envDfsAux mode env fuel (visited.insert n) stack none strLits
                  | some (.axiomInfo ax) =>
                      if allowedKernelAxioms.contains ax.name && !ax.isUnsafe then envDfsAux mode env fuel (visited.insert n) stack none strLits
                      else .error s!"kernel gate: `{declName}` depends on disallowed axiom `{ax.name}` (only {allowedKernelAxioms} are permitted)"
                  | some ci => let visited := visited.insert n; envDfsAux mode env fuel visited (pushConstDeps ci visited stack) none strLits
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
                        let (stack, strLits) := match ci? with
                          | none => (stack, strLits)
                          | some ci => (pushConstDeps ci visited stack (withRecAll := false),
                              if checkLeak then match ci with | .defnInfo v | .opaqueInfo v => collectExprStrLits v.value strLits | _ => strLits else strLits)
                        envDfsAux mode env fuel visited stack none strLits

private def dfsClean (mode : DfsMode) (env : Environment) (declName : Name) (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) :=
  if clean.contains declName then .ok clean else (envDfsAux mode env 2000000 clean #[declName] initCi? {}).map Prod.fst
def verifyNoToolchainPartials (env : Environment) (declName : Name) (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean (.partials declName) env declName clean initCi?
def verifyNoMutableRefs (env : Environment) (declName : Name) (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean (.mutRefs declName) env declName clean initCi?
def verifyConstAxioms (env : Environment) (declName : Name) (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean (.axioms declName) env declName clean initCi?
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
  let axioms ← if doAx then verifyConstAxioms env n axioms ci? else pure axioms
  let partials ← if doPart then verifyNoToolchainPartials env n partials ci? else pure partials
  let mutRefs ← if doRef then verifyNoMutableRefs env n mutRefs ci? else pure mutRefs
  return { axioms, partials, mutRefs, irNodes }

@[noinline] private def verifyReachableEntry (env : Environment) (st : Std.HashSet Name × Array Name) (n : Name) :
    Except String (Std.HashSet Name × Array Name) := do
  if isRuntimeLoopConst n then throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop (`{n}`) is reachable at runtime"
  let (clean, seeds) := st; let clean ← verifyConstAxioms env n clean
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
