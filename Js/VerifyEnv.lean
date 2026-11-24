import Lean

open Lean

namespace Js

def allowedKernelAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

@[inline] def isToolchainModule (modName : Name) : Bool :=
  let r := modName.getRoot; r == `Init || r == `Std || r == `Lean || r == `Lake

@[inline] def definingModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous | none => Name.anonymous

@[inline] def isFrameworkModule (modName : Name) : Bool :=
  let r := modName.getRoot; r == `Qed || r == `Js || r == `Cli

@[inline] private def withPriv (p : Name → Bool) (n : Name) : Bool :=
  p n || (Lean.isPrivateName n && p (Lean.privateToUserName n))

@[specialize] private def hasNamePrefix (p : Name → Bool) : Name → Bool
  | .anonymous => false | .num parent _ => hasNamePrefix p parent | n@(.str parent _) => p n || hasNamePrefix p parent

@[inline] private def exprHasConst (p : Name → Bool) (e : Expr) : Bool :=
  e.foldConsts false fun c acc => acc || p c

private def rootTwoAux : Name → Option String → Option (String × Option String)
  | .str .anonymous r, second => some (r, second)
  | .str p s, _ => rootTwoAux p (some s) | .num p _, _ => rootTwoAux p none | .anonymous, _ => none

private def metaLeanPrefixes : Array String :=
  #["Syntax", "TSyntax", "Macro", "Elab", "Meta", "Parser", "PrettyPrinter", "Environment", "IR"]

private def isMetaNamespaceConst (env : Environment) (n : Name) : Bool :=
  match rootTwoAux n none with
  | some ("Lean", some s) => metaLeanPrefixes.any (s.startsWith ·) && isToolchainModule (definingModule env n)
  | _ => false

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
  c == ``WellFounded.fix || c == `WellFounded.Nat.fix ||
  match c with | .str _ s => s == "_f" || s.startsWith "brecOn" || s.startsWith "_unary" || s.startsWith "_mutual" | _ => false

private def isUnsafeRecName : Name → Bool | .str _ "_unsafe_rec" => true | _ => false

private def isProofApp (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.consumeMData with
  | .const c _ => match env.find? c with | some (.thmInfo _) => true | _ => false
  | _ => false

private def exprEqUpToProofs (env : Environment) (allowProof : Bool) (e1 e2 : Expr) (fuel : Nat := 100000) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      let e1 := e1.consumeMData; let e2 := e2.consumeMData
      if allowProof && isProofApp env e2 then !exprHasConst isUnsafeRecName e1
      else match e1 with
      | .bvar i => match e2 with | .bvar j => i == j | _ => false
      | .fvar a => match e2 with | .fvar b => a == b | _ => false
      | .mvar a => match e2 with | .mvar b => a == b | _ => false
      | .sort u => match e2 with | .sort v => u == v | _ => false
      | .lit a  => match e2 with | .lit b  => a == b | _ => false
      | .const c1 l1 => match e2 with | .const c2 l2 => (match c1 with | .str p "_unsafe_rec" => p | c => c) == c2 && l1 == l2 | _ => false
      | .app f1 a1 => match e2 with | .app f2 a2 => exprEqUpToProofs env allowProof f1 f2 fuel && exprEqUpToProofs env true a1 a2 fuel | _ => false
      | .lam _ t1 b1 _ => match e2 with | .lam _ t2 b2 _ => exprEqUpToProofs env true t1 t2 fuel && exprEqUpToProofs env allowProof b1 b2 fuel | _ => false
      | .forallE _ t1 b1 _ => match e2 with | .forallE _ t2 b2 _ => exprEqUpToProofs env true t1 t2 fuel && exprEqUpToProofs env allowProof b1 b2 fuel | _ => false
      | .letE _ t1 v1 b1 _ => match e2 with | .letE _ t2 v2 b2 _ => exprEqUpToProofs env true t1 t2 fuel && exprEqUpToProofs env true v1 v2 fuel && exprEqUpToProofs env allowProof b1 b2 fuel | _ => false
      | .proj n1 i1 s1 => match e2 with | .proj n2 i2 s2 => n1 == n2 && i1 == i2 && exprEqUpToProofs env false s1 s2 fuel | _ => false
      | .mdata _ _ => false

def isTotalCompilerAux (env : Environment) (declName : Name) : Bool :=
  match declName with
  | .str root "_unsafe_rec" =>
      (Lean.declRangeExt.find? env declName).isNone && (Compiler.getImplementedBy? env root).isNone &&
      env.getModuleIdxFor? declName == env.getModuleIdxFor? root &&
      match env.find? declName, env.find? root with
      | some (.defnInfo dv), some (.defnInfo rdv) =>
          dv.safety == .partial && rdv.safety == .safe && dv.type == rdv.type && dv.levelParams == rdv.levelParams &&
          exprHasConst isRecCombinatorConst rdv.value && exprHasConst isUnsafeRecName dv.value &&
          match (Lean.Elab.WF.eqnInfoExt.find? env root).map (·.value) |>.orElse fun _ =>
                (Lean.Elab.Structural.eqnInfoExt.find? env root).map (·.value) with
          | some eqVal => !isProofApp env eqVal && exprEqUpToProofs env false dv.value eqVal | none => false
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
    | .str parent leaf =>
        (leaf == "_unsafe_rec" || leaf.startsWith "match_" || leaf.startsWith "_cstage") &&
        (env.find? parent).any fun pci => exprHasConst (isMetaNamespaceConst env) pci.type
    | _ => false))

@[inline] private def pushUnseen (clean : Std.HashSet Name) (stack : Array Name) (n : Name) : Array Name :=
  if clean.contains n then stack else stack.push n

private def pushExprDeps (e : Expr) (clean : Std.HashSet Name) (stack : Array Name) : Array Name :=
  e.foldConsts stack fun c acc => if clean.contains c then acc else acc.push c

private def pushConstDeps (ci : ConstantInfo) (clean : Std.HashSet Name) (stack : Array Name)
    (withRecAll : Bool := true) : Array Name :=
  let s := pushExprDeps ci.type clean stack
  match ci with
  | .defnInfo v | .thmInfo v | .opaqueInfo v => pushExprDeps v.value clean s
  | .inductInfo v => v.ctors.foldl (pushUnseen clean) s
  | .ctorInfo v   => if withRecAll then pushUnseen clean s v.name else s
  | .recInfo v    => if withRecAll then v.all.foldl (pushUnseen clean) s else s
  | _             => s

private def pushValAndImplDeps (env : Environment) (n : Name) (ci? : Option ConstantInfo)
    (clean : Std.HashSet Name) (stack : Array Name) : Array Name :=
  let s := (Compiler.getImplementedBy? env n).elim stack (pushUnseen clean stack)
  match ci? with | some (.defnInfo v) | some (.opaqueInfo v) => pushExprDeps v.value clean s | _ => s

private def isAllowedToolchainPartialBase (c : Name) : Bool :=
  let base := match c with | .str p "_unsafe_rec" => p | n => n
  base == `Nat.toSubDigitsAux || base == `Nat.toSuperDigitsAux || base == `Lean.Name.needsNoEscapeAsciiRest || isWfFixLeaf false base

def isForbiddenToolchainPartial (env : Environment) (c : Name) : Bool :=
  isToolchainModule (definingModule env c) && !withPriv isAllowedToolchainPartialBase c &&
  match env.find? c with
  | some (.opaqueInfo _) => !Lean.isExtern env c && env.contains (Name.str c "_unsafe_rec")
  | some (.defnInfo dv)  => dv.safety == .partial && !isTotalCompilerAux env c
  | _                    => false

private inductive DfsMode where | partials | mutRefs | axioms

private def dfsCleanAux (mode : DfsMode) (env : Environment) (declName : Name) :
    Nat → Std.HashSet Name → Array Name → Option ConstantInfo → Except String (Std.HashSet Name)
  | fuel, clean, stack, firstCi? =>
      if stack.isEmpty then .ok clean
      else
        let n := stack.back!; let stack := stack.pop
        match fuel with
        | 0 =>
            let kind := match mode with | .partials => "toolchain totality" | .mutRefs => "mutable-reference" | .axioms => "axiom"
            .error s!"kernel gate: {kind} check for `{declName}` exceeded fuel limit while inspecting `{n}`"
        | fuel + 1 =>
            if firstCi?.isNone && clean.contains n then dfsCleanAux mode env declName fuel clean stack none
            else
              let ci? := match firstCi? with | some ci => some ci | none => env.find? n
              match mode with
              | .partials =>
                  if isForbiddenToolchainPartial env n then .error s!"kernel gate: `{declName}` depends on non-total toolchain `partial` declaration `{n}`"
                  else let clean := clean.insert n; dfsCleanAux mode env declName fuel clean (pushValAndImplDeps env n ci? clean stack) none
              | .mutRefs =>
                  if isMutableRefConst n then .error s!"kernel gate: `{declName}` transitively uses mutable reference primitive `{n}` (Landin's knot) outside framework modules"
                  else
                    let clean := clean.insert n
                    let stack := if isFrameworkModule (definingModule env n) then stack else pushValAndImplDeps env n ci? clean stack
                    dfsCleanAux mode env declName fuel clean stack none
              | .axioms => match ci? with
                  | none => dfsCleanAux mode env declName fuel (clean.insert n) stack none
                  | some (.axiomInfo ax) =>
                      if allowedKernelAxioms.contains ax.name && !ax.isUnsafe then dfsCleanAux mode env declName fuel (clean.insert n) stack none
                      else .error s!"kernel gate: `{declName}` depends on disallowed axiom `{ax.name}` (only {allowedKernelAxioms} are permitted)"
                  | some ci => let clean := clean.insert n; dfsCleanAux mode env declName fuel clean (pushConstDeps ci clean stack) none

private def dfsClean (mode : DfsMode) (env : Environment) (declName : Name)
    (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) :=
  if clean.contains declName then .ok clean else dfsCleanAux mode env declName 2000000 clean #[declName] initCi?

def verifyNoToolchainPartials (env : Environment) (declName : Name) (clean : Std.HashSet Name)
    (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean .partials env declName clean initCi?
def verifyNoMutableRefs (env : Environment) (declName : Name) (clean : Std.HashSet Name)
    (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean .mutRefs env declName clean initCi?
def verifyConstAxioms (env : Environment) (declName : Name) (clean : Std.HashSet Name)
    (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) := dfsClean .axioms env declName clean initCi?

private def forbiddenCustomClass (c : Name) : Bool :=
  c == `Std.Iterator || c == `Std.IteratorLoop || c == `Std.Stream || c == `Std.PRange.UpwardEnumerable

private def metaAliasAllowlist : Array Name := #[
  `Lean.MacroM, `Lean.Macro, `Lean.CoreM, `Lean.Meta.MetaM, `Lean.Elab.Command.CommandElabM,
  `Lean.Elab.Command.CommandElab, `Lean.Elab.Term.TermElabM, `Lean.Elab.Term.TermElab, `Lean.Elab.Tactic.TacticM,
  `Lean.Elab.Tactic.Tactic, `Lean.PrettyPrinter.Formatter, `Lean.PrettyPrinter.Parenthesizer,
  `Lean.PrettyPrinter.Unexpander, `Lean.PrettyPrinter.Delaborator.Delab
]

private def stripTypeBinders : Expr → Expr
  | .forallE _ _ b _ | .lam _ _ b _ | .mdata _ b => stripTypeBinders b | e => e

private def unfoldReturnHead (env : Environment) (stop : Name → Bool) (e : Expr) (fuel : Nat := 16) :
    Except String (Option Name) :=
  let e0 := stripTypeBinders ((stripTypeBinders e).headBeta)
  match e0 with
  | .letE _ _ v b _ => match fuel with
    | 0 => .error "type alias unfolding exceeded depth limit in `let` binder"
    | f + 1 => unfoldReturnHead env stop (b.instantiate1 v) f
  | _ => match e0.getAppFn.consumeMData with
    | .const c _ =>
        if stop c then .ok (some c)
        else match env.find? c with
        | some (.defnInfo dv) => match fuel with
          | 0 => .error s!"type alias unfolding exceeded depth limit at `{c}`"
          | f + 1 => unfoldReturnHead env stop (dv.value.beta e0.getAppArgs) f
        | _ => .ok (some c)
    | _ => .ok none

private def hasMetaReturnType (env : Environment) (e : Expr) : Bool :=
  match unfoldReturnHead env (fun c => isMetaNamespaceConst env c && metaAliasAllowlist.contains c) e with
  | .ok (some c) => isMetaNamespaceConst env c | _ => false

@[inline] private def addCSimp (modName : Name) (e : Lean.Compiler.CSimp.Entry)
    (bad? : Option (Name × Name)) (rm : Std.HashMap Name (Array Name)) :
    Option (Name × Name) × Std.HashMap Name (Array Name) :=
  let bad' := match bad? with
    | some _ => bad?
    | none => if !isToolchainModule modName && !isFrameworkModule modName then some (modName, e.thmName) else none
  let cur := rm.getD e.fromDeclName #[]
  (bad', if cur.contains e.toDeclName then rm else rm.insert e.fromDeclName (cur.push e.toDeclName))

private def collectCSimpData (env : Environment) :
    Option (Name × Name) × Std.HashMap Name (Array Name) := Id.run do
  let mut bad? : Option (Name × Name) := none; let mut rm : Std.HashMap Name (Array Name) := {}
  for modIdx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[modIdx]!
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
      let (b, r) := addCSimp modName (match scEntry with | .global e | .scoped _ e => e) bad? rm; bad? := b; rm := r
  for (_, e) in (Lean.Compiler.CSimp.ext.getState env).map.toList do
    let (b, r) := addCSimp (definingModule env e.thmName) e bad? rm; bad? := b; rm := r
  return (bad?, rm)

private def verifyCSimpClean (env : Environment) : Except String (Std.HashMap Name (Array Name)) := do
  let (bad?, repls) := collectCSimpData env
  if let some (modName, declName) := bad? then
    throw s!"kernel gate: `@[csimp]` declaration `{declName}` in `{modName}` is forbidden outside framework modules"
  return repls

private def owningKernelConst? (env : Environment) : Name → Option Name
  | .anonymous => none
  | n => if env.contains n then some n else match n with | .str p _ | .num p _ => owningKernelConst? env p | .anonymous => none

mutual
private def collectIrCallees : Lean.IR.FnBody → Array Name → Array Name
  | .vdecl _ _ e b, acc => collectIrCallees b (match e with | .fap c _ | .pap c _ => acc.push c | _ => acc)
  | .jdecl _ _ v b, acc => collectIrCallees b (collectIrCallees v acc)
  | .case _ _ _ alts, acc => collectIrCalleesAlts alts.toList acc
  | .set _ _ _ b, acc | .setTag _ _ b, acc | .uset _ _ _ b, acc | .sset _ _ _ _ _ b, acc
  | .inc _ _ _ _ b, acc | .dec _ _ _ _ b, acc | .del _ b, acc => collectIrCallees b acc
  | .ret _, acc | .jmp _ _, acc | .unreachable, acc => acc

private def collectIrCalleesAlts : List Lean.IR.Alt → Array Name → Array Name
  | [], acc => acc | .ctor _ b :: rest, acc | .default b :: rest, acc => collectIrCalleesAlts rest (collectIrCallees b acc)
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
    match ci with
    | .opaqueInfo _ => if !isLegitOpaque env modName n then
        throw s!"kernel gate: `partial` or `opaque` declaration `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"
    | .defnInfo dv =>
        if dv.safety != .safe && !isTotalCompilerAux env n && !isCtorIdxImpl then
          if let .str root "_unsafe_rec" := n then
            if let some (.opaqueInfo _) := env.find? root then
              throw s!"kernel gate: `partial` or `opaque` declaration `{root}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"
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
        for c in collectIrCallees b #[] do checkIrCallee env isNonFw checkTcPartials n modName false c
  if Lean.isExtern env n && !isAllowedExternMod modName then
    throw s!"kernel gate: unverified `@[extern]` `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"

@[inline] private def hasOwnerMarker (env : Environment) (owner marker : Name) : Bool :=
  !owner.isAnonymous && env.contains (owner ++ marker)

def isServerOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && (hasOwnerMarker env owner `_qed_server_marker ||
    (env.find? (owner ++ `dispatchM)).any (exprHasConst (· == `Qed.Server.RequestCtx) ·.type))
def isExternalOwner (env : Environment) (owner : Name) : Bool := hasOwnerMarker env owner `_qed_external_marker
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
private def dbOnlyLeaves : Array String := #["config", "ensureSchema", "ddl", "rlsDdl", "instSafeIOEnsureSchema"]

def isServerOnlyDeclName (env : Environment) : Name → Bool
  | .anonymous => false | .num p _ => isServerOnlyDeclName env p
  | .str owner s =>
      if s.startsWith "_closed_" then isServerOnlyDeclName env owner && !isBenignEmptyCseThunk env (.str owner s)
      else ((serverOnlyLeaves.contains s || s.endsWith "_step" || s.endsWith "_handler" || s.endsWith "_project") && isServerOwner env owner) ||
        (dbOnlyLeaves.contains s && isDatabaseOwner env owner) ||
        ((s == "schema" || s == "decodeRow") && (isDatabaseOwner env owner || isDatabaseOwner env owner.getPrefix)) ||
        (s == "config" && isAuthOwner env owner) || (s == "spec" && isDeployOwner env owner) ||
        (s == "baseUrl" && externalHasSecrets env owner) ||
        (s == "secrets" && (isServerOwner env owner || isExternalOwner env owner || isDatabaseOwner env owner || isAuthOwner env owner)) ||
        isServerOnlyDeclName env owner

private def serverOnlyModules : Std.HashSet Name := Std.HashSet.ofList [
  `Qed.Server.Prim, `Qed.Server.Native, `Qed.Server.Http, `Qed.Server.Net, `Qed.Server.Db.PgWire,
  `Qed.Server.Db.HttpSql, `Qed.Auth.Oidc, `Qed.Deploy, `Qed.Cloud.Compile, `Qed.Cloud.Proofs,
  `Qed.Cloud.GcpApi, `Qed.Cloud.Executor
]
private def serverOnlyDecls : Std.HashSet Name := Std.HashSet.ofList [
  `Qed.Server.ServerEffect, `Qed.Server.execExternalRaw, `Qed.Server.MonadServer.exec, `Qed.Server.MonadServer.httpCall,
  `Qed.Server.MonadServer.dbExec, `Qed.Server.MonadServer.dbExecDdl, `Qed.Server.MonadServer.dbTxBegin,
  `Qed.Server.MonadServer.dbTxExec, `Qed.Server.MonadServer.dbTxCommit, `Qed.Server.MonadServer.dbTxRollback,
  `Qed.Server.MonadServer.setCookie, `Qed.Server.MonadServer.sendSse, `Qed.Server.MonadServer.readEnv,
  `Qed.Server.MonadServer.nowMs, `Qed.Server.MonadServer.randomHex, `Qed.Server.MonadServer.hmacSha256,
  `Qed.Server.MonadServer.wsBroadcast, `Qed.Server.flushWsEmits, `Qed.Server.MonadAtomic.runAtomic,
  `Qed.Server.MonadAtomic.runAtomicRead, `Qed.Server.Webhook.postJson, `Qed.Server.Webhook.postBytes
]

def clientLeakReason? (env : Environment) (n : Name) : Option String :=
  let modName := definingModule env n
  if serverOnlyModules.contains modName then
    some s!"client bundle leak gate: server runtime primitive `{n}` (`{modName}`) cannot be bundled into client JavaScript"
  else if serverOnlyDecls.contains n || n.getPrefix == `Qed.Server.ServerEffect then
    some s!"client bundle leak gate: server I/O or state primitive `{n}` cannot be bundled into client JavaScript"
  else if isServerOnlyDeclName env n then
    some s!"client bundle leak gate: server secret/state/handler `{n}` cannot be bundled into client JavaScript"
  else none

def verifyNoServerLeakInClient (env : Environment) (reachable : Array Name) : Except String Unit := do
  for n in reachable do
    if let some err := clientLeakReason? env n then
      throw err

private def walkKernelClosureAux (env : Environment) (csimpRepls : Std.HashMap Name (Array Name))
    (checkLeak : Bool) : Nat → Array Name → Std.HashSet Name → Std.HashSet String →
    Except String (Std.HashSet Name × Std.HashSet String)
  | fuel, stack, visited, strLits =>
      if stack.isEmpty then .ok (visited, strLits)
      else
        let n := stack.back!; let stack := stack.pop
        match fuel with
        | 0 => .error (if checkLeak then s!"client bundle leak gate: kernel expression check exceeded fuel limit while inspecting `{n}`"
            else s!"kernel gate: reachability closure exceeded fuel limit while inspecting `{n}`")
        | fuel + 1 =>
            if visited.contains n then walkKernelClosureAux env csimpRepls checkLeak fuel stack visited strLits
            else if let some err := if checkLeak then clientLeakReason? env n else none then .error err
            else
              let isTc := isToolchainModule (definingModule env n)
              let visited := if checkLeak || !isTc then visited.insert n else visited
              if isTc then walkKernelClosureAux env csimpRepls checkLeak fuel stack visited strLits
              else
                let stack := (Lean.getInitFnNameFor? env n).elim stack (pushUnseen visited stack)
                let stack := (Compiler.getImplementedBy? env n).elim stack (pushUnseen visited stack)
                let unsafeRec := Name.str n "_unsafe_rec"
                let stack := if env.contains unsafeRec then pushUnseen visited stack unsafeRec else stack
                let stack := (csimpRepls.getD n #[]).foldl (pushUnseen visited) stack
                let (stack, strLits) := match env.find? n with
                  | none => (stack, strLits)
                  | some ci =>
                      let stack := pushConstDeps ci visited stack (withRecAll := false)
                      let strLits := if checkLeak then match ci with | .defnInfo v | .opaqueInfo v => collectExprStrLits v.value strLits | _ => strLits else strLits
                      (stack, strLits)
                walkKernelClosureAux env csimpRepls checkLeak fuel stack visited strLits

private def walkKernelClosure (env : Environment) (csimpRepls : Std.HashMap Name (Array Name))
    (checkLeak : Bool) (seeds : Array Name) (initVisited : Std.HashSet Name)
    (initStrLits : Std.HashSet String := {}) : Except String (Std.HashSet Name × Std.HashSet String) :=
  walkKernelClosureAux env csimpRepls checkLeak 1000000 seeds initVisited initStrLits

private def isCompilerNumSuffix (pfx s : String) : Bool :=
  s.startsWith pfx && let tail := s.toList.drop pfx.length; !tail.isEmpty && tail.all fun c => '0' ≤ c && c ≤ '9'

private def hasStrictSharedIrAuxSuffix : Name → Bool
  | .str p s => isCompilerNumSuffix "_closed_" s || isCompilerNumSuffix "_lam_" s ||
      ((s == "_redArg" || s == "_boxed" || isCompilerNumSuffix "_boxed_const_" s) && hasStrictSharedIrAuxSuffix p)
  | _ => false

private def closedIrStrLit? (env : Environment) (n : Name) : Option String :=
  match Lean.IR.findEnvDecl env n with
  | some (.fdecl _ xs _ (.vdecl v1 _ (.lit (.str s)) (.ret (.var v2))) _) => if xs.isEmpty && v1 == v2 then some s else none
  | _ => none

private def isRuntimeDbgPrim (n : Name) : Bool :=
  n == ``dbgTrace || n == ``dbgTraceIfShared || n == ``dbgSleep || n == ``panicCore || n == ``dbgStackTrace

def verifyNoServerLeakInClientExprs (env : Environment) (roots : List Name) (irReachable : Array Name := #[]) : Except String Unit := do
  let (_, csimpRepls) := collectCSimpData env
  let (exprVis, exprStrLits) ← walkKernelClosure env csimpRepls true roots.toArray
    (Std.HashSet.emptyWithCapacity 4096) (Std.HashSet.emptyWithCapacity 1024)
  let mut exprMods : Std.HashSet Name := {}
  for c in exprVis do let m := definingModule env c; if !m.isAnonymous && !isToolchainModule m then exprMods := exprMods.insert m
  let mut extraSeeds := irReachable
  for n in irReachable do
    if isRuntimeDbgPrim n && !exprVis.contains n then
      throw s!"client bundle leak gate: IR-reachable `{n}` is absent from kernel dependencies of client entrypoints (possible `@[local csimp]` rewrite)"
    let base := (owningKernelConst? env n).getD n; let baseMod := definingModule env base
    let isSharedAux := !env.contains n && hasStrictSharedIrAuxSuffix n
    let missingUserBase := !exprVis.contains base && env.contains base && !isToolchainModule baseMod && !isFrameworkModule baseMod
    if !isSharedAux then
      if missingUserBase then
        throw s!"client bundle leak gate: IR-reachable `{n}` (owner `{base}`) is absent from kernel dependencies of client entrypoints (possible `@[local csimp]` rewrite)"
      if base != n then extraSeeds := extraSeeds.push base
    else if missingUserBase then
      if !exprMods.contains baseMod then
        throw s!"client bundle leak gate: IR-reachable `{n}` (owner `{base}` in `{baseMod}`) is absent from client entrypoint modules (possible `@[local csimp]` rewrite)"
      else if !isBenignEmptyCseThunk env n && !((closedIrStrLit? env n).any exprStrLits.contains) then
        extraSeeds := extraSeeds.push base
  discard <| walkKernelClosure env csimpRepls true extraSeeds exprVis exprStrLits

def verifyReachable (env : Environment) (reachable : Array Name) (roots : List Name := []) : Except String Unit := do
  let csimpRepls ← verifyCSimpClean env
  let mut clean : Std.HashSet Name := Std.HashSet.emptyWithCapacity 4096
  let mut cleanPartials : Std.HashSet Name := Std.HashSet.emptyWithCapacity 4096
  let mut cleanRefs : Std.HashSet Name := Std.HashSet.emptyWithCapacity 4096
  let mut kernelSeeds := roots.toArray
  for n in reachable do
    if isRuntimeLoopConst n then throw s!"kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop (`{n}`) is reachable at runtime"
    clean ← verifyConstAxioms env n clean
    let modName := definingModule env n
    if !isToolchainModule modName then verifyUserDecl env modName n (env.find? n)
    let owner := (owningKernelConst? env n).getD n
    if isForbiddenToolchainPartial env owner then
      throw s!"kernel gate: non-total toolchain `partial` declaration `{owner}` (via `{n}`) is reachable at runtime"
    if !isToolchainModule (definingModule env owner) && env.contains owner then kernelSeeds := kernelSeeds.push owner
  let (kernelClosure, _) ← walkKernelClosure env csimpRepls false kernelSeeds (Std.HashSet.emptyWithCapacity 4096)
  for k in kernelClosure do
    let modName := definingModule env k
    if !isToolchainModule modName then
      let ci? := env.find? k
      verifyUserDecl env modName k ci?
      clean ← verifyConstAxioms env k clean
      if !(isFrameworkModule modName && ci?.any (isCompileTimeMetaDecl env k ·)) then cleanPartials ← verifyNoToolchainPartials env k cleanPartials ci?
      if !isFrameworkModule modName then cleanRefs ← verifyNoMutableRefs env k cleanRefs ci?

private def irSpecTarget? (env : Environment) (n : Name) : Option Name :=
  let rec collectParts : Name → List (Sum String Nat) → List (Sum String Nat)
    | .anonymous, acc => acc | .str p s, acc => collectParts p (.inl s :: acc) | .num p k, acc => collectParts p (.inr k :: acc)
  let rec findAfterAt : List (Sum String Nat) → Option Name
    | [] => none
    | .inl "_at_" :: rest =>
        let cand := rest.foldl (init := Name.anonymous) fun acc part => match part with | .inl s => .str acc s | .inr k => .num acc k
        match owningKernelConst? env cand with
        | some o => if !isToolchainModule (definingModule env o) then some o else findAfterAt rest
        | none   => findAfterAt rest
    | _ :: rest => findAfterAt rest
  findAfterAt (collectParts n [])

private def resolveIrTarget (env : Environment) (n : Name) : Name :=
  match owningKernelConst? env n with
  | some o => if isToolchainModule (definingModule env o) then (irSpecTarget? env n).getD o else o
  | none   => (irSpecTarget? env n).getD n

private def checkTransitiveIr (env : Environment) (modIrMap : Std.HashMap Name Lean.IR.FnBody)
    (irName modName : Name) : Nat → Array Name → Std.HashSet Name → Std.HashSet Name → Std.HashSet Name →
    Except String (Std.HashSet Name × Std.HashSet Name × Std.HashSet Name)
  | fuel, irStack, cleanIrNodes, cleanPartials, cleanRefs =>
      if irStack.isEmpty then .ok (cleanIrNodes, cleanPartials, cleanRefs)
      else match fuel with
        | 0 => .error s!"kernel gate: transitive IR callee check for `{irName}` in `{modName}` exceeded fuel limit"
        | fuel + 1 => do
            let c := irStack.back!; let mut irStack := irStack.pop
            if cleanIrNodes.contains c then
              checkTransitiveIr env modIrMap irName modName fuel irStack cleanIrNodes cleanPartials cleanRefs
            else
              let cleanIrNodes := cleanIrNodes.insert c
              checkIrCallee env true true irName modName true c
              let cOwner := (owningKernelConst? env c).getD c; let cTarget := resolveIrTarget env c
              let mut cp := cleanPartials; let mut cr := cleanRefs
              if !isFrameworkModule (definingModule env cOwner) then
                cp ← verifyNoToolchainPartials env cOwner cp; cr ← verifyNoMutableRefs env cOwner cr
              if cTarget != cOwner && !isFrameworkModule (definingModule env cTarget) then
                cp ← verifyNoToolchainPartials env cTarget cp; cr ← verifyNoMutableRefs env cTarget cr
              let cTargetMod := definingModule env cTarget
              let cb? := (modIrMap.get? c).orElse fun _ =>
                if !isToolchainModule cTargetMod && !isFrameworkModule cTargetMod then
                  match Lean.IR.findEnvDecl env c with | some (.fdecl (body := cb) ..) => some cb | _ => none
                else none
              if let some cb := cb? then irStack := collectIrCallees cb irStack
              checkTransitiveIr env modIrMap irName modName fuel irStack cleanIrNodes cp cr

private def verifyModuleIndices (env : Environment) (idxs : Array Nat) (initCap : Nat) : Except String Nat := do
  let mut clean : Std.HashSet Name := Std.HashSet.emptyWithCapacity initCap
  let mut cleanPartials : Std.HashSet Name := Std.HashSet.emptyWithCapacity initCap
  let mut cleanRefs : Std.HashSet Name := Std.HashSet.emptyWithCapacity initCap
  let mut cleanIrNodes : Std.HashSet Name := Std.HashSet.emptyWithCapacity initCap
  let mut checkedCount : Nat := 0
  let (modNames, modData) := (env.header.moduleNames, env.header.moduleData)
  let csimpThms := (Lean.Compiler.CSimp.ext.getState env).thmNames
  for i in idxs do
    let modName := modNames[i]!; let isNonFw := !isFrameworkModule modName
    let consts := modData[i]!.constants; checkedCount := checkedCount + consts.size
    for ci in consts do
      let n := ci.name
      if isNonFw && csimpThms.contains n then throw s!"kernel gate: `@[csimp]` declaration `{n}` in `{modName}` is forbidden outside framework modules"
      match ci with
      | .axiomInfo _ => throw s!"kernel gate: custom `axiom {n}` declared in `{modName}` is forbidden"
      | .thmInfo _   => clean ← verifyConstAxioms env n clean (some ci)
      | _ => if isNonFw || !isCompileTimeMetaDecl env n ci then
          verifyUserDecl env modName n (some ci) (checkIr := false); clean ← verifyConstAxioms env n clean (some ci)
          if isNonFw && !hasMetaReturnType env ci.type then
            cleanPartials ← verifyNoToolchainPartials env n cleanPartials (some ci)
            cleanRefs ← verifyNoMutableRefs env n cleanRefs (some ci)
    let irEntries := Lean.IR.declMapExt.getModuleEntries env i
    let mut modIrMap : Std.HashMap Name Lean.IR.FnBody := {}
    if isNonFw then for d in irEntries do if let .fdecl (f := irName) (body := b) .. := d then modIrMap := modIrMap.insert irName b
    for d in irEntries do
      if let .fdecl (f := irName) (body := b) .. := d then
        let owner := resolveIrTarget env irName; let ownerCi? := env.find? owner
        let skipFwMeta := !isNonFw && match ownerCi? with | some ci => isCompileTimeMetaDecl env owner ci | none => hasRegBuiltin irName
        if !skipFwMeta then
          let checkTcPartials := isNonFw && !ownerCi?.any (hasMetaReturnType env ·.type)
          let callees := collectIrCallees b #[]
          for c in callees do checkIrCallee env isNonFw checkTcPartials irName modName false c
          if checkTcPartials && !cleanIrNodes.contains irName then
            let (cin, cp, cr) ← checkTransitiveIr env modIrMap irName modName 200000 callees (cleanIrNodes.insert irName) cleanPartials cleanRefs
            cleanIrNodes := cin; cleanPartials := cp; cleanRefs := cr
  return checkedCount

def verifyProjectEnv (env : Environment) (skipFramework : Bool := false) : Except String Nat := do
  discard <| verifyCSimpClean env
  let (modNames, modData) := (env.header.moduleNames, env.header.moduleData)
  let mut active : Array (Nat × Nat) := #[]; let mut totalDecls : Nat := 0
  for i in [0:min modNames.size modData.size] do
    let m := modNames[i]!
    if !isToolchainModule m && !(skipFramework && isFrameworkModule m) then
      let sz := modData[i]!.constants.size
      if sz > 0 then active := active.push (i, sz); totalDecls := totalDecls + sz
  if totalDecls < 4000 || active.size < 4 then return ← verifyModuleIndices env (active.map Prod.fst) (max 4096 (totalDecls * 2))
  let nWorkers := min 8 active.size
  let mut buckets := Array.replicate nWorkers #[]; let mut loads := Array.replicate nWorkers 0
  for (idx, sz) in active.qsort (·.2 > ·.2) do
    let mut bestW := 0
    for w in [1:nWorkers] do if loads[w]! < loads[bestW]! then bestW := w
    buckets := buckets.set! bestW (buckets[bestW]!.push idx); loads := loads.set! bestW (loads[bestW]! + sz)
  let tasks := buckets.map fun b => Task.spawn fun _ => verifyModuleIndices env b 16384
  tasks.foldlM (init := 0) fun acc t => return acc + (← t.get)

end Js
