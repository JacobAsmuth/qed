import Lean

open Lean

namespace Js

/-- The sole foundational axioms permitted in Qed's trusted kernel base:
    propositional extensionality, classical choice, and quotient soundness. -/
def allowedKernelAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

def isToolchainModule (modName : Name) : Bool :=
  let root := modName.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Lake

def definingModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous
  | none     => Name.anonymous

private def isAllowedKernelAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def rootTwoAux : Name → Option String → Option (String × Option String)
  | .str .anonymous r, second => some (r, second)
  | .str p s, _               => rootTwoAux p (some s)
  | .num p _, _               => rootTwoAux p none
  | .anonymous, _             => none

private def isMetaNamespaceConst (n : Name) : Bool :=
  match rootTwoAux n none with
  | some ("Lean", some s) =>
      s.startsWith "Syntax" ||
      s.startsWith "TSyntax" ||
      s.startsWith "Macro" ||
      s.startsWith "Elab" ||
      s.startsWith "Meta" ||
      s.startsWith "Parser" ||
      s.startsWith "PrettyPrinter" ||
      s.startsWith "Environment" ||
      s.startsWith "IR"
  | some ("Qq", _) => n != `Qq
  | _ => false

private def exprMentionsMeta (e : Expr) : Bool :=
  e.foldConsts false fun c acc => acc || isMetaNamespaceConst c

private def isWhileLoopConst : Name → Bool
  | .str (.str (.str p r) "Loop") s =>
      if r.endsWith "Lean" && s.startsWith "forIn" then true
      else isWhileLoopConst (.str (.str p r) "Loop")
  | .str p s => (s.length >= 15 && s.contains "Lean.Loop.forIn") || isWhileLoopConst p
  | .num p _ => isWhileLoopConst p
  | .anonymous => false

private def exprMentionsWhileLoop (e : Expr) : Bool :=
  e.foldConsts false fun c acc => acc || isWhileLoopConst c

private def hasRegBuiltin : Name → Bool
  | .str p s => s.contains "_regBuiltin" || hasRegBuiltin p
  | .num p _ => hasRegBuiltin p
  | .anonymous => false

/-- Find the root declaration of a compiler-synthesized `_unsafe_rec` / stage auxiliary, if any. -/
private def stripCompilerRecSuffix : Name → Option Name
  | .str p "_unsafe_rec" => some p
  | .str p s =>
      if s.startsWith "_unsafe_rec" || s.startsWith "_cstage" || s.startsWith "_closed_" then
        match stripCompilerRecSuffix p with
        | some root => some root
        | none      => some p
      else
        stripCompilerRecSuffix p
  | .num p _ => stripCompilerRecSuffix p
  | .anonymous => none

/-- In Lean 4, a kernel-proved total recursive `def foo` is stored as `ConstantInfo.defnInfo`
    (with a full termination proof in the kernel), while the code generator synthesizes
    `foo._unsafe_rec` and sets `implemented_by foo._unsafe_rec` for direct recursive codegen.
    By contrast, `partial def bar` is stored as `ConstantInfo.opaqueInfo`!
    Thus `foo._unsafe_rec` is legitimate iff `foo` itself is a non-unsafe `ConstantInfo.defnInfo`. -/
def isTotalCompilerAux (env : Environment) (declName : Name) : Bool :=
  match stripCompilerRecSuffix declName with
  | some root =>
      match env.find? root with
      | some (.defnInfo dv) => dv.safety == .safe
      | _                   => false
  | none => false

def isLegitTotalRecImpl (env : Environment) (declName implName : Name) : Bool :=
  match env.find? declName with
  | some (.defnInfo dv) =>
      dv.safety == .safe && implName == Name.str declName "_unsafe_rec"
  | _ => false

def isAllowedExternMod (modName : Name) : Bool :=
  modName == `Qed.Dom || modName == `Qed.Server.Prim

def isLegitOpaque (env : Environment) (modName declName : Name) : Bool :=
  (isAllowedExternMod modName && Lean.isExtern env declName) ||
  (modName == `Qed.Server.Prim &&
    (declName == `Qed.Server.Prim.StateBoxPointed || declName == `Qed.Server.Prim.StaticDirPointed)) ||
  ((Lean.getInitFnNameFor? env declName).isSome && (Compiler.getImplementedBy? env declName).isNone)

/-- True iff `ci` is compile-time macro/elaborator/tactic/compiler infrastructure (never part of
    any Qed web or SSR runtime bundle; runtime bundles are additionally checked with zero meta
    exemptions by `verifyReachable`). -/
def isCompileTimeMetaDecl (env : Environment) (declName : Name) (ci : ConstantInfo) : Bool :=
  if exprMentionsMeta ci.type then true
  else match ci.value? with
  | some v => exprMentionsMeta v
  | none   =>
      let parent := (stripCompilerRecSuffix declName).getD declName.getPrefix
      if !parent.isAnonymous && parent != declName then
        match env.find? parent with
        | some pci => exprMentionsMeta pci.type || (pci.value?.any exprMentionsMeta)
        | none     => false
      else
        hasRegBuiltin declName

private inductive AxiomCheckErr where
  | disallowed (ax : Name)
  | fuelExhausted (pending : Name)

private def pushExprDeps (e : Expr) (clean : Std.HashSet Name) (stack : Array Name) : Array Name :=
  e.foldConsts stack fun c acc => if clean.contains c then acc else acc.push c

private def pushConstDeps (ci : ConstantInfo) (clean : Std.HashSet Name) (stack : Array Name) : Array Name :=
  let stack := pushExprDeps ci.type clean stack
  match ci with
  | .defnInfo val   => pushExprDeps val.value clean stack
  | .thmInfo val    => pushExprDeps val.value clean stack
  | .opaqueInfo val => pushExprDeps val.value clean stack
  | .inductInfo val => val.ctors.foldl (fun acc c => if clean.contains c then acc else acc.push c) stack
  | .ctorInfo val   => if clean.contains val.name then stack else stack.push val.name
  | .recInfo val    => val.all.foldl (fun acc c => if clean.contains c then acc else acc.push c) stack
  | _ => stack

private def checkAxiomLoop (env : Environment) (declName : Name) (initCi? : Option ConstantInfo)
    (clean : Std.HashSet Name) : Except AxiomCheckErr (Std.HashSet Name) := Id.run do
  if clean.contains declName then return .ok clean
  let mut clean := clean
  let mut stack : Array Name := #[]
  let mut fuel : Nat := 2000000
  match initCi? with
  | some (.axiomInfo ax) =>
      if isAllowedKernelAxiom ax.name && !ax.isUnsafe then
        return .ok (clean.insert declName)
      else
        return .error (.disallowed ax.name)
  | some ci =>
      fuel := fuel - 1
      clean := clean.insert declName
      stack := pushConstDeps ci clean stack
  | none =>
      stack := stack.push declName
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if clean.contains n then
      continue
    if fuel == 0 then
      return .error (.fuelExhausted n)
    fuel := fuel - 1
    match env.find? n with
    | none =>
        clean := clean.insert n
    | some (.axiomInfo ax) =>
        if isAllowedKernelAxiom ax.name && !ax.isUnsafe then
          clean := clean.insert n
        else
          return .error (.disallowed ax.name)
    | some ci =>
        clean := clean.insert n
        stack := pushConstDeps ci clean stack
  return .ok clean

/-- Verify that `declName`'s transitive kernel expression dependencies only use axioms in
    `{propext, Classical.choice, Quot.sound}`, reusing `clean` across calls for O(E) performance.
    Fails closed if traversal exceeds fuel. -/
def verifyConstAxioms (env : Environment) (declName : Name)
    (clean : Std.HashSet Name) (initCi? : Option ConstantInfo := none) : Except String (Std.HashSet Name) :=
  match checkAxiomLoop env declName initCi? clean with
  | .ok clean' => .ok clean'
  | .error (.disallowed badAx) =>
      .error s!"kernel gate: `{declName}` depends on disallowed axiom `{badAx}` (only {allowedKernelAxioms} are permitted)"
  | .error (.fuelExhausted pending) =>
      .error s!"kernel gate: axiom check for `{declName}` exceeded fuel limit while inspecting `{pending}`"

private def verifyUserDecl (env : Environment) (modName n : Name) (ci? : Option ConstantInfo) :
    Except String Unit := do
  if let some impl := Compiler.getImplementedBy? env n then
    if !isLegitTotalRecImpl env n impl then
      throw s!"kernel gate: `@[implemented_by {impl}]` or `partial def` on `{n}` in `{modName}` is forbidden"
  if let some ci := ci? then
    if ci.isUnsafe && !isTotalCompilerAux env n then
      throw s!"kernel gate: `unsafe` or `partial` declaration `{n}` in `{modName}` is forbidden"
    match ci with
    | .opaqueInfo _ =>
        if !isLegitOpaque env modName n then
          throw s!"kernel gate: `partial` or `opaque` declaration `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"
    | .defnInfo dv =>
        if exprMentionsWhileLoop dv.value then
          throw s!"kernel gate: unbounded `while`/`repeat` loop inside `{n}` in `{modName}` is forbidden"
    | _ => pure ()
  if Lean.isExtern env n && !isAllowedExternMod modName then
    throw s!"kernel gate: unverified `@[extern]` `{n}` in `{modName}` is forbidden outside `Qed.Dom` and `Qed.Server.Prim`"

/-- True iff `owner` is a `server` namespace (marked by `_qed_server_marker` emitted by
    `server` elaboration, or carrying a `dispatchM` taking `Qed.Server.RequestCtx`). -/
def isServerOwner (env : Environment) (owner : Name) : Bool :=
  if owner.isAnonymous then false
  else if env.contains (owner ++ `_qed_server_marker) then true
  else match env.find? (owner ++ `dispatchM) with
    | some ci => ci.type.foldConsts false fun c acc => acc || c == `Qed.Server.RequestCtx
    | none    => false

/-- True iff `owner` is an `external` service namespace (marked by `_qed_external_marker`). -/
def isExternalOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && env.contains (owner ++ `_qed_external_marker)

/-- True iff `owner` is a `database` namespace (marked by `_qed_database_marker`). -/
def isDatabaseOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && env.contains (owner ++ `_qed_database_marker)

/-- True iff `owner` is an `auth` namespace (marked by `_qed_auth_marker`). -/
def isAuthOwner (env : Environment) (owner : Name) : Bool :=
  !owner.isAnonymous && env.contains (owner ++ `_qed_auth_marker)

/-- True iff `n` (or an enclosing non-`_closed_` declaration prefix, e.g. `match_*` / `_unsafe_rec`
    auxiliaries) is a server-only declaration owned by a `server`, `external`, `database`, or `auth` block.
    Module-wide CSE `_closed_*` thunks (such as a shared empty `Array.mkEmpty 0`) are excluded
    because Lean's closed-term extractor reuses them across unrelated declarations in the same file. -/
def isServerOnlyDeclName (env : Environment) : Name → Bool
  | .anonymous => false
  | .num p _   => isServerOnlyDeclName env p
  | .str owner s =>
      if s.startsWith "_closed_" then
        false
      else if (s == "dispatchM" || s == "wsDispatchM" || s == "initState" || s == "runServer" ||
          s.endsWith "_step" || s.endsWith "_handler") && isServerOwner env owner then
        true
      else if (s == "config" || s == "ensureSchema" || s == "ddl" || s == "rlsDdl") && isDatabaseOwner env owner then
        true
      else if s == "config" && isAuthOwner env owner then
        true
      else if s == "secrets" && (isServerOwner env owner || isExternalOwner env owner || isDatabaseOwner env owner || isAuthOwner env owner) then
        true
      else
        isServerOnlyDeclName env owner

/-- Returns an error message iff `n` is a server-only primitive, secret, state initializer,
    handler, or dispatcher that must never be bundled into client JavaScript. -/
def clientLeakReason? (env : Environment) (n : Name) : Option String :=
  let modName := definingModule env n
  if modName == `Qed.Server.Prim || modName == `Qed.Server.Native ||
     modName == `Qed.Server.Db.PgWire || modName == `Qed.Server.Db.HttpSql ||
     modName == `Qed.Auth.Oidc then
    some s!"client bundle leak gate: server runtime primitive `{n}` (`{modName}`) cannot be bundled into client JavaScript"
  else if n == `Qed.Server.execExternalRaw ||
          n == `Qed.Server.MonadServer.exec ||
          n == `Qed.Server.MonadServer.httpCall ||
          n == `Qed.Server.MonadServer.dbExec ||
          n == `Qed.Server.MonadServer.dbExecDdl ||
          n == `Qed.Server.MonadServer.readEnv ||
          n == `Qed.Server.MonadServer.wsBroadcast ||
          n == `Qed.Server.flushWsEmits ||
          n == `Qed.Server.MonadAtomic.runAtomic ||
          n == `Qed.Server.MonadAtomic.runAtomicRead then
    some s!"client bundle leak gate: server I/O or state primitive `{n}` cannot be bundled into client JavaScript"
  else if isServerOnlyDeclName env n then
    some s!"client bundle leak gate: server secret/state/handler `{n}` cannot be bundled into client JavaScript"
  else
    none

/-- Verifies that zero server-only primitives, secrets, state boxes, handlers, or dispatchers
    are reachable from a compiled client JavaScript bundle. -/
def verifyNoServerLeakInClient (env : Environment) (reachable : Array Name) : Except String Unit := do
  for n in reachable do
    if let some err := clientLeakReason? env n then
      throw err

/-- Strict runtime reachability gate invoked by `Js.emitProgram` on every JS bundle compilation.
    Applies **zero** meta exemptions: every single constant reachable from the compiled entrypoints
    must be total, safe, free of `@[implemented_by]` / `partial` / `while` (`Lean.Loop.forIn`),
    free of unverified `@[extern]`s, and proved solely from standard Lean axioms. -/
def verifyReachable (env : Environment) (reachable : Array Name) : Except String Unit := do
  let mut clean : Std.HashSet Name := Std.HashSet.emptyWithCapacity 4096
  for n in reachable do
    if isWhileLoopConst n then
      throw s!"kernel gate: unbounded `while`/`repeat` loop (`{n}`) is reachable at runtime"
    if !isTotalCompilerAux env n then
      clean ← verifyConstAxioms env n clean
    let modName := definingModule env n
    if !isToolchainModule modName then
      verifyUserDecl env modName n (env.find? n)

/-- Whole-environment kernel verification gate across all non-toolchain modules (`Qed.*`, `Js.*`,
    `Examples.*`, and user app modules). Checks:
    1. Zero user/framework `axiom` declarations anywhere.
    2. 100% of theorems (`thmInfo`) use only `{propext, Classical.choice, Quot.sound}`.
    3. Every non-meta declaration is safe (not `unsafe`), total (no `partial` / `while` /
       `@[implemented_by]`), free of unverified `@[extern]`/`opaque` outside `Qed.Dom`, and
       axiom-clean. -/
def isFrameworkModule (modName : Name) : Bool :=
  let root := modName.getRoot
  root == `Qed || root == `Js || root == `Cli

private def verifyModuleIndices (env : Environment) (idxs : Array Nat) (initCap : Nat) : Except String Nat := do
  let mut clean : Std.HashSet Name := Std.HashSet.emptyWithCapacity initCap
  let mut checkedCount : Nat := 0
  let modNames := env.header.moduleNames
  let modData  := env.header.moduleData
  for i in idxs do
    let modName := modNames[i]!
    let consts := modData[i]!.constants
    checkedCount := checkedCount + consts.size
    for ci in consts do
      let n := ci.name
      match ci with
      | .axiomInfo _ =>
          throw s!"kernel gate: custom `axiom {n}` declared in `{modName}` is forbidden"
      | .thmInfo _ =>
          clean ← verifyConstAxioms env n clean (some ci)
      | _ =>
          if !isCompileTimeMetaDecl env n ci then
            verifyUserDecl env modName n (some ci)
            if !isTotalCompilerAux env n then
              clean ← verifyConstAxioms env n clean (some ci)
  return checkedCount

def verifyProjectEnv (env : Environment) (skipFramework : Bool := false) : Except String Nat := do
  let modNames := env.header.moduleNames
  let modData  := env.header.moduleData
  let mut active : Array (Nat × Nat) := #[]
  let mut totalDecls : Nat := 0
  for i in [0:modNames.size] do
    let modName := modNames[i]!
    let skip := isToolchainModule modName || (skipFramework && isFrameworkModule modName)
    if !skip && i < modData.size then
      let sz := modData[i]!.constants.size
      if sz > 0 then
        active := active.push (i, sz)
        totalDecls := totalDecls + sz
  if totalDecls < 4000 || active.size < 4 then
    return ← verifyModuleIndices env (active.map Prod.fst) (max 4096 (totalDecls * 2))
  -- Greedy longest-processing-time partition across up to 8 workers for balanced parallel checking.
  let sorted := active.qsort fun a b => a.2 > b.2
  let nWorkers := min 8 active.size
  let mut buckets : Array (Array Nat) := Array.replicate nWorkers #[]
  let mut loads : Array Nat := Array.replicate nWorkers 0
  for (idx, sz) in sorted do
    let mut bestW := 0
    let mut bestLoad := loads[0]!
    for w in [1:nWorkers] do
      let l := loads[w]!
      if l < bestLoad then
        bestW := w
        bestLoad := l
    buckets := buckets.set! bestW (buckets[bestW]!.push idx)
    loads := loads.set! bestW (bestLoad + sz)
  let tasks := buckets.map fun b =>
    Task.spawn fun _ => verifyModuleIndices env b 16384
  let mut checkedCount : Nat := 0
  for t in tasks do
    checkedCount := checkedCount + (← t.get)
  return checkedCount

end Js
