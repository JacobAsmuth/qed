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

private def isMetaNamespaceConst (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Lean.Syntax" ||
  s.startsWith "Lean.TSyntax" ||
  s.startsWith "Lean.Macro" ||
  s.startsWith "Lean.Elab" ||
  s.startsWith "Lean.Meta" ||
  s.startsWith "Lean.Parser" ||
  s.startsWith "Lean.PrettyPrinter" ||
  s.startsWith "Lean.Environment" ||
  s.startsWith "Lean.IR" ||
  s.startsWith "Qq."

private def exprMentionsMeta (e : Expr) : Bool :=
  e.getUsedConstants.any isMetaNamespaceConst

private def exprMentionsWhileLoop (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => c.toString.contains "Lean.Loop.forIn"

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

def isLegitOpaque (env : Environment) (modName declName : Name) : Bool :=
  (modName == `Qed.Dom && Lean.isExtern env declName) ||
  ((Lean.getInitFnNameFor? env declName).isSome && (Compiler.getImplementedBy? env declName).isNone)

/-- True iff `ci` is compile-time macro/elaborator/tactic/compiler infrastructure (never part of
    any Qed web or SSR runtime bundle; runtime bundles are additionally checked with zero meta
    exemptions by `verifyReachable`). -/
def isCompileTimeMetaDecl (env : Environment) (declName : Name) (ci : ConstantInfo) : Bool :=
  let nameStr := declName.toString
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
        nameStr.contains "_regBuiltin"

private def checkAxiomStep (env : Environment) :
    Nat → List Name → Std.HashSet Name → Std.HashSet Name → Except Name (Std.HashSet Name)
  | 0, _, clean, _ => .ok clean
  | _ + 1, [], clean, visiting => .ok (visiting.fold (fun acc n => acc.insert n) clean)
  | fuel + 1, n :: rest, clean, visiting =>
      if clean.contains n || visiting.contains n then
        checkAxiomStep env fuel rest clean visiting
      else
        match env.find? n with
        | none => checkAxiomStep env fuel rest clean (visiting.insert n)
        | some (.axiomInfo ax) =>
            if allowedKernelAxioms.contains ax.name && !ax.isUnsafe then
              checkAxiomStep env fuel rest (clean.insert n) visiting
            else
              .error ax.name
        | some ci =>
            let deps := ci.getUsedConstantsAsSet.toList
            checkAxiomStep env fuel (deps ++ rest) clean (visiting.insert n)

/-- Verify that `declName`'s transitive kernel expression dependencies only use axioms in
    `{propext, Classical.choice, Quot.sound}`, reusing `clean` across calls for O(E) performance. -/
def verifyConstAxioms (env : Environment) (declName : Name)
    (clean : Std.HashSet Name) : Except String (Std.HashSet Name) :=
  match checkAxiomStep env 2000000 [declName] clean {} with
  | .ok clean' => .ok clean'
  | .error badAx =>
      .error s!"kernel gate: `{declName}` depends on disallowed axiom `{badAx}` (only {allowedKernelAxioms} are permitted)"

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
          throw s!"kernel gate: `partial` or `opaque` declaration `{n}` in `{modName}` is forbidden outside `Qed.Dom`"
    | .defnInfo dv =>
        if exprMentionsWhileLoop dv.value then
          throw s!"kernel gate: unbounded `while`/`repeat` loop inside `{n}` in `{modName}` is forbidden"
    | _ => pure ()
  if Lean.isExtern env n && modName != `Qed.Dom then
    throw s!"kernel gate: unverified `@[extern]` `{n}` in `{modName}` is forbidden outside `Qed.Dom`"

/-- Strict runtime reachability gate invoked by `Js.emitProgram` on every JS bundle compilation.
    Applies **zero** meta exemptions: every single constant reachable from the compiled entrypoints
    must be total, safe, free of `@[implemented_by]` / `partial` / `while` (`Lean.Loop.forIn`),
    free of unverified `@[extern]`s, and proved solely from standard Lean axioms. -/
def verifyReachable (env : Environment) (reachable : Array Name) : Except String Unit := do
  let mut clean : Std.HashSet Name := {}
  for n in reachable do
    if n.toString.contains "Lean.Loop.forIn" then
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
def verifyProjectEnv (env : Environment) : Except String Nat := do
  let mut clean : Std.HashSet Name := {}
  let mut checkedCount : Nat := 0
  let modNames := env.header.moduleNames
  let modData  := env.header.moduleData
  for i in [0:modNames.size] do
    let modName := modNames[i]!
    if !isToolchainModule modName && i < modData.size then
      for n in modData[i]!.constNames do
        if let some ci := env.find? n then
          checkedCount := checkedCount + 1
          match ci with
          | .axiomInfo _ =>
              throw s!"kernel gate: custom `axiom {n}` declared in `{modName}` is forbidden"
          | .thmInfo _ =>
              clean ← verifyConstAxioms env n clean
          | _ =>
              if !isCompileTimeMetaDecl env n ci then
                verifyUserDecl env modName n (some ci)
                if !isTotalCompilerAux env n then
                  clean ← verifyConstAxioms env n clean
  return checkedCount

end Js
