import Qed.Style.Syntax
import Qed.Runtime.LocalCore
import Lean

namespace Qed.Internal

open Lean Elab Term Meta in
private def isFrameworkRoot (env : Environment) (n : Name) : Bool :=
  let mod := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames.getD idx.toNat n
    | none     => n
  let root := mod.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Lake || root == `Qed

open Lean Elab Term Meta in
private def isStyleConstructorFn (env : Environment) (fn : Name) : Bool :=
  fn == ``Qed.Style.mk ||
  fn == ``Qed.Theme.asStyle || fn == ``Qed.Keyframes.asStyle ||
  match env.find? fn with
  | some (.defnInfo d) => d.type.getForallBody.isConstOf ``Qed.Style && !d.type.isConstOf ``Qed.Style
  | _ => false

open Lean Elab Term Meta in
private partial def collectInlineStylesFromExpr (env : Environment) (e : Expr)
    (acc : Array Expr) : MetaM (Array Expr) := do
  match e with
  | .app .. =>
      let fn := e.getAppFn
      let isClosedStyleApp ←
        if !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
          match fn with
          | .const fnName _ =>
              if isStyleConstructorFn env fnName then
                try
                  let ty ← whnf (← inferType e)
                  pure (ty.isConstOf ``Qed.Style)
                catch _ => pure false
              else pure false
          | _ => pure false
        else pure false
      if isClosedStyleApp then
        if acc.contains e then return acc
        else return acc.push e
      else
        let acc ← collectInlineStylesFromExpr env e.appFn! acc
        collectInlineStylesFromExpr env e.appArg! acc
  | .lam _ _ b _     => collectInlineStylesFromExpr env b acc
  | .letE _ _ v b _  =>
      let acc ← collectInlineStylesFromExpr env v acc
      collectInlineStylesFromExpr env b acc
  | .mdata _ b       => collectInlineStylesFromExpr env b acc
  | .proj _ _ b      => collectInlineStylesFromExpr env b acc
  | _                => return acc

private def isLocalMountConst : Lean.Name → Bool
  | .str _ s => s == "_qed_mount" || s == "_qed_mountWithOpt"
  | _        => false

open Lean Elab Term Meta in
private def walkAppDefs (value : Expr) (onMount : Name → MetaM Unit)
    (onDef : Name → DefinitionVal → MetaM Bool) : MetaM Unit := do
  let env ← getEnv
  let mut pending := value.getUsedConstants.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      let reg := n.getPrefix ++ `regs
      if isLocalMountConst n && env.contains reg then
        onMount reg
        let compView := n.getPrefix ++ `view
        if env.contains compView then
          pending := compView :: pending
      else if let some (.defnInfo d) := env.find? n then
        if (← onDef n d) && !isFrameworkRoot env n then
          pending := d.value.getUsedConstants.toList ++ pending

open Lean Elab Term Meta in
private def discoverRegistrations (value : Expr) : TermElabM Expr := do
  let regsRef ← IO.mkRef (#[] : Array Expr)
  walkAppDefs value
    (fun reg => regsRef.modify (·.push (Lean.mkConst reg)))
    (fun _ d => pure (!d.type.isConstOf ``Qed.Style && !d.type.isConstOf ``Qed.Theme && !d.type.isConstOf ``Qed.Keyframes))
  let mut locals := Lean.mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``LocalDef)
  for reg in (← regsRef.get) do
    locals ← mkAppM ``List.append #[locals, reg]
  mkAppM ``LocalDef.dedupe #[locals]

open Lean Elab Term Meta in
private def discoverStyles (value : Expr) : TermElabM Expr := do
  let env ← getEnv
  let styleMetaMap := Qed.StyleDsl.styleMetaRegistry.getState env
  let tokMetaMap   := Qed.StyleDsl.tokenMetaRegistry.getState env
  let themeMetaMap := Qed.StyleDsl.themeMetaRegistry.getState env
  let stylesRef ← IO.mkRef (#[] : Array Expr)
  let themeStylesRef ← IO.mkRef (#[] : Array Expr)
  let seenThemesRef ← IO.mkRef ({} : NameSet)
  let inlineStylesRef ← IO.mkRef (← collectInlineStylesFromExpr env value #[])
  let addThemeStyle (thNm : Name) : MetaM Unit := do
    if (← seenThemesRef.get).contains thNm then return
    seenThemesRef.modify (·.insert thNm)
    if let some thInfo := themeMetaMap.find? thNm then
      if env.contains thInfo.styleConst then
        themeStylesRef.modify (·.push (Lean.mkConst thInfo.styleConst))
  walkAppDefs value (fun _ => pure ()) fun n d => do
    if d.type.isConstOf ``Qed.Style then
      stylesRef.modify (·.push (Lean.mkConst n))
      if let some sm := styleMetaMap.find? n then
        for thNm in sm.themes do addThemeStyle thNm
      return false
    else if d.type.isConstOf ``Qed.Theme then
      if env.contains (n.getPrefix ++ `style) then addThemeStyle n.getPrefix
      else themeStylesRef.modify (·.push (Lean.mkApp (Lean.mkConst ``Qed.Theme.asStyle) (Lean.mkConst n)))
      return false
    else if d.type.isConstOf ``Qed.Keyframes then
      themeStylesRef.modify (·.push (Lean.mkApp (Lean.mkConst ``Qed.Keyframes.asStyle) (Lean.mkConst n)))
      return false
    else if let some tm := tokMetaMap.find? n then
      if let some thNm := tm.themeName? then addThemeStyle thNm
      return false
    else if !isFrameworkRoot env n then
      inlineStylesRef.set (← collectInlineStylesFromExpr env d.value (← inlineStylesRef.get))
      return true
    else return false
  let mut allStyles := ← themeStylesRef.get
  for s in (← stylesRef.get) ++ (← inlineStylesRef.get) do
    unless allStyles.contains s do allStyles := allStyles.push s
  mkListLit (Lean.mkConst ``Qed.Style) allStyles.toList

syntax (name := registrationsTerm) "qedInternalLocalRegistrations% " term:max : term
syntax (name := stylesTerm) "qedInternalStyles% " term:max : term

open Lean Elab Term in
private def elabValueThen (f : Expr → TermElabM Expr) : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  f (← instantiateMVars value)

open Lean Elab Term in
@[term_elab registrationsTerm] def elabRegistrations : TermElab := elabValueThen discoverRegistrations

open Lean Elab Term in
@[term_elab stylesTerm] def elabStyles : TermElab := elabValueThen discoverStyles

end Qed.Internal
