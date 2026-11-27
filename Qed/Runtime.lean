import Qed.Runtime.Cmd
import Qed.Runtime.App
import Qed.Ssr
import Qed.Style.Syntax
import Lean

namespace Qed.Internal

open Lean Elab Term Meta

private def isFrameworkRoot (env : Environment) (n : Name) : Bool := Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n n) (includeQed := true)

private def isStyleConstructorFn (env : Environment) (fn : Name) : Bool :=
  fn == ``Qed.Style.mk || fn == ``Qed.Theme.asStyle || fn == ``Qed.Keyframes.asStyle ||
  match env.find? fn with | some (.defnInfo d) => d.type.getForallBody.isConstOf ``Qed.Style && !d.type.isConstOf ``Qed.Style | _ => false

@[noinline] private partial def collectInlineStylesFromExpr (env : Environment) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  match e with
  | .app f a =>
      if let .const fnName _ := e.getAppFn then
        if !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && isStyleConstructorFn env fnName then
          if (← try pure ((← whnf (← inferType e)).isConstOf ``Qed.Style) catch _ => pure false) then
            return if acc.contains e then acc else acc.push e
      collectInlineStylesFromExpr env a (← collectInlineStylesFromExpr env f acc)
  | .lam _ _ b _ | .mdata _ b | .proj _ _ b => collectInlineStylesFromExpr env b acc
  | .letE _ _ v b _ => collectInlineStylesFromExpr env b (← collectInlineStylesFromExpr env v acc)
  | _ => return acc

@[noinline] private def walkAppDefs (value : Expr) (onMount : Name → MetaM Unit) (onDef : Name → DefinitionVal → MetaM Bool) : MetaM Unit := do
  let env ← getEnv; let mut pending := value.getUsedConstants.toList; let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n :: rest := pending | break
    pending := rest
    unless seen.contains n do
      seen := seen.insert n
      let isMount := match n with | .str _ s => s == "_qed_mount" || s == "_qed_mountWithOpt" | _ => false
      let reg := n.getPrefix ++ `regs
      if isMount && env.contains reg then
        onMount reg; let compView := n.getPrefix ++ `view; if env.contains compView then pending := compView :: pending
      else if let some (.defnInfo d) := env.find? n then
        if (← onDef n d) && !isFrameworkRoot env n then pending := d.value.getUsedConstants.toList ++ pending

@[noinline] private def discoverRegistrations (value : Expr) : TermElabM Expr := do
  let regsRef ← IO.mkRef (#[] : Array Expr)
  walkAppDefs value (fun reg => regsRef.modify (·.push (Lean.mkConst reg))) fun _ d =>
    pure (!d.type.isConstOf ``Qed.Style && !d.type.isConstOf ``Qed.Theme && !d.type.isConstOf ``Qed.Keyframes)
  let nilE := Lean.mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``LocalDef)
  mkAppM ``LocalDef.dedupe #[← (← regsRef.get).foldlM (init := nilE) fun acc reg => mkAppM ``List.append #[acc, reg]]

@[noinline] private def discoverStyles (value : Expr) : TermElabM Expr := do
  let env ← getEnv
  let (styleMetaMap, tokMetaMap, themeMetaMap) := (Qed.StyleDsl.styleMetaRegistry.getState env, Qed.StyleDsl.tokenMetaRegistry.getState env, Qed.StyleDsl.themeMetaRegistry.getState env)
  let stRef ← IO.mkRef ((#[] : Array Expr), (#[] : Array Expr), ({} : NameSet), ← collectInlineStylesFromExpr env value #[])
  let addThemeStyle (thNm : Name) : MetaM Unit := do
    let (styles, themeStyles, seen, inlines) ← stRef.get
    if seen.contains thNm then return
    let themeStyles := match themeMetaMap.find? thNm with
      | some thInfo => if env.contains thInfo.styleConst then themeStyles.push (Lean.mkConst thInfo.styleConst) else themeStyles
      | none => themeStyles
    stRef.set (styles, themeStyles, seen.insert thNm, inlines)
  walkAppDefs value (fun _ => pure ()) fun n d => do
    if d.type.isConstOf ``Qed.Style then
      stRef.modify fun (s, t, sn, i) => (s.push (Lean.mkConst n), t, sn, i)
      if let some sm := styleMetaMap.find? n then for thNm in sm.themes do addThemeStyle thNm
      return false
    else if d.type.isConstOf ``Qed.Theme then
      if env.contains (n.getPrefix ++ `style) then addThemeStyle n.getPrefix
      else stRef.modify fun (s, t, sn, i) => (s, t.push (Lean.mkApp (Lean.mkConst ``Qed.Theme.asStyle) (Lean.mkConst n)), sn, i)
      return false
    else if d.type.isConstOf ``Qed.Keyframes then
      stRef.modify fun (s, t, sn, i) => (s, t.push (Lean.mkApp (Lean.mkConst ``Qed.Keyframes.asStyle) (Lean.mkConst n)), sn, i); return false
    else if let some tm := tokMetaMap.find? n then
      if let some thNm := tm.themeName? then addThemeStyle thNm
      return false
    else if !isFrameworkRoot env n then
      let (s, t, sn, i) ← stRef.get; stRef.set (s, t, sn, ← collectInlineStylesFromExpr env d.value i); return true
    else return false
  let (styles, themeStyles, _, inlines) ← stRef.get
  mkListLit (Lean.mkConst ``Qed.Style) ((styles ++ inlines).foldl (init := themeStyles) fun acc s => if acc.contains s then acc else acc.push s).toList

syntax (name := registrationsTerm) "qedInternalLocalRegistrations% " term:max : term
syntax (name := stylesTerm) "qedInternalStyles% " term:max : term

private def elabValueThen (f : Expr → TermElabM Expr) : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none; synthesizeSyntheticMVarsNoPostponing; f (← instantiateMVars value)

@[term_elab registrationsTerm] def elabRegistrations : TermElab := elabValueThen discoverRegistrations
@[term_elab stylesTerm] def elabStyles : TermElab := elabValueThen discoverStyles

end Qed.Internal
