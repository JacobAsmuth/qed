import Qed.Style
import Qed.Runtime.App
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
  fn == ``Qed.css || fn == ``Qed.cssNamed || fn == ``Qed.Style.mk ||
  fn == ``Qed.Style.extend || fn == ``Qed.Style.merge || fn == ``Qed.Style.mergeMany ||
  fn == ``Qed.Style.withKeyframes || fn == ``Qed.Style.withExtraRule ||
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

open Lean Elab Term Meta in
private def discoverAssets (value : Expr) : TermElabM (Expr × Expr) := do
  let env ← getEnv
  let styleMetaMap := Qed.StyleDsl.styleMetaRegistry.getState env
  let tokMetaMap   := Qed.StyleDsl.tokenMetaRegistry.getState env
  let themeMetaMap := Qed.StyleDsl.themeMetaRegistry.getState env
  let mut pending := value.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut regs : Array Expr := #[]
  let mut styles : Array Expr := #[]
  let mut themeStyles : Array Expr := #[]
  let mut seenThemes : NameSet := {}
  let mut inlineStyles ← collectInlineStylesFromExpr env value #[]
  let addThemeStyle := fun (thNm : Name) (seenTh : NameSet) (thArr : Array Expr) =>
    if seenTh.contains thNm then (seenTh, thArr)
    else
      match themeMetaMap.find? thNm with
      | some thInfo =>
          if env.contains thInfo.styleConst then
            (seenTh.insert thNm, thArr.push (Lean.mkConst thInfo.styleConst))
          else (seenTh.insert thNm, thArr)
      | none => (seenTh.insert thNm, thArr)
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      let reg := n.getPrefix ++ `regs
      let isMount := match n with
        | .str _ s => s == "_qed_mount" || s == "_qed_mountWithOpt"
        | _ => false
      if isMount && env.contains reg then
        regs := regs.push (Lean.mkConst reg)
        let compView := n.getPrefix ++ `view
        if env.contains compView then
          pending := compView :: pending
      else if let some (.defnInfo d) := env.find? n then
        if d.type.isConstOf ``Qed.Style then
          styles := styles.push (Lean.mkConst n)
          if let some sm := styleMetaMap.find? n then
            for thNm in sm.themes do
              let (st', ta') := addThemeStyle thNm seenThemes themeStyles
              seenThemes := st'; themeStyles := ta'
        else if d.type.isConstOf ``Qed.Theme then
          let styleConst := n.getPrefix ++ `style
          if env.contains styleConst then
            let (st', ta') := addThemeStyle n.getPrefix seenThemes themeStyles
            seenThemes := st'; themeStyles := ta'
          else
            themeStyles := themeStyles.push (Lean.mkApp (Lean.mkConst ``Qed.Theme.asStyle) (Lean.mkConst n))
        else if d.type.isConstOf ``Qed.Keyframes then
          themeStyles := themeStyles.push (Lean.mkApp (Lean.mkConst ``Qed.Keyframes.asStyle) (Lean.mkConst n))
        else if let some tm := tokMetaMap.find? n then
          if let some thNm := tm.themeName? then
            let (st', ta') := addThemeStyle thNm seenThemes themeStyles
            seenThemes := st'; themeStyles := ta'
        else if !isFrameworkRoot env n then
          inlineStyles ← collectInlineStylesFromExpr env d.value inlineStyles
          pending := d.value.getUsedConstants.toList ++ pending
  let mut allStyles : Array Expr := themeStyles
  for s in styles do
    unless allStyles.contains s do allStyles := allStyles.push s
  for s in inlineStyles do
    unless allStyles.contains s do allStyles := allStyles.push s
  let mut locals := Lean.mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``LocalDef)
  for reg in regs do
    locals ← mkAppM ``List.append #[locals, reg]
  return (← mkAppM ``LocalDef.dedupe #[locals], ← mkListLit (Lean.mkConst ``Qed.Style) allStyles.toList)

syntax (name := registrationsTerm) "qedInternalLocalRegistrations% " term:max : term
syntax (name := stylesTerm) "qedInternalStyles% " term:max : term

open Lean Elab Term in
@[term_elab registrationsTerm] def elabRegistrations : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return (← discoverAssets (← instantiateMVars value)).1

open Lean Elab Term in
@[term_elab stylesTerm] def elabStyles : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return (← discoverAssets (← instantiateMVars value)).2

end Qed.Internal
