import Qed.Runtime.App
import Qed.View.Lift
import Lean

namespace Qed

syntax uiOpt := "(" ident (" := " term)? ")"
syntax (name := uiBuilder) "ui " term:max term:max (uiOpt)* " fun " ident " => " term : term
syntax (name := localRegistryTerm) "withLocalRegistry " term:max : term

open Lean Elab Term Meta in
private def discoverAssets (value : Expr) : TermElabM (Expr × Expr) := do
  let env ← getEnv
  let mut pending := value.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut regs : Array Expr := #[]
  let mut styles : Array Expr := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      let reg := n.getPrefix ++ `regs
      let isMount := match n with
        | .str _ s => s == "mount" || s == "mountWith" || s == "mountWithOpt"
        | _ => false
      if isMount && env.contains reg then
        regs := regs.push (Lean.mkConst reg)
        let compView := n.getPrefix ++ `view
        if env.contains compView then
          pending := compView :: pending
      else if let some (.defnInfo d) := env.find? n then
        if d.type.isConstOf ``Qed.Style then
          styles := styles.push (Lean.mkConst n)
        else
          pending := d.value.getUsedConstants.toList ++ pending
  let mut locals := Lean.mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``LocalDef)
  for reg in regs do
    locals ← mkAppM ``List.append #[locals, reg]
  return (← mkAppM ``LocalDef.dedupe #[locals], ← mkListLit (Lean.mkConst ``Qed.Style) styles.toList)

syntax (name := registrationsTerm) "localRegistrations " term:max : term

open Lean Elab Term in
@[term_elab registrationsTerm] def elabRegistrations : TermElab := fun stx _ => do
  let value ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return (← discoverAssets (← instantiateMVars value)).1

open Lean Elab Term Meta in
@[term_elab localRegistryTerm] def elabLocalRegistry : TermElab := fun stx expected => do
  let value ← elabTerm stx[1] expected
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let (locals, styles) ← discoverAssets value
  mkAppM ``App.addLocals #[value, locals, styles]

open Lean in
private def asIdentList? (t : TSyntax `term) : Option (Array Ident) :=
  match t with
  | `([$[$elems:term],*]) =>
      if elems.all (·.raw.isIdent) then some (elems.map fun e => ⟨e.raw⟩) else none
  | _ => none

open Lean in
private def asNegIdentList? (t : TSyntax `term) : Option (Array Ident) := do
  match t with
  | `([$[$elems:term],*]) =>
      if elems.isEmpty then failure
      elems.mapM fun | `(-$f:ident) => some f | _ => none
  | _ => none

open Lean in
private def applyDehydrateOpt (init update : TSyntax `term) (routeE? : Option (TSyntax `term))
    (base : TSyntax `term) : Option (Option (TSyntax `term)) → MacroM (TSyntax `term)
  | none        => `(withAutoDehydrate $init $base)
  | some none   => `(withAutoDehydrate! $init $base)
  | some (some e) => do
      if e.raw.isIdent then
        match e.raw.getId with
        | `true => return ← `(withAutoDehydrate! $init $base)
        | `false | `none | `Option.none => return base
        | _ => pure ()
      let mkFromRoute (getter : TSyntax `term) : MacroM (TSyntax `term) := do
        let some route := routeE? | Macro.throwErrorAt e "ui: `(dehydrate := .fromRoute ...)` requires `(onRoute := ...)`"
        `(Qed.App.withDehydrate (Dehydrate.fromRoute $init $update $route $getter) $base)
      match e with
      | `(.$id:ident) =>
          match id.getId with
          | `full | `auto => `(withAutoDehydrate! $init $base)
          | `none         => pure base
          | `fromRoute    => mkFromRoute (← `(id))
          | _             => `(Qed.App.withDehydrate $e $base)
      | `(.$id:ident $f:ident) =>
          if id.getId == `fromRoute then mkFromRoute (← `(fun m => m.$f:ident))
          else `(Qed.App.withDehydrate $e $base)
      | _ =>
          if let some fs := asIdentList? e then
            let d ← if fs.isEmpty then `(Dehydrate.const $init) else `(Dehydrate.fields $init [$[$fs:ident],*])
            `(Qed.App.withDehydrate $d $base)
          else if let some es := asNegIdentList? e then
            `(Qed.App.withDehydrate (Dehydrate.except $init [$[$es:ident],*]) $base)
          else
            `(Qed.App.withDehydrate $e $base)

open Lean in
macro_rules
  | `(ui $init $update $[$opts:uiOpt]* fun $m => $body) => do
      let tmpl ← `(view% fun $m => $body)
      let mut routeE?       : Option (TSyntax `term) := none
      let mut queriesE?     : Option (TSyntax `term) := none
      let mut dehydrateRaw? : Option (Option (TSyntax `term)) := none
      let mut startE  : TSyntax `term ← `(Qed.Cmd.none)
      let mut localsE : TSyntax `term ← `(([] : List Qed.LocalDef))
      let mut portE   : TSyntax `term ← `(Option.none)
      for opt in opts do
        match opt with
        | `(uiOpt| ($name:ident)) =>
            if name.getId != `dehydrate then
              Macro.throwErrorAt name s!"ui: option '{name.getId}' requires `:= <value>`"
            if dehydrateRaw?.isSome then Macro.throwErrorAt name "ui: duplicate `dehydrate` / `ephemeral` option"
            dehydrateRaw? := some none
        | `(uiOpt| ($name:ident := $e)) =>
            match name.getId with
            | `onRoute   => routeE?   := some e
            | `queries   => queriesE? := some e
            | `dehydrate =>
                if dehydrateRaw?.isSome then Macro.throwErrorAt name "ui: specify either `dehydrate` or `ephemeral`, not both"
                dehydrateRaw? := some (some e)
            | `ephemeral =>
                if dehydrateRaw?.isSome then Macro.throwErrorAt name "ui: specify either `dehydrate` or `ephemeral`, not both"
                if e.raw.isIdent then
                  let f : Ident := ⟨e.raw⟩
                  dehydrateRaw? := some (some (← `([-$f:ident])))
                else if let some es := asIdentList? e then
                  if es.isEmpty then dehydrateRaw? := some none
                  else dehydrateRaw? := some (some (← `([$[-$es:ident],*])))
                else
                  Macro.throwErrorAt e "ui: `ephemeral` expects a field name or list of field names `[field1, field2]`"
            | `start     => startE  := e
            | `locals    => localsE := e
            | `onPort    => portE   := ← `(Qed.ToPortOpt.toPortOpt $e)
            | _ => Macro.throwErrorAt name s!"ui: unknown option '{name.getId}' (expected onRoute/start/locals/onPort/queries/dehydrate/ephemeral)"
        | _ => pure ()
      let base ← match routeE? with
        | some route =>
            `(Qed.mkRoutedApp $init $update $tmpl (onRoute := $route)
                (start := $startE) (locals := $localsE) (onPort := $portE))
        | none =>
            `(Qed.mkApp $init $update $tmpl (start := $startE) (locals := $localsE) (onPort := $portE))
      let base ← applyDehydrateOpt init update routeE? base dehydrateRaw?
      -- Unresolved `mkIdent`: `Qed.Resource` sits above `Qed.Runtime.Ui`, and a bare quotation would pre-resolve `Qed.App.` as a struct projection.
      match queriesE? with
      | some qs => `(withLocalRegistry ($(mkIdent `Qed.App.withQueries) $qs $base))
      | none    => `(withLocalRegistry ($base))

end Qed
