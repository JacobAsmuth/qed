import Qed.Runtime.App
import Qed.View.Lift
import Lean

namespace Qed

syntax portChan := ident " : " term (" => " term)?
syntax (name := portsCmd) "ports " "where " sepBy1IndentSemicolon(portChan) : command

open Lean in
macro_rules
  | `(ports where $[$chans:portChan]*) => do
      let mut outDefs  : Array (TSyntax `command) := #[]
      let mut inTuples : Array (TSyntax `term) := #[]
      for ch in chans do
        -- `__`-prefixed channel names are reserved for framework channels like `__ws`.
        if let some nm := (ch.raw.find? (·.isIdent)).map (·.getId.toString) then
          if nm.startsWith "__" then
            Macro.throwErrorAt ch s!"ports: channel name '{nm}' is reserved (names starting with `__`)"
        match ch with
        | `(portChan| $name:ident : $ty:term => $rhs:term) =>
            inTuples := inTuples.push (← `(($(quote name.getId.toString),
              fun p => (((Json.parse p).bind FromJson.fromJson : Except String $ty).toOption).map $rhs)))
        | `(portChan| $name:ident : $ty:term) =>
            outDefs := outDefs.push (←
              `(def $name {m : Type} (x : $ty) : Cmd m :=
                  Cmd.port $(quote name.getId.toString) (Json.render (ToJson.toJson x))))
        | _ => Macro.throwErrorAt ch "ports: expected `name : Type` (outbound) or `name : Type => ctor` (inbound)"
      let onPortDef ← `(def $(mkIdent `onPort) : String → String → Option $(mkIdent `Msg) :=
        dispatchPorts #[$inTuples,*])
      return mkNullNode ((outDefs.push onPortDef).map (·.raw))

syntax uiOpt := "(" ident " := " term ")"
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
        | .str _ s => s == "mount" || s == "mountWith"
        | _ => false
      if isMount && env.contains reg then
        regs := regs.push (Lean.mkConst reg)
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
macro_rules
  | `(ui $init $update $[$opts:uiOpt]* fun $m => $body) => do
      let tmpl ← `(view% fun $m => $body)
      let mut routeE?     : Option (TSyntax `term) := none
      let mut queriesE?   : Option (TSyntax `term) := none
      let mut dehydrateE? : Option (TSyntax `term) := none
      let mut startE  : TSyntax `term ← `(Qed.Cmd.none)
      let mut localsE : TSyntax `term ← `(([] : List Qed.LocalDef))
      let mut portE   : TSyntax `term ← `(none)
      for opt in opts do
        match opt with
        | `(uiOpt| ($name:ident := $e)) =>
            match name.getId with
            | `onRoute   => routeE?     := some e
            | `queries   => queriesE?   := some e
            | `dehydrate => dehydrateE? := some e
            | `start     => startE  := e
            | `locals    => localsE := e
            | `onPort    => portE   := e
            | _ => Macro.throwErrorAt name s!"ui: unknown option '{name.getId}' (expected onRoute/start/locals/onPort/queries/dehydrate)"
        | _ => pure ()
      let base ← match routeE? with
        | some route =>
            `(Qed.mkRoutedApp $init $update $tmpl (onRoute := $route)
                (start := $startE) (locals := $localsE) (onPort := $portE))
        | none =>
            `(Qed.mkApp $init $update $tmpl (start := $startE) (locals := $localsE) (onPort := $portE))
      let base ← match dehydrateE? with
        | some d => `(Qed.App.withDehydrate $d $base)
        | none   => pure base
      -- Unresolved `mkIdent`: `Qed.Resource` sits above `Qed.Runtime.Ui`, and a bare quotation would pre-resolve `Qed.App.` as a struct projection.
      match queriesE? with
      | some qs => `(withLocalRegistry ($(mkIdent `Qed.App.withQueries) $qs $base))
      | none    => `(withLocalRegistry ($base))

end Qed
