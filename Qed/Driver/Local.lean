import Qed.Driver.Vdom
import Qed.Runtime.LocalCore
import Std.Data.HashMap

namespace Qed

structure LocalInstance where
  handlers : Handlers LocalMsg
  treeRef  : IO.Ref (Html LocalMsg)
  host     : Dom.Node
  view     : String → Html LocalMsg
  props    : String
  onOutput : String → IO Unit
structure LocalCtx where
  registry  : Std.HashMap String LocalDef
  store     : IO.Ref (Std.HashMap String String)
  instances : IO.Ref (Std.HashMap String LocalInstance)

def localRerender (inst : LocalInstance) (s' : String) : IO Unit := do
  inst.handlers.click.set #[]; inst.handlers.input.set #[]
  let newTree := inst.view s'
  discard <| ReaderT.run (patchHtmlSubtreeM (m := DomM LocalMsg) inst.host 0 (← Dom.childAt inst.host 0) (← inst.treeRef.get) newTree) inst.handlers
  inst.treeRef.set newTree
def localRun (ctx : LocalCtx) (fk : String) (inst : LocalInstance) (lm : LocalMsg) : IO Unit := do
  let (s', o) := lm.run ((← ctx.store.get).getD fk "")
  ctx.store.modify (·.insert fk s'); localRerender inst s'
  if let some out := o then inst.onOutput out
def localMountRoot {Msg : Type} (ctx : LocalCtx) (dispatchMsg : Msg → IO Unit)
    (key component : String) (init? : Option String) (props : String) (bubble : String → Option Msg) (host : Dom.Node) : IO Unit :=
  go 64 dispatchMsg key component init? props bubble host
where
  go : Nat → ∀ {M : Type}, (M → IO Unit) → String → String → Option String → String → (String → Option M) → Dom.Node → IO Unit
    | 0, _, _, _, _, _, _, _, _ => pure ()
    | fuel + 1, _, parentBubble, key, component, init?, props, bubble, host => do
        let fk := localKey component key
        let some ldef := ctx.registry[component]? | IO.eprintln s!"qed: component '{component}' is not registered"
        let onOut : String → IO Unit := fun out => if let some lm := bubble out then parentBubble lm else pure ()
        match (← ctx.instances.get)[fk]? with
        | some inst =>
            let next := { inst with view := ldef.viewForProps props, props, onOutput := onOut }
            ctx.instances.modify (·.insert fk next)
            if props != inst.props then localRerender next ((← ctx.store.get).getD fk ldef.init)
        | none =>
            let s0 := (← ctx.store.get).getD fk (init?.getD ldef.init); ctx.store.modify (·.insert fk s0)
            let lh ← Handlers.mkNew fun k c i p b hn =>
              go fuel (fun lm => do if let some self := (← ctx.instances.get)[fk]? then localRun ctx fk self lm) k c i p b hn
            let view := ldef.viewForProps props; let tree := view s0
            if (← Dom.childCount host) > 0 then hydrateDom lh tree (← Dom.childAt host 0)
            else Dom.appendChild host (← buildDom lh (← Dom.childNamespace host) tree)
            ctx.instances.modify (·.insert fk { handlers := lh, treeRef := ← IO.mkRef tree, host, view, props, onOutput := onOut })
end Qed
