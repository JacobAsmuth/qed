import Qed.Driver.Vdom
import Qed.Runtime.Local
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

mutual
partial def spawnInstance (ctx : LocalCtx) (fk : String) (ldef : LocalDef) (s0 props : String)
    (onOut : String → IO Unit) (host : Dom.Node) : IO Unit := do
  ctx.store.modify (·.insert fk s0)
  let cRef ← IO.mkRef (#[] : Array LocalMsg)
  let iRef ← IO.mkRef (#[] : Array (String → LocalMsg))
  -- Look up `fk` lazily at event time since `self` is inserted into `ctx.instances` after `lh` is built.
  let lh : Handlers LocalMsg :=
    { click := cRef, input := iRef,
      mountLocal := fun k c i p b hn =>
        localMountInstance ctx (fun lm => do
          match (← ctx.instances.get)[fk]? with
          | some self => localRun ctx fk self lm
          | none      => pure ()) k c i p b hn }
  let view := (ldef.viewProps.map (fun f => f props)).getD ldef.view
  let tree := view s0
  if (← Dom.childCount host) > 0 then
    hydrateDom lh tree (← Dom.childAt host 0)
  else
    Dom.appendChild host (← buildDom lh (← Dom.childNamespace host) tree)
  let tRef ← IO.mkRef tree
  ctx.instances.modify (·.insert fk
    { handlers := lh, treeRef := tRef, host := host, view, props, onOutput := onOut })

partial def localRerender (inst : LocalInstance) (s' : String) : IO Unit := do
  inst.handlers.click.set #[]; inst.handlers.input.set #[]
  let newTree := inst.view s'
  match diff (← inst.treeRef.get) newTree with
  | .replace newH => Dom.replaceChild inst.host 0 (← buildDom inst.handlers (← Dom.childNamespace inst.host) newH)
  | patch         => applyToDom inst.handlers inst.host 0 (← Dom.childAt inst.host 0) patch
  inst.treeRef.set newTree

partial def localRun (ctx : LocalCtx) (fk : String) (inst : LocalInstance) (lm : LocalMsg) : IO Unit := do
  let (s', o) := lm.run ((← ctx.store.get).getD fk "")
  ctx.store.modify (·.insert fk s')
  localRerender inst s'
  match o with | some out => inst.onOutput out | none => pure ()

partial def localMountInstance {Msg : Type} (ctx : LocalCtx) (parentBubble : Msg → IO Unit)
    (key component : String) (init? : Option String) (props : String) (bubble : String → Option Msg)
    (host : Dom.Node) : IO Unit := do
  let fk := localKey component key
  match ctx.registry[component]? with
  | none      => IO.eprintln s!"qed: component '{component}' is not registered"
  | some ldef =>
      let onOut : String → IO Unit := fun out => match bubble out with
        | some lm => parentBubble lm
        | none    => pure ()
      match (← ctx.instances.get)[fk]? with
      | some inst =>
          let next := { inst with
            view := (ldef.viewProps.map (fun f => f props)).getD ldef.view,
            props, onOutput := onOut }
          ctx.instances.modify (·.insert fk next)
          if props != inst.props then
            localRerender next ((← ctx.store.get).getD fk ldef.init)
      | none =>
          spawnInstance ctx fk ldef ((← ctx.store.get).getD fk (init?.getD ldef.init)) props onOut host
end

partial def localMountRoot {Msg : Type} (ctx : LocalCtx) (dispatchMsg : Msg → IO Unit)
    (key component : String) (init? : Option String) (props : String) (bubble : String → Option Msg)
    (host : Dom.Node) : IO Unit := do
  localMountInstance ctx dispatchMsg key component init? props bubble host

end Qed
