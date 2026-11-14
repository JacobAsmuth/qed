import Qed.Render
import Qed.Diff
import Qed.Dom
import Qed.View.Core

namespace Qed

structure Handlers (msg : Type) where
  click      : IO.Ref (Array msg)
  input      : IO.Ref (Array (String → msg))
  mountLocal : String → String → Option String → String → (String → Option msg) → Dom.Node → IO Unit

def registerHandler {α : Type} (tbl : IO.Ref (Array α)) (node : Dom.Node)
    (key : String) (v : α) : IO Unit := do
  let ts ← tbl.get
  -- Capture `ts.size` before `push`: the JS runtime mutates pushed arrays in place.
  let next := toString ts.size
  match (← Dom.getAttribute node key).toNat? with
  | some i => if i < ts.size then tbl.set (ts.set! i v)
              else do tbl.set (ts.push v); Dom.setAttribute node key next
  | none   => do tbl.set (ts.push v); Dom.setAttribute node key next

def applyAttr (h : Handlers msg) (node : Dom.Node) : Attr msg → IO Unit
  | .cls c                  => Dom.setAttribute node "class" c
  | .attr "value" v         => Dom.setValue node v
  | .attr k v               => Dom.setAttribute node k v
  | .flag "checked" present => Dom.setChecked node present
  | .flag k present         => if present then Dom.setAttribute node k k else Dom.removeAttribute node k
  | .key _                  => pure ()
  | .on event m             => do
      Dom.effect "event.listen" event "" ""
      registerHandler h.click node s!"data-qed-on-{event}" m
  | .onValue event f        => do
      Dom.effect "event.listen" event "" ""
      registerHandler h.input node s!"data-qed-onv-{event}" f
  | .localCell key comp init props bubble => do
      Dom.setAttribute node "data-qed-local" (localKey comp key)
      h.mountLocal key comp init props bubble node
  | .signalBind name        => Dom.bindSignal node name
  | .signalAttr name attr _ => Dom.bindSignalAttr node name attr
  | .rawHtml markup         => Dom.setInnerHtml node markup

def applyAttrs (h : Handlers msg) (node : Dom.Node) (attrs : List (Attr msg)) : IO Unit := do
  let attrs := normalizeAttrs attrs
  let names := attrs.filterMap fun
    | .cls _ => some "class"
    | .attr k _ | .flag k _ => some k
    | .on e _ => some s!"data-qed-on-{e}"
    | .onValue e _ => some s!"data-qed-onv-{e}"
    | .localCell .. => some "data-qed-local"
    | .signalAttr _ a _ => some a
    | .signalBind _ => some "data-qed-signal"
    | _ => none
  Dom.retainAttributes node names
  for a in attrs do applyAttr h node a

def applyDynAttrs (h : Handlers msg) (node : Dom.Node) (attrs : List (VAttr σ msg)) (s : σ) : IO Unit := do
  if attrs.any (fun | .bind _ => true | _ => false) then
    applyAttrs h node (attrs.map (VAttr.eval s))
    return
  for va in attrs do
    match va with
    | .bind f          => applyAttr h node (f s)
    | .dynVal attr get => applyAttr h node (.attr attr (get s))
    | .stat _          => pure ()

def clearHandlerIds (node : Dom.Node) : IO Unit := Dom.clearHandlers node

def ownsChildren (attrs : List (Attr msg)) : Bool :=
  attrs.any (fun | .localCell .. => true | .signalBind .. => true | .rawHtml .. => true | _ => false)

def allCreates : List (KeyedStep msg) → Bool
  | []                => true
  | .create _ :: rest => allCreates rest
  | .reuse _ _ :: _   => false

def positional : Nat → List (KeyedStep msg) → Bool
  | _, []                        => true
  | i, .reuse oldIndex _ :: rest => oldIndex == i && positional (i + 1) rest
  | _, .create _ :: rest         => allCreates rest

partial def buildDom (h : Handlers msg) (ns : String) : Html msg → IO Dom.Node
  | .text s     => Dom.createText s
  | .lazy _ sub => buildDom h ns sub
  | .element tag attrs children => do
      let node ← Dom.createElement ns tag
      applyAttrs h node attrs
      unless ownsChildren attrs do
        let childNs := Dom.childNsOf ns tag
        for c in children do
          Dom.appendChild node (← buildDom h childNs c)
      return node

def hydrateTextSlot (parent : Dom.Node) (index : UInt32) (inTextRun : Bool)
    (s : String) (moreInRun : Unit → Bool) : IO (Dom.Node × Bool) := do
  if s == "" then
    let ph ← Dom.createText ""
    Dom.insertBefore parent index ph
    return (ph, inTextRun)
  else if inTextRun then
    let tn ← Dom.createText s
    Dom.insertBefore parent index tn
    return (tn, true)
  else
    let tn ← Dom.childAt parent index
    if moreInRun () then Dom.setText tn s
    return (tn, true)

mutual
partial def hydrateDom (h : Handlers msg) : Html msg → Dom.Node → IO Unit
  | .text _,     _    => pure ()
  | .lazy _ sub, node => hydrateDom h sub node
  | .element _ attrs children, node => do
      clearHandlerIds node
      applyAttrs h node attrs
      unless ownsChildren attrs do
        hydrateDomKids h node 0 false children

partial def hydrateDomKids (h : Handlers msg) (node : Dom.Node) (i : UInt32) (inTextRun : Bool) :
    List (Html msg) → IO Unit
  | [] => pure ()
  | c :: rest => do
      match c.textOf? with
      | some s =>
          let (_, nextRun) ← hydrateTextSlot node i inTextRun s (fun () => hasMoreText rest)
          hydrateDomKids h node (i + 1) nextRun rest
      | none =>
          hydrateDom h c (← Dom.childAt node i)
          hydrateDomKids h node (i + 1) false rest
end

mutual
partial def applyToDom (h : Handlers msg)
    (parent : Dom.Node) (index : UInt32) (node : Dom.Node) : Patch msg → IO Unit
  | .replace new => do
      Dom.replaceChild parent index (← buildDom h (← Dom.childNamespace parent) new)
  | .setText s => Dom.setText node s
  | .lazyReuse _ _ =>
      -- Trusts `equal key ⇒ equal subtree` rather than rebuilding `sub` like pure `applyPatch`.
      pure ()
  | .lazyPatch _ p =>
      applyToDom h parent index node p
  | .patchElement attrs steps => do
      applyAttrs h node attrs
      if ownsChildren attrs then return
      let oldCount ← Dom.childCount node
      if positional 0 steps then
        let mut j : UInt32 := 0
        for step in steps do
          match step with
          | .reuse _ (.lazyReuse _ _) => pure ()
          | .reuse _ p                => applyToDom h node j (← Dom.childAt node j) p
          | .create newH              => Dom.insertBefore node j (← buildDom h (← Dom.childNamespace node) newH)
          j := j + 1
        let count ← Dom.childCount node
        for _ in [steps.length:count.toNat] do Dom.removeChild node (UInt32.ofNat steps.length)
        return
      let mut live : Array Dom.Node := #[]
      for i in [0:oldCount.toNat] do
        live := live.push (← Dom.childAt node (UInt32.ofNat i))
      let mut j : UInt32 := 0
      for step in steps do
        match step with
        | .reuse oldIndex p => do
            let child := live.getD oldIndex 0
            Dom.insertBefore node j child
            applyToDom h node j child p
        | .create newH => do
            Dom.insertBefore node j (← buildDom h (← Dom.childNamespace node) newH)
        j := j + 1
      let count ← Dom.childCount node
      for _ in [j.toNat:count.toNat] do Dom.removeChild node j
end

end Qed
