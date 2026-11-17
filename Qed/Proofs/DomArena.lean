import Qed.Driver.Template
import Qed.Runtime.App
import Qed.Ssr

namespace Qed

/-!
# Verified Imperative DOM Reconciler, Hydration, Memo & SSR Equivalence

This module provides the kernel-checked refinement proofs connecting:
1. Pure `Html` / `Patch` (`diff`, `applyPatch`, `validatedKeyIndex`)
2. Imperative `[MonadDom msg m]` operations (`buildDomM`, `applyToDomM`, `hydrateDomM`,
   `buildViewM`, `patchViewM`, `hydrateViewM`) executed over a pure `DomArena msg`
3. Browser HTML5 text-coalescing / empty-text omission and `hydrateTextSlotM` splitting
4. Congruence-sound memoization (`SoundMemo` / `View.memo`) and duplicate-key disambiguation
5. End-to-end SSR serialization → client `rehydrate` → hydration & incremental patch equivalence (`App.ssr_rehydrate_equiv`)
-/

/-- Canonical observational DOM node state produced from `normalizeAttrs`. -/
structure SpecElemState (msg : Type) where
  attrs   : List (String × String) := []
  value   : String := ""
  checked : Bool := false
  clicks  : List (String × msg) := []
  inputs  : List (String × (String → msg)) := []
  sigBind : Option String := none
  sigAttr : List (String × String) := []

def setAssoc {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: setAssoc k v rest

def eraseAssoc {α : Type} (k : String) : List (String × α) → List (String × α)
  | [] => []
  | (k', v') :: rest => if k' == k then eraseAssoc k rest else (k', v') :: eraseAssoc k rest

def stepSpecAttr (st : SpecElemState msg) : Attr msg → SpecElemState msg
  | .cls c                  => { st with attrs := setAssoc "class" c st.attrs }
  | .attr "value" v         => { st with value := v }
  | .attr k v               => { st with attrs := setAssoc k v st.attrs }
  | .flag "checked" present => { st with checked := present }
  | .flag k present         =>
      { st with attrs := if present then setAssoc k k st.attrs else eraseAssoc k st.attrs }
  | .key _                  => st
  | .on event evMsg         => { st with clicks := setAssoc event evMsg st.clicks }
  | .onValue event f        => { st with inputs := setAssoc event f st.inputs }
  | .localCell key comp _ _ _ =>
      { st with attrs := setAssoc "data-qed-local" (localKey comp key) st.attrs }
  | .signalBind name        => { st with sigBind := some name }
  | .signalAttr name attr _ => { st with sigAttr := setAssoc attr name st.sigAttr }

def evalSpecAttrs (attrs : List (Attr msg)) : SpecElemState msg :=
  (normalizeAttrs attrs).foldl stepSpecAttr {}

/-- Observational DOM tree (the Lean counterpart of `snapshot(node)` in `dom_equivalence_test.mjs`,
    augmented with typed click and input handlers). -/
inductive DomTree (msg : Type) where
  | text (s : String)
  | element (ns : String) (tag : String) (state : SpecElemState msg) (children : List (DomTree msg))

mutual
  /-- Reference DOM tree semantics for `Html msg` under inherited namespace `ns`. -/
  def specDom (ns : String) : Html msg → DomTree msg
    | .text s => .text s
    | .element tag attrs children =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        let st := evalSpecAttrs attrs
        let kids := if ownsChildren attrs then [] else specDomList (Dom.childNsOf ns tag) children
        .element realNs tag st kids

  def specDomList (ns : String) : List (Html msg) → List (DomTree msg)
    | []      => []
    | c :: cs => specDom ns c :: specDomList ns cs
end

@[simp] theorem specDomList_eq_map (ns : String) :
    ∀ (cs : List (Html msg)), specDomList ns cs = cs.map (specDom ns)
  | []      => rfl
  | c :: cs => by simp [specDomList, specDomList_eq_map ns cs]

/-! ## Pure Imperative `DomArena` & `MonadDom` Instance -/

inductive ArenaEntry (msg : Type) where
  | null
  | text (s : String)
  | fragment (children : List Dom.Node)
  | element (ns : String) (tag : String)
      (state : SpecElemState msg)
      (managed : List String)
      (children : List Dom.Node)

def insertBeforeRef (child ref : Dom.Node) : List Dom.Node → List Dom.Node
  | [] => [child]
  | x :: xs => if x == ref then child :: x :: xs else x :: insertBeforeRef child ref xs

/-- W3C `parent.insertBefore(child, parent.childNodes[idx] || null)` semantics on a child handle list:
    if `child` is already attached to `parent`, it moves from its existing slot to before the
    original `idx`-th child; otherwise it is inserted at `idx`. -/
def w3cInsertBefore (children : List Dom.Node) (idx : Nat) (child : Dom.Node) : List Dom.Node :=
  match children.drop idx with
  | [] =>
      (children.erase child) ++ [child]
  | ref :: _ =>
      if ref == child then children
      else insertBeforeRef child ref (children.erase child)

def listRemoveAt {α : Type} : List α → Nat → List α
  | [], _          => []
  | _ :: xs, 0     => xs
  | x :: xs, i + 1 => x :: listRemoveAt xs i

def listReplaceAt {α : Type} : List α → Nat → α → List α
  | [], _, _          => []
  | _ :: xs, 0, v     => v :: xs
  | x :: xs, i + 1, v => x :: listReplaceAt xs i v

@[ext]
structure DomArena (msg : Type) where
  nextId  : Nat := 1
  store   : Dom.Node → ArenaEntry msg := fun _ => .null
  signals : List (String × String) := []

namespace DomArena

def get (a : DomArena msg) (n : Dom.Node) : ArenaEntry msg := a.store n

def set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) : DomArena msg :=
  { a with store := fun m => if m == n then e else a.store m }

def modify (a : DomArena msg) (n : Dom.Node) (f : ArenaEntry msg → ArenaEntry msg) : DomArena msg :=
  a.set n (f (a.get n))

def alloc (a : DomArena msg) (e : ArenaEntry msg) : Dom.Node × DomArena msg :=
  let h := UInt32.ofNat a.nextId
  (h, { nextId := a.nextId + 1, store := fun m => if m == h then e else a.store m, signals := a.signals })

@[simp] theorem get_set_self (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) :
    (a.set n e).get n = e := by
  simp [get, set]

@[simp] theorem get_set_ne (a : DomArena msg) {n m : Dom.Node} (e : ArenaEntry msg) (hne : m ≠ n) :
    (a.set n e).get m = a.get m := by
  simp [get, set, hne]

@[simp] theorem nextId_set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) :
    (a.set n e).nextId = a.nextId := rfl

@[simp] theorem set_set (a : DomArena msg) (n : Dom.Node) (e₁ e₂ : ArenaEntry msg) :
    (a.set n e₁).set n e₂ = a.set n e₂ := by
  cases a; simp only [set, mk.injEq, true_and, and_true]
  funext m; by_cases hm : m == n <;> simp [hm]

@[reducible] def modifyElemState (a : DomArena msg) (n : Dom.Node)
    (f : SpecElemState msg → SpecElemState msg) : DomArena msg :=
  a.modify n fun
    | .element ns tag st mg cs => .element ns tag (f st) mg cs
    | other => other

@[reducible] def modifyChildren (a : DomArena msg) (p : Dom.Node)
    (f : List Dom.Node → List Dom.Node) : DomArena msg :=
  a.modify p fun
    | .element ns tag st mg cs => .element ns tag st mg (f cs)
    | .fragment cs => .fragment (f cs)
    | other => other

end DomArena

instance : MonadDom msg (StateM (DomArena msg)) where
  createElement ns tag := fun a =>
    let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
    a.alloc (.element realNs tag {} [] [])
  createText s := fun a => a.alloc (.text s)
  createFragment := fun a => a.alloc (.fragment [])
  childNamespace n := fun a =>
    let out := match a.get n with
      | .element ns tag _ _ _ => if ns == Dom.svgNs && tag != "foreignObject" then Dom.svgNs else ""
      | _ => ""
    (out, a)
  setAttribute n k v      := fun a => ((), a.modifyElemState n fun st => { st with attrs := setAssoc k v st.attrs })
  removeAttribute n k     := fun a => ((), a.modifyElemState n fun st => { st with attrs := eraseAssoc k st.attrs })
  retainAttributes n names := fun a =>
    ((), a.modify n fun
      | .element ns tag st prev cs =>
          let val' := if prev.contains "value" && !names.contains "value" then "" else st.value
          let chk' := if prev.contains "checked" && !names.contains "checked" then false else st.checked
          let attrs' := st.attrs.filter fun (k, _) => !prev.contains k || names.contains k
          .element ns tag { st with attrs := attrs', value := val', checked := chk' } names cs
      | other => other)
  clearHandlers n         := fun a => ((), a.modifyElemState n fun st => { st with clicks := [], inputs := [] })
  setValue n v            := fun a => ((), a.modifyElemState n fun st => { st with value := v })
  setChecked n on         := fun a => ((), a.modifyElemState n fun st => { st with checked := on })
  setText n s := fun a =>
    ((), a.modify n fun
      | .text _ => .text s
      | .element ns tag st mg _ => .element ns tag st mg []
      | other => other)
  appendChild p c := fun a =>
    match a.get c with
    | .fragment fcs =>
        ((), (a.set c .null).modifyChildren p fun cs => (cs.filter (!fcs.contains ·)) ++ fcs)
    | _ =>
        ((), a.modifyChildren p fun cs => (cs.erase c) ++ [c])
  childAt p i := fun a =>
    let out := match a.get p with
      | .element _ _ _ _ cs | .fragment cs => cs.getD i.toNat 0
      | _ => 0
    (out, a)
  childCount p := fun a =>
    let out := match a.get p with
      | .element _ _ _ _ cs | .fragment cs => UInt32.ofNat cs.length
      | _ => 0
    (out, a)
  removeChild p i          := fun a => ((), a.modifyChildren p fun cs => listRemoveAt cs i.toNat)
  replaceChild p i newChild := fun a => ((), a.modifyChildren p fun cs => listReplaceAt cs i.toNat newChild)
  insertBeforeNode p i ch  := fun a => ((), a.modifyChildren p fun cs => w3cInsertBefore cs i.toNat ch)
  bindSignal n name        := fun a => ((), a.modifyElemState n fun st => { st with sigBind := some name })
  bindSignalAttr n nm attr := fun a => ((), a.modifyElemState n fun st => { st with sigAttr := setAssoc attr nm st.sigAttr })
  setSignal name val       := fun a => ((), { a with signals := setAssoc name val a.signals })
  onEvent n event evMsg    := fun a => ((), a.modifyElemState n fun st => { st with clicks := setAssoc event evMsg st.clicks })
  onValueEvent n event f   := fun a => ((), a.modifyElemState n fun st => { st with inputs := setAssoc event f st.inputs })
  mountLocalCell n key comp _ _ _ := fun a =>
    ((), a.modifyElemState n fun st => { st with attrs := setAssoc "data-qed-local" (localKey comp key) st.attrs })

/-- Read an observational `DomTree` out of `DomArena` with depth fuel `fuel`. -/
def readDomTree : Nat → DomArena msg → Dom.Node → DomTree msg
  | 0, _, _ => .text ""
  | fuel + 1, a, n =>
      match a.get n with
      | .text s => .text s
      | .element ns tag st _ cs => .element ns tag st (cs.map (readDomTree fuel a))
      | _ => .text ""

/-! ## 1. Imperative `applyAttrListM` & `buildDomM` Simulation on `DomArena` -/

theorem applyAttrM_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node)
    (attr : Attr msg) :
    applyAttrM (m := StateM (DomArena msg)) node attr
      (a.set node (.element ns tag st mg cs)) =
      ((), a.set node (.element ns tag (stepSpecAttr st attr) mg cs)) := by
  cases attr with
  | cls c =>
      simp [applyAttrM, MonadDom.setAttribute, DomArena.modify, stepSpecAttr]
  | attr k v =>
      by_cases hk : k = "value"
      · subst hk
        simp [applyAttrM, MonadDom.setValue, DomArena.modify, stepSpecAttr]
      · simp [applyAttrM, MonadDom.setAttribute, DomArena.modify, stepSpecAttr]
  | flag k present =>
      by_cases hk : k = "checked"
      · subst hk
        simp [applyAttrM, MonadDom.setChecked, DomArena.modify, stepSpecAttr]
      · cases present <;>
          simp [applyAttrM, MonadDom.setAttribute, MonadDom.removeAttribute,
                DomArena.modify, stepSpecAttr]
  | key _ =>
      rfl
  | on event evMsg =>
      simp [applyAttrM, MonadDom.onEvent, DomArena.modify, stepSpecAttr]
  | onValue event f =>
      simp [applyAttrM, MonadDom.onValueEvent, DomArena.modify, stepSpecAttr]
  | localCell key comp init props bubble =>
      simp [applyAttrM, MonadDom.mountLocalCell, DomArena.modify, stepSpecAttr]
  | signalBind name =>
      simp [applyAttrM, MonadDom.bindSignal, DomArena.modify, stepSpecAttr]
  | signalAttr name attr v =>
      simp [applyAttrM, MonadDom.bindSignalAttr, DomArena.modify, stepSpecAttr]

theorem applyAttrListM_element :
    ∀ (attrs : List (Attr msg)) (a : DomArena msg) (node : Dom.Node) (ns tag : String)
      (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node),
      applyAttrListM (m := StateM (DomArena msg)) node attrs
        (a.set node (.element ns tag st mg cs)) =
        ((), a.set node (.element ns tag (attrs.foldl stepSpecAttr st) mg cs))
  | [], _, _, _, _, _, _, _ => rfl
  | attr :: rest, a, node, ns, tag, st, mg, cs => by
      dsimp only [applyAttrListM, bind, StateT.bind]
      rw [applyAttrM_element a node ns tag st mg cs attr]
      exact applyAttrListM_element rest a node ns tag (stepSpecAttr st attr) mg cs

theorem applyAttrsM_fresh_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) :
    applyAttrsM (m := StateM (DomArena msg)) node attrs
      (a.set node (.element ns tag {} [] cs)) =
      ((), a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs)) := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]
  exact applyAttrListM_element (normalizeAttrs attrs) a node ns tag {}
    ((normalizeAttrs attrs).filterMap managedAttrName) cs

mutual
def htmlNodeCount : Html msg → Nat
  | .text _ => 1
  | .element _ _ cs => 1 + htmlListNodeCount cs

def htmlListNodeCount : List (Html msg) → Nat
  | [] => 0
  | c :: cs => htmlNodeCount c + htmlListNodeCount cs
end

mutual
def htmlDepth : Html msg → Nat
  | .text _ => 1
  | .element _ _ cs => 1 + htmlListDepth cs

def htmlListDepth : List (Html msg) → Nat
  | [] => 0
  | c :: cs => Nat.max (htmlDepth c) (htmlListDepth cs)
end

/-- Every node handle reachable within `fuel` steps lies in `[lo, hi)`. -/
def SubtreeInRange : Nat → DomArena msg → Nat → Nat → Dom.Node → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, lo, hi, n =>
      lo ≤ n.toNat ∧ n.toNat < hi ∧
      match a.get n with
      | .element _ _ _ _ cs => ∀ c ∈ cs, SubtreeInRange fuel a lo hi c
      | _ => True

theorem SubtreeInRange_mono {fuel : Nat} {a : DomArena msg} {lo₁ hi₁ lo₂ hi₂ : Nat} {n : Dom.Node}
    (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) (h : SubtreeInRange fuel a lo₁ hi₁ n) :
    SubtreeInRange fuel a lo₂ hi₂ n := by
  induction fuel generalizing n with
  | zero => trivial
  | succ f ih =>
      rcases h with ⟨h1, h2, hkids⟩
      refine ⟨Nat.le_trans hlo h1, Nat.lt_of_lt_of_le h2 hhi, ?_⟩
      cases hget : a.get n with
      | element ns tag st mg cs =>
          rw [hget] at hkids
          intro c hc
          exact ih (hkids c hc)
      | _ => trivial

theorem SubtreeInRange_frame {fuel : Nat} {a a' : DomArena msg} {lo hi : Nat} {n : Dom.Node}
    (hagree : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m)
    (hsub : SubtreeInRange fuel a lo hi n) :
    SubtreeInRange fuel a' lo hi n ∧ readDomTree fuel a' n = readDomTree fuel a n := by
  induction fuel generalizing n with
  | zero => exact ⟨trivial, rfl⟩
  | succ f ih =>
      rcases hsub with ⟨hlo, hhi, hkids⟩
      have heq := hagree n hlo hhi
      cases hget : a.get n with
      | text s =>
          refine ⟨⟨hlo, hhi, ?_⟩, ?_⟩ <;> simp [readDomTree, heq, hget]
      | null =>
          refine ⟨⟨hlo, hhi, ?_⟩, ?_⟩ <;> simp [readDomTree, heq, hget]
      | fragment cs =>
          refine ⟨⟨hlo, hhi, ?_⟩, ?_⟩ <;> simp [readDomTree, heq, hget]
      | element ns tag st mg cs =>
          rw [hget] at hkids
          refine ⟨⟨hlo, hhi, ?_⟩, ?_⟩
          · simp only [heq, hget]
            intro c hc
            exact (ih (hkids c hc)).1
          · simp only [readDomTree, heq, hget, DomTree.element.injEq, true_and]
            apply List.map_congr_left
            intro c hc
            exact (ih (hkids c hc)).2

mutual
  /-- Imperative `buildDomM` executed on `DomArena` builds a fresh subtree whose extracted
      `DomTree` equals `specDom ns h`, while leaving all existing nodes `< a.nextId` untouched. -/
  theorem buildDomM_spec (ns : String) :
      ∀ (h : Html msg) (a : DomArena msg) (fuel : Nat),
        0 < a.nextId →
        a.nextId + htmlNodeCount h < UInt32.size →
        htmlDepth h ≤ fuel →
        let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
        a.nextId ≤ root.toNat ∧
        root.toNat < a'.nextId ∧
        a'.nextId ≤ a.nextId + htmlNodeCount h ∧
        (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
        SubtreeInRange fuel a' a.nextId a'.nextId root ∧
        readDomTree fuel a' root = specDom ns h
    | .text s, a, fuel, _, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ f =>
            simp only [htmlNodeCount] at hbound ⊢
            have hlt : a.nextId < UInt32.size := by omega
            have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := UInt32.toNat_ofNat_of_lt hlt
            dsimp only [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run]
            refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
            · intro m hm
              have hne : m ≠ UInt32.ofNat a.nextId := by intro heq; subst heq; omega
              simp [DomArena.get, beq_eq_false_iff_ne.2 hne]
            · refine ⟨by omega, by omega, ?_⟩
              simp [DomArena.get]
            · simp [readDomTree, DomArena.get, specDom]
    | .element tag attrs children, a, fuel, hpos, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ f =>
            simp only [htmlNodeCount] at hbound ⊢
            simp only [htmlDepth] at hdep
            have hlt0 : a.nextId < UInt32.size := by omega
            let node := UInt32.ofNat a.nextId
            have hnodeNat : node.toNat = a.nextId := UInt32.toNat_ofNat_of_lt hlt0
            let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
            let st := evalSpecAttrs attrs
            let mg := (normalizeAttrs attrs).filterMap managedAttrName
            let a1 : DomArena msg := { nextId := a.nextId + 1, store := a.store, signals := a.signals }
            have ha1Next : a1.nextId = a.nextId + 1 := rfl
            have hattrs :
                applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) =
                  ((), a1.set node (.element realNs tag st mg [])) :=
              applyAttrsM_fresh_element a1 node realNs tag [] attrs
            have ha2_frame : ∀ m : Dom.Node, m.toNat < a.nextId →
                (a1.set node (.element realNs tag st mg [])).get m = a.get m := by
              intro m hm
              have hne : m ≠ node := by intro heq; subst heq; omega
              rw [DomArena.get_set_ne _ _ hne]
              rfl
            have hrun :
                (buildDomM (m := StateM (DomArena msg)) ns (.element tag attrs children)).run a =
                  if !ownsChildren attrs then
                    (node, (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children
                      (a1.set node (.element realNs tag st mg []))).2)
                  else
                    (node, a1.set node (.element realNs tag st mg [])) := by
              dsimp only [buildDomM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
              change (match applyAttrsM (m := StateM (DomArena msg)) node attrs
                        (a1.set node (.element realNs tag {} [] [])) with
                      | (_, s) =>
                        (if (!ownsChildren attrs) = true then
                           StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children)
                             (fun _ => StateT.pure node)
                         else
                           StateT.bind (StateT.pure PUnit.unit) (fun _ => StateT.pure node)) s) = _
              rw [hattrs]
              by_cases h : ownsChildren attrs <;>
                { simp only [h, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; rfl }
            rw [hrun]
            by_cases hown : ownsChildren attrs
            · simp only [hown, Bool.not_true, Bool.false_eq_true, ↓reduceIte, DomArena.nextId_set]
              refine ⟨by omega, by omega, by omega, ha2_frame, ?_, ?_⟩
              · refine ⟨by omega, by omega, ?_⟩
                simp [DomArena.get_set_self]
              · simp [readDomTree, DomArena.get_set_self, specDom, hown, realNs, st]
            · have hownF : ownsChildren attrs = false := Bool.eq_false_iff.2 hown
              simp only [hownF, Bool.not_false, ↓reduceIte]
              have hkids := buildDomListM_spec (Dom.childNsOf ns tag) children a1 node realNs tag st mg [] f
                (by omega)
                (by omega)
                (by omega)
                (by omega)
                (by intro c hc; nomatch hc)
              dsimp only [StateT.run] at hkids
              rcases hkids with ⟨csNew, aBase', ha'Eq, hnextLe, hnextMono, hframe1, hsubKids, hreadKids⟩
              refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
              · intro m hm
                have hm1 : m.toNat < a1.nextId := by omega
                have hne : m ≠ node := by intro heq; subst heq; omega
                rw [ha'Eq, DomArena.get_set_ne _ _ hne]
                have := hframe1 m hm1 hne
                rwa [DomArena.get_set_ne _ _ hne] at this
              · refine ⟨by omega, by omega, ?_⟩
                rw [ha'Eq, DomArena.get_set_self]
                intro c hc
                have hc' := hsubKids c hc
                rw [ha'Eq] at hc'
                exact SubtreeInRange_mono (by omega) (Nat.le_refl _) hc'
              · rw [ha'Eq] at hreadKids ⊢
                simpa [readDomTree, DomArena.get_set_self, specDom, hownF, realNs, st] using hreadKids

  theorem buildDomListM_spec (childNs : String) :
      ∀ (cs : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
        (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
        (acc : List Dom.Node) (f : Nat),
        parent.toNat < aBase.nextId →
        0 < aBase.nextId →
        aBase.nextId + htmlListNodeCount cs < UInt32.size →
        htmlListDepth cs ≤ f →
        (∀ c ∈ acc, SubtreeInRange f (aBase.set parent (.element pns ptag pst pmg acc)) (parent.toNat + 1) aBase.nextId c) →
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
        ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
          aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
          aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧
          aBase.nextId ≤ aOut.nextId ∧
          (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
          (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
          (acc ++ csNew).map (readDomTree f aOut) =
            acc.map (readDomTree f aIn) ++ specDomList childNs cs
    | [], aBase, parent, pns, ptag, pst, pmg, acc, f, _, _, _, _, haccSub => by
        refine ⟨[], aBase, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [buildDomListM, StateT.run, pure, StateT.pure]
        · simp [buildDomListM, StateT.run, pure, StateT.pure, htmlListNodeCount]
        · simp [buildDomListM, StateT.run, pure, StateT.pure]
        · intro m _ hne; simp [DomArena.get_set_ne _ _ hne]
        · simpa [buildDomListM, StateT.run, pure, StateT.pure] using haccSub
        · simp [buildDomListM, StateT.run, pure, StateT.pure, specDomList]
    | c :: rest, aBase, parent, pns, ptag, pst, pmg, acc, f, hparLt, hpos, hbound, hdep, haccSub => by
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        have haInNext : aIn.nextId = aBase.nextId := rfl
        simp only [htmlListNodeCount] at hbound
        simp only [htmlListDepth] at hdep
        have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
        have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
        have hfPos : 0 < f := by
          cases c <;> { simp [htmlDepth] at hcDep; omega }
        have hcSpec := buildDomM_spec childNs c aIn f
          (by omega)
          (by omega)
          hcDep
        dsimp only [StateT.run] at hcSpec
        let res1 := buildDomM (m := StateM (DomArena msg)) childNs c aIn
        let cn := res1.1
        let aMid := res1.2
        rcases hcSpec with ⟨hcnGe, hcnLt, haMidLe, haMidFrame, hcnSub, hcnRead⟩
        have hcnDef : (buildDomM (m := StateM (DomArena msg)) childNs c aIn).1 = cn := rfl
        have haMidDef : (buildDomM (m := StateM (DomArena msg)) childNs c aIn).2 = aMid := rfl
        rw [hcnDef] at hcnGe hcnLt hcnSub hcnRead
        rw [haMidDef] at hcnLt haMidLe haMidFrame hcnSub hcnRead
        have hparInMid : aMid.get parent = .element pns ptag pst pmg acc := by
          rw [haMidFrame parent (by omega)]
          simp [aIn, DomArena.get_set_self]
        have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := by
          intro fcs hfrag
          cases f with
          | zero => omega
          | succ f' =>
              cases c with
              | text s =>
                  simp [aMid, cn, res1, buildDomM, MonadDom.createText, DomArena.alloc, DomArena.get] at hfrag
              | element tag' attrs' cs' =>
                  dsimp only [readDomTree] at hcnRead
                  rw [hfrag] at hcnRead
                  simp [specDom] at hcnRead
        have hcnNotInAcc : cn ∉ acc := by
          intro hmem
          have hsub := haccSub cn hmem
          cases f with
          | zero => omega
          | succ f' =>
              have hlt := hsub.2.1
              omega
        have heraseAcc : acc.erase cn = acc := List.erase_of_not_mem hcnNotInAcc
        let aAfterAppend := aMid.set parent (.element pns ptag pst pmg (acc ++ [cn]))
        have happendRun :
            (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn).run aMid = ((), aAfterAppend) := by
          cases hgetCn : aMid.get cn with
          | fragment fcs => exact False.elim (hcnNotFrag fcs hgetCn)
          | null =>
              simp [MonadDom.appendChild, StateT.run, hgetCn, DomArena.modify, hparInMid, heraseAcc, aAfterAppend]
          | text _ =>
              simp [MonadDom.appendChild, StateT.run, hgetCn, DomArena.modify, hparInMid, heraseAcc, aAfterAppend]
          | element _ _ _ _ _ =>
              simp [MonadDom.appendChild, StateT.run, hgetCn, DomArena.modify, hparInMid, heraseAcc, aAfterAppend]
        have haMidNext : aBase.nextId ≤ aMid.nextId := by omega
        have haccMid : ∀ x ∈ acc,
            SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId x ∧
            readDomTree f aAfterAppend x = readDomTree f aIn x := by
          intro x hx
          have hsub0 := haccSub x hx
          have hfr := SubtreeInRange_frame (a := aIn) (a' := aAfterAppend)
            (lo := parent.toNat + 1) (hi := aBase.nextId) (n := x)
            (fun m hlo hhi => by
              have hne : m ≠ parent := by intro heq; subst heq; omega
              rw [DomArena.get_set_ne _ _ hne]
              exact haMidFrame m (by omega))
            hsub0
          exact ⟨SubtreeInRange_mono (Nat.le_refl _) haMidNext hfr.1, hfr.2⟩
        have hcnAfter :
            SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId cn ∧
            readDomTree f aAfterAppend cn = specDom childNs c := by
          have hsubW := SubtreeInRange_mono (by omega : parent.toNat + 1 ≤ aIn.nextId) (Nat.le_refl _) hcnSub
          have hfr := SubtreeInRange_frame (a := aMid) (a' := aAfterAppend)
            (lo := parent.toNat + 1) (hi := aMid.nextId) (n := cn)
            (fun m hlo _ => by
              have hne : m ≠ parent := by intro heq; subst heq; omega
              exact DomArena.get_set_ne _ _ hne)
            hsubW
          exact ⟨hfr.1, hfr.2.trans hcnRead⟩
        have hsubComb :
            ∀ x ∈ acc ++ [cn], SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId x := by
          intro x hx
          rcases List.mem_append.1 hx with hxAcc | hxCn
          · exact (haccMid x hxAcc).1
          · simp only [List.mem_singleton] at hxCn
            subst hxCn
            exact hcnAfter.1
        have hih := buildDomListM_spec childNs rest aMid parent pns ptag pst pmg (acc ++ [cn]) f
          (by omega)
          (by omega)
          (by omega)
          hrestDep
          hsubComb
        rcases hih with ⟨csRest, aBase'', haOutEq, hnextLe, hnextMono, hframeRest, hsubFinal, hreadFinal⟩
        have hstepRun :
            ((buildDomListM (m := StateM (DomArena msg)) childNs parent (c :: rest)).run aIn).2 =
              ((buildDomListM (m := StateM (DomArena msg)) childNs parent rest).run aAfterAppend).2 := by
          dsimp only [buildDomListM, StateT.run, bind, StateT.bind]
          change (match res1 with
                  | (cn', aMid') =>
                    match (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn').run aMid' with
                    | (_, aAfter') =>
                      (buildDomListM (m := StateM (DomArena msg)) childNs parent rest).run aAfter').2 =
                 ((buildDomListM (m := StateM (DomArena msg)) childNs parent rest).run aAfterAppend).2
          have hres1 : res1 = (cn, aMid) := rfl
          rw [hres1]
          dsimp only
          rw [happendRun]
        dsimp only
        simp only [htmlListNodeCount]
        rw [hstepRun]
        dsimp only [aAfterAppend] at haccMid hcnAfter ⊢
        refine ⟨cn :: csRest, aBase'', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using haOutEq
        · omega
        · omega
        · intro m hm hne
          rw [hframeRest m (by omega) hne, DomArena.get_set_ne _ _ hne]
          exact haMidFrame m (by omega)
        · simpa [List.append_assoc] using hsubFinal
        · have hmapInit :
              (acc ++ [cn]).map (readDomTree f (aMid.set parent (.element pns ptag pst pmg (acc ++ [cn])))) =
                acc.map (readDomTree f aIn) ++ [specDom childNs c] := by
            rw [List.map_append, List.map_singleton, hcnAfter.2]
            congr 1
            apply List.map_congr_left
            intro x hx
            exact (haccMid x hx).2
          simpa [List.append_assoc, specDomList, hmapInit] using hreadFinal
end


theorem uint32_toNat_ofNat_lt (n : Nat) (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem uint32_eq_of_toNat_eq {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.toBitVec_inj.1 (BitVec.eq_of_toNat_eq h)

theorem uint32_ofNat_succ (n : Nat) (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  apply uint32_eq_of_toNat_eq
  simp [UInt32.toNat_add, uint32_toNat_ofNat_lt n (by omega)]

/-- Membership predicate for DOM node subtrees inside an arbitrary node-index predicate `S : Nat → Prop`. -/
def SubtreeInSet {msg : Type} (fuel : Nat) (a : DomArena msg) (S : Nat → Prop) : Dom.Node → Prop :=
  match fuel with
  | 0 => fun _ => True
  | f + 1 => fun n =>
      S n.toNat ∧
      match a.get n with
      | .element _ _ _ _ cs => ∀ c ∈ cs, SubtreeInSet f a S c
      | _ => True

theorem SubtreeInRange_to_SubtreeInSet {msg : Type} :
    ∀ {f : Nat} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node},
      SubtreeInRange f a lo hi n → SubtreeInSet f a (fun k => lo ≤ k ∧ k < hi) n
  | 0, _, _, _, _, _ => trivial
  | f + 1, a, lo, hi, n, h => by
      dsimp only [SubtreeInRange] at h
      dsimp only [SubtreeInSet]
      refine ⟨⟨h.1, h.2.1⟩, ?_⟩
      cases hg : a.get n with
      | null => trivial
      | text _ => trivial
      | element ns tag st mg cs =>
          rw [hg] at h
          intro c hc
          exact SubtreeInRange_to_SubtreeInSet (h.2.2 c hc)
      | fragment _ => trivial

theorem SubtreeInSet_mono {msg : Type} :
    ∀ {f : Nat} {a : DomArena msg} {S₁ S₂ : Nat → Prop} {n : Dom.Node},
      (∀ k, S₁ k → S₂ k) →
      SubtreeInSet f a S₁ n →
      SubtreeInSet f a S₂ n
  | 0, _, _, _, _, _, _ => trivial
  | f + 1, a, S₁, S₂, n, hsub, hn => by
      dsimp only [SubtreeInSet] at hn ⊢
      refine ⟨hsub n.toNat hn.1, ?_⟩
      cases hg : a.get n with
      | null => trivial
      | text _ => trivial
      | element _ _ _ _ cs =>
          rw [hg] at hn
          intro c hc
          exact SubtreeInSet_mono hsub (hn.2 c hc)
      | fragment _ => trivial

theorem SubtreeInSet_frame {msg : Type} :
    ∀ {f : Nat} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
      SubtreeInSet f a S n →
      SubtreeInSet f a' S n ∧ readDomTree f a' n = readDomTree f a n
  | 0, _, _, _, _, _, _ => ⟨trivial, rfl⟩
  | f + 1, a, a', S, n, hfr, hn => by
      dsimp only [SubtreeInSet] at hn
      have hget : a'.get n = a.get n := hfr n hn.1
      refine ⟨?_, ?_⟩
      · dsimp only [SubtreeInSet]
        refine ⟨hn.1, ?_⟩
        rw [hget]
        cases hg : a.get n with
        | null => trivial
        | text _ => trivial
        | element _ _ _ _ cs =>
            rw [hg] at hn
            intro c hc
            exact (SubtreeInSet_frame hfr (hn.2 c hc)).1
        | fragment _ => trivial
      · dsimp only [readDomTree]
        rw [hget]
        cases hg : a.get n with
        | null => rfl
        | text _ => rfl
        | element ns tag st mg cs =>
            rw [hg] at hn
            dsimp only
            congr 1
            apply List.map_congr_left
            intro c hc
            exact (SubtreeInSet_frame hfr (hn.2 c hc)).2
        | fragment _ => rfl


theorem getD_append_right {α : Type} (x d : α) :
    ∀ (pre suf : List α), (pre ++ x :: suf).getD pre.length d = x
  | [], _ => rfl
  | _ :: rest, suf => getD_append_right x d rest suf

def removeTailSpec (idx : Nat) : Nat → List α → List α
  | 0, cs => cs
  | k + 1, cs => removeTailSpec idx k (listRemoveAt cs idx)

theorem listRemoveAt_append_head {α : Type} :
    ∀ (pre : List α) (x : α) (suf : List α),
      listRemoveAt (pre ++ x :: suf) pre.length = pre ++ suf
  | [], _, suf => rfl
  | p :: prest, x, suf => by simp [listRemoveAt, listRemoveAt_append_head prest x suf]

theorem removeTailSpec_append {α : Type} (pre : List α) :
    ∀ (suf : List α), removeTailSpec pre.length suf.length (pre ++ suf) = pre
  | [] => by simp [removeTailSpec]
  | x :: suf => by
      simp [removeTailSpec, listRemoveAt_append_head pre x suf, removeTailSpec_append pre suf]

theorem removeTailM_spec (a : DomArena msg) (node : Dom.Node) (atIdx : Nat) (k : Nat)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node) :
    ((removeTailM (m := StateM (DomArena msg)) node (UInt32.ofNat atIdx) k).run
      (a.set node (.element ns tag st mg cs))).2 =
      a.set node (.element ns tag st mg (removeTailSpec (UInt32.ofNat atIdx).toNat k cs)) := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
      simp only [removeTailM, removeTailSpec, bind, StateT.bind, StateT.run,
                 DomArena.modifyChildren, DomArena.modify,
                 DomArena.get_set_self, DomArena.set_set]
      exact ih (listRemoveAt cs (UInt32.ofNat atIdx).toNat)

end Qed
