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

/-! ## 2. Pure Diff & W3C `insertBefore` Keyed/Positional Reconciler Equivalence -/

/-- For every `old` and `new` `Html` tree, patching `old` with `diff old new` yields a `DomTree`
    identical to building `new` from scratch. -/
theorem specDom_applyPatch_diff (ns : String) (old new : Html msg) :
    specDom ns (applyPatch (diff old new) old) = specDom ns new := by
  rw [diff_apply]

theorem insertBeforeRef_split {child ref : Dom.Node} :
    ∀ (pre suf : List Dom.Node),
      ref ∉ pre →
      insertBeforeRef child ref (pre ++ ref :: suf) = pre ++ child :: ref :: suf
  | [], suf, _ => by simp [insertBeforeRef]
  | x :: xs, suf, href => by
      have hne : (x == ref) = false := beq_eq_false_iff_ne.2 (fun h => href (by simp [h]))
      simp [insertBeforeRef, hne, insertBeforeRef_split xs suf (fun h => href (List.mem_cons_of_mem x h))]

theorem erase_append_right_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    (pre suf : List α) {x : α} (hnot : x ∉ pre) :
    (pre ++ suf).erase x = pre ++ suf.erase x := by
  induction pre with
  | nil => rfl
  | cons a rest ih =>
      have hne : (a == x) = false := beq_eq_false_iff_ne.2 (fun h => hnot (by simp [h]))
      simp [hne, ih (fun h => hnot (List.mem_cons_of_mem a h))]

private theorem not_mem_left_of_nodup_append {α : Type} {xs ys : List α} {y : α}
    (hnd : (xs ++ ys).Nodup) (hy : y ∈ ys) : y ∉ xs := by
  induction xs with
  | nil => intro h; nomatch h
  | cons x rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨hx, hrest⟩
      intro hm
      rcases List.mem_cons.1 hm with rfl | htail
      · exact hx (List.mem_append_right rest hy)
      · exact ih hrest htail

private theorem nodup_erase {α : Type} [BEq α] [LawfulBEq α] {xs : List α} (x : α)
    (hnd : xs.Nodup) : (xs.erase x).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨ha, hrest⟩
      by_cases hax : a == x
      · simpa [List.erase_cons, hax] using hrest
      · simp only [List.erase_cons, hax, Bool.false_eq_true, ↓reduceIte]
        refine List.nodup_cons.2 ⟨fun hm => ha (List.mem_of_mem_erase hm), ih hrest⟩

private theorem nodup_reinsert {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {c : α}
    (hnd : (pre ++ suf).Nodup) (hc : c ∉ pre) :
    (pre ++ c :: suf.erase c).Nodup := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at hnd ⊢
      refine List.nodup_cons.2 ⟨?_, nodup_erase c hnd⟩
      -- Since `suf.Nodup`, erasing `c` removes the only possible occurrence of `c` in `suf`.
      clear hc
      induction suf with
      | nil => simp
      | cons s srest ihS =>
          rcases List.nodup_cons.1 hnd with ⟨hs, hsrest⟩
          by_cases hsc : s == c
          · have heq : s = c := eq_of_beq hsc
            subst heq
            simpa [List.erase_cons] using hs
          · simp only [List.erase_cons, hsc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
            refine ⟨fun h => hsc (beq_iff_eq.2 h.symm), ihS hsrest⟩
  | cons p prest ih =>
      simp only [List.cons_append] at hnd ⊢
      rcases List.nodup_cons.1 hnd with ⟨hp, hprest⟩
      have hcp : c ≠ p := fun h => hc (by simp [h])
      refine List.nodup_cons.2 ⟨?_, ih hprest (fun h => hc (List.mem_cons_of_mem p h))⟩
      intro hm
      rcases List.mem_append.1 hm with h1 | h2
      · exact hp (List.mem_append_left _ h1)
      · rcases List.mem_cons.1 h2 with hpeq | her
        · exact hcp hpeq.symm
        · exact hp (List.mem_append_right _ (List.mem_of_mem_erase her))

/-- Unified W3C `insertBefore` step theorem: whether `child` is freshly created (`child ∉ suf`)
    or reused from `suf` (`child ∈ suf`), as long as `(pre ++ suf).Nodup` and `child ∉ pre`,
    `w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child`. -/
theorem w3cInsertBefore_step (pre suf : List Dom.Node) (child : Dom.Node)
    (hnd : (pre ++ suf).Nodup) (hnotPre : child ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child := by
  unfold w3cInsertBefore
  rw [List.drop_left]
  cases suf with
  | nil =>
      simp [List.erase_of_not_mem hnotPre]
  | cons ref rest =>
      by_cases hrc : ref == child
      · have heq : ref = child := eq_of_beq hrc
        subst heq
        simp
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        rw [erase_append_right_of_not_mem pre (ref :: rest) hnotPre]
        have hrc' : (ref == child) = false := Bool.eq_false_iff.2 hrc
        simp only [List.erase_cons, hrc', Bool.false_eq_true, ↓reduceIte]
        have hrefNotPre : ref ∉ pre := not_mem_left_of_nodup_append hnd (List.mem_cons_self ..)
        exact insertBeforeRef_split pre (rest.erase child) hrefNotPre

def w3cPlaceSeq : List Dom.Node → Nat → List Dom.Node → List Dom.Node
  | cs, _, [] => cs
  | cs, j, target :: rest => w3cPlaceSeq (w3cInsertBefore cs j target) (j + 1) rest

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

theorem w3cPlaceSeq_invariant (targets : List Dom.Node) :
    ∀ (pre suf : List Dom.Node),
      (pre ++ suf).Nodup →
      targets.Nodup →
      (∀ t ∈ targets, t ∉ pre) →
      ∃ rem,
        w3cPlaceSeq (pre ++ suf) pre.length targets = pre ++ targets ++ rem := by
  induction targets with
  | nil =>
      intro pre suf _ _ _
      exact ⟨suf, by simp [w3cPlaceSeq]⟩
  | cons t rest ih =>
      intro pre suf hnd htnd hdisj
      rcases List.nodup_cons.1 htnd with ⟨htRest, hrestNd⟩
      have htNotPre : t ∉ pre := hdisj t (List.mem_cons_self ..)
      have hstep := w3cInsertBefore_step pre suf t hnd htNotPre
      have hnd' : ((pre ++ [t]) ++ suf.erase t).Nodup := by
        simpa [List.append_assoc] using nodup_reinsert hnd htNotPre
      have hdisj' : ∀ r ∈ rest, r ∉ pre ++ [t] := by
        intro r hr hm
        rcases List.mem_append.1 hm with h1 | h2
        · exact hdisj r (List.mem_cons_of_mem t hr) h1
        · simp only [List.mem_singleton] at h2
          subst h2
          exact htRest hr
      have hlen' : (pre ++ [t]).length = pre.length + 1 := by simp
      rcases ih (pre ++ [t]) (suf.erase t) hnd' hrestNd hdisj' with ⟨rem, heq⟩
      refine ⟨rem, ?_⟩
      simp only [w3cPlaceSeq, hstep]
      have hassoc : pre ++ t :: suf.erase t = (pre ++ [t]) ++ suf.erase t := by simp
      rw [hassoc, ← hlen', heq]
      simp [List.append_assoc]

/-- Complete keyed child-order reconciliation theorem: placing any duplicate-free `targets` sequence
    via W3C `insertBefore` over an existing duplicate-free `live` child list and removing the
    trailing unused suffix yields `targets` in exact order. -/
theorem w3cReconcileKeyed_eq (live targets : List Dom.Node)
    (hlive : live.Nodup) (htargets : targets.Nodup) :
    let placed := w3cPlaceSeq live 0 targets
    removeTailSpec targets.length (placed.length - targets.length) placed = targets := by
  rcases w3cPlaceSeq_invariant targets [] live (by simpa using hlive) htargets
    (fun _ _ h => nomatch h) with ⟨rem, hplaced⟩
  dsimp only
  simp only [List.nil_append, List.length_nil] at hplaced
  rw [hplaced]
  have hsub : (targets ++ rem).length - targets.length = rem.length := by simp
  rw [hsub]
  exact removeTailSpec_append targets rem

/-! ## 3. HTML5 Text Coalescing & `hydrateTextSlotM` / `hydrateDomM` Equivalence -/

theorem hasMoreText_false_restOfTextRun :
    ∀ (cs : List (Html msg)), hasMoreText cs = false → restOfTextRun cs = ""
  | [], _ => rfl
  | c :: cs, h => by
      cases hc : c.textOf? with
      | none => simp [restOfTextRun, hc]
      | some s =>
          by_cases hse : s = ""
          · subst hse
            simp only [hasMoreText, hc] at h
            simp [restOfTextRun, hc, hasMoreText_false_restOfTextRun cs h]
          · simp [hasMoreText, hc] at h

/-- Pure DOM-child specification of `hydrateTextSlotM` + `hydrateDomKidsM`: given the coalesced
    child texts emitted by an HTML5 parser (`coalesceTextRun cs`), `hydrateTextSlotM` splits merged
    text runs and inserts `""` placeholder nodes so the hydrated child list matches `cs` 1-for-1. -/
def hydrateDomTextModel (inTextRun : Bool) : List (Html msg) → List (Html msg) → List (Html msg)
  | [], _ => []
  | c :: rest, dom =>
      match c.textOf? with
      | some s =>
          if s == "" then
            .text "" :: hydrateDomTextModel inTextRun rest dom
          else if inTextRun then
            .text s :: hydrateDomTextModel true rest dom
          else
            match dom with
            | .text raw :: domRest =>
                let fixed := if hasMoreText rest then s else raw
                .text fixed :: hydrateDomTextModel true rest domRest
            | _ :: domRest =>
                .text s :: hydrateDomTextModel true rest domRest
            | [] => []
      | none =>
          match dom with
          | _ :: domRest => c :: hydrateDomTextModel false rest domRest
          | [] => []

private theorem textOf_eq_some_iff {h : Html msg} {s : String} :
    h.textOf? = some s ↔ h = .text s := by
  cases h <;> simp [Html.textOf?]

theorem hydrateDomTextModel_roundtrip (cs : List (Html msg)) :
    hydrateDomTextModel false cs (coalesceTextRun cs) = cs ∧
    hydrateDomTextModel true cs (dropCurrentTextRun cs) = cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c rest ih =>
      rcases ih with ⟨ihFalse, ihTrue⟩
      cases hc : c.textOf? with
      | none =>
          refine ⟨?_, ?_⟩ <;>
            simpa [hydrateDomTextModel, coalesceTextRun, dropCurrentTextRun, hc] using ihFalse
      | some s =>
          have hce : c = .text s := textOf_eq_some_iff.1 hc
          subst hce
          cases hs : (s == "") with
          | true =>
              have hse : s = "" := eq_of_beq hs
              subst hse
              refine ⟨?_, ?_⟩
              · simpa [hydrateDomTextModel, coalesceTextRun, Html.textOf?] using ihFalse
              · simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?] using ihTrue
          | false =>
              have hne : s ≠ "" := fun h => by simp [h] at hs
              refine ⟨?_, ?_⟩
              · simp only [coalesceTextRun, Html.textOf?, hs, Bool.false_eq_true, ↓reduceIte,
                           hydrateDomTextModel, ihTrue]
                cases hm : hasMoreText rest with
                | true => simp
                | false =>
                    simp [hasMoreText_false_restOfTextRun rest hm]
              · simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?, hne] using ihTrue

/-- Hydrating an HTML5-coalesced child list restores the exact uncoalesced `Html` child list,
    including preserving existing text nodes untouched when `hasMoreText rest = false`. -/
theorem hydrateTextRun_equiv (cs : List (Html msg)) :
    hydrateDomTextModel false cs (coalesceTextRun cs) = cs :=
  (hydrateDomTextModel_roundtrip cs).1

/-- Imperative `hydrateDomM` on an element node clears stale handler attributes, applies normalized
    attributes (`evalSpecAttrs attrs`), and hydrates children when `!ownsChildren attrs`. -/
theorem hydrateDomM_ownsChildren_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) (children : List (Html msg))
    (hown : ownsChildren attrs = true) :
    ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs children) node).run
      (a.set node (.element ns tag {} [] cs))).2 =
      a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs) := by
  dsimp only [hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure,
              MonadDom.clearHandlers, DomArena.modifyElemState, DomArena.modify]
  rw [if_neg (by simp [hown]), DomArena.get_set_self, DomArena.set_set]
  dsimp only
  rw [applyAttrsM_fresh_element a node ns tag cs attrs]
  rfl

/-! ## 4. Congruence-Sound Memoization (`View.memo`) & Duplicate-Key Safety (`V.forEach`) -/

/-- When `sm.keyOf s₂ = sm.keyOf s₁`, `patchViewM` on `.memo sm` performs **zero** DOM mutations
    (`a' = a`), preserves the exact `node` handle, and by `sm.sound` the existing DOM subtree is
    guaranteed equal to `specDom ns (View.render (.memo sm) s₂)`. -/
theorem patchViewM_memo_hit {σ msg : Type} (sm : SoundMemo σ msg)
    (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (ns : String)
    (hkey : sm.keyOf s₂ = sm.keyOf s₁)
    (hdom : readDomTree fuel a node = specDom ns (View.render (.memo sm) s₁)) :
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.memo sm) s₂
        (.memo node (sm.keyOf s₁) (sm.eval s₁))).run a
    a' = a ∧
    vst' = .memo node (sm.keyOf s₁) (sm.eval s₁) ∧
    readDomTree fuel a' node = specDom ns (View.render (.memo sm) s₂) := by
  have hbeq : (sm.keyOf s₂ == sm.keyOf s₁) = true := beq_iff_eq.2 hkey
  have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey
  simp [patchViewM, StateT.run, pure, StateT.pure, hbeq, View.render, heval, hdom]

/-- Imperative `patchViewM` on `.dyn get` updates the DOM text node when changed and always
    leaves `readDomTree` equal to `specDom "" (View.render (.dyn get) s₂)`. -/
theorem patchViewM_dyn_spec {σ msg : Type} (get : σ → String) (s₁ s₂ : σ)
    (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text (get s₁))
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.dyn get) s₂ (.dyn node (get s₁))).run a0
    vst' = .dyn node (get s₂) ∧
    readDomTree fuel a' node = specDom "" (View.render (.dyn get) s₂) := by
  cases fuel with
  | zero => omega
  | succ f =>
      dsimp only
      by_cases heq : get s₂ = get s₁
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure,
              heq, readDomTree, DomArena.get_set_self, specDom, View.render]
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, heq,
              MonadDom.setText, DomArena.modify, DomArena.get_set_self,
              readDomTree, specDom, View.render]

/-- Every keyed list produced by `V.forEach` (or patched/hydrated by `Template.lean`) disambiguates
    keys so that duplicate sibling keys are impossible (`Nodup` holds unconditionally). -/
theorem forEach_disambiguated_keys_nodup {α σ : Type} (items : σ → Array α) (key : α → String) (s : σ) :
    (disambiguateKeys ((items s).map key)).toList.Nodup :=
  disambiguateKeys_nodup ((items s).map key)

/-! ## 5. End-to-End Isomorphic SSR → Rehydrate → Client Equivalence (`App.ssr_rehydrate_equiv`) -/

/-- Crown-jewel isomorphic rendering theorem for every compiled Qed `App`:
    1. Every server-rendered view `app.view m` satisfies HTML5 & XSS validity (`Html.valid`).
    2. Whenever client `app.rehydrate (app.dehydrate m)` succeeds with `m'`, `m'` satisfies
       `Html.valid (app.view m') = true`, renders the **exact** same `Html` and serialized markup
       as the server (`app.view m' = app.view m`), and has the **exact** same `DomTree` (`specDom`).
    3. Every subsequent client message transition `msg : Msg` reconciled via `diff` produces the
       exact `DomTree` of a fresh render of `(app.update m' msg).1`. -/
theorem App.ssr_rehydrate_equiv {Model Msg : Type} (app : App Model Msg)
    (m m' : Model) (hre : app.rehydrate (app.dehydrate m) = some m') :
    Html.valid (app.view m) = true ∧
    Html.valid (app.view m') = true ∧
    app.view m' = app.view m ∧
    Html.render (app.view m') = Html.render (app.view m) ∧
    specDom "" (app.view m') = specDom "" (app.view m) ∧
    (∀ msg : Msg,
      specDom "" (applyPatch (diff (app.view m') (app.view (app.update m' msg).1)) (app.view m')) =
        specDom "" (app.view (app.update m' msg).1)) := by
  have hvalidM  : Html.valid (app.view m) = true := app.valid_view m
  have hvalidM' : Html.valid (app.view m') = true := app.valid_view m'
  have hview    : app.view m' = app.view m := app.dehydrate_view m m' hre
  refine ⟨hvalidM, hvalidM', hview, congrArg Html.render hview, congrArg (specDom "") hview, ?_⟩
  intro msg
  exact specDom_applyPatch_diff "" (app.view m') (app.view (app.update m' msg).1)

end Qed

