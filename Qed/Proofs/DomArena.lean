import Qed.Driver.Template
import Qed.Runtime.AppCore
import Qed.Ssr

namespace Qed
variable {msg : Type}

/-! # DomArena Refinement, Attribute Retention & Signal-Store Resolution -/

structure SpecElemState (msg : Type) where
  attrs     : List (String × String) := []
  value     : String := ""
  checked   : Bool := false
  clicks    : List (String × msg) := []
  inputs    : List (String × (String → msg)) := []
  sigBind   : Option String := none
  sigAttr   : List (String × String) := []
  sigClicks : List (String × String) := []

inductive DomTree (msg : Type) where
  | text (s : String)
  | element (ns : String) (tag : String) (state : SpecElemState msg) (children : List (DomTree msg))

inductive ArenaEntry (msg : Type) where
  | null | text (s : String) | fragment (children : List Dom.Node)
  | element (ns : String) (tag : String) (state : SpecElemState msg) (managed : List String) (children : List Dom.Node)

structure ArenaTmpl (msg : Type) where
  ns        : String
  proto     : Html msg
  slotPaths : Array (Array UInt32)
  slotAttrs : Array String
  evPaths   : Array (Array UInt32)
  evNames   : Array String

@[ext]
structure DomArena (msg : Type) where
  nextId    : Nat := 1
  store     : Dom.Node → ArenaEntry msg := fun _ => .null
  signals   : List (String × String) := []
  sigEvents : List (String × msg) := []
  tmpls     : Array (ArenaTmpl msg) := #[]
  rowEvs    : Array (Nat → Nat → Option msg) := #[]

inductive AttrSlot where | attr (k : String) | val | chk | click (e : String) | input (e : String)
inductive SlotVal (msg : Type) where
  | optStr (v : Option String) | str (v : String) | bool (v : Bool) | optMsg (v : Option msg) | optFn (v : Option (String → msg))

inductive ListForall2 {α : Type} (R : α → α → Prop) : List α → List α → Prop where
  | nil : ListForall2 R [] []
  | cons {x y : α} {xs ys : List α} : R x y → ListForall2 R xs ys → ListForall2 R (x :: xs) (y :: ys)

structure ArenaExt (a a' : DomArena msg) (W : Nat → Prop) (budget : Nat) : Prop where
  next_ge : a.nextId ≤ a'.nextId
  next_le : a'.nextId ≤ a.nextId + budget
  frame   : ∀ m : Dom.Node, m.toNat < a.nextId → ¬ W m.toNat → a'.store m = a.store m

def setAssoc {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)] | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: setAssoc k v rest
def eraseAssoc {α : Type} (k : String) (xs : List (String × α)) : List (String × α) := xs.filter fun (k', _) => k' != k
def lookupAssoc {α : Type} (k : String) : List (String × α) → Option α
  | [] => none | (k', v) :: rest => if k' == k then some v else lookupAssoc k rest

def AttrSlot.read (st : SpecElemState msg) : AttrSlot → SlotVal msg
  | .attr k => .optStr (lookupAssoc k st.attrs) | .val => .str st.value | .chk => .bool st.checked
  | .click e => .optMsg (lookupAssoc e st.clicks) | .input e => .optFn (lookupAssoc e st.inputs)
def ElemStateEquiv (st₁ st₂ : SpecElemState msg) : Prop := ∀ sl : AttrSlot, sl.read st₁ = sl.read st₂
inductive DomTreeAssocEquiv : DomTree msg → DomTree msg → Prop where
  | text (s : String) : DomTreeAssocEquiv (.text s) (.text s)
  | element {ns tag : String} {st₁ st₂ : SpecElemState msg} {cs₁ cs₂ : List (DomTree msg)} :
      ElemStateEquiv st₁ st₂ → ListForall2 DomTreeAssocEquiv cs₁ cs₂ →
      DomTreeAssocEquiv (.element ns tag st₁ cs₁) (.element ns tag st₂ cs₂)
abbrev DomTreeListAssocEquiv : List (DomTree msg) → List (DomTree msg) → Prop := ListForall2 DomTreeAssocEquiv

mutual
  def htmlNodeCount : Html msg → Nat | .text _ => 1 | .element _ _ cs => 1 + htmlListNodeCount cs
  def htmlListNodeCount : List (Html msg) → Nat | [] => 0 | c :: cs => htmlNodeCount c + htmlListNodeCount cs
end
mutual
  def htmlDepth : Html msg → Nat | .text _ => 1 | .element _ _ cs => 1 + htmlListDepth cs
  def htmlListDepth : List (Html msg) → Nat | [] => 0 | c :: cs => Nat.max (htmlDepth c) (htmlListDepth cs)
end

section
variable {α : Type}

theorem lookupAssoc_setAssoc (k k' : String) (v : α) :
    ∀ (xs : List (String × α)), lookupAssoc k (setAssoc k' v xs) = if k' == k then some v else lookupAssoc k xs
  | [] => rfl
  | (a, _) :: rest => by
      by_cases h1 : a = k'
      · subst h1; by_cases h2 : a = k
        · subst h2; simp only [setAssoc, lookupAssoc, beq_self_eq_true, ↓reduceIte]
        · simp only [setAssoc, lookupAssoc, beq_self_eq_true, beq_eq_false_iff_ne.2 h2, Bool.false_eq_true, ↓reduceIte]
      · by_cases h2 : a = k
        · subst h2; simp only [setAssoc, lookupAssoc, beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 (Ne.symm h1), beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        · simp only [setAssoc, lookupAssoc, beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 h2, Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc k k' v rest]

theorem lookupAssoc_filter (p : String → Bool) (k : String) :
    ∀ (xs : List (String × α)), lookupAssoc k (xs.filter fun (k', _) => p k') = if p k then lookupAssoc k xs else none
  | [] => by cases p k <;> rfl
  | (a, _) :: rest => by
      simp only [List.filter_cons, lookupAssoc]; by_cases ha : a = k
      · subst ha; cases hp : p a <;> simp only [hp, Bool.false_eq_true, ↓reduceIte, lookupAssoc, beq_self_eq_true, lookupAssoc_filter p a rest]
      · cases p a <;> simp only [Bool.false_eq_true, ↓reduceIte, lookupAssoc, beq_eq_false_iff_ne.2 ha, lookupAssoc_filter p k rest]

theorem lookupAssoc_eraseAssoc (k k' : String) (xs : List (String × α)) :
    lookupAssoc k (eraseAssoc k' xs) = if k' == k then none else lookupAssoc k xs := by
  rw [eraseAssoc, lookupAssoc_filter (· != k')]
  by_cases h : k = k'
  · subst h; simp only [bne_self_eq_false, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [bne, beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 (Ne.symm h), Bool.not_false, Bool.false_eq_true, ↓reduceIte]
end

theorem string_append_left_cancel {p a b : String} (h : p ++ a = p ++ b) : a = b :=
  String.ext (List.append_cancel_left (by simpa only [String.toList_append] using congrArg String.toList h))

def stepSpecAttr (st : SpecElemState msg) : Attr msg → SpecElemState msg
  | .cls c                    => { st with attrs := setAssoc "class" c st.attrs }
  | .attr k v                 => if k == "value" then { st with value := v } else { st with attrs := setAssoc k v st.attrs }
  | .flag k present           => if k == "checked" then { st with checked := present }
                                 else { st with attrs := if present then setAssoc k k st.attrs else eraseAssoc k st.attrs }
  | .key _                    => st
  | .on event evMsg           => { st with clicks := setAssoc event evMsg st.clicks }
  | .onValue event f          => { st with inputs := setAssoc event f st.inputs }
  | .localCell key comp _ _ _ => { st with attrs := setAssoc "data-qed-local" (localKey comp key) st.attrs }
  | .signalBind name          => { st with sigBind := some name }
  | .signalAttr name attr _   => { st with sigAttr := setAssoc attr name st.sigAttr }
  | .signalOn name event _    => { st with sigClicks := setAssoc event name st.sigClicks }
def evalSpecAttrs (attrs : List (Attr msg)) : SpecElemState msg := (normalizeAttrs attrs).foldl stepSpecAttr {}

mutual
  def specDom (ns : String) : Html msg → DomTree msg
    | .text s => .text s
    | .element tag attrs children =>
        .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag (evalSpecAttrs attrs)
          (if ownsChildren attrs then [] else specDomList (Dom.childNsOf ns tag) children)
  def specDomList (ns : String) : List (Html msg) → List (DomTree msg)
    | [] => [] | c :: cs => specDom ns c :: specDomList ns cs
end
@[simp] theorem specDomList_eq_map (ns : String) : ∀ (cs : List (Html msg)), specDomList ns cs = cs.map (specDom ns)
  | [] => rfl | c :: cs => congrArg (specDom ns c :: ·) (specDomList_eq_map ns cs)

/-! ## Pure `DomArena` & `MonadDom` Instance -/

def insertBeforeRef (child ref : Dom.Node) : List Dom.Node → List Dom.Node
  | [] => [child] | x :: xs => if x == ref then child :: x :: xs else x :: insertBeforeRef child ref xs
def w3cInsertBefore (children : List Dom.Node) (idx : Nat) (child : Dom.Node) : List Dom.Node :=
  match children.drop idx with
  | [] => (children.erase child) ++ [child]
  | ref :: _ => if ref == child then children else insertBeforeRef child ref (children.erase child)
def w3cInsertBeforeRef (children : List Dom.Node) (ref? : Option Dom.Node) (child : Dom.Node) : List Dom.Node :=
  match ref? with
  | none => (children.erase child) ++ [child]
  | some ref => if ref == child then children else insertBeforeRef child ref (children.erase child)
def listRemoveAt {α : Type} : List α → Nat → List α
  | [], _ => [] | _ :: xs, 0 => xs | x :: xs, i + 1 => x :: listRemoveAt xs i
def listReplaceAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => [] | _ :: xs, 0, v => v :: xs | x :: xs, i + 1, v => x :: listReplaceAt xs i v

private abbrev ArenaM (msg : Type) := StateM (DomArena msg)

namespace DomArena
def get (a : DomArena msg) (n : Dom.Node) : ArenaEntry msg := a.store n
def set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) : DomArena msg := { a with store := fun m => if m == n then e else a.store m }
def modify (a : DomArena msg) (n : Dom.Node) (f : ArenaEntry msg → ArenaEntry msg) : DomArena msg := a.set n (f (a.get n))
def alloc (a : DomArena msg) (e : ArenaEntry msg) : Dom.Node × DomArena msg :=
  let h := UInt32.ofNat a.nextId; (h, { a with nextId := a.nextId + 1, store := fun m => if m == h then e else a.store m })
@[simp] theorem get_set_self (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) : (a.set n e).get n = e := by simp only [get, set, beq_self_eq_true, ↓reduceIte]
@[simp] theorem get_set_ne (a : DomArena msg) {n m : Dom.Node} (e : ArenaEntry msg) (hne : m ≠ n) : (a.set n e).get m = a.get m := by simp only [get, set, beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ↓reduceIte]
@[simp] theorem nextId_set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) : (a.set n e).nextId = a.nextId := rfl
@[simp] theorem set_set (a : DomArena msg) (n : Dom.Node) (e₁ e₂ : ArenaEntry msg) : (a.set n e₁).set n e₂ = a.set n e₂ :=
  DomArena.ext rfl (funext fun m => if hm : m = n then by subst hm; simp only [set, beq_self_eq_true, ↓reduceIte] else by simp only [set, beq_eq_false_iff_ne.2 hm, Bool.false_eq_true, ↓reduceIte]) rfl rfl rfl rfl
theorem set_get_self (a : DomArena msg) {n : Dom.Node} {e : ArenaEntry msg} (h : a.get n = e) : a.set n e = a :=
  DomArena.ext rfl (funext fun m => if hm : m = n then by subst hm; simp only [set, beq_self_eq_true, ↓reduceIte]; exact h.symm else by simp only [set, beq_eq_false_iff_ne.2 hm, Bool.false_eq_true, ↓reduceIte]) rfl rfl rfl rfl
@[reducible] def modifyElemState (a : DomArena msg) (n : Dom.Node) (f : SpecElemState msg → SpecElemState msg) : DomArena msg :=
  a.modify n fun | .element ns tag st mg cs => .element ns tag (f st) mg cs | other => other
@[reducible] def modifyChildren (a : DomArena msg) (p : Dom.Node) (f : List Dom.Node → List Dom.Node) : DomArena msg :=
  a.modify p fun | .element ns tag st mg cs => .element ns tag st mg (f cs) | .fragment cs => .fragment (f cs) | other => other
def SameDom {msg : Type} (a₁ a₂ : DomArena msg) : Prop := a₁.nextId = a₂.nextId ∧ a₁.store = a₂.store
theorem SameDom.refl (a : DomArena msg) : a.SameDom a := ⟨rfl, rfl⟩
theorem SameDom.trans {a₁ a₂ a₃ : DomArena msg} (h1 : a₁.SameDom a₂) (h2 : a₂.SameDom a₃) : a₁.SameDom a₃ := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
theorem SameDom.get_eq {a₁ a₂ : DomArena msg} (h : a₁.SameDom a₂) (m : Dom.Node) : a₁.get m = a₂.get m := congrFun h.2 m
end DomArena

mutual
  def arenaBuildHtml (ns : String) : Html msg → DomArena msg → Dom.Node × DomArena msg
    | .text s, a => a.alloc (.text s)
    | .element tag attrs children, a =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        let st := evalSpecAttrs attrs; let mg := (normalizeAttrs attrs).filterMap managedAttrName
        let (node, a1) := a.alloc (.element realNs tag st mg [])
        if ownsChildren attrs then (node, a1)
        else let (cs, a2) := arenaBuildHtmlList (Dom.childNsOf ns tag) children a1; (node, a2.set node (.element realNs tag st mg cs))
  def arenaBuildHtmlList (ns : String) : List (Html msg) → DomArena msg → List Dom.Node × DomArena msg
    | [], a => ([], a)
    | c :: cs, a => let (cn, a1) := arenaBuildHtml ns c a; let (cns, a2) := arenaBuildHtmlList ns cs a1; (cn :: cns, a2)
end

def patchNodeSlotAt (a : DomArena msg) (n : Dom.Node) (path : List Nat) (attrName val : String) : DomArena msg :=
  match path with
  | [] => if attrName == "" then a.modify n fun | .text _ => .text val | other => other
          else if attrName == "value" then a.modifyElemState n fun st => { st with value := val }
          else a.modifyElemState n fun st => { st with attrs := setAssoc attrName val st.attrs }
  | idx :: rest => match a.get n with
      | .element _ _ _ _ cs => match cs[idx]? with | some child => patchNodeSlotAt a child rest attrName val | none => a
      | _ => a
def patchNodeSlotsLoop (slotPaths : Array (Array UInt32)) (slotAttrs newVals : Array String) (n : Dom.Node) (i : Nat) (a : DomArena msg) : DomArena msg :=
  if hi : i < slotPaths.size then
    patchNodeSlotsLoop slotPaths slotAttrs newVals n (i + 1)
      (patchNodeSlotAt a n ((slotPaths[i].toList).map UInt32.toNat) (slotAttrs.getD i "") (newVals.getD i ""))
  else a
termination_by slotPaths.size - i
def retainElem (prev names : List String) (st : SpecElemState msg) : SpecElemState msg :=
  let keep (k : String) := !prev.contains k || names.contains k
  { st with attrs := st.attrs.filter fun (k, _) => keep k
            value := if prev.contains "value" && !names.contains "value" then "" else st.value
            checked := if prev.contains "checked" && !names.contains "checked" then false else st.checked
            clicks := st.clicks.filter fun (e, _) => keep s!"data-qed-on-{e}"
            inputs := st.inputs.filter fun (e, _) => keep s!"data-qed-onv-{e}" }

instance : MonadDom msg (StateM (DomArena msg)) where
  createElement ns tag     := fun a => a.alloc (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] [])
  createText s             := fun a => a.alloc (.text s)
  createFragment           := fun a => a.alloc (.fragment [])
  childNamespace n         := fun a => (match a.get n with | .element ns tag _ _ _ => if ns == Dom.svgNs && tag != "foreignObject" then Dom.svgNs else "" | _ => "", a)
  setAttribute n k v       := fun a => ((), a.modifyElemState n fun st => { st with attrs := setAssoc k v st.attrs })
  removeAttribute n k      := fun a => ((), a.modifyElemState n fun st => { st with attrs := eraseAssoc k st.attrs })
  retainAttributes n names := fun a => ((), a.modify n fun | .element ns tag st prev cs => .element ns tag (retainElem prev names st) names cs | other => other)
  clearHandlers n          := fun a => ((), a.modifyElemState n fun st => { st with clicks := [], inputs := [] })
  setValue n v             := fun a => ((), a.modifyElemState n fun st => { st with value := v })
  setChecked n on          := fun a => ((), a.modifyElemState n fun st => { st with checked := on })
  setText n s              := fun a => ((), a.modify n fun | .text _ => .text s | .element ns tag st mg _ => .element ns tag st mg [] | other => other)
  appendChild p c          := fun a => match a.get c with
    | .fragment fcs => ((), (a.set c .null).modifyChildren p fun cs => (cs.filter (!fcs.contains ·)) ++ fcs)
    | _ => ((), a.modifyChildren p fun cs => (cs.erase c) ++ [c])
  childAt p i              := fun a => (match a.get p with | .element _ _ _ _ cs | .fragment cs => cs.getD i.toNat 0 | _ => 0, a)
  childCount p             := fun a => (match a.get p with | .element _ _ _ _ cs | .fragment cs => UInt32.ofNat cs.length | _ => 0, a)
  removeChild p i          := fun a => ((), a.modifyChildren p fun cs => listRemoveAt cs i.toNat)
  replaceChild p i nc      := fun a => ((), a.modifyChildren p fun cs => listReplaceAt cs i.toNat nc)
  insertBeforeNode p i ch  := fun a => ((), a.modifyChildren p fun cs => w3cInsertBefore cs i.toNat ch)
  insertBeforeRef p r ch   := fun a => ((), a.modifyChildren p fun cs => w3cInsertBeforeRef cs r ch)
  removeNode p ch          := fun a => ((), a.modifyChildren p fun cs => cs.erase ch)
  clearChildren p          := fun a => ((), a.modifyChildren p fun _ => [])
  bindSignal n name        := fun a => ((), a.modifyElemState n fun st => { st with sigBind := some name })
  bindSignalAttr n nm attr := fun a => ((), a.modifyElemState n fun st => { st with sigAttr := setAssoc attr nm st.sigAttr })
  setSignal name val       := fun a => ((), { a with signals := setAssoc name val a.signals })
  bindSignalOn n nm ev _   := fun a => ((), a.modifyElemState n fun st => { st with sigClicks := setAssoc ev nm st.sigClicks })
  setSignalOn name evMsg   := fun a => ((), { a with sigEvents := setAssoc name evMsg a.sigEvents })
  onEvent n event evMsg    := fun a => ((), a.modifyElemState n fun st => { st with clicks := setAssoc event evMsg st.clicks })
  onValueEvent n event f   := fun a => ((), a.modifyElemState n fun st => { st with inputs := setAssoc event f st.inputs })
  mountLocalCell n k c _ _ _ := fun a => ((), a.modifyElemState n fun st => { st with attrs := setAssoc "data-qed-local" (localKey c k) st.attrs })
  compileRowTmpl ns p sp sa ep en := fun a => (UInt32.ofNat a.tmpls.size, { a with tmpls := a.tmpls.push ⟨ns, p, sp, sa, ep, en⟩ })
  allocRowEvSlot _ fn      := fun a => (UInt32.ofNat a.rowEvs.size, { a with rowEvs := a.rowEvs.push fn })
  setRowEvSlot slot fn     := fun a => ((), if h : slot.toNat < a.rowEvs.size then { a with rowEvs := a.rowEvs.set slot.toNat fn h } else a)
  mountTmplRow id vals     := fun a => match a.tmpls[id.toNat]? with
    | some t => arenaBuildHtml t.ns (applyRowSlots t.proto t.slotPaths t.slotAttrs vals) a | none => (0, a)
  mountTmplRows p id vpr   := fun a => match a.tmpls[id.toNat]? with
    | some t => let (cs, a1) := arenaBuildHtmlList t.ns (vpr.toList.map (applyRowSlots t.proto t.slotPaths t.slotAttrs)) a; (cs.toArray, a1.modifyChildren p (· ++ cs))
    | none => (#[], a)
  patchTmplRow n id nv _   := fun a => ((), match a.tmpls[id.toNat]? with | some t => patchNodeSlotsLoop t.slotPaths t.slotAttrs nv n 0 a | none => a)
  hydrateTmplRow _ _       := fun a => ((), a)

def readDomTree : Nat → DomArena msg → Dom.Node → DomTree msg
  | 0, _, _ => .text ""
  | fuel + 1, a, n => match a.get n with | .text s => .text s | .element ns tag st _ cs => .element ns tag st (cs.map (readDomTree fuel a)) | _ => .text ""
theorem DomArena.SameDom.readDomTree_eq {a₁ a₂ : DomArena msg} (h : a₁.SameDom a₂) : ∀ f n, readDomTree f a₁ n = readDomTree f a₂ n
  | 0, _ => rfl
  | f + 1, n => by simp only [readDomTree, h.get_eq n]; split <;> first | rfl | exact congrArg (DomTree.element _ _ _) (List.map_congr_left fun c _ => h.readDomTree_eq f c)

/-! ## Signal Store Resolution (`emitSignalsM` & `readResolvedDomTree`) -/

def applySignalAttr (st : SpecElemState msg) : String → String → SpecElemState msg
  | "value", v => { st with value := v } | "checked", v => { st with checked := v != "" && v != "false" } | k, v => { st with attrs := setAssoc k v st.attrs }
def resolveElemSignals (signals : List (String × String)) (sigEvents : List (String × msg)) (st : SpecElemState msg) : SpecElemState msg :=
  let st1 := st.sigAttr.foldl (fun cur (k, sig) => match lookupAssoc sig signals with | some v => applySignalAttr cur k v | none => cur) st
  st1.sigClicks.foldl (fun cur (ev, sig) => match lookupAssoc sig sigEvents with | some m => { cur with clicks := setAssoc ev m cur.clicks } | none => cur) st1
def readResolvedDomTree : Nat → DomArena msg → Dom.Node → DomTree msg
  | 0, _, _ => .text ""
  | fuel + 1, a, n => match a.get n with
      | .text s => .text s
      | .element ns tag st _ cs => match st.sigBind with
          | some sig => .text ((lookupAssoc sig a.signals).getD "")
          | none => .element ns tag (resolveElemSignals a.signals a.sigEvents st) (cs.map (readResolvedDomTree fuel a))
      | _ => .text ""
theorem emitSignalsM_spec : ∀ (pairs : List (String × String)) (a : DomArena msg),
    (emitSignalsM (m := ArenaM msg) pairs).run a = ((), { a with signals := pairs.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals })
  | [], _ => rfl | p :: rest, a => emitSignalsM_spec rest { a with signals := setAssoc p.1 p.2 a.signals }
theorem emitSignalOnsM_spec : ∀ (pairs : List (String × msg)) (a : DomArena msg),
    (emitSignalOnsM (m := ArenaM msg) pairs).run a = ((), { a with sigEvents := pairs.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents })
  | [], _ => rfl | p :: rest, a => emitSignalOnsM_spec rest { a with sigEvents := setAssoc p.1 p.2 a.sigEvents }

/-! ## Attribute Retention, Equivalence & Clean-DOM Invariant -/

theorem applyAttrM_eq_modifyElemState (node : Dom.Node) (attr : Attr msg) (a : DomArena msg) :
    applyAttrM (m := ArenaM msg) node attr a = ((), a.modifyElemState node (stepSpecAttr · attr)) := by
  cases attr with
  | attr k _ => by_cases hk : k = "value"; · subst hk; rfl
                · simp only [applyAttrM, stepSpecAttr, beq_eq_false_iff_ne.2 hk, Bool.false_eq_true, ↓reduceIte]; rfl
  | flag k p => by_cases hk : k = "checked"; · subst hk; rfl
                · simp only [applyAttrM, stepSpecAttr, beq_eq_false_iff_ne.2 hk, Bool.false_eq_true, ↓reduceIte]; cases p <;> rfl
  | key _ => dsimp only [applyAttrM, pure, StateT.pure, DomArena.modifyElemState, DomArena.modify, stepSpecAttr]
             cases hg : a.get node <;> exact congrArg ((), ·) (DomArena.set_get_self a hg).symm
  | _ => rfl

theorem applyAttrM_element (a : DomArena msg) (node : Dom.Node) (ns tag : String)
    (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node) (attr : Attr msg) :
    applyAttrM (m := ArenaM msg) node attr (a.set node (.element ns tag st mg cs)) = ((), a.set node (.element ns tag (stepSpecAttr st attr) mg cs)) := by
  rw [applyAttrM_eq_modifyElemState]; simp [DomArena.modifyElemState, DomArena.modify]

theorem applyAttrListM_element :
    ∀ (attrs : List (Attr msg)) (a : DomArena msg) (node : Dom.Node) (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node),
      applyAttrListM (m := ArenaM msg) node attrs (a.set node (.element ns tag st mg cs)) = ((), a.set node (.element ns tag (attrs.foldl stepSpecAttr st) mg cs))
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: rest, a, node, ns, tag, _, _, _ => by dsimp only [applyAttrListM, bind, StateT.bind]; rw [applyAttrM_element]; exact applyAttrListM_element rest a node ns tag ..

theorem applyAttrsM_fresh_element (a : DomArena msg) (node : Dom.Node) (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) :
    applyAttrsM (m := ArenaM msg) node attrs (a.set node (.element ns tag {} [] cs)) =
      ((), a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs)) := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]; exact applyAttrListM_element (normalizeAttrs attrs) a node ns tag ..

theorem applyAttrsM_preserves (a : DomArena msg) (node : Dom.Node) (attrs : List (Attr msg)) :
    let a' := (applyAttrsM (m := ArenaM msg) node attrs a).2
    a'.nextId = a.nextId ∧ ∀ m, m ≠ node → a'.get m = a.get m := by
  let rec go : ∀ (l : List (Attr msg)) (s : DomArena msg),
      let s' := (applyAttrListM (m := ArenaM msg) node l s).2; s'.nextId = s.nextId ∧ ∀ m, m ≠ node → s'.get m = s.get m
    | [], _ => ⟨rfl, fun _ _ => rfl⟩
    | _ :: rest, _ => by dsimp only [applyAttrListM, bind, StateT.bind]; rw [applyAttrM_eq_modifyElemState]
                         exact (go rest _).imp id fun h2 m hm => (h2 m hm).trans (DomArena.get_set_ne _ _ hm)
  exact (go (normalizeAttrs attrs) _).imp id fun h2 m hm => (h2 m hm).trans (DomArena.get_set_ne _ _ hm)

def AttrSlot.managedName : AttrSlot → String
  | .attr k => k | .val => "value" | .chk => "checked" | .click e => s!"data-qed-on-{e}" | .input e => s!"data-qed-onv-{e}"
def Attr.slotUpdate? : Attr msg → AttrSlot → Option (SlotVal msg)
  | .cls s, .attr k => if "class" == k then some (.optStr (some s)) else none
  | .localCell k comp _ _ _, .attr k' => if "data-qed-local" == k' then some (.optStr (some (localKey comp k))) else none
  | .attr k' v, .val => if k' == "value" then some (.str v) else none
  | .attr k' v, .attr k => if k' != "value" && k' == k then some (.optStr (some v)) else none
  | .flag k' p, .chk => if k' == "checked" then some (.bool p) else none
  | .flag k' p, .attr k => if k' != "checked" && k' == k then some (.optStr (if p then some k' else none)) else none
  | .on e' m, .click e => if e' == e then some (.optMsg (some m)) else none
  | .onValue e' f, .input e => if e' == e then some (.optFn (some f)) else none
  | _, _ => none

theorem ElemStateEquiv.refl (st : SpecElemState msg) : ElemStateEquiv st st := fun _ => rfl
theorem ElemStateEquiv.trans {st₁ st₂ st₃ : SpecElemState msg} (h1 : ElemStateEquiv st₁ st₂) (h2 : ElemStateEquiv st₂ st₃) : ElemStateEquiv st₁ st₃ := fun sl => (h1 sl).trans (h2 sl)
theorem ElemStateEquiv.dispatchInput {st₁ st₂ : SpecElemState msg} (h : ElemStateEquiv st₁ st₂) (e raw : String) :
    (lookupAssoc e st₁.inputs).map (· raw) = (lookupAssoc e st₂.inputs).map (· raw) := by rw [SlotVal.optFn.inj (h (.input e))]
def ElemManaged (st : SpecElemState msg) (prev : List String) : Prop := ∀ sl : AttrSlot, sl.read st ≠ sl.read {} → prev.contains sl.managedName = true
theorem ElemManaged_empty {names : List String} : ElemManaged ({} : SpecElemState msg) names := fun _ h => absurd rfl h
def AttrsNoShadow (newAttrs : List (Attr msg)) (st : SpecElemState msg) : Prop :=
  ∀ sl : AttrSlot, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains sl.managedName = true →
    (∃ x ∈ normalizeAttrs newAttrs, (x.slotUpdate? sl).isSome = true) ∨ sl.read st = sl.read {}

private theorem opt_getD_ite {α β : Type} (f : α → β) (b : Bool) (x y : α) :
    f (if b then x else y) = (if b then some (f x) else none).getD (f y) := by cases b <;> rfl

theorem read_stepSpecAttr (st : SpecElemState msg) (a : Attr msg) (sl : AttrSlot) :
    sl.read (stepSpecAttr st a) = (a.slotUpdate? sl).getD (sl.read st) := by
  cases a with
  | cls _ | localCell _ _ _ _ _ => cases sl with | attr _ => dsimp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?]; rw [lookupAssoc_setAssoc]; exact opt_getD_ite .. | _ => rfl
  | on _ _ => cases sl with | click _ => dsimp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?]; rw [lookupAssoc_setAssoc]; exact opt_getD_ite .. | _ => rfl
  | onValue _ _ => cases sl with | input _ => dsimp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?]; rw [lookupAssoc_setAssoc]; exact opt_getD_ite .. | _ => rfl
  | attr k' _ =>
      dsimp only [stepSpecAttr]; cases hv : (k' == "value")
      · rw [ite_eq_right Bool.false_ne_true]
        cases sl with
        | attr _ => dsimp only [AttrSlot.read, Attr.slotUpdate?]; rw [show (k' != "value") = true from by simp only [bne, hv]; rfl, Bool.true_and, lookupAssoc_setAssoc]; exact opt_getD_ite ..
        | val => dsimp only [AttrSlot.read, Attr.slotUpdate?]; rw [hv]; rfl
        | _ => rfl
      · cases beq_iff_eq.1 hv; cases sl <;> rfl
  | flag k' p =>
      dsimp only [stepSpecAttr]; cases hc : (k' == "checked")
      · rw [ite_eq_right Bool.false_ne_true]
        cases sl with
        | attr _ =>
            dsimp only [AttrSlot.read, Attr.slotUpdate?]
            rw [show (k' != "checked") = true from by simp only [bne, hc]; rfl, Bool.true_and]
            cases p with
            | true => rw [ite_eq_left rfl, lookupAssoc_setAssoc]; exact opt_getD_ite ..
            | false => rw [ite_eq_right Bool.false_ne_true, lookupAssoc_eraseAssoc]; exact opt_getD_ite ..
        | chk => dsimp only [AttrSlot.read, Attr.slotUpdate?]; rw [hc]; rfl
        | _ => rfl
      · cases beq_iff_eq.1 hc; cases sl <;> rfl
  | _ => cases sl <;> rfl

private theorem eq_of_ite_some {α : Type} {b : Bool} {x : α} (h : (if b then some x else none).isSome = true) : b = true := by
  cases b
  · cases h
  · rfl

private theorem managedAttrName_of_slotUpdate {a : Attr msg} {sl : AttrSlot} (h : (a.slotUpdate? sl).isSome = true) : managedAttrName a = some sl.managedName := by
  cases a with
  | cls _ | localCell _ _ _ _ _ => cases sl with | attr _ => exact congrArg some (beq_iff_eq.1 (eq_of_ite_some h)) | _ => cases h
  | on _ _ => cases sl with | click _ => exact congrArg some (congrArg ("data-qed-on-" ++ ·) (beq_iff_eq.1 (eq_of_ite_some h))) | _ => cases h
  | onValue _ _ => cases sl with | input _ => exact congrArg some (congrArg ("data-qed-onv-" ++ ·) (beq_iff_eq.1 (eq_of_ite_some h))) | _ => cases h
  | attr _ _ => cases sl with | val => exact congrArg some (beq_iff_eq.1 (eq_of_ite_some h)) | attr _ => exact congrArg some (beq_iff_eq.1 (Bool.and_eq_true_iff.1 (eq_of_ite_some h)).2) | _ => cases h
  | flag _ _ => cases sl with | chk => exact congrArg some (beq_iff_eq.1 (eq_of_ite_some h)) | attr _ => exact congrArg some (beq_iff_eq.1 (Bool.and_eq_true_iff.1 (eq_of_ite_some h)).2) | _ => cases h
  | key _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => cases sl <;> cases h

theorem stepSpecAttr_retains_managed (st : SpecElemState msg) (a : Attr msg) (names : List String)
    (hkeep : match managedAttrName a with | some n => names.contains n = true | none => True) (hm : ElemManaged st names) : ElemManaged (stepSpecAttr st a) names := fun sl hne => by
  rw [read_stepSpecAttr] at hne; cases hu : a.slotUpdate? sl with
  | none => rw [hu] at hne; exact hm sl hne
  | some _ => rw [managedAttrName_of_slotUpdate (by rw [hu]; rfl)] at hkeep; exact hkeep

theorem foldl_stepSpecAttr_read (sl : AttrSlot) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ a ∈ xs, (a.slotUpdate? sl).isSome = true) ∨ sl.read s₁ = sl.read s₂) →
      sl.read (xs.foldl stepSpecAttr s₁) = sl.read (xs.foldl stepSpecAttr s₂)
  | [], _, _, .inl ⟨_, h, _⟩ => nomatch h | [], _, _, .inr h => h
  | x :: rest, _, _, h => by
      simp only [List.foldl_cons]; apply foldl_stepSpecAttr_read sl rest
      cases hx : x.slotUpdate? sl with
      | some _ => exact .inr (by rw [read_stepSpecAttr, read_stepSpecAttr, hx]; rfl)
      | none => exact h.imp (fun ⟨a, ha, hwa⟩ => (List.mem_cons.1 ha).elim (fun e => by subst e; rw [hx] at hwa; cases hwa) (⟨a, ·, hwa⟩))
                  (fun heq => by rw [read_stepSpecAttr, read_stepSpecAttr, hx]; exact heq)

private theorem read_retainElem (prev names : List String) (st : SpecElemState msg) (sl : AttrSlot) :
    sl.read (retainElem prev names st) = if prev.contains sl.managedName && !names.contains sl.managedName then sl.read {} else sl.read st := by
  let keep (k : String) := !prev.contains k || names.contains k
  have hite : ∀ {α β : Type} (f : α → β) (p n : Bool) (x y : α), f (if (!p || n) = true then x else y) = if (p && !n) = true then f y else f x := fun _ p n _ _ => by cases p <;> cases n <;> rfl
  cases sl with
  | attr _ => dsimp only [AttrSlot.read, AttrSlot.managedName, retainElem]; rw [lookupAssoc_filter keep]; exact hite ..
  | click _ => dsimp only [AttrSlot.read, AttrSlot.managedName, retainElem]; rw [lookupAssoc_filter (fun e => keep s!"data-qed-on-{e}")]; exact hite ..
  | input _ => dsimp only [AttrSlot.read, AttrSlot.managedName, retainElem]; rw [lookupAssoc_filter (fun e => keep s!"data-qed-onv-{e}")]; exact hite ..
  | val | chk => simp only [AttrSlot.read, AttrSlot.managedName, retainElem]; split <;> simp only [Bool.false_eq_true, ↓reduceIte, *]

private theorem ElemManaged_foldl_norm (attrs : List (Attr msg)) (s : SpecElemState msg)
    (hs : ElemManaged s ((normalizeAttrs attrs).filterMap managedAttrName)) :
    ElemManaged ((normalizeAttrs attrs).foldl stepSpecAttr s) ((normalizeAttrs attrs).filterMap managedAttrName) :=
  let names := (normalizeAttrs attrs).filterMap managedAttrName
  let rec go : ∀ (xs : List (Attr msg)) (cur : SpecElemState msg),
      (∀ x ∈ xs, match managedAttrName x with | some n => names.contains n = true | none => True) → ElemManaged cur names → ElemManaged (xs.foldl stepSpecAttr cur) names
    | [], _, _, h => h
    | x :: rest, cur, hx, hcur => go rest _ (fun y hy => hx y (.tail _ hy)) (stepSpecAttr_retains_managed cur x names (hx x (.head _)) hcur)
  go (normalizeAttrs attrs) s (fun x hx => by cases hm : managedAttrName x with | none => trivial | some n => exact List.contains_iff_mem.2 (List.mem_filterMap.2 ⟨x, hx, hm⟩)) hs

theorem applyAttrsM_existing_element (a : DomArena msg) (node : Dom.Node) (ns tag : String)
    (st : SpecElemState msg) (prev : List String) (cs : List Dom.Node) (newAttrs : List (Attr msg))
    (hm : ElemManaged st prev) (hNoShadow : AttrsNoShadow newAttrs st) :
    let norm := normalizeAttrs newAttrs; let names := norm.filterMap managedAttrName
    let a' := (applyAttrsM (m := ArenaM msg) node newAttrs (a.set node (.element ns tag st prev cs))).2
    ∃ st', a'.get node = .element ns tag st' names cs ∧ ElemStateEquiv st' (evalSpecAttrs newAttrs) ∧ ElemManaged st' names := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]
  let norm := normalizeAttrs newAttrs; let names := norm.filterMap managedAttrName; let st0 := retainElem prev names st
  rw [applyAttrListM_element norm a node ns tag st0 names cs, DomArena.get_set_self]
  have hretDef : ∀ sl : AttrSlot, (names.contains sl.managedName = true → sl.read st = sl.read {}) → sl.read st0 = sl.read {} := fun sl hns => by
    dsimp only [st0]; rw [read_retainElem]; by_cases hn : names.contains sl.managedName = true
    · simp only [hn, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; exact hns hn
    · by_cases hdef : sl.read st = sl.read {}; · simp [hdef]
      · simp only [hm sl hdef, Bool.eq_false_iff.2 hn, Bool.not_false, Bool.and_true, ↓reduceIte]
  refine ⟨norm.foldl stepSpecAttr st0, rfl,
    fun sl => foldl_stepSpecAttr_read sl norm st0 {} (if hw : ∃ x ∈ norm, (x.slotUpdate? sl).isSome = true then .inl hw else .inr (hretDef sl fun hn => (hNoShadow sl hn).resolve_left hw)),
    ElemManaged_foldl_norm newAttrs st0 fun sl hne => if hn : names.contains sl.managedName = true then hn else absurd (hretDef sl fun h => absurd h hn) hne⟩

def isSpecialManagedKey (k : String) : Bool :=
  k == "value" || k == "checked" || k.startsWith "data-qed-on-" || k.startsWith "data-qed-onv-" || k == "data-qed-signal"
def Attr.DomClean : Attr msg → Bool
  | .attr k _ => k == "value" || !isSpecialManagedKey k | .flag k _ => k == "checked" || !isSpecialManagedKey k | .signalAttr .. | .signalOn .. => false | _ => true
def Html.DomClean : Html msg → Bool
  | .text _ => true
  | .element _ attrs cs => !ownsChildren attrs && attrs.all Attr.DomClean && cs.attach.all fun ⟨c, _⟩ => c.DomClean
termination_by h => sizeOf h
decreasing_by have := List.sizeOf_lt_of_mem ‹_›; simp only [Html.element.sizeOf_spec]; omega
abbrev Html.DomCleanList (cs : List (Html msg)) : Bool := cs.all Html.DomClean
@[simp] theorem Html.DomClean_text (s : String) : (Html.text (msg := msg) s).DomClean = true := by rw [Html.DomClean]
@[simp] theorem Html.DomClean_element (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) :
    (Html.element tag attrs cs).DomClean = (!ownsChildren attrs && attrs.all Attr.DomClean && Html.DomCleanList cs) := by
  rw [Html.DomClean]; dsimp only [Html.DomCleanList]; congr 1
  exact Bool.eq_iff_iff.2 (by simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall])
def ElemClean (st : SpecElemState msg) (prev : List String) : Prop :=
  ElemManaged st prev ∧ ∀ k, isSpecialManagedKey k = true → lookupAssoc k st.attrs = none

private theorem mem_dedupAttrs : ∀ {xs : List (Attr msg)} {x : Attr msg}, x ∈ dedupAttrs xs → x ∈ xs
  | [], _, hx => nomatch hx
  | a :: _, _, hx => by
      simp only [dedupAttrs] at hx; cases hk : a.key? <;> simp only [hk] at hx
      · exact List.mem_cons.2 ((List.mem_cons.1 hx).imp id mem_dedupAttrs)
      · split at hx; · exact .tail _ (mem_dedupAttrs hx)
        · exact List.mem_cons.2 ((List.mem_cons.1 hx).imp id mem_dedupAttrs)

theorem mem_normalizeAttrs_DomClean {attrs : List (Attr msg)} (hc : attrs.all Attr.DomClean = true) : ∀ x ∈ normalizeAttrs attrs, x.DomClean = true := by
  rw [List.all_eq_true] at hc; intro x hx; simp only [normalizeAttrs, List.mem_append] at hx
  rcases hx with hm | hd
  · split at hm; · nomatch hm
    · cases List.mem_singleton.1 hm; rfl
  · exact hc x (List.mem_filter.1 (mem_dedupAttrs hd)).1

private theorem startsWith_append_self (p e : String) : (p ++ e).startsWith p = true := by simp
private theorem append_ne_of_not_startsWith {p e s : String} (h : s.startsWith p = false) : p ++ e ≠ s :=
  fun heq => by rw [← heq, startsWith_append_self] at h; cases h
private theorem on_ne_onv {e₁ e₂ : String} : "data-qed-on-" ++ e₁ ≠ "data-qed-onv-" ++ e₂ := fun heq => by
  have h := congrArg (fun s => (s.toList.drop 11).head?) heq
  rw [String.toList_append, String.toList_append,
    show "data-qed-on-".toList = ['d','a','t','a','-','q','e','d','-','o','n','-'] from rfl,
    show "data-qed-onv-".toList = ['d','a','t','a','-','q','e','d','-','o','n','v','-'] from rfl] at h; cases h

private theorem isSpecial_on (e : String) : isSpecialManagedKey ("data-qed-on-" ++ e) = true := by
  simp only [isSpecialManagedKey, startsWith_append_self, Bool.or_true, Bool.true_or]
private theorem isSpecial_onv (e : String) : isSpecialManagedKey ("data-qed-onv-" ++ e) = true := by
  simp only [isSpecialManagedKey, startsWith_append_self, Bool.or_true, Bool.true_or]

private theorem slot_of_managedName {sl : AttrSlot} (hns : ∀ k, sl = .attr k → isSpecialManagedKey k = false) {s : String} (heq : s = sl.managedName) :
    (s = "value" → sl = .val) ∧ (s = "checked" → sl = .chk) ∧
    (∀ e, s = "data-qed-on-" ++ e → sl = .click e) ∧ (∀ e, s = "data-qed-onv-" ++ e → sl = .input e) ∧
    (s ≠ "data-qed-signal") ∧ (isSpecialManagedKey s = false → sl = .attr s) := by
  have hne : ∀ {p e t : String}, t.startsWith p = false → t ≠ p ++ e := fun h eq => append_ne_of_not_startsWith h eq.symm
  cases sl with
  | attr k =>
      have hk := hns k rfl; subst heq
      exact ⟨fun e => (by rw [e] at hk; cases hk), fun e => (by rw [e] at hk; cases hk),
        fun e eq => (by rw [eq, isSpecial_on] at hk; cases hk), fun e eq => (by rw [eq, isSpecial_onv] at hk; cases hk),
        fun eq => (by rw [eq] at hk; simp only [isSpecialManagedKey, beq_self_eq_true, Bool.or_true] at hk; cases hk), fun _ => rfl⟩
  | val => subst heq; dsimp only [AttrSlot.managedName]
           exact ⟨fun _ => rfl, fun e => absurd e (by decide), fun _ e => absurd e (hne (by simp)), fun _ e => absurd e (hne (by simp)), by decide, fun h => by cases h⟩
  | chk => subst heq; dsimp only [AttrSlot.managedName]
           exact ⟨fun e => absurd e (by decide), fun _ => rfl, fun _ e => absurd e (hne (by simp)), fun _ e => absurd e (hne (by simp)), by decide, fun h => by cases h⟩
  | click e' =>
      subst heq; dsimp only [AttrSlot.managedName, toString]
      exact ⟨fun e => absurd e (append_ne_of_not_startsWith (by simp)), fun e => absurd e (append_ne_of_not_startsWith (by simp)),
        fun _ e => congrArg AttrSlot.click (string_append_left_cancel e), fun _ e => absurd e on_ne_onv,
        append_ne_of_not_startsWith (by simp), fun h => by rw [isSpecial_on] at h; cases h⟩
  | input e' =>
      subst heq; dsimp only [AttrSlot.managedName, toString]
      exact ⟨fun e => absurd e (append_ne_of_not_startsWith (by simp)), fun e => absurd e (append_ne_of_not_startsWith (by simp)),
        fun _ e => absurd e.symm on_ne_onv, fun _ e => congrArg AttrSlot.input (string_append_left_cancel e),
        append_ne_of_not_startsWith (by simp), fun h => by rw [isSpecial_onv] at h; cases h⟩

private theorem managedAttrName_clean_slot {x : Attr msg} {sl : AttrSlot}
    (hxc : x.DomClean = true) (hname : managedAttrName x = some sl.managedName) :
    (x.slotUpdate? sl).isSome = true ∨ (∃ k, sl = .attr k ∧ isSpecialManagedKey k = true) := by
  by_cases hsp : ∃ k, sl = .attr k ∧ isSpecialManagedKey k = true; · exact .inr hsp
  left
  have hS := fun {s} (heq : s = sl.managedName) => slot_of_managedName (fun k hk => Bool.eq_false_iff.2 fun h => hsp ⟨k, hk, h⟩) heq
  cases x with
  | key _ => cases hname
  | signalAttr _ _ _ | signalOn _ _ _ => cases hxc
  | cls _ | localCell _ _ _ _ _ => cases (hS (Option.some.inj hname)).2.2.2.2.2 (by simp [isSpecialManagedKey]); rfl
  | attr k' _ =>
      by_cases hv : k' = "value"
      · subst hv; cases (hS (Option.some.inj hname)).1 rfl; rfl
      · cases (hS (Option.some.inj hname)).2.2.2.2.2 (by simpa only [Attr.DomClean, beq_eq_false_iff_ne.2 hv, Bool.false_or, Bool.not_eq_true'] using hxc)
        simp only [Attr.slotUpdate?, bne_iff_ne.2 hv, beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.isSome_some]
  | flag k' _ =>
      by_cases hc : k' = "checked"
      · subst hc; cases (hS (Option.some.inj hname)).2.1 rfl; rfl
      · cases (hS (Option.some.inj hname)).2.2.2.2.2 (by simpa only [Attr.DomClean, beq_eq_false_iff_ne.2 hc, Bool.false_or, Bool.not_eq_true'] using hxc)
        simp only [Attr.slotUpdate?, bne_iff_ne.2 hc, beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.isSome_some]
  | on ev _ => cases (hS (Option.some.inj hname)).2.2.1 ev rfl; simp only [Attr.slotUpdate?, beq_self_eq_true, ↓reduceIte, Option.isSome_some]
  | onValue ev _ => cases (hS (Option.some.inj hname)).2.2.2.1 ev rfl; simp only [Attr.slotUpdate?, beq_self_eq_true, ↓reduceIte, Option.isSome_some]
  | signalBind _ => exact absurd rfl (hS (Option.some.inj hname)).2.2.2.2.1

theorem AttrsNoShadow_of_clean {newAttrs : List (Attr msg)} {st : SpecElemState msg} {prev : List String}
    (hst : ElemClean st prev) (hc : newAttrs.all Attr.DomClean = true) : AttrsNoShadow newAttrs st := fun sl hmem => by
  rcases List.mem_filterMap.1 (List.contains_iff_mem.1 hmem) with ⟨x, hxMem, hxName⟩
  exact (managedAttrName_clean_slot (mem_normalizeAttrs_DomClean hc x hxMem) hxName).imp (⟨x, hxMem, ·⟩) (fun ⟨k, hEq, hsp⟩ => hEq ▸ congrArg SlotVal.optStr (hst.2 k hsp))

theorem stepSpecAttr_preserves_clean (s : SpecElemState msg) (a : Attr msg)
    (hca : a.DomClean = true) (hcs : ∀ k, isSpecialManagedKey k = true → lookupAssoc k s.attrs = none) :
    ∀ k, isSpecialManagedKey k = true → lookupAssoc k (stepSpecAttr s a).attrs = none := fun k hk => by
  have hnone : a.slotUpdate? (.attr k) = none := by
    cases a with
    | cls _ | localCell _ _ _ _ _ =>
        dsimp only [Attr.slotUpdate?]; split
        · rename_i h; rw [← beq_iff_eq.1 h] at hk; simp [isSpecialManagedKey] at hk
        · rfl
    | attr _ _ =>
        dsimp only [Attr.slotUpdate?]; split
        · rename_i h; rcases Bool.and_eq_true_iff.1 h with ⟨hne, heq⟩; cases beq_iff_eq.1 heq
          simp only [Attr.DomClean, beq_eq_false_iff_ne.2 (bne_iff_ne.1 hne), hk, Bool.false_or, Bool.not_true] at hca; cases hca
        · rfl
    | flag _ _ =>
        dsimp only [Attr.slotUpdate?]; split
        · rename_i h; rcases Bool.and_eq_true_iff.1 h with ⟨hne, heq⟩; cases beq_iff_eq.1 heq
          simp only [Attr.DomClean, beq_eq_false_iff_ne.2 (bne_iff_ne.1 hne), hk, Bool.false_or, Bool.not_true] at hca; cases hca
        · rfl
    | _ => rfl
  have hr := read_stepSpecAttr s a (.attr k); rw [hnone] at hr; exact (SlotVal.optStr.inj hr).trans (hcs k hk)

theorem ElemClean_foldl {xs : List (Attr msg)} {st : SpecElemState msg}
    (hcxs : ∀ x ∈ xs, x.DomClean = true) (hcst : ∀ k, isSpecialManagedKey k = true → lookupAssoc k st.attrs = none) :
    ∀ k, isSpecialManagedKey k = true → lookupAssoc k (xs.foldl stepSpecAttr st).attrs = none := by
  induction xs generalizing st with
  | nil => exact hcst
  | cons x _ ih => exact ih (fun y hy => hcxs y (.tail _ hy)) (stepSpecAttr_preserves_clean st x (hcxs x (.head _)) hcst)

theorem ElemClean_evalSpecAttrs {attrs : List (Attr msg)} (hc : attrs.all Attr.DomClean = true) :
    ElemClean (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) :=
  ⟨ElemManaged_foldl_norm attrs {} ElemManaged_empty, ElemClean_foldl (mem_normalizeAttrs_DomClean hc) (fun _ _ => rfl)⟩

theorem ElemClean_applyAttrsM (a : DomArena msg) (node : Dom.Node) (ns tag : String)
    (st : SpecElemState msg) (prev : List String) (cs : List Dom.Node) (newAttrs : List (Attr msg))
    (hst : ElemClean st prev) (hc : newAttrs.all Attr.DomClean = true) :
    let norm := normalizeAttrs newAttrs; let names := norm.filterMap managedAttrName
    let a' := (applyAttrsM (m := ArenaM msg) node newAttrs (a.set node (.element ns tag st prev cs))).2
    ∃ st', a'.get node = .element ns tag st' names cs ∧ ElemStateEquiv st' (evalSpecAttrs newAttrs) ∧ ElemClean st' names := by
  rcases applyAttrsM_existing_element a node ns tag st prev cs newAttrs hst.1 (AttrsNoShadow_of_clean hst hc) with ⟨st', hget, heqv, hm'⟩
  exact ⟨st', hget, heqv, hm', fun k hk => (SlotVal.optStr.inj (heqv (.attr k))).trans ((ElemClean_evalSpecAttrs hc).2 k hk)⟩

/-! ## Bounded Subtree Framing -/

section
variable {a a' : DomArena msg}
def SubtreeInSet : Nat → DomArena msg → (Nat → Prop) → Dom.Node → Prop
  | 0, _, _, _ => True
  | f + 1, a, S, n => S n.toNat ∧ match a.get n with | .element _ _ _ _ cs => ∀ c ∈ cs, SubtreeInSet f a S c | _ => True
abbrev SubtreeInRange (fuel : Nat) (a : DomArena msg) (lo hi : Nat) (n : Dom.Node) : Prop := SubtreeInSet fuel a (fun k => lo ≤ k ∧ k < hi) n
theorem SubtreeInRange_to_SubtreeInSet {f lo hi : Nat} {n : Dom.Node} (h : SubtreeInRange f a lo hi n) : SubtreeInSet f a (fun k => lo ≤ k ∧ k < hi) n := h
theorem SubtreeInSet_mono {S₁ S₂ : Nat → Prop} (hsub : ∀ k, S₁ k → S₂ k) : ∀ {f : Nat} {n : Dom.Node}, SubtreeInSet f a S₁ n → SubtreeInSet f a S₂ n
  | 0, _, _ => trivial
  | _ + 1, n, hn => by dsimp only [SubtreeInSet] at hn ⊢; refine ⟨hsub n.toNat hn.1, ?_⟩
                       cases hg : a.get n <;> first | trivial | (rw [hg] at hn; exact fun c hc => SubtreeInSet_mono hsub (hn.2 c hc))
theorem SubtreeInRange_mono {fuel lo₁ hi₁ lo₂ hi₂ : Nat} {n : Dom.Node} (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) (h : SubtreeInRange fuel a lo₁ hi₁ n) : SubtreeInRange fuel a lo₂ hi₂ n :=
  SubtreeInSet_mono (fun _ hk => ⟨Nat.le_trans hlo hk.1, Nat.lt_of_lt_of_le hk.2 hhi⟩) h
theorem SubtreeInSet_frame {S : Nat → Prop} (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) :
    ∀ {f : Nat} {n : Dom.Node}, SubtreeInSet f a S n → SubtreeInSet f a' S n ∧ readDomTree f a' n = readDomTree f a n
  | 0, _, _ => ⟨trivial, rfl⟩
  | _ + 1, n, hn => by
      have hget := hfr n hn.1; dsimp only [SubtreeInSet, readDomTree] at hn ⊢; rw [hget]
      cases hg : a.get n with
      | element _ _ _ _ _ => rw [hg] at hn; have hcs := fun c hc => SubtreeInSet_frame hfr (hn.2 c hc)
                             exact ⟨⟨hn.1, fun c hc => (hcs c hc).1⟩, congrArg (DomTree.element _ _ _) (List.map_congr_left fun c hc => (hcs c hc).2)⟩
      | _ => exact ⟨⟨hn.1, trivial⟩, rfl⟩
theorem SubtreeInRange_frame {fuel lo hi : Nat} {n : Dom.Node}
    (hagree : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) (hsub : SubtreeInRange fuel a lo hi n) :
    SubtreeInRange fuel a' lo hi n ∧ readDomTree fuel a' n = readDomTree fuel a n := SubtreeInSet_frame (fun m hm => hagree m hm.1 hm.2) hsub
end

theorem stateM_bind_step {σ α β : Type} {m : StateM σ α} {f : α → StateM σ β} {s s' : σ} {v : α}
    (h : m s = (v, s')) : (m >>= f) s = f v s' := by change f (m s).1 (m s).2 = _; rw [h]

/-! ## `ArenaExt` Framing & `CleanDomSubtree` / `CleanDomChildren` -/

theorem ArenaExt.of_set {a : DomArena msg} {n : Dom.Node} {e : ArenaEntry msg} {W : Nat → Prop} (hW : W n.toNat) : ArenaExt a (a.set n e) W 0 :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ hnW => DomArena.get_set_ne _ _ fun heq => hnW (heq ▸ hW)⟩
theorem ArenaExt.trans {a₁ a₂ a₃ : DomArena msg} {W₁ W₂ W : Nat → Prop} {b₁ b₂ b : Nat} (h1 : ArenaExt a₁ a₂ W₁ b₁) (h2 : ArenaExt a₂ a₃ W₂ b₂)
    (hW1 : ∀ k, W₁ k → W k) (hW2 : ∀ k, k < a₁.nextId → W₂ k → W k) (hb : b₁ + b₂ ≤ b) : ArenaExt a₁ a₃ W b :=
  ⟨Nat.le_trans h1.next_ge h2.next_ge, Nat.le_trans h2.next_le (by have := h1.next_le; omega),
   fun m hm hnW => (h2.frame m (Nat.lt_of_lt_of_le hm h1.next_ge) fun hw2 => hnW (hW2 _ hm hw2)).trans (h1.frame m hm fun hw1 => hnW (hW1 _ hw1))⟩
theorem ArenaExt.sameDom {a₁ a₂ a₃ : DomArena msg} {W : Nat → Prop} {b : Nat} (h : ArenaExt a₁ a₂ W b) (hs : a₃.SameDom a₂) : ArenaExt a₁ a₃ W b :=
  ⟨hs.1 ▸ h.next_ge, hs.1 ▸ h.next_le, fun m hm hnW => (hs.get_eq m).trans (h.frame m hm hnW)⟩

def DisjointDomList {α : Type} (P : α → (Nat → Prop) → Dom.Node → Prop) : List α → (Nat → Prop) → List Dom.Node → Prop
  | [], _, [] => True
  | c :: cs, S, d :: ds => ∃ Sc Srest, (∀ k, Sc k → S k) ∧ (∀ k, Srest k → S k) ∧ (∀ k, Sc k → Srest k → False) ∧ P c Sc d ∧ DisjointDomList P cs Srest ds
  | _, _, _ => False
theorem DisjointDomList.singleton {α : Type} {P : α → (Nat → Prop) → Dom.Node → Prop} {c : α} {S : Nat → Prop} {d : Dom.Node} (h : P c S d) : DisjointDomList P [c] S [d] :=
  ⟨S, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, h, trivial⟩
private theorem DisjointDomList.imp {α : Type} {P Q : α → (Nat → Prop) → Dom.Node → Prop} :
    ∀ {cs : List α} {S : Nat → Prop} {ds : List Dom.Node},
      (∀ c Sc d, (∀ k, Sc k → S k) → P c Sc d → Q c Sc d) → DisjointDomList P cs S ds → DisjointDomList Q cs S ds
  | [], _, [], _, _ => trivial
  | _ :: _, _, _ :: _, h, ⟨Sc, Sr, hSc, hSr, hD, hH, hT⟩ => ⟨Sc, Sr, hSc, hSr, hD, h _ _ _ hSc hH, DisjointDomList.imp (fun c S' d hS' => h c S' d fun k hk => hSr k (hS' k hk)) hT⟩
  | [], _, _ :: _, _, hc | _ :: _, _, [], _, hc => hc.elim

def CleanDomSubtree : Nat → String → Html msg → DomArena msg → (Nat → Prop) → Dom.Node → Prop
  | 0, _, _, _, _, _ => False
  | _ + 1, _, .text s, a, S, n => S n.toNat ∧ a.get n = .text s
  | f + 1, ns, .element tag attrs cs, a, S, n =>
      let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
      S n.toNat ∧ ownsChildren attrs = false ∧ attrs.all Attr.DomClean = true ∧
      ∃ st mg domCs, a.get n = .element realNs tag st mg domCs ∧ ElemClean st mg ∧ ElemStateEquiv st (evalSpecAttrs attrs) ∧
        (∀ nm ∈ (normalizeAttrs attrs).filterMap managedAttrName, mg.contains nm = true) ∧
        DisjointDomList (CleanDomSubtree f (Dom.childNsOf ns tag) · a) cs (fun k => S k ∧ k ≠ n.toNat) domCs
abbrev CleanDomChildren (f : Nat) (ns : String) (cs : List (Html msg)) (a : DomArena msg) (S : Nat → Prop) (ds : List Dom.Node) : Prop :=
  DisjointDomList (CleanDomSubtree f ns · a) cs S ds

section
variable {f : Nat} {ns : String} {a a' : DomArena msg}
theorem CleanDomSubtree_root_mem : ∀ {f : Nat} {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node}, CleanDomSubtree f ns h a S n → S n.toNat
  | 0, _, _, _, _, h => h.elim | _ + 1, _, .text _, _, _, h | _ + 1, _, .element .., _, _, h => h.1
theorem CleanDomChildren_mem : ∀ {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node}, CleanDomChildren f ns cs a S ds → ∀ d ∈ ds, S d.toNat
  | [], _, [], _ => fun _ h => nomatch h
  | _ :: _, _, _ :: _, ⟨_, _, hSc, hSr, _, hH, hT⟩ => fun d hd => (List.mem_cons.1 hd).elim (· ▸ hSc _ (CleanDomSubtree_root_mem hH)) (fun hr => hSr _ (CleanDomChildren_mem hT d hr))
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim
theorem CleanDomChildren_nodup : ∀ {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node}, CleanDomChildren f ns cs a S ds → ds.Nodup ∧ ds.length = cs.length
  | [], _, [], _ => ⟨.nil, rfl⟩
  | _ :: _, _, _ :: _, ⟨_, _, _, _, hD, hH, hT⟩ => have ⟨hnd, hlen⟩ := CleanDomChildren_nodup hT
      ⟨List.nodup_cons.2 ⟨fun hm => hD _ (CleanDomSubtree_root_mem hH) (CleanDomChildren_mem hT _ hm), hnd⟩, congrArg Nat.succ hlen⟩
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim
theorem CleanDomChildren_mono {cs : List (Html msg)} {S S' : Nat → Prop} {ds : List Dom.Node} (hsub : ∀ k, S k → S' k) :
    CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a S' ds := match cs, ds with
  | [], [] => id | [], _ :: _ | _ :: _, [] => False.elim
  | _ :: _, _ :: _ => fun ⟨Sc, Sr, hSc, hSr, hD, hH, hT⟩ => ⟨Sc, Sr, fun k h => hsub k (hSc k h), fun k h => hsub k (hSr k h), hD, hH, hT⟩
theorem CleanDomSubtree_mono : ∀ {f : Nat} {ns : String} {h : Html msg} {S S' : Nat → Prop} {n : Dom.Node}, (∀ k, S k → S' k) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a S' n
  | 0, _, _, _, _, _, _, h => h.elim | _ + 1, _, .text _, _, _, _, hsub, ⟨hn, hg⟩ => ⟨hsub _ hn, hg⟩
  | _ + 1, _, .element .., _, _, _, hsub, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ => ⟨hsub _ hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, CleanDomChildren_mono (fun _ hk => ⟨hsub _ hk.1, hk.2⟩) hcs⟩
theorem CleanDomSubtree_frame : ∀ {f : Nat} {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
    (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n
  | 0, _, _, _, _, _, h => h.elim | _ + 1, _, .text _, _, n, hfr, ⟨hn, hg⟩ => ⟨hn, (hfr n hn).trans hg⟩
  | _ + 1, _, .element .., _, n, hfr, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
      ⟨hn, ho, ha, st, mg, domCs, (hfr n hn).trans hg, hcl, heq, hmg, DisjointDomList.imp (fun _ _ _ hS => CleanDomSubtree_frame fun m hm => hfr m (hS _ hm).1) hcs⟩
theorem CleanDomChildren_frame {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node} (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) (h : CleanDomChildren f ns cs a S ds) : CleanDomChildren f ns cs a' S ds :=
  DisjointDomList.imp (fun _ _ _ hS => CleanDomSubtree_frame fun m hm => hfr m (hS _ hm)) h
private theorem DisjointDomList.to_equiv (hSub : ∀ {h : Html msg} {S : Nat → Prop} {n : Dom.Node}, CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)) :
    ∀ {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node}, CleanDomChildren f ns cs a S ds → DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs)
  | [], _, [], _ => .nil | _ :: _, _, _ :: _, ⟨_, _, _, _, _, hH, hT⟩ => .cons (hSub hH) (DisjointDomList.to_equiv hSub hT) | [], _, _ :: _, h | _ :: _, _, [], h => h.elim
theorem CleanDomSubtree_equiv : ∀ {f : Nat} {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node}, CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, .text _, _, _, ⟨_, hg⟩ => by dsimp only [readDomTree, specDom]; rw [hg]; exact .text _
  | _ + 1, _, .element .., _, _, ⟨_, ho, _, _, _, _, hg, _, heq, _, hcs⟩ => by dsimp only [readDomTree, specDom]; rw [hg, ho]; exact .element heq (DisjointDomList.to_equiv CleanDomSubtree_equiv hcs)
theorem CleanDomChildren_append : ∀ {xs₁ xs₂ : List (Html msg)} {S₁ S₂ : Nat → Prop} {ds₁ ds₂ : List Dom.Node},
    (∀ k, S₁ k → S₂ k → False) → CleanDomChildren f ns xs₁ a S₁ ds₁ → CleanDomChildren f ns xs₂ a S₂ ds₂ → CleanDomChildren f ns (xs₁ ++ xs₂) a (fun k => S₁ k ∨ S₂ k) (ds₁ ++ ds₂)
  | [], _, _, _, [], _, _, _, h2 => CleanDomChildren_mono (fun _ => .inr) h2
  | _ :: _, _, _, S₂, _ :: _, _, hD, ⟨Sc, Sr, hSc, hSr, hDS, hH, hT⟩, h2 =>
      ⟨Sc, fun k => Sr k ∨ S₂ k, fun k h => .inl (hSc k h), fun k h => h.elim (fun h => .inl (hSr k h)) .inr,
       fun k h1 h2 => h2.elim (hDS k h1) (hD k (hSc k h1)), hH, CleanDomChildren_append (fun k h1 => hD k (hSr k h1)) hT h2⟩
  | [], _, _, _, _ :: _, _, _, h, _ | _ :: _, _, _, _, [], _, _, h, _ => h.elim
theorem CleanDomChildren_indexed : ∀ {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node}, CleanDomChildren f ns cs a S ds →
    ∃ (Si : Nat → Nat → Prop), (∀ i k, Si i k → S k) ∧ (∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False) ∧ (∀ (i : Nat) (h1 : i < cs.length) (h2 : i < ds.length), CleanDomSubtree f ns cs[i] a (Si i) ds[i])
  | [], _, [], _ => ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => nomatch h⟩
  | _ :: _, _, _ :: _, ⟨Sc, Sr, hSc, hSr, hD, hH, hT⟩ => let ⟨SiTail, hSub, hPair, hGet⟩ := CleanDomChildren_indexed hT
      ⟨fun | 0 => Sc | i + 1 => SiTail i, fun | 0, k, hk => hSc k hk | i + 1, k, hk => hSr k (hSub i k hk),
       fun | 0, 0, h, _, _, _ => absurd rfl h | 0, _ + 1, _, k, h1, h2 => hD k h1 (hSub _ k h2) | _ + 1, 0, _, k, h1, h2 => hD k h2 (hSub _ k h1) | _ + 1, _ + 1, h, k, h1, h2 => hPair _ _ (by omega) k h1 h2,
       fun | 0, _, _ => hH | i + 1, h1, h2 => hGet i (by simpa using h1) (by simpa using h2)⟩
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim
theorem CleanDomSubtree_not_fragment : ∀ {f : Nat} {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node}, CleanDomSubtree f ns h a S n → ∀ fcs, a.get n ≠ .fragment fcs
  | 0, _, _, _, _, h, _, _ => h.elim | _ + 1, _, .text _, _, _, ⟨_, hg⟩, _, hf | _ + 1, _, .element .., _, _, ⟨_, _, _, _, _, _, hg, _⟩, _, hf => by rw [hg] at hf; cases hf
end

/-! ## `buildDomM` & Utility Theorems -/

theorem uint32_toNat_ofNat_lt (n : Nat) (h : n < UInt32.size) : (UInt32.ofNat n).toNat = n := by simp [Nat.mod_eq_of_lt h]
theorem uint32_eq_of_toNat_eq {a b : UInt32} (h : a.toNat = b.toNat) : a = b := UInt32.toBitVec_inj.1 (BitVec.eq_of_toNat_eq h)
theorem node_ne_of_toNat_ne {a b : Dom.Node} (h : a.toNat ≠ b.toNat) : a ≠ b := fun heq => h (congrArg UInt32.toNat heq)
theorem uint32_ofNat_succ (n : Nat) (h : n + 1 < UInt32.size) : UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) :=
  uint32_eq_of_toNat_eq (by simp [UInt32.toNat_add, uint32_toNat_ofNat_lt n (by omega)])
theorem getD_append_right {α : Type} (x d : α) : ∀ (pre suf : List α), (pre ++ x :: suf).getD pre.length d = x
  | [], _ => rfl | _ :: rest, suf => getD_append_right x d rest suf
def removeTailSpec (idx : Nat) : Nat → List α → List α
  | 0, cs => cs | k + 1, cs => removeTailSpec idx k (listRemoveAt cs idx)
theorem listRemoveAt_append_head {α : Type} : ∀ (pre : List α) (x : α) (suf : List α), listRemoveAt (pre ++ x :: suf) pre.length = pre ++ suf
  | [], _, _ => rfl | _ :: prest, x, suf => by simp [listRemoveAt, listRemoveAt_append_head prest x suf]
theorem removeTailSpec_append {α : Type} (pre : List α) : ∀ (suf : List α), removeTailSpec pre.length suf.length (pre ++ suf) = pre
  | [] => by simp [removeTailSpec] | x :: suf => by simp [removeTailSpec, listRemoveAt_append_head pre x suf, removeTailSpec_append pre suf]

theorem removeTailM_spec (a : DomArena msg) (node : Dom.Node) (atIdx : Nat) (k : Nat)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node) :
    ((removeTailM (m := ArenaM msg) node (UInt32.ofNat atIdx) k).run (a.set node (.element ns tag st mg cs))).2 =
      a.set node (.element ns tag st mg (removeTailSpec (UInt32.ofNat atIdx).toNat k cs)) := by
  induction k generalizing cs with
  | zero => rfl
  | succ _ ih => simp only [removeTailM, removeTailSpec, bind, StateT.bind, StateT.run, MonadDom.removeChild, DomArena.modifyChildren, DomArena.modify, DomArena.get_set_self, DomArena.set_set]; exact ih _

private abbrev IsParMk (mkPar : List Dom.Node → ArenaEntry msg) : Prop :=
  (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)

theorem buildDomListM_step (childNs : String) (parent : Dom.Node) (c : Html msg) (rest : List (Html msg)) (aIn aMid : DomArena msg) (cn : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg) (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)) (acc : List Dom.Node)
    (hbuild : buildDomM (m := ArenaM msg) childNs c aIn = (cn, aMid)) (hparMid : aMid.get parent = mkPar acc)
    (hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs) (hcnNotInAcc : cn ∉ acc) :
    ((buildDomListM (m := ArenaM msg) childNs parent (c :: rest)).run aIn).2 =
      ((buildDomListM (m := ArenaM msg) childNs parent rest).run (aMid.set parent (mkPar (acc ++ [cn])))).2 := by
  have happend : MonadDom.appendChild (m := ArenaM msg) parent cn aMid = ((), aMid.set parent (mkPar (acc ++ [cn]))) := by
    cases hgetCn : aMid.get cn with
    | fragment fcs => exact False.elim (hcnNotFrag fcs hgetCn)
    | _ => rcases hmk with ⟨_, _, _, _, hm⟩ | hm <;> simp [MonadDom.appendChild, hgetCn, DomArena.modify, hparMid, hm, List.erase_of_not_mem hcnNotInAcc]
  dsimp only [buildDomListM, StateT.run]; rw [stateM_bind_step hbuild, stateM_bind_step happend]

private abbrev BuildDomPost (ns : String) (h : Html msg) (a : DomArena msg) (f : Nat) : Prop :=
  let (root, a') := (buildDomM (m := ArenaM msg) ns h).run a
  a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ ArenaExt a a' (fun _ => False) (htmlNodeCount h) ∧
  SubtreeInRange f a' a.nextId a'.nextId root ∧ readDomTree f a' root = specDom ns h ∧
  (h.DomClean = true → CleanDomSubtree f ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root)

private abbrev BuildDomListPost (childNs : String) (cs : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg) (acc : List Dom.Node) (f : Nat) : Prop :=
  let aIn := aBase.set parent (mkPar acc); let aOut := ((buildDomListM (m := ArenaM msg) childNs parent cs).run aIn).2
  ∃ (csNew : List Dom.Node) (aBase' : DomArena msg), aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
    ArenaExt aBase aOut (fun k => k = parent.toNat) (htmlListNodeCount cs) ∧
    (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
    ((∀ c ∈ acc, SubtreeInRange f aIn (parent.toNat + 1) aBase.nextId c) →
      (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧ (acc ++ csNew).map (readDomTree f aOut) = acc.map (readDomTree f aIn) ++ specDomList childNs cs) ∧
    (∀ (hsAcc : List (Html msg)) (Sacc : Nat → Prop), Html.DomCleanList cs = true → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
      CleanDomChildren f childNs hsAcc aIn Sacc acc → CleanDomChildren f childNs (hsAcc ++ cs) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew))

private theorem SubtreeInRange_frame_set_ne {f lo hi : Nat} {a : DomArena msg} {p n : Dom.Node} {e : ArenaEntry msg} (hp : p.toNat < lo) (h : SubtreeInRange f a lo hi n) :
    SubtreeInRange f (a.set p e) lo hi n ∧ readDomTree f (a.set p e) n = readDomTree f a n :=
  SubtreeInRange_frame (fun _ hlo _ => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hp hlo)))) h

private theorem ArenaExt_alloc {a : DomArena msg} {e : ArenaEntry msg} {b : Nat} (hb : 1 ≤ b) (hlt : a.nextId < UInt32.size) : ArenaExt a (a.alloc e).2 (fun _ => False) b :=
  ⟨Nat.le_succ _, Nat.add_le_add_left hb a.nextId, fun _ hm _ =>
    DomArena.get_set_ne (a := { a with nextId := a.nextId + 1 }) e (node_ne_of_toNat_ne (Nat.ne_of_lt ((uint32_toNat_ofNat_lt a.nextId hlt).symm ▸ hm)))⟩

private theorem buildDomListM_spec_full_of (f : Nat)
    (hBuild : ∀ (ns : String) (h : Html msg) (a : DomArena msg), 0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ f → BuildDomPost ns h a f)
    (childNs : String) (cs : List (Html msg)) :
    ∀ (aBase : DomArena msg) (parent : Dom.Node) (mkPar : List Dom.Node → ArenaEntry msg), IsParMk mkPar →
      ∀ (acc : List Dom.Node), parent.toNat < aBase.nextId → 0 < aBase.nextId →
      aBase.nextId + htmlListNodeCount cs < UInt32.size → htmlListDepth cs ≤ f → (∀ c ∈ acc, c.toNat < aBase.nextId) →
      BuildDomListPost childNs cs aBase parent mkPar acc f := by
  induction cs with
  | nil => intro aBase parent mkPar _ acc _ _ _ _ _
           exact ⟨[], aBase, by simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil],
             ArenaExt.of_set (n := parent) (e := mkPar acc) rfl, fun _ _ hne => (DomArena.get_set_ne _ _ hne).symm,
             fun h => ⟨by simpa only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil, DomArena.nextId_set] using h, by simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil, specDomList]⟩,
             fun _ _ _ _ h => by simpa only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil] using CleanDomChildren_mono (fun _ => .inl) h⟩
  | cons c rest ih =>
      intro aBase parent mkPar hmk acc hparLt hpos hbound hdep haccLt
      let aIn := aBase.set parent (mkPar acc); have haInNext : aIn.nextId = aBase.nextId := rfl
      simp only [htmlListNodeCount] at hbound; simp only [htmlListDepth] at hdep
      have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
      have hfPos : 0 < f := by cases c with | text _ => exact hcDep | element _ _ _ => exact Nat.lt_of_lt_of_le (Nat.add_pos_left (Nat.succ_pos 0) _) hcDep
      have hcSpec := hBuild childNs c aIn hpos (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound) hcDep
      dsimp only [BuildDomPost, StateT.run] at hcSpec
      cases hR : buildDomM (m := ArenaM msg) childNs c aIn with
      | mk cn aMid =>
          rw [hR] at hcSpec; rcases hcSpec with ⟨hcnGe, hcnLt, haMidExt, hcnSub, hcnRead, hcnCleanFn⟩
          have haMidGe := haMidExt.next_ge; have haMidLe := haMidExt.next_le
          have haMidFrame : ∀ m : Dom.Node, m.toNat < aBase.nextId → aMid.get m = aIn.get m := fun m hm => haMidExt.frame m hm id
          rw [haInNext] at hcnGe haMidGe haMidLe hcnSub hcnCleanFn
          have hparInMid : aMid.get parent = mkPar acc := (haMidFrame parent hparLt).trans (DomArena.get_set_self ..)
          have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := fun fcs hfrag => by
            cases f with | zero => cases hfPos | succ _ => cases c with
              | text _ => cases hR; dsimp only [DomArena.get, DomArena.alloc] at hfrag; simp only [beq_self_eq_true, ↓reduceIte] at hfrag; cases hfrag
              | element _ _ _ => dsimp only [readDomTree] at hcnRead; rw [hfrag] at hcnRead; cases hcnRead
          let aAfter := aMid.set parent (mkPar (acc ++ [cn]))
          have hfrAfter : ∀ m : Dom.Node, parent.toNat < m.toNat → m.toNat < aBase.nextId → aAfter.get m = aIn.get m :=
            fun m hlo hhi => (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (Nat.ne_of_gt hlo))).trans (haMidFrame m hhi)
          rcases ih aMid parent mkPar hmk (acc ++ [cn]) (Nat.lt_of_lt_of_le hparLt haMidGe) (Nat.lt_of_lt_of_le hpos haMidGe)
            (Nat.lt_of_le_of_lt (Nat.add_le_add_right haMidLe _) (Nat.add_assoc _ _ _ ▸ hbound)) (Nat.le_trans (Nat.le_max_right _ _) hdep)
            (fun x hx => (List.mem_append.1 hx).elim (fun h1 => Nat.lt_of_lt_of_le (haccLt x h1) haMidGe) (fun h2 => (List.mem_singleton.1 h2) ▸ hcnLt)) with
            ⟨csRest, aBase'', haOutEq, haOutExt, hframeRest, hsubRestFn, hcleanRestFn⟩
          dsimp only [BuildDomListPost]; simp only [htmlListNodeCount]
          rw [buildDomListM_step childNs parent c rest aIn aMid cn mkPar hmk acc hR hparInMid hcnNotFrag (fun hm => Nat.not_lt_of_ge hcnGe (haccLt cn hm))]
          rw [List.append_assoc, List.singleton_append] at haOutEq hsubRestFn hcleanRestFn
          refine ⟨cn :: csRest, aBase'', haOutEq,
            ((ArenaExt.of_set (n := parent) (e := mkPar acc) (W := (· = parent.toNat)) rfl).trans haMidExt
              (fun _ h => h) (fun _ _ h => h.elim) (Nat.zero_add _ ▸ Nat.le_refl _)).trans haOutExt (fun _ h => h) (fun _ _ h => h) (Nat.le_refl _),
            fun m hm hne => by rw [hframeRest m (Nat.lt_of_lt_of_le hm haMidGe) hne, DomArena.get_set_ne _ _ hne]; exact haMidFrame m hm,
            fun haccSub => ?_, fun hsAcc Sacc hclean hSacc haccClean => ?_⟩
          · have haccMid := fun x hx => SubtreeInRange_frame (fun m hlo hhi => hfrAfter m (Nat.lt_of_succ_le hlo) hhi) (haccSub x hx)
            have hcnAfter := SubtreeInRange_frame_set_ne (p := parent) (e := mkPar (acc ++ [cn])) (Nat.lt_succ_self _) (SubtreeInRange_mono hparLt (Nat.le_refl _) hcnSub)
            have ⟨hsubFinal, hreadFinal⟩ := hsubRestFn fun x hx =>
              (List.mem_append.1 hx).elim (fun h1 => SubtreeInRange_mono (Nat.le_refl _) haMidGe (haccMid x h1).1) (fun h2 => (List.mem_singleton.1 h2) ▸ hcnAfter.1)
            have hmapInit : (acc ++ [cn]).map (readDomTree f aAfter) = acc.map (readDomTree f aIn) ++ [specDom childNs c] := by
              rw [List.map_append, List.map_singleton, hcnAfter.2.trans hcnRead, List.map_congr_left fun x hx => (haccMid x hx).2]
            rw [hmapInit, List.append_assoc, List.singleton_append] at hreadFinal; exact ⟨hsubFinal, hreadFinal⟩
          · simp only [Html.DomCleanList, List.all_cons, Bool.and_eq_true] at hclean
            let Sc : Nat → Prop := fun k => aBase.nextId ≤ k ∧ k < aMid.nextId
            have hcombClean : CleanDomChildren f childNs (hsAcc ++ [c]) aAfter (fun k => Sacc k ∨ Sc k) (acc ++ [cn]) :=
              CleanDomChildren_append (fun k hk1 hk2 => Nat.not_lt_of_ge hk2.1 (hSacc k hk1).2)
                (CleanDomChildren_frame (fun m hm => have hb := hSacc _ hm; hfrAfter m hb.1 hb.2) haccClean)
                (DisjointDomList.singleton (CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hparLt hm.1)))) (hcnCleanFn hclean.1)))
            have hcleanFinal := hcleanRestFn (hsAcc ++ [c]) (fun k => Sacc k ∨ Sc k) hclean.2
              (fun k hk => hk.elim (fun h => let b := hSacc k h; ⟨b.1, Nat.lt_of_lt_of_le b.2 haMidGe⟩) (fun h => ⟨Nat.lt_of_lt_of_le hparLt h.1, h.2⟩)) hcombClean
            simp only [List.append_assoc, List.singleton_append] at hcleanFinal
            exact CleanDomChildren_mono (fun k hk => hk.elim (fun h => h.elim .inl fun hSc => .inr ⟨hSc.1, Nat.lt_of_lt_of_le hSc.2 haOutExt.next_ge⟩)
              fun hRest => .inr ⟨Nat.le_trans haMidGe hRest.1, hRest.2⟩) hcleanFinal

theorem buildDomM_spec_full (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat) :
    0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ fuel →
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ ArenaExt a a' (fun _ => False) (htmlNodeCount h) ∧
    SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns h ∧
    (h.DomClean = true → CleanDomSubtree fuel ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root) := by
  induction fuel generalizing ns h a with
  | zero => intro _ _ hdep; cases h with | text _ => cases hdep | element _ _ _ => exact absurd hdep (Nat.not_le_of_lt (Nat.add_pos_left (Nat.succ_pos 0) _))
  | succ f ih =>
      intro hpos hbound hdep
      cases h with
      | text s =>
          simp only [htmlNodeCount] at hbound ⊢
          have hltSz : a.nextId < UInt32.size := Nat.lt_trans (Nat.lt_succ_self _) hbound
          have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt _ hltSz
          dsimp only [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run, SubtreeInRange, SubtreeInSet]
          have hget : ({ a with nextId := a.nextId + 1, store := fun m => if m == UInt32.ofNat a.nextId then .text s else a.store m } : DomArena msg).get (UInt32.ofNat a.nextId) = .text s := by
            simp only [DomArena.get, beq_self_eq_true, ↓reduceIte]
          have hlo : a.nextId ≤ (UInt32.ofNat a.nextId).toNat := htoNat.symm ▸ Nat.le_refl _
          have hhi : (UInt32.ofNat a.nextId).toNat < a.nextId + 1 := htoNat.symm ▸ Nat.lt_succ_self _
          exact ⟨hlo, hhi, ArenaExt_alloc (Nat.le_refl _) hltSz, ⟨⟨hlo, hhi⟩, by rw [hget]; trivial⟩,
            by dsimp only [readDomTree, specDom]; rw [hget], fun _ => ⟨⟨hlo, hhi⟩, hget⟩⟩
      | element tag attrs children =>
          simp only [htmlNodeCount] at hbound ⊢; simp only [htmlDepth] at hdep
          have hltSz : a.nextId < UInt32.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right 1 _) _) hbound))
          let node := UInt32.ofNat a.nextId; have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt _ hltSz
          have hlo : a.nextId ≤ node.toNat := hnodeNat.symm ▸ Nat.le_refl _
          have hhi : node.toNat < a.nextId + 1 := hnodeNat.symm ▸ Nat.lt_succ_self _
          let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
          let st := evalSpecAttrs attrs; let mg := (normalizeAttrs attrs).filterMap managedAttrName
          let a1 : DomArena msg := { a with nextId := a.nextId + 1 }; let aElem := a1.set node (.element realNs tag st mg [])
          have hrun : (buildDomM (m := ArenaM msg) ns (.element tag attrs children)).run a =
              if !ownsChildren attrs then (node, ((buildDomListM (m := ArenaM msg) (Dom.childNsOf ns tag) node children).run aElem).2) else (node, aElem) := by
            dsimp only [buildDomM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
            rw [show a.alloc (.element realNs tag {} [] []) = (node, a1.set node (.element realNs tag {} [] [])) from rfl]
            dsimp only; rw [applyAttrsM_fresh_element a1 node realNs tag [] attrs]; cases ownsChildren attrs <;> rfl
          rw [hrun]; by_cases hown : ownsChildren attrs
          · simp only [hown, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hlo, hhi, ArenaExt_alloc (e := .element realNs tag st mg []) (Nat.le_add_right 1 _) hltSz,
              ⟨⟨hlo, hhi⟩, by dsimp only [aElem]; rw [DomArena.get_set_self]; exact fun _ h => nomatch h⟩,
              by dsimp only [readDomTree, aElem, specDom]; rw [DomArena.get_set_self, ite_eq_left hown]; rfl, fun hcl => by simp only [Html.DomClean_element, hown, Bool.not_true, Bool.false_and] at hcl; cases hcl⟩
          · have hownF : ownsChildren attrs = false := Bool.eq_false_iff.2 hown
            simp only [hownF, Bool.not_false, ↓reduceIte]
            rcases buildDomListM_spec_full_of f (fun ns' h' a' => ih ns' h' a') (Dom.childNsOf ns tag) children a1 node
              (ArenaEntry.element realNs tag st mg) (.inl ⟨realNs, tag, st, mg, fun _ => rfl⟩) []
              hhi (Nat.succ_pos _) (Nat.add_assoc a.nextId 1 _ ▸ hbound) (Nat.le_of_add_le_add_left (a := 1) (Nat.add_comm f 1 ▸ hdep)) (fun _ h => nomatch h) with
              ⟨csNew, aBase', ha'Eq, haOutExt, _, hsubKidsFn, hcleanKidsFn⟩
            have ⟨hsubKids, hreadKids⟩ := hsubKidsFn (fun _ h => nomatch h); dsimp only [aElem]
            have hnextGe : a.nextId + 1 ≤ _ := haOutExt.next_ge; have hnextLe : _ ≤ a.nextId + (1 + htmlListNodeCount children) := Nat.add_assoc a.nextId 1 _ ▸ haOutExt.next_le
            have hnodeLtOut : node.toNat < _ := Nat.lt_of_lt_of_le hhi hnextGe
            refine ⟨hlo, hnodeLtOut,
              ⟨Nat.le_trans (Nat.le_succ _) hnextGe, hnextLe, fun m hm _ => haOutExt.frame m (Nat.lt_succ_of_lt hm) (fun h => Nat.ne_of_lt hm (h.trans hnodeNat))⟩,
              ⟨⟨hlo, hnodeLtOut⟩, by rw [ha'Eq, DomArena.get_set_self]; exact fun c hc => SubtreeInRange_mono (hnodeNat.symm ▸ Nat.le_succ _) (Nat.le_refl _) (ha'Eq ▸ hsubKids c hc)⟩,
              by rw [ha'Eq] at hreadKids ⊢; simp only [List.nil_append, List.map_nil, readDomTree, specDom, DomArena.get_set_self, hownF, Bool.false_eq_true, ↓reduceIte] at hreadKids ⊢
                 exact congrArg (DomTree.element realNs tag st) hreadKids,
              fun hcl => by
                simp only [Html.DomClean_element, hownF, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hcl
                have hcleanOut := hcleanKidsFn [] (fun _ => False) hcl.2 (fun _ h => h.elim) trivial; rw [List.nil_append, List.nil_append] at hcleanOut
                exact ⟨⟨hlo, hnodeLtOut⟩, hownF, hcl.1, st, mg, csNew, by rw [ha'Eq, DomArena.get_set_self, List.nil_append],
                  ElemClean_evalSpecAttrs hcl.1, ElemStateEquiv.refl st, fun _ => List.contains_iff_mem.2,
                  CleanDomChildren_mono (fun k hk => hk.elim False.elim fun h => ⟨⟨Nat.le_trans (Nat.le_succ _) h.1, h.2⟩, Nat.ne_of_gt (hnodeNat.symm ▸ Nat.lt_of_succ_le h.1)⟩) hcleanOut⟩⟩

theorem buildDomM_spec (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat)
    (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount h < UInt32.size) (hdep : htmlDepth h ≤ fuel) :
    let (root, a') := (buildDomM (m := ArenaM msg) ns h).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount h ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧ SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns h :=
  have ⟨h1, h2, hext, hsub, hread, _⟩ := buildDomM_spec_full ns h a fuel hpos hbound hdep
  ⟨h1, h2, hext.next_le, fun m hm => hext.frame m hm id, hsub, hread⟩

theorem buildDomListM_spec_full (childNs : String) (cs : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg) (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)) (acc : List Dom.Node) (f : Nat)
    (hparLt : parent.toNat < aBase.nextId) (hpos : 0 < aBase.nextId) (hbound : aBase.nextId + htmlListNodeCount cs < UInt32.size)
    (hdep : htmlListDepth cs ≤ f) (haccLt : ∀ c ∈ acc, c.toNat < aBase.nextId) : BuildDomListPost childNs cs aBase parent mkPar acc f :=
  buildDomListM_spec_full_of f (fun ns' h' a' => buildDomM_spec_full ns' h' a' f) childNs cs aBase parent mkPar hmk acc hparLt hpos hbound hdep haccLt

def DomArena.withMeta (a : DomArena msg) (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg)) : DomArena msg := { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }
def DomArena.MetaIndep {α : Type} (op : ArenaM msg α) : Prop :=
  ∀ sigs evs tmpls rowEvs (a : DomArena msg), op (a.withMeta sigs evs tmpls rowEvs) = ((op a).1, (op a).2.withMeta sigs evs tmpls rowEvs)
theorem DomArena.MetaIndep.pure {α : Type} (x : α) : DomArena.MetaIndep (msg := msg) (Pure.pure x) := fun _ _ _ _ _ => rfl
theorem DomArena.MetaIndep.bind {α β : Type} {op : ArenaM msg α} {f : α → ArenaM msg β} (h1 : DomArena.MetaIndep op) (h2 : ∀ x, DomArena.MetaIndep (f x)) : DomArena.MetaIndep (op >>= f) :=
  fun sigs evs tmpls rowEvs a => by change (let (x, s) := op (a.withMeta sigs evs tmpls rowEvs); f x s) = _; rw [h1 sigs evs tmpls rowEvs a]; exact h2 (op a).1 sigs evs tmpls rowEvs (op a).2
theorem DomArena.MetaIndep.sameDom {α : Type} {op : ArenaM msg α} (h : DomArena.MetaIndep op) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) : (op a₁).2.SameDom (op a₂).2 := by
  rw [show a₁ = a₂.withMeta a₁.signals a₁.sigEvents a₁.tmpls a₁.rowEvs from DomArena.ext hs.1 hs.2 rfl rfl rfl rfl, h]; exact ⟨rfl, rfl⟩
theorem DomArena.MetaIndep.appendChild (parent child : Dom.Node) : DomArena.MetaIndep (MonadDom.appendChild (m := ArenaM msg) parent child) := fun _ _ _ _ a => by
  simp only [MonadDom.appendChild, DomArena.get, DomArena.set, DomArena.modifyChildren, DomArena.modify, DomArena.withMeta]; cases a.store child <;> rfl
theorem applyAttrsM_metaIndep (node : Dom.Node) (attrs : List (Attr msg)) : DomArena.MetaIndep (applyAttrsM (m := ArenaM msg) node attrs) :=
  let rec go : ∀ (xs : List (Attr msg)), DomArena.MetaIndep (applyAttrListM (m := ArenaM msg) node xs)
    | [] => .pure () | _ :: rest => .bind (fun _ _ _ _ _ => by rw [applyAttrM_eq_modifyElemState, applyAttrM_eq_modifyElemState]; rfl) fun _ => go rest
  .bind (fun _ _ _ _ _ => rfl) fun _ => go (normalizeAttrs attrs)
mutual
  theorem buildDomM_metaIndep (ns : String) : (h : Html msg) → DomArena.MetaIndep (buildDomM (m := ArenaM msg) ns h)
    | .text _ => fun _ _ _ _ _ => rfl
    | .element tag attrs children => by
        dsimp only [buildDomM]; refine .bind (fun _ _ _ _ _ => rfl) fun el => .bind (applyAttrsM_metaIndep el attrs) fun _ => ?_
        cases ownsChildren attrs; · exact .bind (buildDomListM_metaIndep (Dom.childNsOf ns tag) el children) fun _ => .pure el
        · exact .pure el
  theorem buildDomListM_metaIndep (ns : String) (parent : Dom.Node) : (cs : List (Html msg)) → DomArena.MetaIndep (buildDomListM (m := ArenaM msg) ns parent cs)
    | [] => .pure () | c :: rest => .bind (buildDomM_metaIndep ns c) fun cn => .bind (.appendChild parent cn) fun _ => buildDomListM_metaIndep ns parent rest
end

theorem seedRowsM_run_eq (inst : String) (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg)) (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg) :
    let d := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
    (seedRowsM (m := ArenaM msg) inst rowSig rowEv newMarks oldMarks oldSigs).run a =
      (d.1, { a with signals := d.2.1.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals
                     sigEvents := d.2.2.toList.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents }) := by
  dsimp only [seedRowsM, StateT.run]; rcases diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[] with ⟨_, toEmit, toEv⟩; dsimp only
  rw [stateM_bind_step (show emitSignalsM (m := ArenaM msg) toEmit.toList a = _ from emitSignalsM_spec toEmit.toList a),
      stateM_bind_step (show emitSignalOnsM (m := ArenaM msg) toEv.toList _ = _ from emitSignalOnsM_spec toEv.toList _)]; rfl
theorem seedRowsM_sameDom (inst : String) (rowSig : Nat → Array (String × String)) (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg) :
    ((seedRowsM (m := ArenaM msg) inst rowSig rowEv newMarks oldMarks oldSigs).run a).2.SameDom a := by rw [seedRowsM_run_eq]; exact ⟨rfl, rfl⟩
theorem buildDomListM_sameDom (ns : String) (parent : Dom.Node) (cs : List (Html msg)) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (buildDomListM (m := ArenaM msg) ns parent cs a₁).2.SameDom (buildDomListM (m := ArenaM msg) ns parent cs a₂).2 := (buildDomListM_metaIndep ns parent cs).sameDom hs

end Qed
