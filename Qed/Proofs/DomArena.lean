import Qed.Driver.Template
import Qed.Runtime.AppCore
import Qed.Ssr

namespace Qed

/-!
# DomArena Refinement, Attribute Retention & Signal-Store Resolution

Core imperative DOM model on `DomArena`:
- Observational `SpecElemState` / `DomTree` semantics (`specDom`) and `MonadDom` over `StateM (DomArena msg)`
- Attribute retention & non-shadowing cleanup (`applyAttrsM_existing_element`, `Attr.DomClean`, `ElemClean`)
- Association-equivalence (`DomTreeAssocEquiv`) and bounded subtree framing (`SubtreeInSet` / `SubtreeInRange`)
- `buildDomM_spec` / `buildDomListM_spec`, signal emission (`emitSignalsM_spec`), and signal resolution (`readResolvedDomTree`)
-/

structure SpecElemState (msg : Type) where
  attrs   : List (String × String) := []
  value   : String := ""
  checked : Bool := false
  clicks  : List (String × msg) := []
  inputs  : List (String × (String → msg)) := []
  sigBind   : Option String := none
  sigAttr   : List (String × String) := []
  sigClicks : List (String × String) := []

def setAssoc {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: setAssoc k v rest

def eraseAssoc {α : Type} (k : String) : List (String × α) → List (String × α)
  | [] => []
  | (k', v') :: rest => if k' == k then eraseAssoc k rest else (k', v') :: eraseAssoc k rest

def lookupAssoc {α : Type} (k : String) : List (String × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' == k then some v else lookupAssoc k rest

theorem lookupAssoc_mem {α : Type} {k : String} {v : α} :
    ∀ {xs : List (String × α)}, lookupAssoc k xs = some v → (k, v) ∈ xs
  | [], h => by simp [lookupAssoc] at h
  | (a, b) :: rest, h => by
      simp only [lookupAssoc] at h
      split at h
      · rename_i heq
        have : a = k := eq_of_beq heq
        subst this; cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lookupAssoc_mem h)

theorem lookupAssoc_setAssoc {α : Type} (k k' : String) (v : α) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (setAssoc k' v xs) = if k' == k then some v else lookupAssoc k xs
  | [] => by simp [setAssoc, lookupAssoc]
  | (a, b) :: rest => by
      simp only [setAssoc]
      by_cases ha : a == k'
      · have : a = k' := eq_of_beq ha
        subst this
        simp only [ha, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k <;> simp [hk]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k
        · have : a = k := eq_of_beq hk
          subst this
          have hne : (k' == a) = false := beq_eq_false_iff_ne.2 fun h => ha (beq_iff_eq.2 h.symm)
          simp [hne]
        · simp only [hk, Bool.false_eq_true, ↓reduceIte]
          exact lookupAssoc_setAssoc k k' v rest

theorem lookupAssoc_filter {α : Type} (p : String → Bool) (k : String) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (xs.filter fun (k', _) => p k') = if p k then lookupAssoc k xs else none
  | [] => by simp [lookupAssoc]
  | (a, b) :: rest => by
      simp only [List.filter_cons]
      by_cases hpa : p a
      · simp only [hpa, ↓reduceIte, lookupAssoc]
        by_cases hak : a == k
        · have : a = k := eq_of_beq hak; subst this; simp [hpa]
        · simp [hak, lookupAssoc_filter p k rest]
      · simp only [hpa, Bool.false_eq_true, ↓reduceIte]
        rw [lookupAssoc_filter p k rest]
        by_cases hpk : p k
        · have hak : (a == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [hpk] at hpa
          simp [hpk, hak, lookupAssoc]
        · simp [hpk]

theorem lookupAssoc_eraseAssoc {α : Type} (k k' : String) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (eraseAssoc k' xs) = if k' == k then none else lookupAssoc k xs
  | [] => by simp [eraseAssoc, lookupAssoc]
  | (a, b) :: rest => by
      simp only [eraseAssoc]
      by_cases ha : a == k'
      · have : a = k' := eq_of_beq ha; subst this
        simp only [ha, ↓reduceIte, lookupAssoc_eraseAssoc k a rest]
        by_cases hk : a == k <;> simp [lookupAssoc, hk]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k
        · have : a = k := eq_of_beq hk; subst this
          have hne : (k' == a) = false := beq_eq_false_iff_ne.2 fun h => ha (beq_iff_eq.2 h.symm)
          simp [hne]
        · simp [hk, lookupAssoc_eraseAssoc k k' rest]

theorem string_append_left_cancel {p a b : String} (h : p ++ a = p ++ b) : a = b :=
  String.ext (by have := congrArg String.toList h; simp_all)

def stepSpecAttr (st : SpecElemState msg) : Attr msg → SpecElemState msg
  | .cls c                    => { st with attrs := setAssoc "class" c st.attrs }
  | .attr "value" v           => { st with value := v }
  | .attr k v                 => { st with attrs := setAssoc k v st.attrs }
  | .flag "checked" present   => { st with checked := present }
  | .flag k present           =>
      { st with attrs := if present then setAssoc k k st.attrs else eraseAssoc k st.attrs }
  | .key _                    => st
  | .on event evMsg           => { st with clicks := setAssoc event evMsg st.clicks }
  | .onValue event f          => { st with inputs := setAssoc event f st.inputs }
  | .localCell key comp _ _ _ => { st with attrs := setAssoc "data-qed-local" (localKey comp key) st.attrs }
  | .signalBind name          => { st with sigBind := some name }
  | .signalAttr name attr _   => { st with sigAttr := setAssoc attr name st.sigAttr }
  | .signalOn name event _    => { st with sigClicks := setAssoc event name st.sigClicks }

def evalSpecAttrs (attrs : List (Attr msg)) : SpecElemState msg :=
  (normalizeAttrs attrs).foldl stepSpecAttr {}

inductive DomTree (msg : Type) where
  | text (s : String)
  | element (ns : String) (tag : String) (state : SpecElemState msg) (children : List (DomTree msg))

mutual
  def specDom (ns : String) : Html msg → DomTree msg
    | .text s => .text s
    | .element tag attrs children =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        let kids := if ownsChildren attrs then [] else specDomList (Dom.childNsOf ns tag) children
        .element realNs tag (evalSpecAttrs attrs) kids

  def specDomList (ns : String) : List (Html msg) → List (DomTree msg)
    | []      => []
    | c :: cs => specDom ns c :: specDomList ns cs
end

@[simp] theorem specDomList_eq_map (ns : String) :
    ∀ (cs : List (Html msg)), specDomList ns cs = cs.map (specDom ns)
  | []      => rfl
  | c :: cs => by simp [specDomList, specDomList_eq_map ns cs]

/-! ## Pure `DomArena` & `MonadDom` Instance -/

inductive ArenaEntry (msg : Type) where
  | null
  | text (s : String)
  | fragment (children : List Dom.Node)
  | element (ns : String) (tag : String) (state : SpecElemState msg)
      (managed : List String) (children : List Dom.Node)

def insertBeforeRef (child ref : Dom.Node) : List Dom.Node → List Dom.Node
  | [] => [child]
  | x :: xs => if x == ref then child :: x :: xs else x :: insertBeforeRef child ref xs

def w3cInsertBefore (children : List Dom.Node) (idx : Nat) (child : Dom.Node) : List Dom.Node :=
  match children.drop idx with
  | []       => (children.erase child) ++ [child]
  | ref :: _ => if ref == child then children else insertBeforeRef child ref (children.erase child)

def w3cInsertBeforeRef (children : List Dom.Node) (ref? : Option Dom.Node) (child : Dom.Node) : List Dom.Node :=
  match ref? with
  | none     => (children.erase child) ++ [child]
  | some ref => if ref == child then children else insertBeforeRef child ref (children.erase child)

def listRemoveAt {α : Type} : List α → Nat → List α
  | [], _          => []
  | _ :: xs, 0     => xs
  | x :: xs, i + 1 => x :: listRemoveAt xs i

def listReplaceAt {α : Type} : List α → Nat → α → List α
  | [], _, _          => []
  | _ :: xs, 0, v     => v :: xs
  | x :: xs, i + 1, v => x :: listReplaceAt xs i v

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

namespace DomArena

def get (a : DomArena msg) (n : Dom.Node) : ArenaEntry msg := a.store n

def set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) : DomArena msg :=
  { a with store := fun m => if m == n then e else a.store m }

def modify (a : DomArena msg) (n : Dom.Node) (f : ArenaEntry msg → ArenaEntry msg) : DomArena msg :=
  a.set n (f (a.get n))

def alloc (a : DomArena msg) (e : ArenaEntry msg) : Dom.Node × DomArena msg :=
  let h := UInt32.ofNat a.nextId
  (h, { a with nextId := a.nextId + 1, store := fun m => if m == h then e else a.store m })

@[simp] theorem get_set_self (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) :
    (a.set n e).get n = e := by simp [get, set]

@[simp] theorem get_set_ne (a : DomArena msg) {n m : Dom.Node} (e : ArenaEntry msg) (hne : m ≠ n) :
    (a.set n e).get m = a.get m := by simp [get, set, hne]

@[simp] theorem nextId_set (a : DomArena msg) (n : Dom.Node) (e : ArenaEntry msg) :
    (a.set n e).nextId = a.nextId := rfl

@[simp] theorem set_set (a : DomArena msg) (n : Dom.Node) (e₁ e₂ : ArenaEntry msg) :
    (a.set n e₁).set n e₂ = a.set n e₂ := by
  cases a; simp only [set, mk.injEq, true_and, and_true]
  funext m; by_cases hm : m == n <;> simp [hm]

theorem set_get_self (a : DomArena msg) {n : Dom.Node} {e : ArenaEntry msg}
    (h : a.get n = e) : a.set n e = a := by
  cases a; simp only [set, mk.injEq, true_and, and_true]
  funext m; by_cases hm : m = n
  · subst hm; simp [← h, get]
  · simp [hm]

@[reducible] def modifyElemState (a : DomArena msg) (n : Dom.Node)
    (f : SpecElemState msg → SpecElemState msg) : DomArena msg :=
  a.modify n fun | .element ns tag st mg cs => .element ns tag (f st) mg cs | other => other

@[reducible] def modifyChildren (a : DomArena msg) (p : Dom.Node)
    (f : List Dom.Node → List Dom.Node) : DomArena msg :=
  a.modify p fun | .element ns tag st mg cs => .element ns tag st mg (f cs) | .fragment cs => .fragment (f cs) | other => other

def SameDom {msg : Type} (a₁ a₂ : DomArena msg) : Prop :=
  a₁.nextId = a₂.nextId ∧ a₁.store = a₂.store

theorem SameDom.refl (a : DomArena msg) : a.SameDom a := ⟨rfl, rfl⟩
theorem SameDom.symm {a₁ a₂ : DomArena msg} (h : a₁.SameDom a₂) : a₂.SameDom a₁ := ⟨h.1.symm, h.2.symm⟩
theorem SameDom.trans {a₁ a₂ a₃ : DomArena msg} (h1 : a₁.SameDom a₂) (h2 : a₂.SameDom a₃) : a₁.SameDom a₃ :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
theorem SameDom.get_eq {a₁ a₂ : DomArena msg} (h : a₁.SameDom a₂) (m : Dom.Node) : a₁.get m = a₂.get m :=
  congrFun h.2 m

end DomArena

mutual
  def arenaBuildHtml (ns : String) : Html msg → DomArena msg → Dom.Node × DomArena msg
    | .text s, a => a.alloc (.text s)
    | .element tag attrs children, a =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        let st := evalSpecAttrs attrs
        let mg := (normalizeAttrs attrs).filterMap managedAttrName
        let (node, a1) := a.alloc (.element realNs tag st mg [])
        if ownsChildren attrs then
          (node, a1)
        else
          let (cs, a2) := arenaBuildHtmlList (Dom.childNsOf ns tag) children a1
          (node, a2.set node (.element realNs tag st mg cs))

  def arenaBuildHtmlList (ns : String) : List (Html msg) → DomArena msg → List Dom.Node × DomArena msg
    | [], a => ([], a)
    | c :: cs, a =>
        let (cn, a1) := arenaBuildHtml ns c a
        let (cns, a2) := arenaBuildHtmlList ns cs a1
        (cn :: cns, a2)
end

def patchNodeSlotAt (a : DomArena msg) (n : Dom.Node) (path : List Nat) (attrName val : String) : DomArena msg :=
  match path with
  | [] =>
      if attrName == "" then
        a.modify n fun | .text _ => .text val | other => other
      else if attrName == "value" then
        a.modifyElemState n fun st => { st with value := val }
      else
        a.modifyElemState n fun st => { st with attrs := setAssoc attrName val st.attrs }
  | idx :: rest =>
      match a.get n with
      | .element _ _ _ _ cs =>
          match cs[idx]? with
          | some child => patchNodeSlotAt a child rest attrName val
          | none => a
      | _ => a

def patchNodeSlotsLoop (slotPaths : Array (Array UInt32)) (slotAttrs newVals : Array String)
    (n : Dom.Node) (i : Nat) (a : DomArena msg) : DomArena msg :=
  if hi : i < slotPaths.size then
    let p := (slotPaths[i].toList).map UInt32.toNat
    let attr := slotAttrs.getD i ""
    let v := newVals.getD i ""
    patchNodeSlotsLoop slotPaths slotAttrs newVals n (i + 1) (patchNodeSlotAt a n p attr v)
  else a
termination_by slotPaths.size - i

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
          let clicks' := st.clicks.filter fun (e, _) =>
            !prev.contains s!"data-qed-on-{e}" || names.contains s!"data-qed-on-{e}"
          let inputs' := st.inputs.filter fun (e, _) =>
            !prev.contains s!"data-qed-onv-{e}" || names.contains s!"data-qed-onv-{e}"
          .element ns tag { st with attrs := attrs', value := val', checked := chk', clicks := clicks', inputs := inputs' } names cs
      | other => other)
  clearHandlers n         := fun a => ((), a.modifyElemState n fun st => { st with clicks := [], inputs := [] })
  setValue n v            := fun a => ((), a.modifyElemState n fun st => { st with value := v })
  setChecked n on         := fun a => ((), a.modifyElemState n fun st => { st with checked := on })
  setText n s := fun a =>
    ((), a.modify n fun | .text _ => .text s | .element ns tag st mg _ => .element ns tag st mg [] | other => other)
  appendChild p c := fun a =>
    match a.get c with
    | .fragment fcs => ((), (a.set c .null).modifyChildren p fun cs => (cs.filter (!fcs.contains ·)) ++ fcs)
    | _ => ((), a.modifyChildren p fun cs => (cs.erase c) ++ [c])
  childAt p i := fun a =>
    (match a.get p with | .element _ _ _ _ cs | .fragment cs => cs.getD i.toNat 0 | _ => 0, a)
  childCount p := fun a =>
    (match a.get p with | .element _ _ _ _ cs | .fragment cs => UInt32.ofNat cs.length | _ => 0, a)
  removeChild p i          := fun a => ((), a.modifyChildren p fun cs => listRemoveAt cs i.toNat)
  replaceChild p i newChild := fun a => ((), a.modifyChildren p fun cs => listReplaceAt cs i.toNat newChild)
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
  mountLocalCell n key comp _ _ _ := fun a =>
    ((), a.modifyElemState n fun st => { st with attrs := setAssoc "data-qed-local" (localKey comp key) st.attrs })
  compileRowTmpl ns proto slotPaths slotAttrs evPaths evNames := fun a =>
    (UInt32.ofNat a.tmpls.size, { a with tmpls := a.tmpls.push ⟨ns, proto, slotPaths, slotAttrs, evPaths, evNames⟩ })
  allocRowEvSlot _ fn := fun a =>
    (UInt32.ofNat a.rowEvs.size, { a with rowEvs := a.rowEvs.push fn })
  setRowEvSlot slot fn := fun a =>
    ((), if h : slot.toNat < a.rowEvs.size then { a with rowEvs := a.rowEvs.set slot.toNat fn h } else a)
  mountTmplRow tmplId vals := fun a =>
    match a.tmpls[tmplId.toNat]? with
    | some t => arenaBuildHtml t.ns (applyRowSlots t.proto t.slotPaths t.slotAttrs vals) a
    | none => (0, a)
  mountTmplRows parent tmplId valsPerRow := fun a =>
    match a.tmpls[tmplId.toNat]? with
    | some t =>
        let (cs, a1) := arenaBuildHtmlList t.ns (valsPerRow.toList.map (applyRowSlots t.proto t.slotPaths t.slotAttrs)) a
        (cs.toArray, a1.modifyChildren parent (· ++ cs))
    | none => (#[], a)
  patchTmplRow node tmplId newVals _ := fun a =>
    match a.tmpls[tmplId.toNat]? with
    | some t => ((), patchNodeSlotsLoop t.slotPaths t.slotAttrs newVals node 0 a)
    | none => ((), a)
  hydrateTmplRow _ _ := fun a => ((), a)

def readDomTree : Nat → DomArena msg → Dom.Node → DomTree msg
  | 0, _, _ => .text ""
  | fuel + 1, a, n =>
      match a.get n with
      | .text s => .text s
      | .element ns tag st _ cs => .element ns tag st (cs.map (readDomTree fuel a))
      | _ => .text ""

theorem DomArena.SameDom.readDomTree_eq {a₁ a₂ : DomArena msg} (h : a₁.SameDom a₂) :
    ∀ f n, readDomTree f a₁ n = readDomTree f a₂ n
  | 0, _ => rfl
  | f + 1, n => by
      simp only [readDomTree, h.get_eq n]
      split <;> try rfl
      congr 1; exact List.map_congr_left fun c _ => h.readDomTree_eq f c

/-! ## Signal Store Resolution (`emitSignalsM` & `readResolvedDomTree`) -/

def applySignalAttr (st : SpecElemState msg) : String → String → SpecElemState msg
  | "value", v   => { st with value := v }
  | "checked", v => { st with checked := v != "" && v != "false" }
  | k, v         => { st with attrs := setAssoc k v st.attrs }

def resolveElemSignals (signals : List (String × String)) (sigEvents : List (String × msg))
    (st : SpecElemState msg) : SpecElemState msg :=
  let st1 := st.sigAttr.foldl (fun cur (k, sig) =>
    match lookupAssoc sig signals with
    | some v => applySignalAttr cur k v
    | none   => cur) st
  st1.sigClicks.foldl (fun cur (ev, sig) =>
    match lookupAssoc sig sigEvents with
    | some m => { cur with clicks := setAssoc ev m cur.clicks }
    | none   => cur) st1

def readResolvedDomTree : Nat → DomArena msg → Dom.Node → DomTree msg
  | 0, _, _ => .text ""
  | fuel + 1, a, n =>
      match a.get n with
      | .text s => .text s
      | .element ns tag st _ cs =>
          match st.sigBind with
          | some sig => .text ((lookupAssoc sig a.signals).getD "")
          | none     => .element ns tag (resolveElemSignals a.signals a.sigEvents st) (cs.map (readResolvedDomTree fuel a))
      | _ => .text ""

theorem emitSignalsM_spec (pairs : List (String × String)) (a : DomArena msg) :
    (emitSignalsM (m := StateM (DomArena msg)) pairs).run a =
      ((), { a with signals := pairs.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals }) := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p rest ih =>
      dsimp only [emitSignalsM, StateT.run, bind, StateT.bind, MonadDom.setSignal]
      simpa [List.foldl_cons] using ih { a with signals := setAssoc p.1 p.2 a.signals }

theorem emitSignalOnsM_spec (pairs : List (String × msg)) (a : DomArena msg) :
    (emitSignalOnsM (m := StateM (DomArena msg)) pairs).run a =
      ((), { a with sigEvents := pairs.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents }) := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p rest ih =>
      dsimp only [emitSignalOnsM, StateT.run, bind, StateT.bind, MonadDom.setSignalOn]
      simpa [List.foldl_cons] using ih { a with sigEvents := setAssoc p.1 p.2 a.sigEvents }

/-! ## Attribute Retention, Equivalence & Clean-DOM Invariant -/

theorem applyAttrM_eq_modifyElemState (node : Dom.Node) (attr : Attr msg) (a : DomArena msg) :
    applyAttrM (m := StateM (DomArena msg)) node attr a =
      ((), a.modifyElemState node (fun st => stepSpecAttr st attr)) := by
  cases attr with
  | attr k v =>
      by_cases hk : k = "value" <;>
        simp [applyAttrM, hk, MonadDom.setValue, MonadDom.setAttribute, stepSpecAttr]
  | flag k p =>
      by_cases hk : k = "checked"
      · subst hk; simp [applyAttrM, MonadDom.setChecked, stepSpecAttr]
      · cases p <;> simp [applyAttrM, MonadDom.setAttribute, MonadDom.removeAttribute, stepSpecAttr]
  | key _ =>
      dsimp only [applyAttrM, pure, StateT.pure, DomArena.modifyElemState, DomArena.modify, stepSpecAttr]
      cases hg : a.get node <;> exact congrArg ((), ·) (DomArena.set_get_self a hg).symm
  | cls _ => rfl
  | on _ _ => rfl
  | onValue _ _ => rfl
  | localCell _ _ _ _ _ => rfl
  | signalBind _ => rfl
  | signalAttr _ _ _ => rfl
  | signalOn _ _ _ => rfl

theorem applyAttrM_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node)
    (attr : Attr msg) :
    applyAttrM (m := StateM (DomArena msg)) node attr (a.set node (.element ns tag st mg cs)) =
      ((), a.set node (.element ns tag (stepSpecAttr st attr) mg cs)) := by
  rw [applyAttrM_eq_modifyElemState]
  simp [DomArena.modifyElemState, DomArena.modify]

theorem applyAttrListM_element :
    ∀ (attrs : List (Attr msg)) (a : DomArena msg) (node : Dom.Node) (ns tag : String)
      (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node),
      applyAttrListM (m := StateM (DomArena msg)) node attrs (a.set node (.element ns tag st mg cs)) =
        ((), a.set node (.element ns tag (attrs.foldl stepSpecAttr st) mg cs))
  | [], _, _, _, _, _, _, _ => rfl
  | attr :: rest, a, node, ns, tag, st, mg, cs => by
      dsimp only [applyAttrListM, bind, StateT.bind]
      rw [applyAttrM_element a node ns tag st mg cs attr]
      exact applyAttrListM_element rest a node ns tag (stepSpecAttr st attr) mg cs

theorem applyAttrsM_fresh_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) :
    applyAttrsM (m := StateM (DomArena msg)) node attrs (a.set node (.element ns tag {} [] cs)) =
      ((), a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs)) := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]
  exact applyAttrListM_element (normalizeAttrs attrs) a node ns tag {}
    ((normalizeAttrs attrs).filterMap managedAttrName) cs

private theorem applyAttrM_preserves (x : Attr msg) (node : Dom.Node) (s : DomArena msg) :
    let s' := (applyAttrM (m := StateM (DomArena msg)) node x).run s |>.2
    s'.nextId = s.nextId ∧ ∀ m, m ≠ node → s'.get m = s.get m := by
  dsimp only [StateT.run]; rw [applyAttrM_eq_modifyElemState]
  exact ⟨rfl, fun m hne => DomArena.get_set_ne _ _ hne⟩

private theorem applyAttrListM_preserves (l : List (Attr msg)) (node : Dom.Node) (s : DomArena msg) :
    let s' := (applyAttrListM (m := StateM (DomArena msg)) node l).run s |>.2
    s'.nextId = s.nextId ∧ ∀ m, m ≠ node → s'.get m = s.get m := by
  induction l generalizing s with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
      dsimp only [applyAttrListM, StateT.run, bind, StateT.bind]
      cases hx : applyAttrM (m := StateM (DomArena msg)) node x s with
      | mk _ s1 =>
          have h1 := applyAttrM_preserves x node s
          dsimp only [StateT.run] at h1; rw [hx] at h1
          have h2 := ih s1; dsimp only [StateT.run] at h2
          exact ⟨h2.1.trans h1.1, fun m hm => (h2.2 m hm).trans (h1.2 m hm)⟩

theorem applyAttrsM_nextId (a : DomArena msg) (node : Dom.Node)
    (attrs : List (Attr msg)) (e : ArenaEntry msg) :
    ((applyAttrsM (m := StateM (DomArena msg)) node attrs).run (a.set node e)).2.nextId = a.nextId := by
  dsimp only [applyAttrsM, StateT.run, bind, StateT.bind]
  exact (applyAttrListM_preserves (normalizeAttrs attrs) node _).1

theorem applyAttrsM_get_ne (a : DomArena msg) (node : Dom.Node)
    (attrs : List (Attr msg)) (e : ArenaEntry msg) (m : Dom.Node) (hne : m ≠ node) :
    ((applyAttrsM (m := StateM (DomArena msg)) node attrs).run (a.set node e)).2.get m = a.get m := by
  dsimp only [applyAttrsM, StateT.run, bind, StateT.bind, MonadDom.retainAttributes]
  exact ((applyAttrListM_preserves (normalizeAttrs attrs) node _).2 m hne).trans
    (by simp [DomArena.modify, DomArena.get_set_ne _ _ hne])

def ElemStateEquiv {msg : Type} (st₁ st₂ : SpecElemState msg) : Prop :=
  (∀ k, lookupAssoc k st₁.attrs = lookupAssoc k st₂.attrs) ∧
  st₁.value = st₂.value ∧ st₁.checked = st₂.checked ∧
  (∀ e, lookupAssoc e st₁.clicks = lookupAssoc e st₂.clicks) ∧
  (∀ e, lookupAssoc e st₁.inputs = lookupAssoc e st₂.inputs)

theorem ElemStateEquiv.refl (st : SpecElemState msg) : ElemStateEquiv st st :=
  ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem ElemStateEquiv.symm {st₁ st₂ : SpecElemState msg} (h : ElemStateEquiv st₁ st₂) : ElemStateEquiv st₂ st₁ :=
  ⟨fun k => (h.1 k).symm, h.2.1.symm, h.2.2.1.symm, fun e => (h.2.2.2.1 e).symm, fun e => (h.2.2.2.2 e).symm⟩

theorem ElemStateEquiv.trans {st₁ st₂ st₃ : SpecElemState msg}
    (h1 : ElemStateEquiv st₁ st₂) (h2 : ElemStateEquiv st₂ st₃) : ElemStateEquiv st₁ st₃ :=
  ⟨fun k => (h1.1 k).trans (h2.1 k), h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
   fun e => (h1.2.2.2.1 e).trans (h2.2.2.2.1 e), fun e => (h1.2.2.2.2 e).trans (h2.2.2.2.2 e)⟩

theorem ElemStateEquiv.dispatchInput {st₁ st₂ : SpecElemState msg}
    (h : ElemStateEquiv st₁ st₂) (e raw : String) :
    (lookupAssoc e st₁.inputs).map (· raw) = (lookupAssoc e st₂.inputs).map (· raw) := by
  rw [h.2.2.2.2 e]

def ElemManaged (st : SpecElemState msg) (prev : List String) : Prop :=
  (∀ kv ∈ st.attrs, prev.contains kv.1 = true) ∧
  (st.value ≠ "" → prev.contains "value" = true) ∧
  (st.checked = true → prev.contains "checked" = true) ∧
  (∀ kv ∈ st.clicks, prev.contains s!"data-qed-on-{kv.1}" = true) ∧
  (∀ kv ∈ st.inputs, prev.contains s!"data-qed-onv-{kv.1}" = true)

theorem ElemManaged_empty {names : List String} : ElemManaged ({} : SpecElemState msg) names :=
  ⟨fun _ h => by simp at h, fun h => by simp at h, fun h => by simp at h,
   fun _ h => by simp at h, fun _ h => by simp at h⟩

def attrWritesKey (k : String) : Attr msg → Bool
  | .cls _        => k == "class"
  | .attr k' _    => k' != "value" && k' == k
  | .flag k' _    => k' != "checked" && k' == k
  | .localCell .. => k == "data-qed-local"
  | _             => false

def AttrsNoShadow {msg : Type} (newAttrs : List (Attr msg)) (st : SpecElemState msg) : Prop :=
  (∀ k, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains k = true →
    (∃ x ∈ normalizeAttrs newAttrs, attrWritesKey k x = true) ∨ lookupAssoc k st.attrs = none) ∧
  (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "value" = true →
    (∃ v, .attr "value" v ∈ normalizeAttrs newAttrs) ∨ st.value = "") ∧
  (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "checked" = true →
    (∃ p, .flag "checked" p ∈ normalizeAttrs newAttrs) ∨ st.checked = false) ∧
  (∀ e, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains s!"data-qed-on-{e}" = true →
    (∃ m, .on e m ∈ normalizeAttrs newAttrs) ∨ lookupAssoc e st.clicks = none) ∧
  (∀ e, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains s!"data-qed-onv-{e}" = true →
    (∃ f, .onValue e f ∈ normalizeAttrs newAttrs) ∨ lookupAssoc e st.inputs = none)

private theorem setAssoc_prop {α : Type} {p : String → Bool} {k : String} {v : α} (hk : p k = true) :
    ∀ {xs : List (String × α)}, (∀ kv ∈ xs, p kv.1 = true) → ∀ kv ∈ setAssoc k v xs, p kv.1 = true
  | [], _, kv, h => by simp [setAssoc] at h; rcases h with ⟨rfl, rfl⟩; exact hk
  | x :: rest, hxs, kv, h => by
      simp only [setAssoc] at h
      split at h <;> rcases List.mem_cons.1 h with rfl | hr
      · exact hk
      · exact hxs kv (List.mem_cons_of_mem x hr)
      · exact hxs x (List.mem_cons_self ..)
      · exact setAssoc_prop hk (fun q hq => hxs q (List.mem_cons_of_mem x hq)) kv hr

private theorem eraseAssoc_prop {α : Type} {p : String → Bool} {k : String} :
    ∀ {xs : List (String × α)}, (∀ kv ∈ xs, p kv.1 = true) → ∀ kv ∈ eraseAssoc k xs, p kv.1 = true
  | [], _, _, h => by simp [eraseAssoc] at h
  | x :: rest, hxs, kv, h => by
      simp only [eraseAssoc] at h
      split at h
      · exact eraseAssoc_prop (fun q hq => hxs q (List.mem_cons_of_mem x hq)) kv h
      · rcases List.mem_cons.1 h with rfl | hr
        · exact hxs x (List.mem_cons_self ..)
        · exact eraseAssoc_prop (fun q hq => hxs q (List.mem_cons_of_mem x hq)) kv hr

theorem stepSpecAttr_retains_managed (st : SpecElemState msg) (a : Attr msg) (names : List String)
    (hkeep : match managedAttrName a with | some n => names.contains n = true | none => True)
    (hm : ElemManaged st names) : ElemManaged (stepSpecAttr st a) names := by
  rcases hm with ⟨ha, hv, hc, hcl, hin⟩
  cases a with
  | cls _ => exact ⟨setAssoc_prop hkeep ha, hv, hc, hcl, hin⟩
  | attr k v =>
      by_cases h : k = "value"
      · subst h; exact ⟨ha, fun _ => hkeep, hc, hcl, hin⟩
      · exact ⟨fun q hq => by simp [stepSpecAttr] at hq; exact setAssoc_prop hkeep ha q hq,
               fun hne => hv (by simpa [stepSpecAttr, h] using hne),
               fun hch => hc (by simpa [stepSpecAttr, h] using hch),
               fun q hq => by simp [stepSpecAttr] at hq; exact hcl q hq,
               fun q hq => by simp [stepSpecAttr] at hq; exact hin q hq⟩
  | flag k p =>
      by_cases h : k = "checked"
      · subst h; cases p <;> simp [stepSpecAttr]
        · exact ⟨ha, hv, fun b => absurd b Bool.false_ne_true, hcl, hin⟩
        · exact ⟨ha, hv, fun _ => hkeep, hcl, hin⟩
      · cases p
        · exact ⟨fun q hq => by simp [stepSpecAttr] at hq; exact eraseAssoc_prop ha q hq,
                 fun hne => hv (by simpa [stepSpecAttr, h] using hne),
                 fun hch => hc (by simpa [stepSpecAttr, h] using hch),
                 fun q hq => by simp [stepSpecAttr] at hq; exact hcl q hq,
                 fun q hq => by simp [stepSpecAttr] at hq; exact hin q hq⟩
        · exact ⟨fun q hq => by simp [stepSpecAttr] at hq; exact setAssoc_prop hkeep ha q hq,
                 fun hne => hv (by simpa [stepSpecAttr, h] using hne),
                 fun hch => hc (by simpa [stepSpecAttr, h] using hch),
                 fun q hq => by simp [stepSpecAttr] at hq; exact hcl q hq,
                 fun q hq => by simp [stepSpecAttr] at hq; exact hin q hq⟩
  | on _ _ => exact ⟨ha, hv, hc, setAssoc_prop (p := fun q => names.contains s!"data-qed-on-{q}") hkeep hcl, hin⟩
  | onValue _ _ => exact ⟨ha, hv, hc, hcl, setAssoc_prop (p := fun q => names.contains s!"data-qed-onv-{q}") hkeep hin⟩
  | localCell _ _ _ _ _ => exact ⟨setAssoc_prop hkeep ha, hv, hc, hcl, hin⟩
  | key _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => exact ⟨ha, hv, hc, hcl, hin⟩

private theorem foldl_stepSpecAttr_eqv {msg : Type} {β : Type} (proj : SpecElemState msg → β)
    (writes : Attr msg → Bool)
    (hpres : ∀ s₁ s₂ x, writes x = false → proj s₁ = proj s₂ → proj (stepSpecAttr s₁ x) = proj (stepSpecAttr s₂ x))
    (hset : ∀ s₁ s₂ x, writes x = true → proj (stepSpecAttr s₁ x) = proj (stepSpecAttr s₂ x)) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ a ∈ xs, writes a = true) ∨ proj s₁ = proj s₂) →
      proj (xs.foldl stepSpecAttr s₁) = proj (xs.foldl stepSpecAttr s₂)
  | [], _, _, .inl ⟨_, h, _⟩ => nomatch h
  | [], _, _, .inr h => h
  | x :: rest, s₁, s₂, h => by
      simp only [List.foldl_cons]
      apply foldl_stepSpecAttr_eqv proj writes hpres hset rest
      by_cases hxw : writes x = true
      · exact .inr (hset s₁ s₂ x hxw)
      · have hxwF : writes x = false := Bool.eq_false_iff.2 hxw
        rcases h with ⟨a, ha, hwa⟩ | heq
        · rcases List.mem_cons.1 ha with rfl | hmem
          · exact absurd hwa hxw
          · exact .inl ⟨a, hmem, hwa⟩
        · exact .inr (hpres s₁ s₂ x hxwF heq)

theorem foldl_stepSpecAttr_attrs (k : String) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ a ∈ xs, attrWritesKey k a = true) ∨ lookupAssoc k s₁.attrs = lookupAssoc k s₂.attrs) →
      lookupAssoc k (xs.foldl stepSpecAttr s₁).attrs = lookupAssoc k (xs.foldl stepSpecAttr s₂).attrs :=
  fun xs s₁ s₂ h => foldl_stepSpecAttr_eqv (fun s => lookupAssoc k s.attrs) (attrWritesKey k)
    (fun _ _ x hw hcur => by
      cases x with
      | cls _ | localCell _ _ _ _ _ => simp [attrWritesKey] at hw; simp [stepSpecAttr, lookupAssoc_setAssoc, hcur]
      | attr k' _ =>
          by_cases hv : k' = "value"
          · subst hv; exact hcur
          · have hne : (k' == k) = false := by simp [attrWritesKey, hv] at hw; exact beq_eq_false_iff_ne.2 (fun h => hw h)
            simp [stepSpecAttr, lookupAssoc_setAssoc, hne, hcur]
      | flag k' p =>
          by_cases hc : k' = "checked"
          · subst hc; exact hcur
          · have hne : (k' == k) = false := by simp [attrWritesKey, hc] at hw; exact beq_eq_false_iff_ne.2 (fun h => hw h)
            cases p <;> simp [stepSpecAttr, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, hne, hcur]
      | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => exact hcur)
    (fun _ _ x hxw => by
      cases x with
      | cls _ | localCell _ _ _ _ _ => simp [attrWritesKey] at hxw; subst hxw; simp [stepSpecAttr, lookupAssoc_setAssoc]
      | attr k' _ => simp only [attrWritesKey, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hxw; rcases hxw with ⟨_, rfl⟩; simp [stepSpecAttr, lookupAssoc_setAssoc]
      | flag k' p => simp only [attrWritesKey, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hxw; rcases hxw with ⟨_, rfl⟩; cases p <;> simp [stepSpecAttr, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc]
      | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => simp [attrWritesKey] at hxw)
    xs s₁ s₂ h

theorem foldl_stepSpecAttr_val :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      (s₁.value = s₂.value ∨ ∃ v, .attr "value" v ∈ xs) →
      (xs.foldl stepSpecAttr s₁).value = (xs.foldl stepSpecAttr s₂).value := fun xs s₁ s₂ h =>
  foldl_stepSpecAttr_eqv (·.value) (fun | .attr "value" _ => true | _ => false)
    (fun _ _ x hw heq => by cases x with
      | attr k' _ => by_cases hk : k' = "value" <;> simp [stepSpecAttr, hk, heq] at hw ⊢
      | flag k' _ => by_cases hk : k' = "checked" <;> simp [stepSpecAttr, hk, heq]
      | _ => exact heq)
    (fun _ _ x hw => by dsimp only at hw; split at hw <;> simp [stepSpecAttr] at hw ⊢)
    xs s₁ s₂ (by rcases h with heq | ⟨v, hv⟩; exact .inr heq; exact .inl ⟨.attr "value" v, hv, rfl⟩)

theorem foldl_stepSpecAttr_chk :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      (s₁.checked = s₂.checked ∨ ∃ p, .flag "checked" p ∈ xs) →
      (xs.foldl stepSpecAttr s₁).checked = (xs.foldl stepSpecAttr s₂).checked := fun xs s₁ s₂ h =>
  foldl_stepSpecAttr_eqv (·.checked) (fun | .flag "checked" _ => true | _ => false)
    (fun _ _ x hw heq => by cases x with
      | attr k' _ => by_cases hk : k' = "value" <;> simp [stepSpecAttr, hk, heq]
      | flag k' _ => by_cases hk : k' = "checked" <;> simp [stepSpecAttr, hk, heq] at hw ⊢
      | _ => exact heq)
    (fun _ _ x hw => by dsimp only at hw; split at hw <;> simp [stepSpecAttr] at hw ⊢)
    xs s₁ s₂ (by rcases h with heq | ⟨p, hp⟩; exact .inr heq; exact .inl ⟨.flag "checked" p, hp, rfl⟩)

theorem foldl_stepSpecAttr_clicks (e : String) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ m, .on e m ∈ xs) ∨ lookupAssoc e s₁.clicks = lookupAssoc e s₂.clicks) →
      lookupAssoc e (xs.foldl stepSpecAttr s₁).clicks = lookupAssoc e (xs.foldl stepSpecAttr s₂).clicks :=
  fun xs s₁ s₂ h => foldl_stepSpecAttr_eqv (fun s => lookupAssoc e s.clicks)
    (fun | .on e' _ => e' == e | _ => false)
    (fun _ _ x hw heq => by cases x with
      | on e' _ => simp [stepSpecAttr, lookupAssoc_setAssoc, hw, heq]
      | attr k' _ => by_cases hk : k' = "value" <;> simp [stepSpecAttr, hk, heq]
      | flag k' _ => by_cases hk : k' = "checked" <;> simp [stepSpecAttr, hk, heq]
      | _ => exact heq)
    (fun _ _ x hw => by cases x with
      | on _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, hw]
      | attr _ _ => simp at hw | flag _ _ => simp at hw | _ => simp at hw)
    xs s₁ s₂ (by rcases h with ⟨m, hm⟩ | heq; exact .inl ⟨.on e m, hm, beq_self_eq_true e⟩; exact .inr heq)

theorem foldl_stepSpecAttr_inputs (e : String) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ f, .onValue e f ∈ xs) ∨ lookupAssoc e s₁.inputs = lookupAssoc e s₂.inputs) →
      lookupAssoc e (xs.foldl stepSpecAttr s₁).inputs = lookupAssoc e (xs.foldl stepSpecAttr s₂).inputs :=
  fun xs s₁ s₂ h => foldl_stepSpecAttr_eqv (fun s => lookupAssoc e s.inputs)
    (fun | .onValue e' _ => e' == e | _ => false)
    (fun _ _ x hw heq => by cases x with
      | onValue e' _ => simp [stepSpecAttr, lookupAssoc_setAssoc, hw, heq]
      | attr k' _ => by_cases hk : k' = "value" <;> simp [stepSpecAttr, hk, heq]
      | flag k' _ => by_cases hk : k' = "checked" <;> simp [stepSpecAttr, hk, heq]
      | _ => exact heq)
    (fun _ _ x hw => by cases x with
      | onValue _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, hw]
      | attr _ _ => simp at hw | flag _ _ => simp at hw | _ => simp at hw)
    xs s₁ s₂ (by rcases h with ⟨f, hf⟩ | heq; exact .inl ⟨.onValue e f, hf, beq_self_eq_true e⟩; exact .inr heq)

private theorem filter_managed_prop {α : Type} {prev names : List String} {keyFn : String → String}
    {xs : List (String × α)} (hxs : ∀ kv ∈ xs, prev.contains (keyFn kv.1) = true) :
    ∀ kv ∈ (xs.filter fun (k, _) => !prev.contains (keyFn k) || names.contains (keyFn k)),
      names.contains (keyFn kv.1) = true := by
  intro ⟨k, v⟩ hkv
  simp only [List.mem_filter, Bool.or_eq_true, Bool.not_eq_true'] at hkv
  rcases hkv.2 with hp | hn
  · exact absurd ((hxs (k, v) hkv.1).symm.trans hp) (fun h => Bool.false_ne_true h.symm)
  · exact hn

private theorem filter_managed_lookup_none {α : Type} {prev names : List String} {keyFn : String → String}
    {xs : List (String × α)} (hxs : ∀ kv ∈ xs, prev.contains (keyFn kv.1) = true)
    (k : String) (hns : names.contains (keyFn k) = true → lookupAssoc k xs = none) :
    lookupAssoc k (xs.filter fun (k', _) => !prev.contains (keyFn k') || names.contains (keyFn k')) = none := by
  rw [lookupAssoc_filter (fun k' => !prev.contains (keyFn k') || names.contains (keyFn k'))]
  by_cases hp : prev.contains (keyFn k) = true
  · by_cases hn : names.contains (keyFn k) = true
    · simp only [hp, hn, Bool.not_true, Bool.false_or, ↓reduceIte]; exact hns hn
    · simp only [hp, Bool.not_true, Bool.false_or, Bool.eq_false_iff.2 hn, Bool.false_eq_true, ↓reduceIte]
  · cases hl : lookupAssoc k xs with
    | none => simp only [Bool.eq_false_iff.2 hp, Bool.not_false, Bool.true_or, ↓reduceIte]
    | some v => exact absurd (hxs (k, v) (lookupAssoc_mem hl)) hp

private theorem ElemManaged_foldl_norm (attrs : List (Attr msg)) (s : SpecElemState msg)
    (hs : ElemManaged s ((normalizeAttrs attrs).filterMap managedAttrName)) :
    ElemManaged ((normalizeAttrs attrs).foldl stepSpecAttr s) ((normalizeAttrs attrs).filterMap managedAttrName) := by
  let names := (normalizeAttrs attrs).filterMap managedAttrName
  have hpres : ∀ (xs : List (Attr msg)) (cur : SpecElemState msg),
      (∀ x ∈ xs, match managedAttrName x with | some n => names.contains n = true | none => True) →
      ElemManaged cur names → ElemManaged (xs.foldl stepSpecAttr cur) names := by
    intro xs; induction xs with
    | nil => intro _ _ h; exact h
    | cons x rest ih =>
        intro cur hx hcur
        exact ih _ (fun y hy => hx y (List.mem_cons_of_mem x hy))
          (stepSpecAttr_retains_managed cur x names (hx x (List.mem_cons_self ..)) hcur)
  refine hpres (normalizeAttrs attrs) s (fun x hx => ?_) hs
  cases hmName : managedAttrName x with
  | none => trivial
  | some n => exact List.contains_iff_mem.2 (List.mem_filterMap.2 ⟨x, hx, hmName⟩)

theorem applyAttrsM_existing_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (prev : List String) (cs : List Dom.Node)
    (newAttrs : List (Attr msg)) (hm : ElemManaged st prev) (hNoShadow : AttrsNoShadow newAttrs st) :
    let norm := normalizeAttrs newAttrs
    let names := norm.filterMap managedAttrName
    let a' := (applyAttrsM (m := StateM (DomArena msg)) node newAttrs (a.set node (.element ns tag st prev cs))).2
    ∃ st', a'.get node = .element ns tag st' names cs ∧
      ElemStateEquiv st' (evalSpecAttrs newAttrs) ∧
      ElemManaged st' names := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]
  let norm := normalizeAttrs newAttrs
  let names := norm.filterMap managedAttrName
  let val' := if prev.contains "value" && !names.contains "value" then "" else st.value
  let chk' := if prev.contains "checked" && !names.contains "checked" then false else st.checked
  let attrs' := st.attrs.filter fun (k, _) => !prev.contains k || names.contains k
  let clicks' := st.clicks.filter fun (e, _) => !prev.contains s!"data-qed-on-{e}" || names.contains s!"data-qed-on-{e}"
  let inputs' := st.inputs.filter fun (e, _) => !prev.contains s!"data-qed-onv-{e}" || names.contains s!"data-qed-onv-{e}"
  let st0 : SpecElemState msg := { st with attrs := attrs', value := val', checked := chk', clicks := clicks', inputs := inputs' }
  rw [applyAttrListM_element norm a node ns tag st0 names cs, DomArena.get_set_self]
  refine ⟨norm.foldl stepSpecAttr st0, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k; apply foldl_stepSpecAttr_attrs k norm st0 {}
    by_cases hw : ∃ x ∈ norm, attrWritesKey k x = true
    · exact .inl hw
    · exact .inr (filter_managed_lookup_none (keyFn := id) hm.1 k fun hn => (hNoShadow.1 k hn).resolve_left hw)
  · apply foldl_stepSpecAttr_val norm st0 {}
    by_cases hv : ∃ v, .attr "value" v ∈ norm
    · exact .inr hv
    · left; change val' = ""; dsimp only [val']
      by_cases hnv : names.contains "value" = true
      · rcases hNoShadow.2.1 hnv with hv' | hst
        · exact False.elim (hv hv')
        · simp only [hnv, Bool.not_true, Bool.and_false]; exact hst
      · have hnvF : names.contains "value" = false := Bool.eq_false_iff.2 hnv
        by_cases hst : st.value = ""
        · simp only [hnvF, Bool.not_false, Bool.and_true]; cases prev.contains "value" <;> simp [hst]
        · simp only [hm.2.1 hst, hnvF, Bool.not_false, Bool.and_self, ↓reduceIte]
  · apply foldl_stepSpecAttr_chk norm st0 {}
    by_cases hc : ∃ p, .flag "checked" p ∈ norm
    · exact .inr hc
    · left; change chk' = false; dsimp only [chk']
      by_cases hnc : names.contains "checked" = true
      · rcases hNoShadow.2.2.1 hnc with hc' | hst
        · exact False.elim (hc hc')
        · simp only [hnc, Bool.not_true, Bool.and_false]; exact hst
      · have hncF : names.contains "checked" = false := Bool.eq_false_iff.2 hnc
        cases hst : st.checked
        · simp only [hncF, Bool.not_false, Bool.and_true]; cases prev.contains "checked" <;> simp
        · simp only [hm.2.2.1 hst, hncF, Bool.not_false, Bool.and_self, ↓reduceIte]
  · intro e; apply foldl_stepSpecAttr_clicks e norm st0 {}
    by_cases hcl : ∃ m, .on e m ∈ norm
    · exact .inl hcl
    · exact .inr (filter_managed_lookup_none (keyFn := fun e => s!"data-qed-on-{e}") hm.2.2.2.1 e
        fun hn => (hNoShadow.2.2.2.1 e hn).resolve_left hcl)
  · intro e; apply foldl_stepSpecAttr_inputs e norm st0 {}
    by_cases hin : ∃ f, .onValue e f ∈ norm
    · exact .inl hin
    · exact .inr (filter_managed_lookup_none (keyFn := fun e => s!"data-qed-onv-{e}") hm.2.2.2.2 e
        fun hn => (hNoShadow.2.2.2.2 e hn).resolve_left hin)
  · have hm0 : ElemManaged st0 names := by
      refine ⟨filter_managed_prop (keyFn := id) hm.1, fun hne => ?_, fun hchk => ?_,
        filter_managed_prop (keyFn := fun e => s!"data-qed-on-{e}") hm.2.2.2.1,
        filter_managed_prop (keyFn := fun e => s!"data-qed-onv-{e}") hm.2.2.2.2⟩
      · by_cases hnv : names.contains "value" = true
        · exact hnv
        · have hnvF : names.contains "value" = false := Bool.eq_false_iff.2 hnv
          by_cases hst : st.value = ""
          · simp only [st0, val', hst, ite_self, ne_eq, not_true_eq_false] at hne
          · have hpv := hm.2.1 hst
            simp only [st0, val', hpv, hnvF, Bool.not_false, Bool.and_self, ↓reduceIte, ne_eq, not_true_eq_false] at hne
      · by_cases hnc : names.contains "checked" = true
        · exact hnc
        · have hncF : names.contains "checked" = false := Bool.eq_false_iff.2 hnc
          cases hst : st.checked
          · simp only [st0, chk', hst, ite_self, Bool.false_eq_true] at hchk
          · have hpc := hm.2.2.1 hst
            simp only [st0, chk', hpc, hncF, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true] at hchk
    exact ElemManaged_foldl_norm newAttrs st0 hm0

def isSpecialManagedKey (k : String) : Bool :=
  k == "value" || k == "checked" ||
  k.startsWith "data-qed-on-" || k.startsWith "data-qed-onv-" || k == "data-qed-signal"

def Attr.DomClean : Attr msg → Bool
  | .attr "value" _   => true
  | .flag "checked" _ => true
  | .attr k _         => !isSpecialManagedKey k
  | .flag k _         => !isSpecialManagedKey k
  | .signalAttr ..    => false
  | .signalOn ..      => false
  | _                 => true

mutual
  def Html.DomClean : Html msg → Bool
    | .text _ => true
    | .element _ attrs cs => !ownsChildren attrs && attrs.all Attr.DomClean && Html.DomCleanList cs

  def Html.DomCleanList : List (Html msg) → Bool
    | []      => true
    | c :: cs => Html.DomClean c && Html.DomCleanList cs
end

def ElemClean (st : SpecElemState msg) (prev : List String) : Prop :=
  ElemManaged st prev ∧ ∀ k, isSpecialManagedKey k = true → lookupAssoc k st.attrs = none

private theorem mem_dedupAttrs {xs : List (Attr msg)} {x : Attr msg} (hx : x ∈ dedupAttrs xs) : x ∈ xs := by
  induction xs with
  | nil => simp [dedupAttrs] at hx
  | cons a rest ih =>
      simp only [dedupAttrs] at hx
      cases hk : a.key? with
      | none => simp only [hk] at hx; rcases List.mem_cons.1 hx with rfl | h; exact .head _; exact .tail _ (ih h)
      | some k =>
          simp only [hk] at hx
          split at hx
          · exact .tail _ (ih hx)
          · rcases List.mem_cons.1 hx with rfl | h; exact .head _; exact .tail _ (ih h)

theorem mem_normalizeAttrs_DomClean {attrs : List (Attr msg)} (hc : attrs.all Attr.DomClean = true) :
    ∀ x ∈ normalizeAttrs attrs, x.DomClean = true := by
  rw [List.all_eq_true] at hc
  intro x hx
  simp only [normalizeAttrs, List.mem_append] at hx
  rcases hx with hm | hd
  · split at hm
    · nomatch hm
    · simp only [List.mem_singleton] at hm; subst hm; rfl
  · exact hc x (List.mem_filter.1 (mem_dedupAttrs hd)).1

private theorem append_drop11_ne {p e q : String}
    (hp : ((p ++ e).toList.drop 11).head? ≠ (q.toList.drop 11).head?) : p ++ e ≠ q :=
  fun h => hp (congrArg (fun s => (s.toList.drop 11).head?) h)

private theorem isSpecialManagedKey_on_contra {p : String} (e : String) (hp : p = "data-qed-on-" ∨ p = "data-qed-onv-")
    (h1 : (!isSpecialManagedKey (p ++ e)) = true) : False := by
  rcases hp with rfl | rfl <;> simp [isSpecialManagedKey, String.startsWith] at h1

theorem AttrsNoShadow_of_clean {newAttrs : List (Attr msg)} {st : SpecElemState msg} {prev : List String}
    (hst : ElemClean st prev) (hc : newAttrs.all Attr.DomClean = true) :
    AttrsNoShadow newAttrs st := by
  have hnorm := mem_normalizeAttrs_DomClean hc
  refine ⟨fun k hk => ?_, fun hval => ?_, fun hchk => ?_, fun e hev => ?_, fun e hinp => ?_⟩
  · rw [List.contains_iff_mem] at hk
    rcases List.mem_filterMap.1 hk with ⟨x, hxMem, hxName⟩
    have hxc := hnorm x hxMem
    cases x with
    | cls _ => simp [managedAttrName] at hxName; rcases hxName with rfl; exact .inl ⟨_, hxMem, rfl⟩
    | attr k' v =>
        simp only [managedAttrName, Option.some.injEq] at hxName; rcases hxName with rfl
        by_cases hv : k' = "value"
        · subst hv; exact .inr (hst.2 "value" rfl)
        · exact .inl ⟨.attr k' v, hxMem, by simp [attrWritesKey, hv]⟩
    | flag k' p =>
        simp only [managedAttrName, Option.some.injEq] at hxName; rcases hxName with rfl
        by_cases hc' : k' = "checked"
        · subst hc'; exact .inr (hst.2 "checked" rfl)
        · exact .inl ⟨.flag k' p, hxMem, by simp [attrWritesKey, hc']⟩
    | localCell _ _ _ _ _ => simp [managedAttrName] at hxName; rcases hxName with rfl; exact .inl ⟨_, hxMem, rfl⟩
    | key _ => simp [managedAttrName] at hxName
    | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hxc
    | on _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; rcases hxName with rfl
        exact .inr (hst.2 _ (by simp [isSpecialManagedKey, String.startsWith]))
    | onValue _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; rcases hxName with rfl
        exact .inr (hst.2 _ (by simp [isSpecialManagedKey, String.startsWith]))
    | signalBind _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; rcases hxName with rfl
        exact .inr (hst.2 "data-qed-signal" (by simp [isSpecialManagedKey]))
  · rw [List.contains_iff_mem] at hval
    rcases List.mem_filterMap.1 hval with ⟨x, hxMem, hxName⟩
    have hxc := hnorm x hxMem
    cases x with
    | attr _ v => simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName; exact .inl ⟨v, hxMem⟩
    | flag _ _ => simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName; simp [Attr.DomClean, isSpecialManagedKey] at hxc
    | cls _ | key _ | localCell _ _ _ _ _ | signalBind _ => simp [managedAttrName] at hxName
    | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hxc
    | on _ _ | onValue _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have hd := congrArg (·.toList.head?) hxName; simp [String.toList_append] at hd
  · rw [List.contains_iff_mem] at hchk
    rcases List.mem_filterMap.1 hchk with ⟨x, hxMem, hxName⟩
    have hxc := hnorm x hxMem
    cases x with
    | flag _ p => simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName; exact .inl ⟨p, hxMem⟩
    | attr _ _ => simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName; simp [Attr.DomClean, isSpecialManagedKey] at hxc
    | cls _ | key _ | localCell _ _ _ _ _ | signalBind _ => simp [managedAttrName] at hxName
    | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hxc
    | on _ _ | onValue _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have hd := congrArg (·.toList.head?) hxName; simp [String.toList_append] at hd
  · rw [List.contains_iff_mem] at hev
    rcases List.mem_filterMap.1 hev with ⟨x, hxMem, hxName⟩
    have hxc := hnorm x hxMem
    cases x with
    | on e' ev =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have heq := string_append_left_cancel hxName; subst heq; exact .inl ⟨ev, hxMem⟩
    | onValue _ _ | signalBind _ | cls _ | localCell _ _ _ _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have hd := congrArg (fun s => s.toList.drop 11 |>.head?) hxName; simp [String.toList_append] at hd
    | key _ => simp [managedAttrName] at hxName
    | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hxc
    | attr k' _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName
        have hv : ("data-qed-on-" ++ e) ≠ "value" :=
          append_drop11_ne (by simp [String.toList_append])
        exact False.elim (isSpecialManagedKey_on_contra e (.inl rfl) (by simpa [Attr.DomClean, hv] using hxc))
    | flag k' _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName
        have hc' : ("data-qed-on-" ++ e) ≠ "checked" :=
          append_drop11_ne (by simp [String.toList_append])
        exact False.elim (isSpecialManagedKey_on_contra e (.inl rfl) (by simpa [Attr.DomClean, hc'] using hxc))
  · rw [List.contains_iff_mem] at hinp
    rcases List.mem_filterMap.1 hinp with ⟨x, hxMem, hxName⟩
    have hxc := hnorm x hxMem
    cases x with
    | onValue e' f =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have heq := string_append_left_cancel hxName; subst heq; exact .inl ⟨f, hxMem⟩
    | on _ _ | signalBind _ | cls _ | localCell _ _ _ _ _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName
        have hd := congrArg (fun s => s.toList.drop 11 |>.head?) hxName; simp [String.toList_append] at hd
    | key _ => simp [managedAttrName] at hxName
    | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hxc
    | attr k' _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName
        have hv : ("data-qed-onv-" ++ e) ≠ "value" :=
          append_drop11_ne (by simp [String.toList_append])
        exact False.elim (isSpecialManagedKey_on_contra e (.inr rfl) (by simpa [Attr.DomClean, hv] using hxc))
    | flag k' _ =>
        simp only [managedAttrName, Option.some.injEq] at hxName; subst hxName
        have hc' : ("data-qed-onv-" ++ e) ≠ "checked" :=
          append_drop11_ne (by simp [String.toList_append])
        exact False.elim (isSpecialManagedKey_on_contra e (.inr rfl) (by simpa [Attr.DomClean, hc'] using hxc))

theorem stepSpecAttr_preserves_clean (s : SpecElemState msg) (a : Attr msg)
    (hca : a.DomClean = true) (hcs : ∀ k, isSpecialManagedKey k = true → lookupAssoc k s.attrs = none) :
    ∀ k, isSpecialManagedKey k = true → lookupAssoc k (stepSpecAttr s a).attrs = none := by
  intro k hk
  cases a with
  | attr k' _ =>
      by_cases hv : k' = "value"
      · subst hv; exact hcs k hk
      · have hne : (k' == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [Attr.DomClean, hk] at hca
        simp [stepSpecAttr, lookupAssoc_setAssoc, hne, hcs k hk]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; exact hcs k hk
      · have hne : (k' == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [Attr.DomClean, hk] at hca
        cases p <;> simp [stepSpecAttr, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, hne, hcs k hk]
  | cls _ =>
      have hne : ("class" == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [isSpecialManagedKey] at hk
      simp [stepSpecAttr, lookupAssoc_setAssoc, hne, hcs k hk]
  | localCell _ _ _ _ _ =>
      have hne : ("data-qed-local" == k) = false := beq_eq_false_iff_ne.2 fun h => by
        subst h; simp [isSpecialManagedKey, String.startsWith] at hk
      simp [stepSpecAttr, lookupAssoc_setAssoc, hne, hcs k hk]
  | key _ | on _ _ | onValue _ _ | signalBind _ => exact hcs k hk
  | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hca

theorem ElemClean_foldl {xs : List (Attr msg)} {st : SpecElemState msg}
    (hcxs : ∀ x ∈ xs, x.DomClean = true)
    (hcst : ∀ k, isSpecialManagedKey k = true → lookupAssoc k st.attrs = none) :
    ∀ k, isSpecialManagedKey k = true → lookupAssoc k (xs.foldl stepSpecAttr st).attrs = none := by
  induction xs generalizing st with
  | nil => exact hcst
  | cons x rest ih => exact ih (fun y hy => hcxs y (.tail _ hy)) (stepSpecAttr_preserves_clean st x (hcxs x (.head _)) hcst)

theorem ElemClean_evalSpecAttrs {attrs : List (Attr msg)} (hc : attrs.all Attr.DomClean = true) :
    ElemClean (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) :=
  ⟨ElemManaged_foldl_norm attrs {} ElemManaged_empty,
   ElemClean_foldl (mem_normalizeAttrs_DomClean hc) (fun _ _ => rfl)⟩

theorem ElemClean_applyAttrsM (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (prev : List String) (cs : List Dom.Node)
    (newAttrs : List (Attr msg)) (hst : ElemClean st prev) (hc : newAttrs.all Attr.DomClean = true) :
    let norm := normalizeAttrs newAttrs
    let names := norm.filterMap managedAttrName
    let a' := (applyAttrsM (m := StateM (DomArena msg)) node newAttrs (a.set node (.element ns tag st prev cs))).2
    ∃ st', a'.get node = .element ns tag st' names cs ∧
      ElemStateEquiv st' (evalSpecAttrs newAttrs) ∧
      ElemClean st' names := by
  have he := applyAttrsM_existing_element a node ns tag st prev cs newAttrs hst.1 (AttrsNoShadow_of_clean hst hc)
  rcases he with ⟨st', hget, heqv, hm'⟩
  refine ⟨st', hget, heqv, hm', fun k hk => ?_⟩
  rw [heqv.1 k]
  exact (ElemClean_evalSpecAttrs hc).2 k hk

/-! ## `DomTreeAssocEquiv` & Bounded Subtree Framing -/

mutual
  def DomTreeAssocEquiv {msg : Type} : DomTree msg → DomTree msg → Prop
    | .text s₁, .text s₂ => s₁ = s₂
    | .element ns₁ tag₁ st₁ cs₁, .element ns₂ tag₂ st₂ cs₂ =>
        ns₁ = ns₂ ∧ tag₁ = tag₂ ∧ ElemStateEquiv st₁ st₂ ∧ DomTreeListAssocEquiv cs₁ cs₂
    | _, _ => False

  def DomTreeListAssocEquiv {msg : Type} : List (DomTree msg) → List (DomTree msg) → Prop
    | [], [] => True
    | x :: xs, y :: ys => DomTreeAssocEquiv x y ∧ DomTreeListAssocEquiv xs ys
    | _, _ => False
end

mutual
  theorem DomTreeAssocEquiv.refl : ∀ t : DomTree msg, DomTreeAssocEquiv t t
    | .text _ => rfl
    | .element _ _ st cs => ⟨rfl, rfl, ElemStateEquiv.refl st, DomTreeListAssocEquiv.refl cs⟩

  theorem DomTreeListAssocEquiv.refl : ∀ cs : List (DomTree msg), DomTreeListAssocEquiv cs cs
    | [] => trivial
    | c :: cs => ⟨DomTreeAssocEquiv.refl c, DomTreeListAssocEquiv.refl cs⟩
end

mutual
  theorem DomTreeAssocEquiv.symm : ∀ {t₁ t₂ : DomTree msg}, DomTreeAssocEquiv t₁ t₂ → DomTreeAssocEquiv t₂ t₁
    | .text _, .text _, h => Eq.symm h
    | .element _ _ _ _, .element _ _ _ _, ⟨h1, h2, hst, hcs⟩ =>
        ⟨h1.symm, h2.symm, hst.symm, DomTreeListAssocEquiv.symm hcs⟩
    | .text _, .element _ _ _ _, h => False.elim h
    | .element _ _ _ _, .text _, h => False.elim h

  theorem DomTreeListAssocEquiv.symm :
      ∀ {xs ys : List (DomTree msg)}, DomTreeListAssocEquiv xs ys → DomTreeListAssocEquiv ys xs
    | [], [], _ => trivial
    | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨DomTreeAssocEquiv.symm h1, DomTreeListAssocEquiv.symm h2⟩
    | [], _ :: _, h | _ :: _, [], h => False.elim h
end

mutual
  theorem DomTreeAssocEquiv.trans :
      ∀ {t₁ t₂ t₃ : DomTree msg}, DomTreeAssocEquiv t₁ t₂ → DomTreeAssocEquiv t₂ t₃ → DomTreeAssocEquiv t₁ t₃
    | .text _, .text _, .text _, h1, h2 => Eq.trans h1 h2
    | .element _ _ _ _, .element _ _ _ _, .element _ _ _ _,
      ⟨hns1, ht1, hst1, hcs1⟩, ⟨hns2, ht2, hst2, hcs2⟩ =>
        ⟨hns1.trans hns2, ht1.trans ht2, hst1.trans hst2, DomTreeListAssocEquiv.trans hcs1 hcs2⟩
    | .text _, .text _, .element _ _ _ _, _, h2 => False.elim h2
    | .text _, .element _ _ _ _, _, h1, _ => False.elim h1
    | .element _ _ _ _, .text _, _, h1, _ => False.elim h1
    | .element _ _ _ _, .element _ _ _ _, .text _, _, h2 => False.elim h2

  theorem DomTreeListAssocEquiv.trans :
      ∀ {xs ys zs : List (DomTree msg)},
        DomTreeListAssocEquiv xs ys → DomTreeListAssocEquiv ys zs → DomTreeListAssocEquiv xs zs
    | [], [], [], _, _ => trivial
    | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨DomTreeAssocEquiv.trans h1 h3, DomTreeListAssocEquiv.trans h2 h4⟩
    | [], [], _ :: _, _, h2 => False.elim h2
    | [], _ :: _, _, h1, _ => False.elim h1
    | _ :: _, [], _, h1, _ => False.elim h1
    | _ :: _, _ :: _, [], _, h2 => False.elim h2
end

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

def SubtreeInSet {msg : Type} : Nat → DomArena msg → (Nat → Prop) → Dom.Node → Prop
  | 0, _, _, _ => True
  | f + 1, a, S, n =>
      S n.toNat ∧
      match a.get n with
      | .element _ _ _ _ cs => ∀ c ∈ cs, SubtreeInSet f a S c
      | _ => True

abbrev SubtreeInRange {msg : Type} (fuel : Nat) (a : DomArena msg) (lo hi : Nat) (n : Dom.Node) : Prop :=
  SubtreeInSet fuel a (fun k => lo ≤ k ∧ k < hi) n

theorem SubtreeInRange_to_SubtreeInSet {msg : Type} {f : Nat} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node}
    (h : SubtreeInRange f a lo hi n) : SubtreeInSet f a (fun k => lo ≤ k ∧ k < hi) n := h

theorem SubtreeInSet_mono {msg : Type} :
    ∀ {f : Nat} {a : DomArena msg} {S₁ S₂ : Nat → Prop} {n : Dom.Node},
      (∀ k, S₁ k → S₂ k) → SubtreeInSet f a S₁ n → SubtreeInSet f a S₂ n
  | 0, _, _, _, _, _, _ => trivial
  | f + 1, a, S₁, S₂, n, hsub, hn => by
      dsimp only [SubtreeInSet] at hn ⊢
      refine ⟨hsub n.toNat hn.1, ?_⟩
      cases hg : a.get n with
      | element _ _ _ _ cs => rw [hg] at hn; exact fun c hc => SubtreeInSet_mono hsub (hn.2 c hc)
      | null | text _ | fragment _ => trivial

theorem SubtreeInRange_mono {fuel : Nat} {a : DomArena msg} {lo₁ hi₁ lo₂ hi₂ : Nat} {n : Dom.Node}
    (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) (h : SubtreeInRange fuel a lo₁ hi₁ n) :
    SubtreeInRange fuel a lo₂ hi₂ n :=
  SubtreeInSet_mono (fun _ hk => ⟨Nat.le_trans hlo hk.1, Nat.lt_of_lt_of_le hk.2 hhi⟩) h

theorem SubtreeInSet_frame {msg : Type} :
    ∀ {f : Nat} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
      SubtreeInSet f a S n → SubtreeInSet f a' S n ∧ readDomTree f a' n = readDomTree f a n
  | 0, _, _, _, _, _, _ => ⟨trivial, rfl⟩
  | f + 1, a, a', S, n, hfr, hn => by
      dsimp only [SubtreeInSet] at hn ⊢
      have hget : a'.get n = a.get n := hfr n hn.1
      refine ⟨⟨hn.1, ?_⟩, ?_⟩
      · rw [hget]; cases hg : a.get n with
        | element _ _ _ _ cs => rw [hg] at hn; exact fun c hc => (SubtreeInSet_frame hfr (hn.2 c hc)).1
        | null | text _ | fragment _ => trivial
      · dsimp only [readDomTree]; rw [hget]; cases hg : a.get n with
        | element _ _ _ _ cs =>
            rw [hg] at hn; simp only [DomTree.element.injEq, true_and]
            exact List.map_congr_left fun c hc => (SubtreeInSet_frame hfr (hn.2 c hc)).2
        | null | text _ | fragment _ => rfl

theorem SubtreeInRange_frame {fuel : Nat} {a a' : DomArena msg} {lo hi : Nat} {n : Dom.Node}
    (hagree : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m)
    (hsub : SubtreeInRange fuel a lo hi n) :
    SubtreeInRange fuel a' lo hi n ∧ readDomTree fuel a' n = readDomTree fuel a n :=
  SubtreeInSet_frame (fun m hm => hagree m hm.1 hm.2) hsub

/-! ## `buildDomM` & Utility Theorems -/

theorem uint32_toNat_ofNat_lt (n : Nat) (h : n < UInt32.size) : (UInt32.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem uint32_eq_of_toNat_eq {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.toBitVec_inj.1 (BitVec.eq_of_toNat_eq h)

theorem node_ne_of_toNat_ne {a b : Dom.Node} (h : a.toNat ≠ b.toNat) : a ≠ b :=
  fun heq => h (congrArg UInt32.toNat heq)

theorem uint32_ofNat_succ (n : Nat) (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) :=
  uint32_eq_of_toNat_eq (by simp [UInt32.toNat_add, uint32_toNat_ofNat_lt n (by omega)])

theorem getD_append_right {α : Type} (x d : α) :
    ∀ (pre suf : List α), (pre ++ x :: suf).getD pre.length d = x
  | [], _ => rfl
  | _ :: rest, suf => getD_append_right x d rest suf

def removeTailSpec (idx : Nat) : Nat → List α → List α
  | 0, cs => cs
  | k + 1, cs => removeTailSpec idx k (listRemoveAt cs idx)

theorem listRemoveAt_append_head {α : Type} :
    ∀ (pre : List α) (x : α) (suf : List α), listRemoveAt (pre ++ x :: suf) pre.length = pre ++ suf
  | [], _, _ => rfl
  | _ :: prest, x, suf => by simp [listRemoveAt, listRemoveAt_append_head prest x suf]

theorem removeTailSpec_append {α : Type} (pre : List α) :
    ∀ (suf : List α), removeTailSpec pre.length suf.length (pre ++ suf) = pre
  | [] => by simp [removeTailSpec]
  | x :: suf => by simp [removeTailSpec, listRemoveAt_append_head pre x suf, removeTailSpec_append pre suf]

theorem removeTailM_spec (a : DomArena msg) (node : Dom.Node) (atIdx : Nat) (k : Nat)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node) :
    ((removeTailM (m := StateM (DomArena msg)) node (UInt32.ofNat atIdx) k).run
      (a.set node (.element ns tag st mg cs))).2 =
      a.set node (.element ns tag st mg (removeTailSpec (UInt32.ofNat atIdx).toNat k cs)) := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
      simp only [removeTailM, removeTailSpec, bind, StateT.bind, StateT.run,
                 DomArena.modifyChildren, DomArena.modify, DomArena.get_set_self, DomArena.set_set]
      exact ih (listRemoveAt cs (UInt32.ofNat atIdx).toNat)

theorem buildDomListM_step {msg : Type} (childNs : String) (parent : Dom.Node)
    (c : Html msg) (rest : List (Html msg)) (aIn aMid : DomArena msg) (cn : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg)
    (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds))
    (acc : List Dom.Node)
    (hbuild : buildDomM (m := StateM (DomArena msg)) childNs c aIn = (cn, aMid))
    (hparMid : aMid.get parent = mkPar acc)
    (hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs)
    (hcnNotInAcc : cn ∉ acc) :
    ((buildDomListM (m := StateM (DomArena msg)) childNs parent (c :: rest)).run aIn).2 =
      ((buildDomListM (m := StateM (DomArena msg)) childNs parent rest).run
        (aMid.set parent (mkPar (acc ++ [cn])))).2 := by
  have happend : MonadDom.appendChild (m := StateM (DomArena msg)) parent cn aMid =
      ((), aMid.set parent (mkPar (acc ++ [cn]))) := by
    cases hgetCn : aMid.get cn with
    | fragment fcs => exact False.elim (hcnNotFrag fcs hgetCn)
    | null | text _ | element _ _ _ _ _ =>
        rcases hmk with ⟨pns, ptag, pst, pmg, hme⟩ | hmf
        · simp [MonadDom.appendChild, hgetCn, DomArena.modify, hparMid, hme, List.erase_of_not_mem hcnNotInAcc]
        · simp [MonadDom.appendChild, hgetCn, DomArena.modify, hparMid, hmf, List.erase_of_not_mem hcnNotInAcc]
  dsimp only [buildDomListM, StateT.run, bind, StateT.bind]
  change (match buildDomM (m := StateM (DomArena msg)) childNs c aIn with
          | (cn', aMid') => match MonadDom.appendChild (m := StateM (DomArena msg)) parent cn' aMid' with
            | (_, aAfter') => buildDomListM (m := StateM (DomArena msg)) childNs parent rest aAfter').2 = _
  rw [hbuild]; dsimp only; rw [happend]

mutual
  theorem buildDomM_spec (ns : String) :
      ∀ (h : Html msg) (a : DomArena msg) (fuel : Nat),
        0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ fuel →
        let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
        a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount h ∧
        (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
        SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns h
    | .text s, a, fuel, _, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ f =>
            simp only [htmlNodeCount] at hbound ⊢
            have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
            dsimp only [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run, SubtreeInRange, SubtreeInSet]
            refine ⟨by omega, by omega, by omega, fun m hm => ?_, ⟨⟨by omega, by omega⟩, by simp [DomArena.get]⟩,
                    by simp [readDomTree, DomArena.get, specDom]⟩
            have hne : m ≠ UInt32.ofNat a.nextId := fun heq => by subst heq; omega
            simp [DomArena.get, beq_eq_false_iff_ne.2 hne]
    | .element tag attrs children, a, fuel, hpos, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ f =>
            simp only [htmlNodeCount] at hbound ⊢; simp only [htmlDepth] at hdep
            let node := UInt32.ofNat a.nextId
            have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
            let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
            let st := evalSpecAttrs attrs
            let mg := (normalizeAttrs attrs).filterMap managedAttrName
            let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
            let aElem := a1.set node (.element realNs tag st mg [])
            have ha1Next : a1.nextId = a.nextId + 1 := rfl
            have haElemNext : aElem.nextId = a.nextId + 1 := rfl
            have ha2_frame : ∀ m : Dom.Node, m.toNat < a.nextId → aElem.get m = a.get m := fun m hm => by
              have hne : m ≠ node := fun heq => by subst heq; omega
              rw [DomArena.get_set_ne _ _ hne]; rfl
            have hrun : (buildDomM (m := StateM (DomArena msg)) ns (.element tag attrs children)).run a =
                if !ownsChildren attrs then
                  (node, ((buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children).run aElem).2)
                else (node, aElem) := by
              dsimp only [buildDomM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
              change (match applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
                      | (_, s) => (if (!ownsChildren attrs) = true then
                         StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children) (fun _ => StateT.pure node)
                         else StateT.bind (StateT.pure PUnit.unit) (fun _ => StateT.pure node)) s) = _
              rw [applyAttrsM_fresh_element a1 node realNs tag [] attrs]
              cases ownsChildren attrs <;> rfl
            rw [hrun]
            by_cases hown : ownsChildren attrs
            · simp only [hown, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              refine ⟨by omega, by omega, by omega, ha2_frame, ?_,
                      by simp [readDomTree, aElem, DomArena.get_set_self, specDom, hown, realNs, st]⟩
              dsimp only [SubtreeInRange, SubtreeInSet]
              exact ⟨⟨by omega, by omega⟩, by simp [aElem, DomArena.get_set_self]⟩
            · have hownF : ownsChildren attrs = false := Bool.eq_false_iff.2 hown
              simp only [hownF, Bool.not_false, ↓reduceIte]
              have hkids := buildDomListM_spec (Dom.childNsOf ns tag) children a1 node realNs tag st mg [] f
                (by omega) (by omega) (by omega) (by omega) (fun _ h => nomatch h)
              rcases hkids with ⟨csNew, aBase', ha'Eq, hnextLe, hnextMono, hframe1, hsubKids, hreadKids⟩
              dsimp only [aElem]
              refine ⟨by omega, by omega, by omega, fun m hm => ?_, ?_, ?_⟩
              · have hne : m ≠ node := fun heq => by subst heq; omega
                rw [ha'Eq, DomArena.get_set_ne _ _ hne]
                have := hframe1 m (by omega) hne
                rwa [DomArena.get_set_ne _ _ hne] at this
              · dsimp only [SubtreeInRange, SubtreeInSet]
                refine ⟨⟨by omega, by omega⟩, ?_⟩
                rw [ha'Eq, DomArena.get_set_self]
                intro c hc; have := hsubKids c hc; rw [ha'Eq] at this
                exact SubtreeInRange_mono (by omega) (Nat.le_refl _) this
              · rw [ha'Eq] at hreadKids ⊢
                simpa [readDomTree, DomArena.get_set_self, specDom, hownF, realNs, st] using hreadKids

  theorem buildDomListM_spec (childNs : String) :
      ∀ (cs : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
        (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (acc : List Dom.Node) (f : Nat),
        parent.toNat < aBase.nextId → 0 < aBase.nextId → aBase.nextId + htmlListNodeCount cs < UInt32.size →
        htmlListDepth cs ≤ f →
        (∀ c ∈ acc, SubtreeInRange f (aBase.set parent (.element pns ptag pst pmg acc)) (parent.toNat + 1) aBase.nextId c) →
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
        ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
          aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
          aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧ aBase.nextId ≤ aOut.nextId ∧
          (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
          (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
          (acc ++ csNew).map (readDomTree f aOut) = acc.map (readDomTree f aIn) ++ specDomList childNs cs
    | [], aBase, parent, pns, ptag, pst, pmg, acc, f, _, _, _, _, haccSub => by
        refine ⟨[], aBase, ?_, ?_, ?_, fun _ _ hne => (DomArena.get_set_ne _ _ hne).symm, ?_, ?_⟩
        · simp [buildDomListM, StateT.run, pure, StateT.pure]
        · simp [buildDomListM, StateT.run, pure, StateT.pure, htmlListNodeCount]
        · simp [buildDomListM, StateT.run, pure, StateT.pure]
        · simpa [buildDomListM, StateT.run, pure, StateT.pure] using haccSub
        · simp [buildDomListM, StateT.run, pure, StateT.pure, specDomList]
    | c :: rest, aBase, parent, pns, ptag, pst, pmg, acc, f, hparLt, hpos, hbound, hdep, haccSub => by
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        have haInNext : aIn.nextId = aBase.nextId := rfl
        simp only [htmlListNodeCount] at hbound; simp only [htmlListDepth] at hdep
        have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
        have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
        have hfPos : 0 < f := by cases c <;> { simp [htmlDepth] at hcDep; omega }
        have hcSpec := buildDomM_spec childNs c aIn f (by omega) (by omega) hcDep
        dsimp only [StateT.run] at hcSpec
        let res1 := buildDomM (m := StateM (DomArena msg)) childNs c aIn
        let cn := res1.1
        let aMid := res1.2
        rcases hcSpec with ⟨hcnGe, hcnLt, haMidLe, haMidFrame, hcnSub, hcnRead⟩
        change aIn.nextId ≤ cn.toNat at hcnGe
        change cn.toNat < aMid.nextId at hcnLt
        change aMid.nextId ≤ aIn.nextId + htmlNodeCount c at haMidLe
        change ∀ m : Dom.Node, m.toNat < aIn.nextId → aMid.get m = aIn.get m at haMidFrame
        change SubtreeInRange f aMid aIn.nextId aMid.nextId cn at hcnSub
        change readDomTree f aMid cn = specDom childNs c at hcnRead
        have hparInMid : aMid.get parent = .element pns ptag pst pmg acc := by
          rw [haMidFrame parent (by omega)]; simp [aIn, DomArena.get_set_self]
        have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := fun fcs hfrag => by
          cases f with
          | zero => omega
          | succ _ => cases c with
            | text _ => simp [aMid, cn, res1, buildDomM, MonadDom.createText, DomArena.alloc, DomArena.get] at hfrag
            | element _ _ _ => dsimp only [readDomTree] at hcnRead; rw [hfrag] at hcnRead; cases hcnRead
        have hcnNotInAcc : cn ∉ acc := fun hmem => by
          have := haccSub cn hmem
          cases f with
          | zero => omega
          | succ _ => dsimp only [SubtreeInRange, SubtreeInSet] at this; omega
        let aAfterAppend := aMid.set parent (.element pns ptag pst pmg (acc ++ [cn]))
        have haccMid : ∀ x ∈ acc, SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId x ∧
            readDomTree f aAfterAppend x = readDomTree f aIn x := fun x hx => by
          have hfr := SubtreeInRange_frame (a := aIn) (a' := aAfterAppend)
            (fun m hlo hhi => by
              have hne : m ≠ parent := fun heq => by subst heq; omega
              rw [DomArena.get_set_ne _ _ hne]; exact haMidFrame m (by omega))
            (haccSub x hx)
          exact ⟨SubtreeInRange_mono (Nat.le_refl _) (by omega) hfr.1, hfr.2⟩
        have hcnAfter : SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId cn ∧
            readDomTree f aAfterAppend cn = specDom childNs c := by
          have hfr := SubtreeInRange_frame (a := aMid) (a' := aAfterAppend)
            (fun m _ _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega)
            (SubtreeInRange_mono (by omega : parent.toNat + 1 ≤ aIn.nextId) (Nat.le_refl _) hcnSub)
          exact ⟨hfr.1, hfr.2.trans hcnRead⟩
        have hih := buildDomListM_spec childNs rest aMid parent pns ptag pst pmg (acc ++ [cn]) f
          (by omega) (by omega) (by omega) hrestDep fun x hx => by
            rcases List.mem_append.1 hx with h1 | h2
            · exact (haccMid x h1).1
            · simp only [List.mem_singleton] at h2; subst h2; exact hcnAfter.1
        rcases hih with ⟨csRest, aBase'', haOutEq, hnextLe, hnextMono, hframeRest, hsubFinal, hreadFinal⟩
        have hstepRun := buildDomListM_step childNs parent c rest aIn aMid cn
          (ArenaEntry.element pns ptag pst pmg) (.inl ⟨pns, ptag, pst, pmg, fun _ => rfl⟩) acc
          rfl hparInMid hcnNotFrag hcnNotInAcc
        dsimp only [aAfterAppend] at haccMid hcnAfter hstepRun ⊢
        simp only [htmlListNodeCount]
        rw [hstepRun]
        refine ⟨cn :: csRest, aBase'', by simpa [List.append_assoc] using haOutEq, by omega, by omega,
                fun m hm hne => by rw [hframeRest m (by omega) hne, DomArena.get_set_ne _ _ hne]; exact haMidFrame m (by omega),
                by simpa [List.append_assoc] using hsubFinal, ?_⟩
        have hmapInit : (acc ++ [cn]).map (readDomTree f (aMid.set parent (.element pns ptag pst pmg (acc ++ [cn])))) =
            acc.map (readDomTree f aIn) ++ [specDom childNs c] := by
          rw [List.map_append, List.map_singleton, hcnAfter.2]
          congr 1; exact List.map_congr_left fun x hx => (haccMid x hx).2
        rw [hmapInit] at hreadFinal
        simpa only [List.append_assoc, specDomList] using hreadFinal
end

theorem buildDomM_not_fragment {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat)
    (fcs : List Dom.Node) (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount h < UInt32.size)
    (hdep : htmlDepth h ≤ fuel) :
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    a'.get root ≠ .fragment fcs := by
  cases h with
  | text s =>
      simp [buildDomM, StateT.run, MonadDom.createText, DomArena.alloc, DomArena.get]
  | element tag attrs cs =>
      have ⟨_, _, _, _, _, hread⟩ := buildDomM_spec ns (.element tag attrs cs) a fuel hpos hbound hdep
      cases fuel with
      | zero => simp [htmlDepth] at hdep
      | succ _ => intro hf; dsimp only [readDomTree] at hread; rw [hf] at hread; cases hread

theorem applyAttrsM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg))
    (node : Dom.Node) (attrs : List (Attr msg)) (a : DomArena msg) :
    (applyAttrsM (m := StateM (DomArena msg)) node attrs { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
      { ((applyAttrsM (m := StateM (DomArena msg)) node attrs).run a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
  have h1 : ∀ (xs : List (Attr msg)) (s : DomArena msg),
      (applyAttrListM (m := StateM (DomArena msg)) node xs { s with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
        { (applyAttrListM (m := StateM (DomArena msg)) node xs s).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons x rest ih =>
        intro s
        dsimp only [applyAttrListM, bind, StateT.bind]
        have hx : (applyAttrM (m := StateM (DomArena msg)) node x { s with signals := sigs, sigEvents := evs, tmpls, rowEvs }) =
            ((), { (applyAttrM (m := StateM (DomArena msg)) node x s).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }) := by
          rw [applyAttrM_eq_modifyElemState, applyAttrM_eq_modifyElemState]
          simp only [DomArena.modifyElemState, DomArena.modify, DomArena.set, DomArena.get]
        have hx2 : (applyAttrM (m := StateM (DomArena msg)) node x { s with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
            { (applyAttrM (m := StateM (DomArena msg)) node x s).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := congrArg Prod.snd hx
        cases hr1 : applyAttrM (m := StateM (DomArena msg)) node x { s with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
        | mk _ s1 =>
            cases hr2 : applyAttrM (m := StateM (DomArena msg)) node x s with
            | mk _ s2 =>
                rw [hr1] at hx2; rw [hr2] at hx2; dsimp only at hx2; rw [hx2]; exact ih s2
  dsimp only [applyAttrsM, StateT.run, bind, StateT.bind]
  let a1 := (MonadDom.retainAttributes (m := StateM (DomArena msg)) node ((normalizeAttrs attrs).filterMap managedAttrName) a).2
  change (applyAttrListM (m := StateM (DomArena msg)) node (normalizeAttrs attrs) { a1 with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
    { (applyAttrListM (m := StateM (DomArena msg)) node (normalizeAttrs attrs) a1).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }
  exact h1 (normalizeAttrs attrs) a1

mutual
  theorem buildDomM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
      (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg)) (ns : String) :
      ∀ (h : Html msg) (a : DomArena msg),
        (buildDomM (m := StateM (DomArena msg)) ns h { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).1 =
          (buildDomM (m := StateM (DomArena msg)) ns h a).1 ∧
        (buildDomM (m := StateM (DomArena msg)) ns h { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
          { (buildDomM (m := StateM (DomArena msg)) ns h a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }
    | .text _, _ => ⟨rfl, rfl⟩
    | .element tag attrs children, a => by
        dsimp only [buildDomM, MonadDom.createElement, DomArena.alloc, bind, StateT.bind, pure, StateT.pure]
        let a0 : DomArena msg := { a with
          nextId := a.nextId + 1
          store := fun m =>
            if m == UInt32.ofNat a.nextId then
              .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []
            else a.store m }
        have ha := applyAttrsM_withSignals sigs evs tmpls rowEvs (UInt32.ofNat a.nextId) attrs a0
        dsimp only [StateT.run] at ha
        cases hr1 : applyAttrsM (m := StateM (DomArena msg)) (UInt32.ofNat a.nextId) attrs { a0 with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
        | mk _ s1 =>
            cases hr2 : applyAttrsM (m := StateM (DomArena msg)) (UInt32.ofNat a.nextId) attrs a0 with
            | mk _ s2 =>
                have hsEq : s1 = { s2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
                  rw [hr1, hr2] at ha; exact ha
                rw [hsEq]
                cases ownsChildren attrs with
                | true => exact ⟨rfl, rfl⟩
                | false =>
                    simp only [Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
                    have hk := buildDomListM_withSignals sigs evs tmpls rowEvs (Dom.childNsOf ns tag) (UInt32.ofNat a.nextId) children s2
                    cases hb1 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) (UInt32.ofNat a.nextId) children { s2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
                    | mk _ b1 =>
                        cases hb2 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) (UInt32.ofNat a.nextId) children s2 with
                        | mk _ b2 =>
                            dsimp only; rw [hb1, hb2] at hk; exact ⟨rfl, hk⟩

  theorem buildDomListM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
      (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg)) (ns : String) (parent : Dom.Node) :
      ∀ (cs : List (Html msg)) (a : DomArena msg),
        (buildDomListM (m := StateM (DomArena msg)) ns parent cs { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
          { (buildDomListM (m := StateM (DomArena msg)) ns parent cs a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }
    | [], _ => rfl
    | c :: rest, a => by
        have hc := buildDomM_withSignals sigs evs tmpls rowEvs ns c a
        dsimp only [buildDomListM, bind, StateT.bind, pure, StateT.pure]
        cases hb1 : buildDomM (m := StateM (DomArena msg)) ns c { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
        | mk cn1 a1 =>
            cases hb2 : buildDomM (m := StateM (DomArena msg)) ns c a with
            | mk cn2 a2 =>
                rw [hb1, hb2] at hc; dsimp only at hc
                rcases hc with ⟨rfl, rfl⟩
                dsimp only
                have happ : (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn1 { a2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
                    { (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn1 a2).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
                  simp only [MonadDom.appendChild, DomArena.get, DomArena.set, DomArena.modifyChildren, DomArena.modify]
                  cases a2.store cn1 <;> rfl
                cases ha1 : MonadDom.appendChild (m := StateM (DomArena msg)) parent cn1 { a2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
                | mk _ s1 =>
                    cases ha2 : MonadDom.appendChild (m := StateM (DomArena msg)) parent cn1 a2 with
                    | mk _ s2 =>
                        dsimp only
                        rw [ha1, ha2] at happ; dsimp only at happ; rw [happ]
                        exact buildDomListM_withSignals sigs evs tmpls rowEvs ns parent rest s2
end

theorem seedRowsM_sameDom {msg : Type} (inst : String) (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg) :
    ((seedRowsM (m := StateM (DomArena msg)) inst rowSig rowEv newMarks oldMarks oldSigs).run a).2.SameDom a := by
  dsimp only [seedRowsM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  cases hd : diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[] with
  | mk _ rest =>
      rcases rest with ⟨toEmit, toEv⟩
      dsimp only
      have he := emitSignalsM_spec toEmit.toList a
      dsimp only [StateT.run] at he
      rw [he]; dsimp only
      have hev := emitSignalOnsM_spec toEv.toList { a with signals := toEmit.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals }
      dsimp only [StateT.run] at hev
      rw [hev]; exact ⟨rfl, rfl⟩

theorem buildDomListM_sameDom {msg : Type} (ns : String) (parent : Dom.Node) (cs : List (Html msg))
    {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (buildDomListM (m := StateM (DomArena msg)) ns parent cs a₁).2.SameDom
      (buildDomListM (m := StateM (DomArena msg)) ns parent cs a₂).2 := by
  have heq : a₁ = { a₂ with signals := a₁.signals, sigEvents := a₁.sigEvents, tmpls := a₁.tmpls, rowEvs := a₁.rowEvs } :=
    DomArena.ext hs.1 hs.2 rfl rfl rfl rfl
  rw [heq, buildDomListM_withSignals a₁.signals a₁.sigEvents a₁.tmpls a₁.rowEvs ns parent cs a₂]
  exact ⟨rfl, rfl⟩

end Qed
