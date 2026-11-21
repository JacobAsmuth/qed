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
  | .attr k v                 =>
      if k == "value" then { st with value := v }
      else { st with attrs := setAssoc k v st.attrs }
  | .flag k present           =>
      if k == "checked" then { st with checked := present }
      else { st with attrs := if present then setAssoc k k st.attrs else eraseAssoc k st.attrs }
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
      by_cases hk : k = "value"
      · subst hk; rfl
      · simp only [applyAttrM, stepSpecAttr, beq_eq_false_iff_ne.2 hk, Bool.false_eq_true, ↓reduceIte]
        rfl
  | flag k p =>
      by_cases hk : k = "checked"
      · subst hk; rfl
      · simp only [applyAttrM, stepSpecAttr, beq_eq_false_iff_ne.2 hk, Bool.false_eq_true, ↓reduceIte]
        cases p <;> rfl
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
      dsimp only [stepSpecAttr]
      by_cases h : (k == "value") = true
      · rw [if_pos h]
        have hk : k = "value" := beq_iff_eq.1 h
        subst hk
        exact ⟨ha, fun _ => hkeep, hc, hcl, hin⟩
      · rw [if_neg h]
        exact ⟨setAssoc_prop hkeep ha, hv, hc, hcl, hin⟩
  | flag k p =>
      dsimp only [stepSpecAttr]
      by_cases h : (k == "checked") = true
      · rw [if_pos h]
        have hk : k = "checked" := beq_iff_eq.1 h
        subst hk
        cases p
        · exact ⟨ha, hv, fun b => absurd b Bool.false_ne_true, hcl, hin⟩
        · exact ⟨ha, hv, fun _ => hkeep, hcl, hin⟩
      · rw [if_neg h]
        cases p
        · exact ⟨eraseAssoc_prop ha, hv, hc, hcl, hin⟩
        · exact ⟨setAssoc_prop hkeep ha, hv, hc, hcl, hin⟩
  | on _ _ => exact ⟨ha, hv, hc, setAssoc_prop (p := fun q => names.contains s!"data-qed-on-{q}") hkeep hcl, hin⟩
  | onValue _ _ => exact ⟨ha, hv, hc, hcl, setAssoc_prop (p := fun q => names.contains s!"data-qed-onv-{q}") hkeep hin⟩
  | localCell _ _ _ _ _ => exact ⟨setAssoc_prop hkeep ha, hv, hc, hcl, hin⟩
  | key _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => exact ⟨ha, hv, hc, hcl, hin⟩

inductive AttrSlot where
  | attr (k : String) | val | chk | click (e : String) | input (e : String)

inductive SlotVal (msg : Type) where
  | optStr (v : Option String) | str (v : String) | bool (v : Bool)
  | optMsg (v : Option msg) | optFn (v : Option (String → msg))

def AttrSlot.read {msg : Type} (st : SpecElemState msg) : AttrSlot → SlotVal msg
  | .attr k  => .optStr (lookupAssoc k st.attrs)
  | .val     => .str st.value
  | .chk     => .bool st.checked
  | .click e => .optMsg (lookupAssoc e st.clicks)
  | .input e => .optFn (lookupAssoc e st.inputs)

def AttrSlot.managedName : AttrSlot → String
  | .attr k  => k
  | .val     => "value"
  | .chk     => "checked"
  | .click e => s!"data-qed-on-{e}"
  | .input e => s!"data-qed-onv-{e}"

def Attr.slotUpdate? {msg : Type} : Attr msg → AttrSlot → Option (SlotVal msg)
  | .cls s, .attr k => if "class" == k then some (.optStr (some s)) else none
  | .localCell k comp _ _ _, .attr k' => if "data-qed-local" == k' then some (.optStr (some (localKey comp k))) else none
  | .attr k' v, .val => if k' == "value" then some (.str v) else none
  | .attr k' v, .attr k => if k' != "value" && k' == k then some (.optStr (some v)) else none
  | .flag k' p, .chk => if k' == "checked" then some (.bool p) else none
  | .flag k' p, .attr k => if k' != "checked" && k' == k then some (.optStr (if p then some k' else none)) else none
  | .on e' m, .click e => if e' == e then some (.optMsg (some m)) else none
  | .onValue e' f, .input e => if e' == e then some (.optFn (some f)) else none
  | _, _ => none

theorem ElemStateEquiv_iff {msg : Type} {st₁ st₂ : SpecElemState msg} :
    ElemStateEquiv st₁ st₂ ↔ ∀ sl : AttrSlot, sl.read st₁ = sl.read st₂ :=
  ⟨fun h sl => by cases sl with
    | attr k => exact congrArg SlotVal.optStr (h.1 k)
    | val => exact congrArg SlotVal.str h.2.1
    | chk => exact congrArg SlotVal.bool h.2.2.1
    | click e => exact congrArg SlotVal.optMsg (h.2.2.2.1 e)
    | input e => exact congrArg SlotVal.optFn (h.2.2.2.2 e),
   fun h => ⟨fun k => SlotVal.optStr.inj (h (.attr k)), SlotVal.str.inj (h .val),
     SlotVal.bool.inj (h .chk), fun e => SlotVal.optMsg.inj (h (.click e)),
     fun e => SlotVal.optFn.inj (h (.input e))⟩⟩

theorem read_stepSpecAttr (st : SpecElemState msg) (a : Attr msg) (sl : AttrSlot) :
    sl.read (stepSpecAttr st a) = (a.slotUpdate? sl).getD (sl.read st) := by
  cases a with
  | cls s => cases sl <;> simp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?, lookupAssoc_setAssoc, Option.getD_none] <;> split <;> rfl
  | localCell k comp _ _ _ => cases sl <;> simp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?, lookupAssoc_setAssoc, Option.getD_none] <;> split <;> rfl
  | attr k' v =>
      dsimp only [stepSpecAttr]; by_cases hv : (k' == "value") = true
      · have hk' : k' = "value" := beq_iff_eq.1 hv; subst hk'
        cases sl <;> simp [AttrSlot.read, Attr.slotUpdate?]
      · have hvf : (k' == "value") = false := Bool.eq_false_iff.2 hv
        cases sl <;> simp only [AttrSlot.read, Attr.slotUpdate?, hvf, bne, Bool.not_false, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, Option.getD_none] <;> split <;> rfl
  | flag k' p =>
      dsimp only [stepSpecAttr]; by_cases hc : (k' == "checked") = true
      · have hk' : k' = "checked" := beq_iff_eq.1 hc; subst hk'
        cases sl <;> simp [AttrSlot.read, Attr.slotUpdate?]
      · have hcf : (k' == "checked") = false := Bool.eq_false_iff.2 hc
        cases sl with
        | attr k =>
            cases p <;> simp only [AttrSlot.read, Attr.slotUpdate?, hcf, bne, Bool.not_false, Bool.true_and,
              Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc] <;> split <;> rfl
        | val | chk | click _ | input _ =>
            cases p <;> simp [AttrSlot.read, Attr.slotUpdate?, hcf]
  | on e' m => cases sl <;> simp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?, lookupAssoc_setAssoc, Option.getD_none] <;> split <;> rfl
  | onValue e' f => cases sl <;> simp only [stepSpecAttr, AttrSlot.read, Attr.slotUpdate?, lookupAssoc_setAssoc, Option.getD_none] <;> split <;> rfl
  | key _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => cases sl <;> rfl

theorem stepSpecAttr_equiv {msg : Type} {s₁ s₂ : SpecElemState msg} (a : Attr msg)
    (he : ElemStateEquiv s₁ s₂) : ElemStateEquiv (stepSpecAttr s₁ a) (stepSpecAttr s₂ a) :=
  ElemStateEquiv_iff.2 fun sl => by rw [read_stepSpecAttr, read_stepSpecAttr, ElemStateEquiv_iff.1 he sl]

theorem foldl_stepSpecAttr_read (sl : AttrSlot) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      ((∃ a ∈ xs, (a.slotUpdate? sl).isSome = true) ∨ sl.read s₁ = sl.read s₂) →
      sl.read (xs.foldl stepSpecAttr s₁) = sl.read (xs.foldl stepSpecAttr s₂)
  | [], _, _, .inl ⟨_, h, _⟩ => nomatch h
  | [], _, _, .inr h => h
  | x :: rest, s₁, s₂, h => by
      simp only [List.foldl_cons]
      apply foldl_stepSpecAttr_read sl rest
      cases hx : x.slotUpdate? sl with
      | some v => exact .inr (by rw [read_stepSpecAttr, read_stepSpecAttr, hx]; rfl)
      | none =>
          rcases h with ⟨a, ha, hwa⟩ | heq
          · rcases List.mem_cons.1 ha with rfl | hmem
            · rw [hx] at hwa; cases hwa
            · exact .inl ⟨a, hmem, hwa⟩
          · exact .inr (by rw [read_stepSpecAttr, read_stepSpecAttr, hx]; exact heq)

private theorem attrWritesKey_iff_slotUpdate {k : String} {x : Attr msg} :
    attrWritesKey k x = true ↔ (x.slotUpdate? (.attr k)).isSome = true := by
  cases x with
  | cls _ =>
      dsimp only [attrWritesKey, Attr.slotUpdate?]
      by_cases h : k = "class"
      · subst h; simp
      · simp [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 (Ne.symm h)]
  | localCell _ _ _ _ _ =>
      dsimp only [attrWritesKey, Attr.slotUpdate?]
      by_cases h : k = "data-qed-local"
      · subst h; simp
      · simp [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 (Ne.symm h)]
  | attr k' _ | flag k' _ =>
      dsimp only [attrWritesKey, Attr.slotUpdate?]; split <;> simp [*]
  | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
      simp [attrWritesKey, Attr.slotUpdate?]

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

private theorem retainScalar_eq_default {α : Type} {dflt cur : α} {prev names : List String} {k : String}
    (hm : cur ≠ dflt → prev.contains k = true)
    (hns : names.contains k = true → cur = dflt) :
    (if prev.contains k && !names.contains k then dflt else cur) = dflt := by
  by_cases hn : names.contains k = true
  · simp only [hn, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; exact hns hn
  · by_cases hcur : cur = dflt
    · simp only [hcur, ite_self]
    · simp only [hm hcur, Bool.eq_false_iff.2 hn, Bool.not_false, Bool.and_self, ↓reduceIte]

private theorem retainScalar_managed {α : Type} {dflt cur : α} {prev names : List String} {k : String}
    (hm : cur ≠ dflt → prev.contains k = true)
    (hne : (if prev.contains k && !names.contains k then dflt else cur) ≠ dflt) :
    names.contains k = true := by
  by_cases hn : names.contains k = true
  · exact hn
  · exact absurd (retainScalar_eq_default hm fun h => absurd h hn) hne

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
  have hmChk : st.checked ≠ false → prev.contains "checked" = true := fun h => hm.2.2.1 (by cases hst : st.checked <;> simp_all)
  rw [applyAttrListM_element norm a node ns tag st0 names cs, DomArena.get_set_self]
  refine ⟨norm.foldl stepSpecAttr st0, rfl, ElemStateEquiv_iff.2 fun sl => foldl_stepSpecAttr_read sl norm st0 {} ?_, ?_⟩
  · cases sl with
    | attr k =>
        by_cases hw : ∃ x ∈ norm, attrWritesKey k x = true
        · rcases hw with ⟨x, hx, hwx⟩; exact .inl ⟨x, hx, attrWritesKey_iff_slotUpdate.1 hwx⟩
        · exact .inr (congrArg SlotVal.optStr (filter_managed_lookup_none (keyFn := id) hm.1 k fun hn => (hNoShadow.1 k hn).resolve_left hw))
    | val =>
        by_cases hv : ∃ v, .attr "value" v ∈ norm
        · rcases hv with ⟨v, hv⟩; exact .inl ⟨.attr "value" v, hv, rfl⟩
        · exact .inr (congrArg SlotVal.str (retainScalar_eq_default hm.2.1 fun hnv => (hNoShadow.2.1 hnv).resolve_left hv))
    | chk =>
        by_cases hc : ∃ p, .flag "checked" p ∈ norm
        · rcases hc with ⟨p, hp⟩; exact .inl ⟨.flag "checked" p, hp, rfl⟩
        · exact .inr (congrArg SlotVal.bool (retainScalar_eq_default hmChk fun hnc => (hNoShadow.2.2.1 hnc).resolve_left hc))
    | click e =>
        by_cases hcl : ∃ m, .on e m ∈ norm
        · rcases hcl with ⟨m, hm'⟩; exact .inl ⟨.on e m, hm', by simp [Attr.slotUpdate?]⟩
        · exact .inr (congrArg SlotVal.optMsg (filter_managed_lookup_none (keyFn := fun e => s!"data-qed-on-{e}") hm.2.2.2.1 e
            fun hn => (hNoShadow.2.2.2.1 e hn).resolve_left hcl))
    | input e =>
        by_cases hin : ∃ f, .onValue e f ∈ norm
        · rcases hin with ⟨f, hf⟩; exact .inl ⟨.onValue e f, hf, by simp [Attr.slotUpdate?]⟩
        · exact .inr (congrArg SlotVal.optFn (filter_managed_lookup_none (keyFn := fun e => s!"data-qed-onv-{e}") hm.2.2.2.2 e
            fun hn => (hNoShadow.2.2.2.2 e hn).resolve_left hin))
  · exact ElemManaged_foldl_norm newAttrs st0
      ⟨filter_managed_prop (keyFn := id) hm.1,
       fun hne => retainScalar_managed hm.2.1 hne,
       fun hchk => retainScalar_managed hmChk (fun hf => Bool.false_ne_true (hf.symm.trans hchk)),
       filter_managed_prop (keyFn := fun e => s!"data-qed-on-{e}") hm.2.2.2.1,
       filter_managed_prop (keyFn := fun e => s!"data-qed-onv-{e}") hm.2.2.2.2⟩

def isSpecialManagedKey (k : String) : Bool :=
  k == "value" || k == "checked" ||
  k.startsWith "data-qed-on-" || k.startsWith "data-qed-onv-" || k == "data-qed-signal"

def Attr.DomClean : Attr msg → Bool
  | .attr k _         => k == "value" || !isSpecialManagedKey k
  | .flag k _         => k == "checked" || !isSpecialManagedKey k
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

private theorem startsWith_append_self (p e : String) : (p ++ e).startsWith p = true := by
  simp [String.startsWith]

private theorem append_ne_of_not_startsWith {p e s : String} (h : s.startsWith p = false) : p ++ e ≠ s :=
  fun heq => by rw [← heq, startsWith_append_self] at h; cases h

private theorem on_ne_onv {e₁ e₂ : String} : "data-qed-on-" ++ e₁ ≠ "data-qed-onv-" ++ e₂ := fun heq => by
  have h := congrArg (fun s => (s.toList.drop 11).head?) heq
  dsimp only at h
  have h1 : ("data-qed-on-").toList = ['d','a','t','a','-','q','e','d','-','o','n','-'] := rfl
  have h2 : ("data-qed-onv-").toList = ['d','a','t','a','-','q','e','d','-','o','n','v','-'] := rfl
  rw [String.toList_append, String.toList_append, h1, h2] at h
  cases h

private theorem isSpecialManagedKey_on (e : String) : isSpecialManagedKey ("data-qed-on-" ++ e) = true := by
  simp only [isSpecialManagedKey, startsWith_append_self, Bool.or_true, Bool.true_or]

private theorem isSpecialManagedKey_onv (e : String) : isSpecialManagedKey ("data-qed-onv-" ++ e) = true := by
  simp only [isSpecialManagedKey, startsWith_append_self, Bool.or_true, Bool.true_or]

private theorem isSpecialManagedKey_signal : isSpecialManagedKey "data-qed-signal" = true := by
  simp only [isSpecialManagedKey, beq_self_eq_true, Bool.or_true]

private theorem isSpecialManagedKey_local_false : isSpecialManagedKey "data-qed-local" = false := by
  simp [isSpecialManagedKey, String.startsWith]

private theorem isSpecialManagedKey_class_false : isSpecialManagedKey "class" = false := by
  simp [isSpecialManagedKey, String.startsWith]

private theorem managedAttrName_clean_slot {x : Attr msg} {sl : AttrSlot}
    (hxc : x.DomClean = true) (hname : managedAttrName x = some sl.managedName) :
    (x.slotUpdate? sl).isSome = true ∨ (∃ k, sl = .attr k ∧ isSpecialManagedKey k = true) := by
  have hnotSp : ∀ {s : String}, isSpecialManagedKey s = false → sl.managedName = s → sl = .attr s := fun {s} hs h => by
    cases sl with
    | attr k => exact congrArg AttrSlot.attr h
    | val | chk => rw [← h] at hs; cases hs
    | click e => have : isSpecialManagedKey s = true := h ▸ isSpecialManagedKey_on e; rw [this] at hs; cases hs
    | input e => have : isSpecialManagedKey s = true := h ▸ isSpecialManagedKey_onv e; rw [this] at hs; cases hs
  cases x with
  | cls _ =>
      simp only [managedAttrName, Option.some.injEq] at hname
      have hsl := hnotSp isSpecialManagedKey_class_false hname.symm
      subst hsl; exact .inl rfl
  | localCell _ _ _ _ _ =>
      simp only [managedAttrName, Option.some.injEq] at hname
      have hsl := hnotSp isSpecialManagedKey_local_false hname.symm
      subst hsl; exact .inl rfl
  | attr k' v =>
      simp only [managedAttrName, Option.some.injEq] at hname
      by_cases hsp : isSpecialManagedKey k' = true
      · simp only [Attr.DomClean, hsp, Bool.not_true, Bool.or_false, beq_iff_eq] at hxc
        subst hxc; cases sl with
        | val => exact .inl rfl
        | attr k => dsimp only [AttrSlot.managedName] at hname; exact .inr ⟨k, rfl, hname ▸ hsp⟩
        | chk => exact absurd hname (by decide)
        | click e => exact absurd hname.symm (append_ne_of_not_startsWith (by simp [String.startsWith]))
        | input e => exact absurd hname.symm (append_ne_of_not_startsWith (by simp [String.startsWith]))
      · have hsl := hnotSp (Bool.eq_false_iff.2 hsp) hname.symm
        subst hsl; have hnv : (k' == "value") = false := beq_eq_false_iff_ne.2 fun h => hsp (h ▸ rfl)
        exact .inl (by simp [Attr.slotUpdate?, bne, hnv])
  | flag k' p =>
      simp only [managedAttrName, Option.some.injEq] at hname
      by_cases hsp : isSpecialManagedKey k' = true
      · simp only [Attr.DomClean, hsp, Bool.not_true, Bool.or_false, beq_iff_eq] at hxc
        subst hxc; cases sl with
        | chk => exact .inl rfl
        | attr k => dsimp only [AttrSlot.managedName] at hname; exact .inr ⟨k, rfl, hname ▸ hsp⟩
        | val => exact absurd hname (by decide)
        | click e => exact absurd hname.symm (append_ne_of_not_startsWith (by simp [String.startsWith]))
        | input e => exact absurd hname.symm (append_ne_of_not_startsWith (by simp [String.startsWith]))
      · have hsl := hnotSp (Bool.eq_false_iff.2 hsp) hname.symm
        subst hsl; have hnc : (k' == "checked") = false := beq_eq_false_iff_ne.2 fun h => hsp (h ▸ rfl)
        exact .inl (by simp [Attr.slotUpdate?, bne, hnc])
  | on e' _ =>
      simp only [managedAttrName, Option.some.injEq, toString] at hname
      cases sl with
      | click e => dsimp only [AttrSlot.managedName, toString] at hname; have he := string_append_left_cancel hname; subst he; exact .inl (by simp [Attr.slotUpdate?])
      | attr k => dsimp only [AttrSlot.managedName] at hname; exact .inr ⟨k, rfl, hname ▸ isSpecialManagedKey_on e'⟩
      | val | chk => dsimp only [AttrSlot.managedName] at hname; exact absurd hname (append_ne_of_not_startsWith (by simp [String.startsWith]))
      | input _ => dsimp only [AttrSlot.managedName, toString] at hname; exact absurd hname on_ne_onv
  | onValue e' _ =>
      simp only [managedAttrName, Option.some.injEq, toString] at hname
      cases sl with
      | input e => dsimp only [AttrSlot.managedName, toString] at hname; have he := string_append_left_cancel hname; subst he; exact .inl (by simp [Attr.slotUpdate?])
      | attr k => dsimp only [AttrSlot.managedName] at hname; exact .inr ⟨k, rfl, hname ▸ isSpecialManagedKey_onv e'⟩
      | val | chk => dsimp only [AttrSlot.managedName] at hname; exact absurd hname (append_ne_of_not_startsWith (by simp [String.startsWith]))
      | click _ => dsimp only [AttrSlot.managedName, toString] at hname; exact absurd hname.symm on_ne_onv
  | signalBind _ =>
      simp only [managedAttrName, Option.some.injEq] at hname
      cases sl with
      | attr k => dsimp only [AttrSlot.managedName] at hname; exact .inr ⟨k, rfl, hname ▸ isSpecialManagedKey_signal⟩
      | val | chk => exact absurd hname (by decide)
      | click _ | input _ => dsimp only [AttrSlot.managedName, toString] at hname; exact absurd hname.symm (append_ne_of_not_startsWith (by simp [String.startsWith]))
  | key _ => cases hname
  | signalAttr _ _ _ | signalOn _ _ _ => cases hxc

theorem AttrsNoShadow_of_clean {newAttrs : List (Attr msg)} {st : SpecElemState msg} {prev : List String}
    (hst : ElemClean st prev) (hc : newAttrs.all Attr.DomClean = true) :
    AttrsNoShadow newAttrs st := by
  have hnorm := mem_normalizeAttrs_DomClean hc
  have hfind : ∀ (sl : AttrSlot),
      ((normalizeAttrs newAttrs).filterMap managedAttrName).contains sl.managedName = true →
      (∃ x ∈ normalizeAttrs newAttrs, (x.slotUpdate? sl).isSome = true) ∨
        (∃ k, sl = .attr k ∧ isSpecialManagedKey k = true) := fun sl hmem => by
    rcases List.mem_filterMap.1 (List.contains_iff_mem.1 hmem) with ⟨x, hxMem, hxName⟩
    exact (managedAttrName_clean_slot (hnorm x hxMem) hxName).imp (fun h => ⟨x, hxMem, h⟩) id
  refine ⟨fun k hk => ?_, fun hval => ?_, fun hchk => ?_, fun e hev => ?_, fun e hinp => ?_⟩
  · rcases hfind (.attr k) hk with ⟨x, hx, hwx⟩ | ⟨_, hEq, hsp⟩
    · exact .inl ⟨x, hx, attrWritesKey_iff_slotUpdate.2 hwx⟩
    · cases hEq; exact .inr (hst.2 k hsp)
  · rcases hfind .val hval with ⟨x, hx, hwx⟩ | ⟨_, h, _⟩
    · cases x with
      | attr k' v => simp only [Attr.slotUpdate?] at hwx; split at hwx <;> simp_all only [Option.isSome_some, Option.isSome_none, beq_iff_eq, Bool.false_eq_true]; exact .inl ⟨v, hx⟩
      | _ => cases hwx
    · cases h
  · rcases hfind .chk hchk with ⟨x, hx, hwx⟩ | ⟨_, h, _⟩
    · cases x with
      | flag k' p => simp only [Attr.slotUpdate?] at hwx; split at hwx <;> simp_all only [Option.isSome_some, Option.isSome_none, beq_iff_eq, Bool.false_eq_true]; exact .inl ⟨p, hx⟩
      | _ => cases hwx
    · cases h
  · rcases hfind (.click e) hev with ⟨x, hx, hwx⟩ | ⟨_, h, _⟩
    · cases x with
      | on e' m => simp only [Attr.slotUpdate?] at hwx; split at hwx <;> simp_all only [Option.isSome_some, Option.isSome_none, beq_iff_eq, Bool.false_eq_true]; exact .inl ⟨m, hx⟩
      | _ => cases hwx
    · cases h
  · rcases hfind (.input e) hinp with ⟨x, hx, hwx⟩ | ⟨_, h, _⟩
    · cases x with
      | onValue e' f => simp only [Attr.slotUpdate?] at hwx; split at hwx <;> simp_all only [Option.isSome_some, Option.isSome_none, beq_iff_eq, Bool.false_eq_true]; exact .inl ⟨f, hx⟩
      | _ => cases hwx
    · cases h

theorem stepSpecAttr_preserves_clean (s : SpecElemState msg) (a : Attr msg)
    (hca : a.DomClean = true) (hcs : ∀ k, isSpecialManagedKey k = true → lookupAssoc k s.attrs = none) :
    ∀ k, isSpecialManagedKey k = true → lookupAssoc k (stepSpecAttr s a).attrs = none := fun k hk => by
  have hnone : a.slotUpdate? (.attr k) = none := by
    cases a with
    | attr k' _ =>
        simp only [Attr.slotUpdate?]; split
        · rename_i h; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h; rcases h with ⟨hne, rfl⟩
          simp only [Attr.DomClean, beq_eq_false_iff_ne.2 hne, Bool.false_or, hk, Bool.not_true] at hca; cases hca
        · rfl
    | flag k' _ =>
        simp only [Attr.slotUpdate?]; split
        · rename_i h; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h; rcases h with ⟨hne, rfl⟩
          simp only [Attr.DomClean, beq_eq_false_iff_ne.2 hne, Bool.false_or, hk, Bool.not_true] at hca; cases hca
        · rfl
    | cls _ =>
        have hne : ("class" == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; cases isSpecialManagedKey_class_false.symm.trans hk
        simp only [Attr.slotUpdate?, hne, Bool.false_eq_true, ↓reduceIte]
    | localCell _ _ _ _ _ =>
        have hne : ("data-qed-local" == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; cases isSpecialManagedKey_local_false.symm.trans hk
        simp only [Attr.slotUpdate?, hne, Bool.false_eq_true, ↓reduceIte]
    | key _ | on _ _ | onValue _ _ | signalBind _ => rfl
    | signalAttr _ _ _ | signalOn _ _ _ => cases hca
  have hr := read_stepSpecAttr s a (.attr k); rw [hnone] at hr
  exact (SlotVal.optStr.inj hr).trans (hcs k hk)

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
  theorem DomTreeAssocEquiv.refl {msg : Type} : (t : DomTree msg) → DomTreeAssocEquiv t t
    | .text _ => rfl
    | .element _ _ st cs => ⟨rfl, rfl, ElemStateEquiv.refl st, DomTreeListAssocEquiv.refl cs⟩

  theorem DomTreeListAssocEquiv.refl {msg : Type} : (cs : List (DomTree msg)) → DomTreeListAssocEquiv cs cs
    | [] => trivial
    | c :: cs => ⟨DomTreeAssocEquiv.refl c, DomTreeListAssocEquiv.refl cs⟩
end

mutual
  theorem DomTreeAssocEquiv.symm {msg : Type} : {t₁ t₂ : DomTree msg} → DomTreeAssocEquiv t₁ t₂ → DomTreeAssocEquiv t₂ t₁
    | .text _, .text _, h => Eq.symm h
    | .element _ _ _ _, .element _ _ _ _, ⟨h1, h2, hst, hcs⟩ =>
        ⟨Eq.symm h1, Eq.symm h2, hst.symm, DomTreeListAssocEquiv.symm hcs⟩
    | .text _, .element _ _ _ _, h | .element _ _ _ _, .text _, h => False.elim h

  theorem DomTreeListAssocEquiv.symm {msg : Type} : {xs ys : List (DomTree msg)} → DomTreeListAssocEquiv xs ys → DomTreeListAssocEquiv ys xs
    | [], [], _ => trivial
    | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨DomTreeAssocEquiv.symm h1, DomTreeListAssocEquiv.symm h2⟩
    | [], _ :: _, h | _ :: _, [], h => False.elim h
end

mutual
  theorem DomTreeAssocEquiv.trans {msg : Type} : {t₁ t₂ t₃ : DomTree msg} →
      DomTreeAssocEquiv t₁ t₂ → DomTreeAssocEquiv t₂ t₃ → DomTreeAssocEquiv t₁ t₃
    | .text _, .text _, .text _, h1, h2 => Eq.trans h1 h2
    | .element _ _ _ _, .element _ _ _ _, .element _ _ _ _, ⟨hns1, ht1, hst1, hcs1⟩, ⟨hns2, ht2, hst2, hcs2⟩ =>
        ⟨Eq.trans hns1 hns2, Eq.trans ht1 ht2, hst1.trans hst2, DomTreeListAssocEquiv.trans hcs1 hcs2⟩
    | .text _, .text _, .element _ _ _ _, _, h2 | .element _ _ _ _, .element _ _ _ _, .text _, _, h2 => False.elim h2
    | .text _, .element _ _ _ _, _, h1, _ | .element _ _ _ _, .text _, _, h1, _ => False.elim h1

  theorem DomTreeListAssocEquiv.trans {msg : Type} : {xs ys zs : List (DomTree msg)} →
      DomTreeListAssocEquiv xs ys → DomTreeListAssocEquiv ys zs → DomTreeListAssocEquiv xs zs
    | [], [], [], _, _ => trivial
    | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ =>
        ⟨DomTreeAssocEquiv.trans h1 h3, DomTreeListAssocEquiv.trans h2 h4⟩
    | [], [], _ :: _, _, h2 | _ :: _, _ :: _, [], _, h2 => False.elim h2
    | [], _ :: _, _, h1, _ | _ :: _, [], _, h1, _ => False.elim h1
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

theorem stateM_bind_eq {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (StateT.bind m f) s = f (m s).1 (m s).2 := rfl

theorem stateM_bind_step {σ α β : Type} {m : StateM σ α} {f : α → StateM σ β} {s s' : σ} {v : α}
    (h : m s = (v, s')) : (StateT.bind m f) s = f v s' := by
  change f (m s).1 (m s).2 = _; rw [h]

theorem stateM_pure_run {σ α : Type} (x : α) (s : σ) :
    (StateT.pure x : StateM σ α) s = (x, s) := rfl

/-! ## `ArenaExt` Framing & `CleanDomSubtree` / `CleanDomChildren` -/

structure ArenaExt {msg : Type} (a a' : DomArena msg) (W : Nat → Prop) (budget : Nat) : Prop where
  next_ge : a.nextId ≤ a'.nextId
  next_le : a'.nextId ≤ a.nextId + budget
  frame   : ∀ m : Dom.Node, m.toNat < a.nextId → ¬ W m.toNat → a'.get m = a.get m

theorem ArenaExt.refl {msg : Type} (a : DomArena msg) (W : Nat → Prop) (budget : Nat := 0) :
    ArenaExt a a W budget :=
  ⟨Nat.le_refl _, Nat.le_add_right _ _, fun _ _ _ => rfl⟩

theorem ArenaExt.of_set {msg : Type} {a : DomArena msg} {n : Dom.Node} {e : ArenaEntry msg}
    {W : Nat → Prop} (hW : W n.toNat) : ArenaExt a (a.set n e) W 0 :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ hnW =>
    DomArena.get_set_ne _ _ fun heq => hnW (heq ▸ hW)⟩

theorem ArenaExt.mono {msg : Type} {a a' : DomArena msg} {W₁ W₂ : Nat → Prop} {b₁ b₂ : Nat}
    (h : ArenaExt a a' W₁ b₁) (hW : ∀ k, W₁ k → W₂ k) (hb : b₁ ≤ b₂) :
    ArenaExt a a' W₂ b₂ :=
  ⟨h.next_ge, Nat.le_trans h.next_le (Nat.add_le_add_left hb _),
   fun m hm hnW => h.frame m hm fun hw => hnW (hW _ hw)⟩

theorem ArenaExt.trans {msg : Type} {a₁ a₂ a₃ : DomArena msg} {W₁ W₂ W : Nat → Prop} {b₁ b₂ b : Nat}
    (h1 : ArenaExt a₁ a₂ W₁ b₁) (h2 : ArenaExt a₂ a₃ W₂ b₂)
    (hW1 : ∀ k, W₁ k → W k) (hW2 : ∀ k, k < a₁.nextId → W₂ k → W k) (hb : b₁ + b₂ ≤ b) :
    ArenaExt a₁ a₃ W b :=
  ⟨Nat.le_trans h1.next_ge h2.next_ge,
   Nat.le_trans h2.next_le (by have := h1.next_le; omega),
   fun m hm hnW =>
     (h2.frame m (Nat.lt_of_lt_of_le hm h1.next_ge) fun hw2 => hnW (hW2 _ hm hw2)).trans
       (h1.frame m hm fun hw1 => hnW (hW1 _ hw1))⟩

theorem ArenaExt.sameDom {msg : Type} {a₁ a₂ a₃ : DomArena msg} {W : Nat → Prop} {b : Nat}
    (h : ArenaExt a₁ a₂ W b) (hs : a₃.SameDom a₂) : ArenaExt a₁ a₃ W b :=
  ⟨hs.1 ▸ h.next_ge, hs.1 ▸ h.next_le, fun m hm hnW => (hs.get_eq m).trans (h.frame m hm hnW)⟩

theorem ArenaExt.frame_pred {msg : Type} {a a' : DomArena msg} {W S : Nat → Prop} {b : Nat}
    (h : ArenaExt a a' W b) (hS : ∀ k, S k → k < a.nextId ∧ ¬ W k) :
    ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m :=
  fun m hm => let ⟨hlt, hnW⟩ := hS m.toNat hm; h.frame m hlt hnW

mutual
  def CleanDomSubtree {msg : Type} : Nat → String → Html msg → DomArena msg → (Nat → Prop) → Dom.Node → Prop
    | 0, _, _, _, _, _ => False
    | _ + 1, _, .text s, a, S, n => S n.toNat ∧ a.get n = .text s
    | f + 1, ns, .element tag attrs cs, a, S, n =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        S n.toNat ∧ ownsChildren attrs = false ∧ attrs.all Attr.DomClean = true ∧
        ∃ st mg domCs, a.get n = .element realNs tag st mg domCs ∧
          ElemClean st mg ∧ ElemStateEquiv st (evalSpecAttrs attrs) ∧
          (∀ nm ∈ (normalizeAttrs attrs).filterMap managedAttrName, mg.contains nm = true) ∧
          CleanDomChildren f (Dom.childNsOf ns tag) cs a (fun k => S k ∧ k ≠ n.toNat) domCs

  def CleanDomChildren {msg : Type} : Nat → String → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
    | _, _, [], _, _, [] => True
    | f, ns, c :: cs, a, S, d :: ds =>
        ∃ Sc Srest, (∀ k, Sc k → S k) ∧ (∀ k, Srest k → S k) ∧ (∀ k, Sc k → Srest k → False) ∧
          CleanDomSubtree f ns c a Sc d ∧ CleanDomChildren f ns cs a Srest ds
    | _, _, _, _, _, _ => False
end

theorem CleanDomSubtree_root_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → S n.toNat
  | 0, _, _, _, _, _, h => by simp [CleanDomSubtree] at h
  | _ + 1, _, .text _, _, _, _, h => h.1
  | _ + 1, _, .element _ _ _, _, _, _, h => h.1

theorem CleanDomChildren_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ∀ d ∈ ds, S d.toNat
  | _, _, [], _, _, [], _ => fun _ hm => nomatch hm
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, hSc, hSr, _, hHd, hTl⟩ => fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hr
      · exact hSc _ (CleanDomSubtree_root_mem hHd)
      · exact hSr _ (CleanDomChildren_mem hTl d hr)
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

theorem CleanDomChildren_nodup {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ds.Nodup ∧ ds.length = cs.length
  | _, _, [], _, _, [], _ => ⟨List.nodup_nil, rfl⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, _, _, hDisj, hHd, hTl⟩ => by
      have ⟨hnd, hlen⟩ := CleanDomChildren_nodup hTl
      exact ⟨List.nodup_cons.2 ⟨fun hm => hDisj _ (CleanDomSubtree_root_mem hHd) (CleanDomChildren_mem hTl _ hm), hnd⟩, by simp [hlen]⟩
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

theorem CleanDomChildren_mono {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S S' : Nat → Prop} {ds : List Dom.Node},
      (∀ k, S k → S' k) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a S' ds
  | _, _, [], _, _, _, [], _, _ => trivial
  | _, _, _ :: _, _, _, _, _ :: _, hsub, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
      ⟨Sc, Srest, fun k hk => hsub k (hSc k hk), fun k hk => hsub k (hSr k hk), hDisj, hHd, hTl⟩
  | _, _, [], _, _, _, _ :: _, _, hc => False.elim hc
  | _, _, _ :: _, _, _, _, [], _, hc => False.elim hc

theorem CleanDomSubtree_mono {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S S' : Nat → Prop} {n : Dom.Node},
      (∀ k, S k → S' k) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a S' n
  | 0, _, _, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, _, hsub, ⟨hn, hg⟩ => ⟨hsub _ hn, hg⟩
  | _ + 1, _, .element _ _ _, _, _, _, _, hsub, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
      ⟨hsub _ hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, CleanDomChildren_mono (fun _ hk => ⟨hsub _ hk.1, hk.2⟩) hcs⟩

private theorem cleanDomChildren_frame_of {msg : Type} {f : Nat} {a a' : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a' S ds
  | _, [], _, [], _, _ => trivial
  | _, _ :: _, _, _ :: _, hfr, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
      ⟨Sc, Srest, hSc, hSr, hDisj,
       hSub (fun m hm => hfr m (hSc _ hm)) hHd,
       cleanDomChildren_frame_of hSub (fun m hm => hfr m (hSr _ hm)) hTl⟩
  | _, [], _, _ :: _, _, hc => False.elim hc
  | _, _ :: _, _, [], _, hc => False.elim hc

theorem CleanDomSubtree_frame {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n
  | 0, _, _, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, n, hfr, ⟨hn, hg⟩ => ⟨hn, (hfr n hn).trans hg⟩
  | _ + 1, _, .element _ _ _, _, _, _, n, hfr, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
      ⟨hn, ho, ha, st, mg, domCs, (hfr n hn).trans hg, hcl, heq, hmg,
       cleanDomChildren_frame_of (fun hfr' h => CleanDomSubtree_frame hfr' h) (fun m hm => hfr m hm.1) hcs⟩

theorem CleanDomChildren_frame {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)} {a a' : DomArena msg}
    {S : Nat → Prop} {ds : List Dom.Node}
    (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) (h : CleanDomChildren f ns cs a S ds) :
    CleanDomChildren f ns cs a' S ds :=
  cleanDomChildren_frame_of (fun hfr' h' => CleanDomSubtree_frame hfr' h') hfr h

theorem ArenaExt.frame_cleanSubtree {msg : Type} {f : Nat} {ns : String} {h : Html msg}
    {a a' : DomArena msg} {W S : Nat → Prop} {b : Nat} {n : Dom.Node}
    (hext : ArenaExt a a' W b) (hS : ∀ k, S k → k < a.nextId ∧ ¬ W k) (hcl : CleanDomSubtree f ns h a S n) :
    CleanDomSubtree f ns h a' S n :=
  CleanDomSubtree_frame (hext.frame_pred hS) hcl

theorem ArenaExt.frame_cleanChildren {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)}
    {a a' : DomArena msg} {W S : Nat → Prop} {b : Nat} {ds : List Dom.Node}
    (hext : ArenaExt a a' W b) (hS : ∀ k, S k → k < a.nextId ∧ ¬ W k) (hcl : CleanDomChildren f ns cs a S ds) :
    CleanDomChildren f ns cs a' S ds :=
  CleanDomChildren_frame (hext.frame_pred hS) hcl

private theorem cleanDomChildren_equiv_of {msg : Type} {f : Nat} {a : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs)
  | _, [], _, [], _ => trivial
  | _, _ :: _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => ⟨hSub hHd, cleanDomChildren_equiv_of hSub hTl⟩
  | _, [], _, _ :: _, hc => False.elim hc
  | _, _ :: _, _, [], hc => False.elim hc

theorem CleanDomSubtree_equiv {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)
  | 0, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, ⟨_, hg⟩ => by
      dsimp only [readDomTree, specDom, DomTreeAssocEquiv]; rw [hg]; rfl
  | _ + 1, _, .element _ _ _, _, _, _, ⟨_, ho, _, _, _, _, hg, _, heq, _, hcs⟩ => by
      dsimp only [readDomTree, specDom]; rw [hg, ho]
      exact ⟨rfl, rfl, heq, cleanDomChildren_equiv_of (fun h' => CleanDomSubtree_equiv h') hcs⟩

theorem CleanDomChildren_equiv {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg}
    {S : Nat → Prop} {ds : List Dom.Node} (h : CleanDomChildren f ns cs a S ds) :
    DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs) :=
  cleanDomChildren_equiv_of (fun h' => CleanDomSubtree_equiv h') h

theorem CleanDomChildren_append {msg : Type} :
    ∀ {f : Nat} {ns : String} {xs₁ xs₂ : List (Html msg)} {a : DomArena msg}
      {S₁ S₂ : Nat → Prop} {ds₁ ds₂ : List Dom.Node},
      (∀ k, S₁ k → S₂ k → False) →
      CleanDomChildren f ns xs₁ a S₁ ds₁ → CleanDomChildren f ns xs₂ a S₂ ds₂ →
      CleanDomChildren f ns (xs₁ ++ xs₂) a (fun k => S₁ k ∨ S₂ k) (ds₁ ++ ds₂)
  | _, _, [], _, _, _, _, [], _, _, _, h2 => CleanDomChildren_mono (fun _ hk => .inr hk) h2
  | _, _, _ :: _, _, _, _, S₂, _ :: _, _, hDisj, ⟨Sc, Srest, hSc, hSr, hD, hHd, hTl⟩, h2 =>
      ⟨Sc, fun k => Srest k ∨ S₂ k, fun k hk => .inl (hSc k hk), fun k hk => hk.elim (fun h => .inl (hSr k h)) .inr,
       fun k hk1 hk2 => hk2.elim (hD k hk1) (hDisj k (hSc k hk1)), hHd, CleanDomChildren_append (fun k h1 h2' => hDisj k (hSr k h1) h2') hTl h2⟩
  | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ => False.elim hc
  | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc

theorem CleanDomChildren_indexed {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds →
      ∃ (Si : Nat → Nat → Prop), (∀ i k, Si i k → S k) ∧
        (∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False) ∧
        (∀ (i : Nat) (h1 : i < cs.length) (h2 : i < ds.length), CleanDomSubtree f ns cs[i] a (Si i) ds[i])
  | _, _, [], _, _, [], _ => ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => nomatch h⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ => by
      rcases CleanDomChildren_indexed hTl with ⟨SiTail, hSub, hPair, hGet⟩
      refine ⟨fun | 0 => Sc | i + 1 => SiTail i, ?_, ?_, ?_⟩
      · intro i k hk; cases i with | zero => exact hSc k hk | succ i => exact hSr k (hSub i k hk)
      · intro i₁ i₂ hne k h1 h2
        cases i₁ <;> cases i₂
        · exact absurd rfl hne
        · exact hDisj k h1 (hSub _ k h2)
        · exact hDisj k h2 (hSub _ k h1)
        · exact hPair _ _ (by omega) k h1 h2
      · intro i h1 h2; cases i with | zero => exact hHd | succ i => exact hGet i (by simpa using h1) (by simpa using h2)
  | _, _, [], _, _, _ :: _, hc => False.elim hc
  | _, _, _ :: _, _, _, [], hc => False.elim hc

private theorem cleanDomChildren_DomCleanList_of {msg : Type} {f : Nat} {a : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → h.DomClean = true) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → Html.DomCleanList cs = true
  | _, [], _, [], _ => rfl
  | _, _ :: _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => by
      simp only [Html.DomCleanList, hSub hHd, cleanDomChildren_DomCleanList_of hSub hTl, Bool.and_self]
  | _, [], _, _ :: _, hc => False.elim hc
  | _, _ :: _, _, [], hc => False.elim hc

theorem CleanDomSubtree_DomClean {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → h.DomClean = true
  | 0, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, _ => rfl
  | _ + 1, _, .element _ _ _, _, _, _, ⟨_, ho, ha, _, _, _, _, _, _, _, hcs⟩ => by
      simp only [Html.DomClean, ho, ha, cleanDomChildren_DomCleanList_of (fun h' => CleanDomSubtree_DomClean h') hcs,
        Bool.not_false, Bool.and_self]

theorem CleanDomChildren_DomCleanList {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)}
    {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node} (h : CleanDomChildren f ns cs a S ds) :
    Html.DomCleanList cs = true :=
  cleanDomChildren_DomCleanList_of (fun h' => CleanDomSubtree_DomClean h') h

theorem CleanDomSubtree_not_fragment {msg : Type} {f : Nat} {ns : String} {h : Html msg}
    {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node} (hcl : CleanDomSubtree f ns h a S n) :
    ∀ fcs, a.get n ≠ .fragment fcs := by
  cases f with
  | zero => simp only [CleanDomSubtree] at hcl
  | succ _ => cases h with
    | text _ => intro fcs hf; dsimp only [CleanDomSubtree] at hcl; rw [hcl.2] at hf; cases hf
    | element _ _ _ => intro fcs hf; rcases hcl with ⟨_, _, _, _, _, _, hg, _⟩; rw [hg] at hf; cases hf

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

private theorem buildDomListM_spec_full_of {msg : Type} (f : Nat)
    (hBuild : ∀ (ns : String) (h : Html msg) (a : DomArena msg),
      0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ f →
      let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
      a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
      ArenaExt a a' (fun _ => False) (htmlNodeCount h) ∧
      SubtreeInRange f a' a.nextId a'.nextId root ∧ readDomTree f a' root = specDom ns h ∧
      (h.DomClean = true → CleanDomSubtree f ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root))
    (childNs : String) (cs : List (Html msg)) :
    ∀ (aBase : DomArena msg) (parent : Dom.Node)
      (mkPar : List Dom.Node → ArenaEntry msg),
      ((∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)) →
      ∀ (acc : List Dom.Node),
      parent.toNat < aBase.nextId → 0 < aBase.nextId → aBase.nextId + htmlListNodeCount cs < UInt32.size →
      htmlListDepth cs ≤ f → (∀ c ∈ acc, c.toNat < aBase.nextId) →
      let aIn := aBase.set parent (mkPar acc)
      let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
      ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
        aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
        ArenaExt aBase aOut (fun k => k = parent.toNat) (htmlListNodeCount cs) ∧
        (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
        ((∀ c ∈ acc, SubtreeInRange f aIn (parent.toNat + 1) aBase.nextId c) →
          (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
          (acc ++ csNew).map (readDomTree f aOut) = acc.map (readDomTree f aIn) ++ specDomList childNs cs) ∧
        (∀ (hsAcc : List (Html msg)) (Sacc : Nat → Prop),
          Html.DomCleanList cs = true → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
          CleanDomChildren f childNs hsAcc aIn Sacc acc →
          CleanDomChildren f childNs (hsAcc ++ cs) aOut
            (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew)) := by
  induction cs with
  | nil =>
      intro aBase parent mkPar _ acc _ _ _ _ _
      refine ⟨[], aBase, ?_, ?_, fun _ _ hne => (DomArena.get_set_ne _ _ hne).symm, ?_, ?_⟩
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil]
      · exact (ArenaExt.of_set (n := parent) (e := mkPar acc) rfl)
      · intro haccSub
        simp only [buildDomListM, StateT.run, pure, StateT.pure, specDomList, List.append_nil, and_true]
        exact haccSub
      · intro hsAcc Sacc _ _ haccClean
        simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil]
        exact CleanDomChildren_mono (fun _ hk => .inl hk) haccClean
  | cons c rest ih =>
      intro aBase parent mkPar hmk acc hparLt hpos hbound hdep haccLt
      let aIn := aBase.set parent (mkPar acc)
      have haInNext : aIn.nextId = aBase.nextId := rfl
      simp only [htmlListNodeCount] at hbound; simp only [htmlListDepth] at hdep
      have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
      have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
      have hfPos : 0 < f := by cases c <;> { simp only [htmlDepth] at hcDep; omega }
      have hcSpec := hBuild childNs c aIn hpos (by omega) hcDep
      dsimp only [StateT.run] at hcSpec
      cases hR : buildDomM (m := StateM (DomArena msg)) childNs c aIn with
      | mk cn aMid =>
          rw [hR] at hcSpec; dsimp only at hcSpec
          rcases hcSpec with ⟨hcnGe, hcnLt, haMidExt, hcnSub, hcnRead, hcnCleanFn⟩
          have haMidGe := haMidExt.next_ge; have haMidLe := haMidExt.next_le
          have haMidFrame : ∀ m : Dom.Node, m.toNat < aBase.nextId → aMid.get m = aIn.get m :=
            fun m hm => haMidExt.frame m hm id
          rw [haInNext] at hcnGe haMidGe haMidLe hcnSub hcnCleanFn
          have hparInMid : aMid.get parent = mkPar acc := by
            rw [haMidFrame parent hparLt]; exact DomArena.get_set_self ..
          have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := fun fcs hfrag => by
            cases f with
            | zero => omega
            | succ _ => cases c with
              | text _ =>
                  dsimp only [buildDomM, MonadDom.createText, DomArena.alloc] at hR
                  cases hR; dsimp only [DomArena.get] at hfrag; rw [beq_self_eq_true, if_pos rfl] at hfrag; cases hfrag
              | element _ _ _ => dsimp only [readDomTree] at hcnRead; rw [hfrag] at hcnRead; cases hcnRead
          have hcnNotInAcc : cn ∉ acc := fun hmem => by have := haccLt cn hmem; omega
          let aAfter := aMid.set parent (mkPar (acc ++ [cn]))
          have haAfterNext : aAfter.nextId = aMid.nextId := rfl
          have hih := ih aMid parent mkPar hmk (acc ++ [cn])
            (by omega) (by omega) (by omega) hrestDep (fun x hx => by
              rcases List.mem_append.1 hx with h1 | h2
              · have := haccLt x h1; omega
              · rw [List.mem_singleton] at h2; subst h2; exact hcnLt)
          rcases hih with ⟨csRest, aBase'', haOutEq, haOutExt, hframeRest, hsubRestFn, hcleanRestFn⟩
          have hstepRun := buildDomListM_step childNs parent c rest aIn aMid cn mkPar hmk acc hR hparInMid hcnNotFrag hcnNotInAcc
          dsimp only [aAfter] at hstepRun haOutEq haOutExt hframeRest hsubRestFn hcleanRestFn ⊢
          simp only [htmlListNodeCount]
          rw [hstepRun]
          rw [List.append_assoc, List.singleton_append] at haOutEq hsubRestFn hcleanRestFn
          have hExtIn : ArenaExt aBase aMid (fun k => k = parent.toNat) (htmlNodeCount c) :=
            (ArenaExt.of_set (n := parent) (e := mkPar acc) (W := fun k => k = parent.toNat) rfl).trans haMidExt
              (fun _ h => h) (fun _ _ h => h.elim) (by omega)
          refine ⟨cn :: csRest, aBase'', haOutEq,
            hExtIn.trans haOutExt (fun _ h => h) (fun _ _ h => h) (Nat.le_refl _),
            fun m hm hne => by rw [hframeRest m (by omega) hne, DomArena.get_set_ne _ _ hne]; exact haMidFrame m hm,
            fun haccSub => ?_, fun hsAcc Sacc hclean hSacc haccClean => ?_⟩
          · have haccMid : ∀ x ∈ acc, SubtreeInRange f aAfter (parent.toNat + 1) aMid.nextId x ∧
                readDomTree f aAfter x = readDomTree f aIn x := fun x hx => by
              have hfr := SubtreeInRange_frame (a := aIn) (a' := aAfter)
                (fun m hlo hhi => by
                  rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))]; exact haMidFrame m hhi)
                (haccSub x hx)
              exact ⟨SubtreeInRange_mono (Nat.le_refl _) haMidGe hfr.1, hfr.2⟩
            have hcnAfter : SubtreeInRange f aAfter (parent.toNat + 1) aMid.nextId cn ∧
                readDomTree f aAfter cn = specDom childNs c := by
              have hfr := SubtreeInRange_frame (a := aMid) (a' := aAfter)
                (fun m hlo _ => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)))
                (SubtreeInRange_mono hparLt (Nat.le_refl _) hcnSub)
              exact ⟨hfr.1, hfr.2.trans hcnRead⟩
            have ⟨hsubFinal, hreadFinal⟩ := hsubRestFn fun x hx => by
              rcases List.mem_append.1 hx with h1 | h2
              · exact (haccMid x h1).1
              · rw [List.mem_singleton] at h2; subst h2; exact hcnAfter.1
            have hmapInit : (acc ++ [cn]).map (readDomTree f aAfter) = acc.map (readDomTree f aIn) ++ [specDom childNs c] := by
              rw [List.map_append, List.map_singleton, hcnAfter.2]
              congr 1; exact List.map_congr_left fun x hx => (haccMid x hx).2
            rw [hmapInit, List.append_assoc, List.singleton_append] at hreadFinal
            exact ⟨hsubFinal, hreadFinal⟩
          · simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
            let Sc : Nat → Prop := fun k => aBase.nextId ≤ k ∧ k < aMid.nextId
            have haccMid : CleanDomChildren f childNs hsAcc aAfter Sacc acc :=
              CleanDomChildren_frame (fun m hm => by
                have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))]; exact haMidFrame m hb.2) haccClean
            have hcAfter : CleanDomSubtree f childNs c aAfter Sc cn :=
              CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) (hcnCleanFn hclean.1)
            have hcombClean : CleanDomChildren f childNs (hsAcc ++ [c]) aAfter (fun k => Sacc k ∨ Sc k) (acc ++ [cn]) :=
              CleanDomChildren_append (fun k hk1 hk2 => by have := hSacc k hk1; omega) haccMid
                ⟨Sc, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcAfter, trivial⟩
            have hcleanFinal := hcleanRestFn (hsAcc ++ [c]) (fun k => Sacc k ∨ Sc k) hclean.2
              (fun k hk => hk.elim (fun h => let b := hSacc k h; ⟨b.1, by omega⟩) (fun h => ⟨by omega, h.2⟩))
              hcombClean
            simp only [List.append_assoc, List.singleton_append] at hcleanFinal
            refine CleanDomChildren_mono (fun k hk => ?_) hcleanFinal
            rcases hk with (hS | hSc) | hRest
            · exact .inl hS
            · exact .inr ⟨hSc.1, Nat.lt_of_lt_of_le hSc.2 haOutExt.next_ge⟩
            · exact .inr ⟨Nat.le_trans haMidGe hRest.1, hRest.2⟩

theorem buildDomM_spec_full {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat) :
    0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ fuel →
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
    ArenaExt a a' (fun _ => False) (htmlNodeCount h) ∧
    SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns h ∧
    (h.DomClean = true → CleanDomSubtree fuel ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root) := by
  induction fuel generalizing ns h a with
  | zero =>
      intro _ _ hdep; cases h <;> { simp only [htmlDepth] at hdep; omega }
  | succ f ih =>
      intro hpos hbound hdep
      cases h with
      | text s =>
          simp only [htmlNodeCount] at hbound ⊢
          have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
          dsimp only [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run, SubtreeInRange, SubtreeInSet]
          refine ⟨by omega, by rw [htoNat]; exact Nat.lt_succ_self _,
            ⟨Nat.le_succ _, Nat.le_refl _, fun m hm _ => ?_⟩,
            ⟨⟨by omega, by rw [htoNat]; exact Nat.lt_succ_self _⟩, by dsimp only [DomArena.get]; rw [beq_self_eq_true, if_pos rfl]; trivial⟩,
            by dsimp only [readDomTree, DomArena.get, specDom]; rw [beq_self_eq_true, if_pos rfl],
            fun _ => ⟨⟨by omega, by rw [htoNat]; exact Nat.lt_succ_self _⟩, by dsimp only [DomArena.get]; rw [beq_self_eq_true, if_pos rfl]⟩⟩
          have hne : m ≠ UInt32.ofNat a.nextId := node_ne_of_toNat_ne (by omega)
          dsimp only [DomArena.get]; rw [beq_eq_false_iff_ne.2 hne]; rfl
      | element tag attrs children =>
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
          have ha2_frame : ∀ m : Dom.Node, m.toNat < a.nextId → aElem.get m = a.get m := fun m hm =>
            DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))
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
            refine ⟨by omega, by omega, ⟨by omega, by omega, fun m hm _ => ha2_frame m hm⟩, ?_, ?_, fun hcl => ?_⟩
            · dsimp only [SubtreeInRange, SubtreeInSet]
              refine ⟨⟨by omega, by omega⟩, ?_⟩
              dsimp only [aElem]; rw [DomArena.get_set_self]; exact fun _ h => nomatch h
            · dsimp only [readDomTree, aElem, specDom]
              rw [DomArena.get_set_self, if_pos hown]; rfl
            · simp only [Html.DomClean, hown, Bool.not_true, Bool.false_and] at hcl; cases hcl
          · have hownF : ownsChildren attrs = false := Bool.eq_false_iff.2 hown
            simp only [hownF, Bool.not_false, ↓reduceIte]
            have hkids := buildDomListM_spec_full_of f (fun ns' h' a' => ih ns' h' a')
              (Dom.childNsOf ns tag) children a1 node (ArenaEntry.element realNs tag st mg)
              (.inl ⟨realNs, tag, st, mg, fun _ => rfl⟩) []
              (by omega) (by omega) (by omega) (by omega) (fun _ h => nomatch h)
            rcases hkids with ⟨csNew, aBase', ha'Eq, haOutExt, hframe1, hsubKidsFn, hcleanKidsFn⟩
            have ⟨hsubKids, hreadKids⟩ := hsubKidsFn (fun _ h => nomatch h)
            dsimp only [aElem]
            have hnextGe : a.nextId + 1 ≤ _ := haOutExt.next_ge
            have hnextLe : _ ≤ a.nextId + 1 + htmlListNodeCount children := haOutExt.next_le
            refine ⟨by omega, by omega, ⟨by omega, by omega, fun m hm _ => ?_⟩, ?_, ?_, fun hcl => ?_⟩
            · have hne : m ≠ node := node_ne_of_toNat_ne (by omega)
              rw [haOutExt.frame m (by omega) (fun h => hne (uint32_eq_of_toNat_eq h))]; rfl
            · dsimp only [SubtreeInRange, SubtreeInSet]
              refine ⟨⟨by omega, by omega⟩, ?_⟩
              rw [ha'Eq, DomArena.get_set_self]
              intro c hc; have := hsubKids c hc; rw [ha'Eq] at this
              exact SubtreeInRange_mono (by omega) (Nat.le_refl _) this
            · rw [ha'Eq] at hreadKids ⊢
              rw [List.nil_append, List.map_nil, List.nil_append] at hreadKids
              dsimp only [readDomTree, specDom]
              rw [DomArena.get_set_self, hownF, if_neg Bool.false_ne_true, List.nil_append]
              exact congrArg (DomTree.element realNs tag st) hreadKids
            · simp only [Html.DomClean, hownF, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hcl
              have hcleanOut := hcleanKidsFn [] (fun _ => False) hcl.2 (fun _ h => h.elim) trivial
              rw [List.nil_append, List.nil_append] at hcleanOut
              refine ⟨⟨by omega, by omega⟩, hownF, hcl.1, st, mg, csNew, ?_,
                ElemClean_evalSpecAttrs hcl.1, ElemStateEquiv.refl st,
                fun nm hnm => List.contains_iff_mem.2 hnm, ?_⟩
              · rw [ha'Eq, DomArena.get_set_self, List.nil_append]
              · exact CleanDomChildren_mono (fun k hk => hk.elim False.elim fun h =>
                  ⟨⟨Nat.le_trans (Nat.le_succ _) h.1, h.2⟩, by dsimp only [a1] at h; omega⟩) hcleanOut

theorem buildDomM_spec {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat)
    (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount h < UInt32.size) (hdep : htmlDepth h ≤ fuel) :
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount h ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns h := by
  rcases buildDomM_spec_full ns h a fuel hpos hbound hdep with ⟨h1, h2, hext, hsub, hread, _⟩
  exact ⟨h1, h2, hext.next_le, fun m hm => hext.frame m hm id, hsub, hread⟩

theorem CleanDomSubtree_of_buildDomM {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat)
    (hcl : h.DomClean = true) (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount h < UInt32.size)
    (hdep : htmlDepth h ≤ fuel) :
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    CleanDomSubtree fuel ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root :=
  (buildDomM_spec_full ns h a fuel hpos hbound hdep).2.2.2.2.2 hcl

theorem buildDomListM_spec_full {msg : Type} (childNs : String) (cs : List (Html msg))
    (aBase : DomArena msg) (parent : Dom.Node) (mkPar : List Dom.Node → ArenaEntry msg)
    (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds))
    (acc : List Dom.Node) (f : Nat)
    (hparLt : parent.toNat < aBase.nextId) (hpos : 0 < aBase.nextId)
    (hbound : aBase.nextId + htmlListNodeCount cs < UInt32.size) (hdep : htmlListDepth cs ≤ f)
    (haccLt : ∀ c ∈ acc, c.toNat < aBase.nextId) :
    let aIn := aBase.set parent (mkPar acc)
    let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
    ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
      aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
      ArenaExt aBase aOut (fun k => k = parent.toNat) (htmlListNodeCount cs) ∧
      (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
      ((∀ c ∈ acc, SubtreeInRange f aIn (parent.toNat + 1) aBase.nextId c) →
        (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
        (acc ++ csNew).map (readDomTree f aOut) = acc.map (readDomTree f aIn) ++ specDomList childNs cs) ∧
      (∀ (hsAcc : List (Html msg)) (Sacc : Nat → Prop),
        Html.DomCleanList cs = true → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
        CleanDomChildren f childNs hsAcc aIn Sacc acc →
        CleanDomChildren f childNs (hsAcc ++ cs) aOut
          (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew)) :=
  buildDomListM_spec_full_of f (fun ns' h' a' => buildDomM_spec_full ns' h' a' f)
    childNs cs aBase parent mkPar hmk acc hparLt hpos hbound hdep haccLt

theorem buildDomListM_spec {msg : Type} (childNs : String)
    (cs : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (acc : List Dom.Node) (f : Nat)
    (hparLt : parent.toNat < aBase.nextId) (hpos : 0 < aBase.nextId)
    (hbound : aBase.nextId + htmlListNodeCount cs < UInt32.size) (hdep : htmlListDepth cs ≤ f)
    (haccSub : ∀ c ∈ acc, SubtreeInRange f (aBase.set parent (.element pns ptag pst pmg acc)) (parent.toNat + 1) aBase.nextId c) :
    let aIn := aBase.set parent (.element pns ptag pst pmg acc)
    let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
    ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
      aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
      aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧ aBase.nextId ≤ aOut.nextId ∧
      (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
      (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
      (acc ++ csNew).map (readDomTree f aOut) = acc.map (readDomTree f aIn) ++ specDomList childNs cs := by
  cases cs with
  | nil =>
      refine ⟨[], aBase, ?_, ?_, Nat.le_refl _, fun _ _ hne => (DomArena.get_set_ne _ _ hne).symm, ?_, ?_⟩
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil]
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, htmlListNodeCount, Nat.add_zero, DomArena.set]; exact Nat.le_refl _
      · rw [List.append_nil]; exact haccSub
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, specDomList, List.append_nil]
  | cons c rest =>
      have hfPos : 0 < f := by
        simp only [htmlListDepth] at hdep
        have := Nat.le_trans (Nat.le_max_left _ _) hdep
        cases c <;> { simp only [htmlDepth] at this; omega }
      have haccLt : ∀ x ∈ acc, x.toNat < aBase.nextId := fun x hx => by
        cases f with | zero => omega | succ _ => exact (haccSub x hx).1.2
      rcases buildDomListM_spec_full childNs (c :: rest) aBase parent (ArenaEntry.element pns ptag pst pmg)
        (.inl ⟨pns, ptag, pst, pmg, fun _ => rfl⟩) acc f hparLt hpos hbound hdep haccLt with
        ⟨csNew, aBase', hEq, hext, hfr, hsubFn, _⟩
      have ⟨hsub, hread⟩ := hsubFn haccSub
      exact ⟨csNew, aBase', hEq, hext.next_le, hext.next_ge, hfr, hsub, hread⟩

theorem CleanDomChildren_of_buildDomListM {msg : Type} (childNs : String)
    (cs hsAcc : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg)
    (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds))
    (acc : List Dom.Node) (f : Nat) (Sacc : Nat → Prop)
    (hcl : Html.DomCleanList cs = true) (hparLt : parent.toNat < aBase.nextId) (hpos : 0 < aBase.nextId)
    (hbound : aBase.nextId + htmlListNodeCount cs < UInt32.size) (hdep : htmlListDepth cs ≤ f)
    (hSacc : ∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId)
    (haccClean : CleanDomChildren f childNs hsAcc (aBase.set parent (mkPar acc)) Sacc acc) :
    let aIn := aBase.set parent (mkPar acc)
    let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
    ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
      aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
      aBase.nextId ≤ aOut.nextId ∧
      aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧
      (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
      CleanDomChildren f childNs (hsAcc ++ cs) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew) := by
  rcases buildDomListM_spec_full childNs cs aBase parent mkPar hmk acc f hparLt hpos hbound hdep
    (fun c hc => (hSacc _ (CleanDomChildren_mem haccClean c hc)).2) with
    ⟨csNew, aBase', hEq, hext, _, _, hclFn⟩
  exact ⟨csNew, aBase', hEq, hext.next_ge, hext.next_le,
    fun m hm hne => hext.frame m hm (fun h => hne (uint32_eq_of_toNat_eq h)),
    hclFn hsAcc Sacc hcl hSacc haccClean⟩

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

def DomArena.withMeta {msg : Type} (a : DomArena msg) (sigs : List (String × String))
    (evs : List (String × msg)) (tmpls : Array (ArenaTmpl msg))
    (rowEvs : Array (Nat → Nat → Option msg)) : DomArena msg :=
  { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }

def DomArena.MetaIndep {msg α : Type} (op : StateM (DomArena msg) α) : Prop :=
  ∀ sigs evs tmpls rowEvs (a : DomArena msg),
    op (a.withMeta sigs evs tmpls rowEvs) =
      ((op a).1, (op a).2.withMeta sigs evs tmpls rowEvs)

theorem DomArena.MetaIndep.pure {msg α : Type} (x : α) :
    DomArena.MetaIndep (msg := msg) (Pure.pure x) :=
  fun _ _ _ _ _ => rfl

theorem DomArena.MetaIndep.bind {msg α β : Type} {op : StateM (DomArena msg) α}
    {f : α → StateM (DomArena msg) β} (h1 : DomArena.MetaIndep op)
    (h2 : ∀ x, DomArena.MetaIndep (f x)) : DomArena.MetaIndep (op >>= f) :=
  fun sigs evs tmpls rowEvs a => by
    change (let (x, s) := op (a.withMeta sigs evs tmpls rowEvs); f x s) = _
    rw [h1 sigs evs tmpls rowEvs a]
    exact h2 (op a).1 sigs evs tmpls rowEvs (op a).2

theorem DomArena.MetaIndep.sameDom {msg α : Type} {op : StateM (DomArena msg) α}
    (h : DomArena.MetaIndep op) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (op a₁).2.SameDom (op a₂).2 := by
  have heq : a₁ = a₂.withMeta a₁.signals a₁.sigEvents a₁.tmpls a₁.rowEvs :=
    DomArena.ext hs.1 hs.2 rfl rfl rfl rfl
  rw [heq, h]; exact ⟨rfl, rfl⟩

theorem DomArena.MetaIndep.appendChild {msg : Type} (parent child : Dom.Node) :
    DomArena.MetaIndep (MonadDom.appendChild (m := StateM (DomArena msg)) parent child) :=
  fun _ _ _ _ a => by
    simp only [MonadDom.appendChild, DomArena.get, DomArena.set, DomArena.modifyChildren, DomArena.modify, DomArena.withMeta]
    cases a.store child <;> rfl

theorem applyAttrsM_metaIndep {msg : Type} (node : Dom.Node) (attrs : List (Attr msg)) :
    DomArena.MetaIndep (applyAttrsM (m := StateM (DomArena msg)) node attrs) := by
  have hlist : ∀ (xs : List (Attr msg)),
      DomArena.MetaIndep (applyAttrListM (m := StateM (DomArena msg)) node xs) := by
    intro xs; induction xs with
    | nil => exact .pure ()
    | cons x rest ih =>
        refine .bind (fun _ _ _ _ _ => ?_) fun _ => ih
        rw [applyAttrM_eq_modifyElemState, applyAttrM_eq_modifyElemState]; rfl
  exact .bind (fun _ _ _ _ _ => rfl) fun _ => hlist (normalizeAttrs attrs)

mutual
  theorem buildDomM_metaIndep {msg : Type} (ns : String) :
      (h : Html msg) → DomArena.MetaIndep (buildDomM (m := StateM (DomArena msg)) ns h)
    | .text _ => fun _ _ _ _ _ => rfl
    | .element tag attrs children => by
        dsimp only [buildDomM]
        refine .bind (fun _ _ _ _ _ => rfl) fun el => .bind (applyAttrsM_metaIndep el attrs) fun _ => ?_
        cases ownsChildren attrs
        · exact .bind (buildDomListM_metaIndep (Dom.childNsOf ns tag) el children) fun _ => .pure el
        · exact .pure el

  theorem buildDomListM_metaIndep {msg : Type} (ns : String) (parent : Dom.Node) :
      (cs : List (Html msg)) → DomArena.MetaIndep (buildDomListM (m := StateM (DomArena msg)) ns parent cs)
    | [] => .pure ()
    | c :: rest =>
        .bind (buildDomM_metaIndep ns c) fun cn =>
          .bind (.appendChild parent cn) fun _ =>
            buildDomListM_metaIndep ns parent rest
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
      (buildDomListM (m := StateM (DomArena msg)) ns parent cs a₂).2 :=
  (buildDomListM_metaIndep ns parent cs).sameDom hs

end Qed
