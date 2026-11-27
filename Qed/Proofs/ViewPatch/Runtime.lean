import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {α σ msg : Type}

/-! ## 4. Template Keyed Row Alignment, Signal Store & Diff Soundness -/

theorem diffRowSigs_sound (rowSig : Nat → Array (String × String)) (rowEv : Nat → Array (String × msg)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[])
    (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) (accEv : Array (String × msg))
    (hiLe : i ≤ newMarks.size) (hsz : accSigs.size = i) (hprev : ∀ k, k < i → accSigs[k]! = rowSig k) :
    let (outSigs, _) := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs i accSigs accEmit accEv
    outSigs.size = newMarks.size ∧ ∀ k, k < newMarks.size → outSigs[k]! = rowSig k := by
  dsimp only; rw [diffRowSigs.eq_1]; split
  · rename_i hlt; dsimp only
    have hstep (v : Array (String × String)) (hv : v = rowSig i) (ae aev) :=
      diffRowSigs_sound rowSig rowEv inst newMarks oldMarks oldSigs hmark (i + 1) (accSigs.push v) ae aev (by omega) (by simp [hsz]) fun k hk => by
        rw [getElem!_pos _ k (by simp [hsz]; omega)]
        exact array_push_step_inv (f := fun j _ => rowSig j) hlt hsz (fun j hj => by rw [← getElem!_pos accSigs j (by omega)]; exact hprev j hj) hv k hk
    split
    · rename_i h; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
      exact hstep _ (hmark i hlt (by simpa [hlt] using h.1) (by simpa [hlt] using h.2)).symm _ _
    · exact hstep _ rfl _ _
  · exact ⟨by simp [hsz]; omega, fun k hk => hprev k (by omega)⟩
termination_by newMarks.size - i

theorem seedRowsM_spec (inst : String) (rowSig : Nat → Array (String × String)) (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg)
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    let res := (seedRowsM (m := StateM (DomArena msg)) inst rowSig rowEv newMarks oldMarks oldSigs).run a
    let d := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
    res.1.size = newMarks.size ∧ (∀ k, k < newMarks.size → res.1[k]! = rowSig k) ∧ res.2.nextId = a.nextId ∧ res.2.store = a.store ∧
    res.2.signals = d.2.1.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals ∧ res.2.sigEvents = d.2.2.toList.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents := by
  have hs := diffRowSigs_sound rowSig rowEv inst newMarks oldMarks oldSigs hmark 0 #[] #[] #[] (Nat.zero_le _) rfl (fun _ h => nomatch h)
  dsimp only; rw [seedRowsM_run_eq]; exact ⟨hs.1, hs.2, rfl, rfl, rfl, rfl⟩

theorem renderSig_resolved_spec (ns : String) (get : σ → String) (s₁ s₂ : σ) (pre : String) (n : Nat) (a : DomArena msg) (f : Nat) (hbound : a.nextId + 1 < UInt32.size) :
    let (sigHtml, _, _) := View.renderSig (.dyn get : View σ msg) s₁ pre n
    let (root, aMid) := (buildDomM (m := StateM (DomArena msg)) ns sigHtml).run a
    let aOut := (MonadDom.setSignal (m := StateM (DomArena msg)) s!"{pre}#{n}" (get s₂) aMid).2
    readResolvedDomTree (f + 1) aOut root = specDom ns (View.render (.dyn get) s₂) ∧ aOut.nextId = a.nextId + 1 ∧ ∀ m : Dom.Node, m.toNat < a.nextId → aOut.get m = a.get m := by
  let node := UInt32.ofNat a.nextId; let sigNm := s!"{pre}#{n}"; let realNs := if ns == "" && "span" == "svg" then Dom.svgNs else ns; let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
  dsimp only [View.renderSig, buildDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.createElement, DomArena.alloc]
  rw [show ({ a with nextId := a.nextId + 1, store := fun m => if (m == node) = true then ArenaEntry.element realNs "span" {} [] [] else a.store m } : DomArena msg) =
        a1.set node (.element realNs "span" {} [] []) from rfl, applyAttrsM_fresh_element a1 node realNs "span" [] [.signalBind sigNm]]
  simp only [ownsChildren, List.any, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, MonadDom.setSignal, View.render, specDom, readResolvedDomTree, DomArena.get]
  exact ⟨by simp only [show (evalSpecAttrs ([Attr.signalBind sigNm] : List (Attr msg))).sigBind = some sigNm from rfl, sigNm, node, DomArena.set, lookupAssoc_setAssoc, beq_self_eq_true, ↓reduceIte, Option.getD_some],
    rfl, fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by dsimp only [node]; rw [uint32_toNat_ofNat_lt a.nextId (by omega)]; omega))⟩

/-! ## 5. Browser Runtime & Local Island Driver Specifications -/

theorem registerHandlerSpec_sound (arr : Array α) (h : α) :
    let id := arr.size; let arr' := arr.push h; arr'[id]? = some h ∧ ∀ j, j < arr.size → arr'[j]? = arr[j]? :=
  ⟨by simp, fun j hj => by simp [Array.getElem?_push, Nat.ne_of_lt hj]⟩

structure LocalInstSpec where
  props : String
  rendered : Html LocalMsg

structure LocalRuntimeSpec where
  store : Std.HashMap String String
  instances : Std.HashMap String LocalInstSpec

def localMountStep (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec) (key component : String) (init? : Option String) (props : String) : LocalRuntimeSpec :=
  let fk := localKey component key
  match reg[component]? with
  | none => st
  | some ldef => match st.instances[fk]? with
    | some inst => { st with instances := st.instances.insert fk { props, rendered := if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered } }
    | none => let s0 := st.store.getD fk (init?.getD ldef.init); { store := st.store.insert fk s0, instances := st.instances.insert fk { props, rendered := ldef.viewForProps props s0 } }

theorem localMountSpec_init_vs_rerender (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec)
    (key component : String) (init? : Option String) (props : String) (ldef : LocalDef) (hreg : reg[component]? = some ldef) :
    let fk := localKey component key; let st' := localMountStep reg st key component init? props
    (st.instances[fk]? = none → let s0 := st.store.getD fk (init?.getD ldef.init); st'.store[fk]? = some s0 ∧ st'.instances[fk]? = some ⟨props, ldef.viewForProps props s0⟩) ∧
    (∀ inst, st.instances[fk]? = some inst → st'.store = st.store ∧ st'.instances[fk]? = some ⟨props, if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered⟩) :=
  ⟨fun h => by simp [localMountStep, hreg, h], fun inst h => by simp [localMountStep, hreg, h]⟩

def gcLocalsSpec (isConn : String → Bool) (st : LocalRuntimeSpec) : LocalRuntimeSpec :=
  let dead := st.instances.toList.filterMap (fun (k, _) => if isConn k then none else some k)
  { store := dead.foldl (·.erase ·) st.store, instances := dead.foldl (·.erase ·) st.instances }

private theorem foldl_erase_getElem? {α : Type} : ∀ (ks : List String) (m : Std.HashMap String α) (k : String), (ks.foldl (·.erase ·) m)[k]? = if k ∈ ks then none else m[k]?
  | [], _, _ => by simp
  | x :: xs, m, k => by rw [List.foldl_cons, foldl_erase_getElem? xs]; by_cases hx : k ∈ xs <;> by_cases hkx : x = k <;> simp [hx, hkx, Ne.symm, Std.HashMap.getElem?_erase]

theorem gcLocalsSpec_frame (isConn : String → Bool) (st : LocalRuntimeSpec) (k : String) :
    let st' := gcLocalsSpec isConn st
    (isConn k = true → st'.store[k]? = st.store[k]? ∧ st'.instances[k]? = st.instances[k]?) ∧
    ((∃ inst, (k, inst) ∈ st.instances.toList) → isConn k = false → st'.store[k]? = none ∧ st'.instances[k]? = none) := by
  dsimp only [gcLocalsSpec]
  have hmem : k ∈ st.instances.toList.filterMap (fun (k, _) => if isConn k then none else some k) ↔ (∃ v, (k, v) ∈ st.instances.toList) ∧ isConn k = false := by
    simp only [List.mem_filterMap]
    exact ⟨fun ⟨⟨_, v⟩, hm, hp⟩ => by split at hp <;> simp at hp; subst hp; exact ⟨⟨v, hm⟩, Bool.eq_false_iff.2 ‹_›⟩, fun ⟨⟨v, hm⟩, hc⟩ => ⟨(k, v), hm, by simp [hc]⟩⟩
  exact ⟨fun hc => by have h : k ∉ _ := (fun hd => by rw [(hmem.1 hd).2] at hc; cases hc); simp only [foldl_erase_getElem?, h, ↓reduceIte, and_self],
         fun hv hc => by simp only [foldl_erase_getElem?, hmem.2 ⟨hv, hc⟩, ↓reduceIte, and_self]⟩

def snapshotLocalsJson (entries : List (String × String)) : String := Json.render (Json.obj (entries.map fun (k, v) => (k, .str v)))
private def localJsonStep (st : Std.HashMap String String) (kv : String × Json) : Std.HashMap String String := match kv.2 with | .str str => st.insert kv.1 str | _ => st
def restoreLocalsFromJson (s : String) (base : Std.HashMap String String) : Std.HashMap String String := match Json.parse s with | .ok (.obj members) => members.foldl localJsonStep base | _ => base

private theorem foldl_localJsonStep_spec : ∀ (rs : List (String × String)) (b : Std.HashMap String String) (k : String),
    (k ∉ rs.map Prod.fst → ((rs.map fun (k, v) => (k, Json.str v)).foldl localJsonStep b)[k]? = b[k]?) ∧
    ((rs.map Prod.fst).Nodup → ∀ v, (k, v) ∈ rs → ((rs.map fun (k, v) => (k, Json.str v)).foldl localJsonStep b)[k]? = some v)
  | [], _, _ => ⟨fun _ => rfl, fun _ _ h => nomatch h⟩
  | (x, u) :: rest, b, k =>
      ⟨fun hnm => by simpa [List.foldl_cons, localJsonStep, Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.2 (fun h : x = k => hnm (h ▸ .head _))]
         using (foldl_localJsonStep_spec rest (b.insert x u) k).1 fun hm => hnm (.tail _ hm),
       fun hnd v hv => by rcases List.nodup_cons.1 hnd with ⟨hni, hnr⟩; rcases List.mem_cons.1 hv with hEq | ht
                          · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩; simpa [List.foldl_cons, localJsonStep] using (foldl_localJsonStep_spec rest (b.insert k v) k).1 hni
                          · exact (foldl_localJsonStep_spec rest (b.insert x u) k).2 hnr v ht⟩

theorem snapshot_restore_locals_roundtrip (entries : List (String × String)) (hnd : (entries.map Prod.fst).Nodup) (base : Std.HashMap String String) :
    let out := restoreLocalsFromJson (snapshotLocalsJson entries) base; ∀ kv ∈ entries, out[kv.1]? = some kv.2 := by
  have hdep : (Json.obj (entries.map fun x => (x.1, Json.str x.2))).depth ≤ 64 := by
    have : Json.maxObj (entries.map fun x => (x.1, Json.str x.2)) ≤ 0 := Json.maxObj_le_iff.2 fun _ h => by rcases List.mem_map.1 h with ⟨_, _, rfl⟩; exact Nat.le_refl _
    dsimp only [Json.depth]; omega
  dsimp only; intro ⟨k, v⟩ hkv
  simpa [restoreLocalsFromJson, snapshotLocalsJson, parse_render hdep] using (foldl_localJsonStep_spec entries base k).2 hnd v hkv

def drainQueueSpec {Msg : Type} (step : σ → Msg → σ × List Msg) : Nat → σ → Array Msg → σ × Array Msg
  | 0, st, q => (st, q)
  | fuel + 1, st, q => if q.isEmpty then (st, #[])
      else let (st', nextQ) := q.toList.foldl (fun (acc, nxt) m => let (s', sp) := step acc m; (s', nxt ++ sp)) (st, [])
           drainQueueSpec step fuel st' nextQ.toArray

theorem drainPendingQueue_fifo_spec {Msg : Type} (step : σ → Msg → σ) (st : σ) (q : Array Msg) (fuel : Nat) (hf : 0 < fuel) :
    drainQueueSpec (fun s m => (step s m, [])) fuel st q = (q.toList.foldl step st, #[]) := by
  cases fuel with | zero => omega | succ f =>
  have hfold : ∀ (ms : List Msg) (s : σ) (acc : List Msg), ms.foldl (fun p m => (step p.1 m, p.2 ++ [])) (s, acc) = (ms.foldl step s, acc) := fun ms => by
    induction ms with | nil => exact fun _ _ => rfl | cons m ms ih => exact fun s acc => by simpa [List.foldl_cons] using ih (step s m) acc
  cases q with | mk l => cases l with | nil => simp [drainQueueSpec] | cons _ _ =>
    dsimp only [drainQueueSpec]; simp only [Array.isEmpty, List.size_toArray, List.length_cons, Nat.succ_ne_zero, hfold]; cases f <;> simp [drainQueueSpec]

private theorem renderSigAttrs_of_dynValGets_empty (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), dynValGets attrs = [] → dynOnGets attrs = [] → (renderSigAttrs s pre attrs n en).1 = attrs.map (VAttr.eval s)
  | [], _, _, _, _ => rfl | .dynVal _ _ :: _, _, _, h, _ => by simp [dynValGets] at h | .dynOn _ _ :: _, _, _, _, h => by simp [dynOnGets] at h
  | .stat _ :: rest, n, en, h, he | .bind _ :: rest, n, en, h, he => by simp [renderSigAttrs, VAttr.eval, renderSigAttrs_of_dynValGets_empty s pre rest n en h he]

mutual
  private theorem renderSig_of_collectDyn_empty : ∀ (v : View σ msg), v.collectDyn = [] → v.collectDynOn = [] → ∀ (s : σ) (pre : String) (n en : Nat), (v.renderSig s pre n en).1 = v.render s
    | .text _, _, _, _, _, _, _ | .keyedList .., _, _, _, _, _, _ | .static _, _, _, _, _, _, _ | .dynNode _, _, _, _, _, _, _ | .memo _, _, _, _, _, _, _ => rfl
    | .dyn _, h, _, _, _, _, _ => by simp [View.collectDyn] at h
    | .element _ attrs kids, h, he, s, pre, n, en => by
        simp only [View.collectDyn, View.collectDynOn, List.append_eq_nil_iff] at h he
        simp only [View.renderSig, View.render, renderSigAttrs_of_dynValGets_empty s pre attrs n en h.1 he.1, renderSigList_of_collectDynList_empty kids h.2 he.2 s pre]
    | .ifElse c y no, h, he, s, pre, n, en => by
        simp only [View.collectDyn, View.collectDynOn, List.append_eq_nil_iff] at h he
        by_cases hc : c s = true <;> simp [View.renderSig, View.render, hc, renderSig_of_collectDyn_empty y h.1 he.1 s pre n en, renderSig_of_collectDyn_empty no h.2 he.2 s pre]
  private theorem renderSigList_of_collectDynList_empty : ∀ (ks : List (View σ msg)), View.collectDynList ks = [] → View.collectDynOnList ks = [] →
      ∀ (s : σ) (pre : String) (n en : Nat), (View.renderSigList ks s pre n en).1 = View.renderEach ks s
    | [], _, _, _, _, _, _ => rfl
    | k :: ks, h, he, s, pre, n, en => by
        simp only [View.collectDynList, View.collectDynOnList, List.append_eq_nil_iff] at h he
        simp [View.renderSigList, View.renderEach, renderSig_of_collectDyn_empty k h.1 he.1 s pre n en, renderSigList_of_collectDynList_empty ks h.2 he.2 s pre]
end

theorem View.DomClean_forEach (tag : String) (items : σ → Array α) (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String)
    (ha : VAttrListClean attrs) (hdyn : (View.collectDyn child).isEmpty = true) (hdynOn : (View.collectDynOn child).isEmpty = true)
    (hcl : ∀ a, (child.render a).DomClean = true) (htxt : ∀ a, (child.render a).textOf? = none)
    (hnd : ∀ s, (((items s).map key).toList).Nodup) (hkey : ∀ a b, key a = key b → child.render a = child.render b) :
    View.DomClean (V.forEach tag items key child attrs sigPrefix) := by
  dsimp only [V.forEach]
  have hnotDirect : V.isDirectTmpl child = false := by cases child with | element _ _ _ => simp only [V.isDirectTmpl, hdyn, hdynOn, Bool.not_true, Bool.or_self, Bool.false_and] | _ => rfl
  split
  · intro s; simp only [Html.DomClean_element, ha.1 s, ha.2.1 s, Bool.not_false, Bool.true_and, Array.toList_map, Html.DomCleanList, List.all_map, List.all_eq_true, Function.comp_apply, Html.DomClean_withKey]
    exact fun a _ => hcl a
  · simp only [hnotDirect, Bool.false_eq_true, ↓reduceIte]
    have hde := List.isEmpty_iff.1 hdyn; have hdo := List.isEmpty_iff.1 hdynOn
    have hu (s : σ) : disambiguateKeys ((items s).map key) = (items s).map key := disambiguateKeys_of_nodup (by simpa only [Array.toList_map] using hnd s)
    refine ⟨ha, fun s => by simp only [List.length_map, List.length_zipIdx, Array.length_toList, hu s, Array.size_map],
      fun s => by dsimp only [Html.DomCleanList]; rw [List.all_map, List.all_eq_true]; exact fun p _ => by simp only [Function.comp_apply, Html.DomClean_withKey, renderSig_of_collectDyn_empty child hde hdo p.1, hcl p.1],
      fun s r hr => by rcases List.mem_map.1 hr with ⟨p, _, rfl⟩; rw [Html.textOf?_withKey, renderSig_of_collectDyn_empty child hde hdo]; exact htxt p.1,
      fun s₁ s₂ i j hi hj hkeq => by
        have hi' : i < (items s₁).size := (by simpa only [hu s₁, Array.size_map] using hi)
        have hj' : j < (items s₂).size := (by simpa only [hu s₂, Array.size_map] using hj)
        have hka : key (items s₁)[i] = key (items s₂)[j] := (by simpa only [hu s₁, hu s₂, Array.getElem_map] using hkeq)
        simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hj', Option.map_some, Nat.zero_add, renderSig_of_collectDyn_empty child hde hdo]
        simp [hu s₁, hu s₂, Array.getD, hi', hj', hka, hkey _ _ hka]⟩

/-! ## 6. Compiled Row-Template & Prefix/Suffix/Swap Fast-Path Soundness -/

private theorem matchLen_sound_of {f : Nat → Nat} {P : Nat → Prop} {bound : Nat}
    (hstep : ∀ t, t < f t → P t ∧ f t = f (t + 1) ∧ t < bound) {i k : Nat} (hik : i ≤ k) (hklt : k < f i) : P k := by
  have hiLe : i ≤ bound := Nat.le_of_lt (hstep i (Nat.lt_of_le_of_lt hik hklt)).2.2
  induction i, hiLe using down_ind with
  | base => exact absurd (hstep bound (Nat.lt_of_le_of_lt hik hklt)).2.2 (Nat.lt_irrefl _)
  | step t _ ih =>
      have ⟨hP, hEq, _⟩ := hstep t (Nat.lt_of_le_of_lt hik hklt)
      if heq : k = t then exact heq ▸ hP else exact ih (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hik (Ne.symm heq))) (hEq ▸ hklt)

theorem prefixMatchLen_bound (oldMarks newMarks : Array USize) (i : Nat) (ho : i ≤ oldMarks.size) (hn : i ≤ newMarks.size) :
    prefixMatchLen oldMarks newMarks i ≤ oldMarks.size ∧ prefixMatchLen oldMarks newMarks i ≤ newMarks.size := by
  unfold prefixMatchLen; split <;> try exact ⟨ho, hn⟩
  dsimp only; split <;> first | exact prefixMatchLen_bound oldMarks newMarks (i + 1) (by omega) (by omega) | exact ⟨ho, hn⟩
termination_by oldMarks.size - i

private theorem matchLen_step {f : Nat → Nat} {Q C : Prop} [Decidable C] {M : C → Bool} {t bound : Nat}
    (heq : f t = if h : C then if M h then f (t + 1) else t else t)
    (hmk : ∀ h : C, M h = true → Q ∧ t < bound) (ht : t < f t) : Q ∧ f t = f (t + 1) ∧ t < bound := by
  rw [heq] at ht ⊢; split at ht
  · rename_i h; split at ht
    · rename_i hm; have ⟨hP, hb⟩ := hmk h hm; exact ⟨hP, by simp only [h, ↓reduceDIte, hm, ↓reduceIte], hb⟩
    · exact absurd ht (Nat.lt_irrefl _)
  · exact absurd ht (Nat.lt_irrefl _)

theorem prefixMatchLen_sound (oldMarks newMarks : Array USize) (i k : Nat) (hik : i ≤ k) (hklt : k < prefixMatchLen oldMarks newMarks i) :
    ∃ (ho : k < oldMarks.size) (hn : k < newMarks.size), newMarks[k]'hn ≠ 0 ∧ oldMarks[k]'ho = newMarks[k]'hn :=
  matchLen_sound_of (f := prefixMatchLen oldMarks newMarks) (P := fun k => ∃ (ho : k < oldMarks.size) (hn : k < newMarks.size), newMarks[k]'hn ≠ 0 ∧ oldMarks[k]'ho = newMarks[k]'hn)
    (bound := oldMarks.size) (fun t => matchLen_step (prefixMatchLen.eq_1 oldMarks newMarks t) fun h hm => by
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm; exact ⟨⟨h.1, h.2, hm.1, hm.2⟩, h.1⟩) hik hklt

theorem suffixMatchLen_sound (oldMarks newMarks : Array USize) (p q j : Nat) (hqj : q ≤ j) (hjlt : j < suffixMatchLen oldMarks newMarks p q) :
    p + j < oldMarks.size ∧ p + j < newMarks.size ∧ ∃ (ho : oldMarks.size - 1 - j < oldMarks.size) (hn : newMarks.size - 1 - j < newMarks.size),
      newMarks[newMarks.size - 1 - j]'hn ≠ 0 ∧ oldMarks[oldMarks.size - 1 - j]'ho = newMarks[newMarks.size - 1 - j]'hn :=
  matchLen_sound_of (f := suffixMatchLen oldMarks newMarks p) (P := fun j => p + j < oldMarks.size ∧ p + j < newMarks.size ∧ ∃ (ho : oldMarks.size - 1 - j < oldMarks.size) (hn : newMarks.size - 1 - j < newMarks.size), newMarks[newMarks.size - 1 - j]'hn ≠ 0 ∧ oldMarks[oldMarks.size - 1 - j]'ho = newMarks[newMarks.size - 1 - j]'hn)
    (bound := oldMarks.size) (fun t => matchLen_step (suffixMatchLen.eq_1 oldMarks newMarks p t) fun h hm => by
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm; exact ⟨⟨h.1, h.2, by omega, by omega, hm.1, hm.2⟩, Nat.lt_of_le_of_lt (Nat.le_add_left t p) h.1⟩) hqj hjlt

private theorem mem_collectChangedMarksLoop_of_mem (oldMarks newMarks : Array USize) (i : Nat) (acc : Array Nat) (x : Nat) (hx : x ∈ acc.toList) :
    x ∈ (collectChangedMarksLoop oldMarks newMarks i acc).toList := by
  unfold collectChangedMarksLoop; split <;> try exact hx
  exact mem_collectChangedMarksLoop_of_mem oldMarks newMarks (i + 1) _ x (by split; exact hx; simp [hx])
termination_by newMarks.size - i

theorem collectChangedMarksLoop_sound (oldMarks newMarks : Array USize) (i : Nat) (acc : Array Nat) (k : Nat) (hk : k < newMarks.size)
    (hik : i ≤ k) (hnot : k ∉ (collectChangedMarksLoop oldMarks newMarks i acc).toList) :
    newMarks[k]'hk ≠ 0 ∧ oldMarks[k]? = some (newMarks[k]'hk) := by
  unfold collectChangedMarksLoop at hnot; simp only [show i < newMarks.size by omega, ↓reduceDIte] at hnot
  if heq : k = i then
    subst heq; split at hnot
    · rename_i hm; simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hm
    · exact False.elim (hnot (mem_collectChangedMarksLoop_of_mem oldMarks newMarks (k + 1) (acc.push k) k (by simp)))
  else exact collectChangedMarksLoop_sound oldMarks newMarks (i + 1) _ k hk (by omega) hnot
termination_by newMarks.size - i

theorem patchNodeSlotAt_nextId (a : DomArena msg) (n : Dom.Node) (path : List Nat) (attrName val : String) : (patchNodeSlotAt a n path attrName val).nextId = a.nextId := by
  induction path generalizing n with
  | nil => dsimp only [patchNodeSlotAt]; split <;> first | rfl | (split <;> rfl)
  | cons idx _ ih => dsimp only [patchNodeSlotAt]; cases a.get n with | element _ _ _ _ cs => (dsimp only; cases cs[idx]? with | none => rfl | some c => exact ih c) | _ => rfl

theorem patchNodeSlotAt_text_root (a : DomArena msg) (n : Dom.Node) (old val : String) (hget : a.get n = .text old) :
    (patchNodeSlotAt a n [] "" val).get n = .text val ∧ ∀ m, m ≠ n → (patchNodeSlotAt a n [] "" val).get m = a.get m :=
  ⟨by simp [patchNodeSlotAt, DomArena.modify, hget], fun m hm => by simp [patchNodeSlotAt, DomArena.modify, hm]⟩

end
end Qed
