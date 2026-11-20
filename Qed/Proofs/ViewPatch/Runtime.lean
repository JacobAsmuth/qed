import Qed.Proofs.ViewPatch.Attrs

namespace Qed

/-! ## 4. Template Keyed Row Alignment, Signal Store & Diff Soundness -/

theorem diffRowSigs_sound {msg : Type} (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    ∀ (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) (accEv : Array (String × msg)),
      i ≤ newMarks.size → accSigs.size = i → (∀ k, k < i → accSigs[k]! = rowSig k) →
      let (outSigs, _) := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs i accSigs accEmit accEv
      outSigs.size = newMarks.size ∧ ∀ k, k < newMarks.size → outSigs[k]! = rowSig k := by
  intro i; induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro accSigs accEmit accEv hiLe hsz hprev; have hge : ¬ i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hge, ↓reduceDIte]; refine ⟨by omega, fun k hk => hprev k (by omega)⟩
  | succ _ ih =>
      intro accSigs accEmit accEv hiLe hsz hprev; have hlt : i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hlt, ↓reduceDIte]
      by_cases hskip : (newMarks[i] != 0 && oldMarks[i]? == some newMarks[i]) = true
      · simp only [hskip, ↓reduceIte]
        have hnz : newMarks[i]! ≠ 0 := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.1
        have hold : oldMarks[i]? = some newMarks[i]! := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.2
        have hsigEq : oldSigs[i]?.getD #[] = rowSig i := (hmark i hlt hnz hold).symm
        apply ih (i + 1) (by omega) (accSigs.push (oldSigs[i]?.getD #[])) accEmit accEv (by omega) (by simp [hsz])
        intro k hk; have hkLtPush : k < (accSigs.push (oldSigs[i]?.getD #[])).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          rw [getElem!_pos _ k hkLtPush, Array.getElem_push_lt hkLt, ← getElem!_pos accSigs k hkLt]
          exact hprev k hki
        · have heq : k = i := by omega
          subst heq
          have hPushIdx : (accSigs.push (oldSigs[k]?.getD #[]))[k]'hkLtPush = oldSigs[k]?.getD #[] := by
            subst hsz; exact Array.getElem_push_eq
          rw [getElem!_pos _ k hkLtPush, hPushIdx, hsigEq]
      · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
        apply ih (i + 1) (by omega) (accSigs.push (rowSig i)) _ _ (by omega) (by simp [hsz])
        intro k hk; have hkLtPush : k < (accSigs.push (rowSig i)).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          rw [getElem!_pos _ k hkLtPush, Array.getElem_push_lt hkLt, ← getElem!_pos accSigs k hkLt]
          exact hprev k hki
        · have heq : k = i := by omega
          subst heq
          have hPushIdx : (accSigs.push (rowSig k))[k]'hkLtPush = rowSig k := by
            subst hsz; exact Array.getElem_push_eq
          rw [getElem!_pos _ k hkLtPush, hPushIdx]

theorem seedRowsM_spec {msg : Type} (inst : String) (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg)
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    let res := (seedRowsM (m := StateM (DomArena msg)) inst rowSig rowEv newMarks oldMarks oldSigs).run a
    let d := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
    res.1.size = newMarks.size ∧ (∀ k, k < newMarks.size → res.1[k]! = rowSig k) ∧
    res.2.nextId = a.nextId ∧ res.2.store = a.store ∧
    res.2.signals = d.2.1.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals ∧
    res.2.sigEvents = d.2.2.toList.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents := by
  have hs := diffRowSigs_sound rowSig rowEv inst newMarks oldMarks oldSigs hmark 0 #[] #[] #[] (Nat.zero_le _) rfl (fun _ h => nomatch h)
  dsimp only [seedRowsM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  cases hd : diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[] with
  | mk newSigs rest =>
      rcases rest with ⟨toEmit, toEv⟩
      rw [hd] at hs; dsimp only at hs ⊢
      have he := emitSignalsM_spec toEmit.toList a
      dsimp only [StateT.run] at he
      rw [he]; dsimp only
      have hev := emitSignalOnsM_spec toEv.toList { a with signals := toEmit.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals }
      dsimp only [StateT.run] at hev
      rw [hev]; exact ⟨hs.1, hs.2, rfl, rfl, rfl, rfl⟩

theorem renderSig_resolved_spec {σ msg : Type} (ns : String) (get : σ → String)
    (s₁ s₂ : σ) (pre : String) (n : Nat) (a : DomArena msg) (f : Nat) (hbound : a.nextId + 1 < UInt32.size) :
    let (sigHtml, _, _) := View.renderSig (.dyn get : View σ msg) s₁ pre n
    let (root, aMid) := (buildDomM (m := StateM (DomArena msg)) ns sigHtml).run a
    let aOut := (MonadDom.setSignal (m := StateM (DomArena msg)) s!"{pre}#{n}" (get s₂) aMid).2
    readResolvedDomTree (f + 1) aOut root = specDom ns (View.render (.dyn get) s₂) ∧
    aOut.nextId = a.nextId + 1 ∧ ∀ m : Dom.Node, m.toNat < a.nextId → aOut.get m = a.get m := by
  let node := UInt32.ofNat a.nextId
  let sigNm := s!"{pre}#{n}"
  let realNs := if ns == "" && "span" == "svg" then Dom.svgNs else ns
  let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
  have haMid : (buildDomM (m := StateM (DomArena msg)) ns (.element "span" [.signalBind sigNm] [.text (get s₁)])).run a =
      (node, (applyAttrsM (m := StateM (DomArena msg)) node [.signalBind sigNm] (a1.set node (.element realNs "span" {} [] []))).2) := by
    dsimp only [buildDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.createElement, DomArena.alloc]
    have hset : ({ a with nextId := a.nextId + 1, store := fun m => if (m == node) = true then ArenaEntry.element realNs "span" {} [] [] else a.store m } : DomArena msg) =
        a1.set node (.element realNs "span" {} [] []) := rfl
    rw [hset]
    cases applyAttrsM (m := StateM (DomArena msg)) node [.signalBind sigNm] (a1.set node (.element realNs "span" {} [] [])); rfl
  have hev : (evalSpecAttrs ([Attr.signalBind sigNm] : List (Attr msg))).sigBind = some sigNm := rfl
  dsimp only [View.renderSig]
  rw [haMid, applyAttrsM_fresh_element a1 node realNs "span" [] [.signalBind sigNm]]
  simp only [sigNm, MonadDom.setSignal, View.render, specDom, readResolvedDomTree, DomArena.get,
    show (a1.set node (ArenaEntry.element realNs "span" (evalSpecAttrs [Attr.signalBind sigNm])
      (List.filterMap managedAttrName (normalizeAttrs [Attr.signalBind sigNm])) [])).store node =
      ArenaEntry.element realNs "span" (evalSpecAttrs [Attr.signalBind sigNm])
        (List.filterMap managedAttrName (normalizeAttrs [Attr.signalBind sigNm])) [] from DomArena.get_set_self _ _ _,
    hev, lookupAssoc_setAssoc, beq_self_eq_true, ↓reduceIte, Option.getD_some]
  refine ⟨trivial, rfl, fun m hm => ?_⟩
  have hne : m ≠ node := node_ne_of_toNat_ne (by dsimp only [node]; rw [uint32_toNat_ofNat_lt a.nextId (by omega)]; omega)
  exact DomArena.get_set_ne _ _ hne

/-! ## 5. Browser Runtime & Local Island Driver Specifications -/

theorem registerHandlerSpec_sound {α : Type} (arr : Array α) (h : α) :
    let id := arr.size; let arr' := arr.push h
    arr'[id]? = some h ∧ ∀ j, j < arr.size → arr'[j]? = arr[j]? :=
  ⟨by simp, fun j hj => by simp [Array.getElem?_push, Nat.ne_of_lt hj]⟩

structure LocalInstSpec where
  props : String
  rendered : Html LocalMsg

structure LocalRuntimeSpec where
  store     : Std.HashMap String String
  instances : Std.HashMap String LocalInstSpec

def localMountStep (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec)
    (key component : String) (init? : Option String) (props : String) : LocalRuntimeSpec :=
  let fk := localKey component key
  match reg[component]? with
  | none => st
  | some ldef =>
      match st.instances[fk]? with
      | some inst =>
          let next : LocalInstSpec := { props := props, rendered := if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered }
          { st with instances := st.instances.insert fk next }
      | none =>
          let s0 := st.store.getD fk (init?.getD ldef.init)
          { store := st.store.insert fk s0, instances := st.instances.insert fk { props, rendered := ldef.viewForProps props s0 } }

theorem localMountSpec_init_vs_rerender (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec)
    (key component : String) (init? : Option String) (props : String) (ldef : LocalDef) (hreg : reg[component]? = some ldef) :
    let fk := localKey component key; let st' := localMountStep reg st key component init? props
    (st.instances[fk]? = none → let s0 := st.store.getD fk (init?.getD ldef.init); st'.store[fk]? = some s0 ∧ st'.instances[fk]? = some ⟨props, ldef.viewForProps props s0⟩) ∧
    (∀ inst, st.instances[fk]? = some inst → st'.store = st.store ∧ st'.instances[fk]? = some ⟨props, if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered⟩) :=
  ⟨fun h => by simp [localMountStep, hreg, h], fun inst h => by simp [localMountStep, hreg, h]⟩

def gcLocalsSpec (isConn : String → Bool) (st : LocalRuntimeSpec) : LocalRuntimeSpec :=
  let dead := st.instances.toList.filterMap (fun (k, _) => if isConn k then none else some k)
  { store := dead.foldl (·.erase ·) st.store, instances := dead.foldl (·.erase ·) st.instances }

private theorem foldl_erase_mem {α : Type} :
    ∀ (ks : List String) (m : Std.HashMap String α) (k : String), k ∈ ks → (ks.foldl (·.erase ·) m)[k]? = none
  | [], _, _, h => nomatch h
  | x :: xs, m, k, h => by
      rcases List.mem_cons.1 h with rfl | ht
      · by_cases hx : k ∈ xs; exact foldl_erase_mem xs (m.erase k) k hx
        have hf : ∀ (l : List String) (m' : Std.HashMap String α), k ∉ l → (l.foldl (·.erase ·) m')[k]? = m'[k]? := by
          intro l; induction l with
          | nil => intro _ _; rfl
          | cons y ys ihl =>
              intro m' hnl; have hne : y ≠ k := fun hEq => hnl (hEq ▸ .head _)
              simpa [List.foldl_cons, Std.HashMap.getElem?_erase, beq_eq_false_iff_ne.2 hne] using ihl (m'.erase y) (fun hm => hnl (.tail _ hm))
        simpa [List.foldl_cons] using hf xs (m.erase k) hx
      · exact foldl_erase_mem xs (m.erase x) k ht

private theorem foldl_erase_not_mem {α : Type} :
    ∀ (ks : List String) (m : Std.HashMap String α) (k : String), k ∉ ks → (ks.foldl (·.erase ·) m)[k]? = m[k]?
  | [], _, _, _ => rfl
  | x :: xs, m, k, h => by
      have hne : x ≠ k := fun hEq => h (hEq ▸ .head _)
      simpa [List.foldl_cons, Std.HashMap.getElem?_erase, beq_eq_false_iff_ne.2 hne] using foldl_erase_not_mem xs (m.erase x) k (fun hm => h (.tail _ hm))

theorem gcLocalsSpec_frame (isConn : String → Bool) (st : LocalRuntimeSpec) (k : String) :
    let st' := gcLocalsSpec isConn st
    (isConn k = true → st'.store[k]? = st.store[k]? ∧ st'.instances[k]? = st.instances[k]?) ∧
    ((∃ inst, (k, inst) ∈ st.instances.toList) → isConn k = false → st'.store[k]? = none ∧ st'.instances[k]? = none) := by
  let dead := st.instances.toList.filterMap (fun p => if isConn p.1 then none else some p.1)
  have hmem : ∀ x, x ∈ dead ↔ (∃ v, (x, v) ∈ st.instances.toList) ∧ isConn x = false := by
    intro x; simp only [dead, List.mem_filterMap]; constructor
    · rintro ⟨⟨a, v⟩, hm, hp⟩; split at hp <;> simp at hp; subst hp; exact ⟨⟨v, hm⟩, Bool.eq_false_iff.2 ‹_›⟩
    · rintro ⟨⟨v, hm⟩, hc⟩; exact ⟨(x, v), hm, by simp [hc]⟩
  refine ⟨fun hc => ?_, fun ⟨v, hv⟩ hc => ?_⟩
  · have hnd : k ∉ dead := fun hd => by rw [(hmem k).1 hd |>.2] at hc; cases hc
    exact ⟨foldl_erase_not_mem dead st.store k hnd, foldl_erase_not_mem dead st.instances k hnd⟩
  · have hd : k ∈ dead := (hmem k).2 ⟨⟨v, hv⟩, hc⟩
    exact ⟨foldl_erase_mem dead st.store k hd, foldl_erase_mem dead st.instances k hd⟩

def snapshotLocalsJson (entries : List (String × String)) : String :=
  Json.render (Json.obj (entries.map fun (k, v) => (k, .str v)))

def restoreLocalsFromJson (s : String) (base : Std.HashMap String String) : Std.HashMap String String :=
  match Json.parse s with
  | .ok (.obj members) => members.foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) base
  | _ => base

theorem snapshot_restore_locals_roundtrip (entries : List (String × String))
    (hnd : (entries.map Prod.fst).Nodup) (base : Std.HashMap String String) :
    let out := restoreLocalsFromJson (snapshotLocalsJson entries) base
    ∀ kv ∈ entries, out[kv.1]? = some kv.2 := by
  have hdep : (Json.obj (entries.map fun x => (x.1, Json.str x.2))).depth ≤ 64 := by
    have hm : Json.maxObj (entries.map fun x => (x.1, Json.str x.2)) ≤ 0 :=
      Json.maxObj_le_iff.2 fun kv hkv => by rcases List.mem_map.1 hkv with ⟨p, _, rfl⟩; exact Nat.le_refl _
    dsimp only [Json.depth]; omega
  have hpr := parse_render hdep
  have hfold : ∀ (es : List (String × String)) (b : Std.HashMap String String), (es.map Prod.fst).Nodup →
      ∀ kv ∈ es, ((es.map fun (k, v) => (k, Json.str v)).foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) b)[kv.1]? = some kv.2 := by
    intro es; induction es with
    | nil => intro _ _ _ hm; nomatch hm
    | cons kv rest ih =>
        intro b hnde p hp; rcases List.nodup_cons.1 hnde with ⟨hnotin, hndr⟩
        rcases List.mem_cons.1 hp with rfl | ht
        · have hpres : ∀ (rs : List (String × String)) (b' : Std.HashMap String String), p.1 ∉ rs.map Prod.fst →
              ((rs.map fun (k, v) => (k, Json.str v)).foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) b')[p.1]? = b'[p.1]? := by
            intro rs; induction rs with
            | nil => intro _ _; rfl
            | cons q qt ihr =>
                intro b' hnm; have hne : q.1 ≠ p.1 := fun h => hnm (h ▸ .head _)
                simpa [List.foldl_cons, Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.2 hne] using ihr (b'.insert q.1 q.2) (fun hm => hnm (.tail _ hm))
          simpa [List.foldl_cons] using (hpres rest (b.insert p.1 p.2) hnotin).trans (by simp)
        · exact ih (b.insert kv.1 kv.2) hndr p ht
  simpa [restoreLocalsFromJson, snapshotLocalsJson, hpr] using hfold entries base hnd

def drainQueueSpec {σ Msg : Type} (step : σ → Msg → σ × List Msg) :
    Nat → σ → Array Msg → σ × Array Msg
  | 0, st, q => (st, q)
  | fuel + 1, st, q =>
      if q.isEmpty then (st, #[])
      else
        let (st', nextQ) := q.toList.foldl (fun (acc, nxt) m => let (s', sp) := step acc m; (s', nxt ++ sp)) (st, [])
        drainQueueSpec step fuel st' nextQ.toArray

theorem drainPendingQueue_fifo_spec {σ Msg : Type} (step : σ → Msg → σ)
    (st : σ) (q : Array Msg) (fuel : Nat) (hf : 0 < fuel) :
    drainQueueSpec (fun s m => (step s m, [])) fuel st q = (q.toList.foldl step st, #[]) := by
  cases fuel with
  | zero => omega
  | succ f =>
      dsimp only [drainQueueSpec]
      by_cases hemp : q.isEmpty
      · have hnil : q.toList = [] := by cases q; simp_all
        simp [hemp, hnil]
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        have hfold : ∀ (ms : List Msg) (s : σ) (acc : List Msg),
            ms.foldl (fun p m => (step p.1 m, p.2 ++ [])) (s, acc) = (ms.foldl step s, acc) := by
          intro ms; induction ms with | nil => intro _ _; rfl | cons m ms ih => intro s acc; simpa [List.foldl_cons] using ih (step s m) acc
        rw [hfold q.toList st []]; cases f <;> simp [drainQueueSpec]

private theorem renderSigAttrs_of_dynValGets_empty {σ msg : Type} (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), dynValGets attrs = [] → dynOnGets attrs = [] →
      (renderSigAttrs s pre attrs n en).1 = attrs.map (VAttr.eval s)
  | [], _, _, _, _ => rfl
  | .stat _ :: rest, n, en, h, he => by simp [renderSigAttrs, VAttr.eval, renderSigAttrs_of_dynValGets_empty s pre rest n en h he]
  | .bind _ :: rest, n, en, h, he => by simp [renderSigAttrs, VAttr.eval, renderSigAttrs_of_dynValGets_empty s pre rest n en h he]
  | .dynVal _ _ :: _, _, _, h, _ => by simp [dynValGets] at h
  | .dynOn _ _ :: _, _, _, _, he => by simp [dynOnGets] at he

mutual
  private theorem renderSig_of_collectDyn_empty {σ msg : Type} :
      ∀ (v : View σ msg), v.collectDyn = [] → v.collectDynOn = [] → ∀ (s : σ) (pre : String) (n en : Nat),
        (v.renderSig s pre n en).1 = v.render s
    | .text _, _, _, _, _, _, _ | .keyedList .., _, _, _, _, _, _ | .static _, _, _, _, _, _, _
    | .dynNode _, _, _, _, _, _, _ | .memo _, _, _, _, _, _, _ => rfl
    | .dyn _, h, _, _, _, _, _ => by simp [View.collectDyn] at h
    | .element _ attrs kids, h, he, s, pre, n, en => by
        simp only [View.collectDyn, List.append_eq_nil_iff] at h
        simp only [View.collectDynOn, List.append_eq_nil_iff] at he
        simp only [View.renderSig, View.render,
          renderSigAttrs_of_dynValGets_empty s pre attrs n en h.1 he.1,
          renderSigList_of_collectDynList_empty kids h.2 he.2 s pre]
    | .ifElse cond y no, h, he, s, pre, n, en => by
        simp only [View.collectDyn, List.append_eq_nil_iff] at h
        simp only [View.collectDynOn, List.append_eq_nil_iff] at he
        by_cases hc : cond s = true <;>
          simp [View.renderSig, View.render, hc,
            renderSig_of_collectDyn_empty y h.1 he.1 s pre n en,
            renderSig_of_collectDyn_empty no h.2 he.2 s pre]

  private theorem renderSigList_of_collectDynList_empty {σ msg : Type} :
      ∀ (ks : List (View σ msg)), View.collectDynList ks = [] → View.collectDynOnList ks = [] →
        ∀ (s : σ) (pre : String) (n en : Nat), (View.renderSigList ks s pre n en).1 = View.renderEach ks s
    | [], _, _, _, _, _, _ => rfl
    | k :: ks, h, he, s, pre, n, en => by
        simp only [View.collectDynList, List.append_eq_nil_iff] at h
        simp only [View.collectDynOnList, List.append_eq_nil_iff] at he
        simp [View.renderSigList, View.renderEach,
          renderSig_of_collectDyn_empty k h.1 he.1 s pre n en,
          renderSigList_of_collectDynList_empty ks h.2 he.2 s pre]
end

private theorem getElem?_map_zipIdx {α β : Type} (g : α × Nat → β) :
    ∀ (xs : List α) (k i : Nat), ((xs.zipIdx k).map g)[i]? = xs[i]?.map (fun a => g (a, k + i))
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp [List.zipIdx]
  | _ :: rest, k, i + 1 => by simpa [List.zipIdx, Nat.add_assoc, Nat.add_comm 1 i] using getElem?_map_zipIdx g rest (k + 1) i

private theorem Html.DomCleanList_map {α msg : Type} (f : α → Html msg) :
    ∀ (xs : List α), (∀ a ∈ xs, (f a).DomClean = true) → Html.DomCleanList (xs.map f) = true
  | [], _ => rfl
  | x :: rest, h => by simp [Html.DomCleanList, h x (.head _), Html.DomCleanList_map f rest (fun a ha => h a (.tail _ ha))]

theorem View.DomClean_forEach {α σ msg : Type} (tag : String) (items : σ → Array α)
    (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String)
    (ha : VAttrListClean attrs)
    (hdyn : (View.collectDyn child).isEmpty = true)
    (hdynOn : (View.collectDynOn child).isEmpty = true)
    (hcl : ∀ a, (child.render a).DomClean = true)
    (htxt : ∀ a, (child.render a).textOf? = none)
    (hnd : ∀ s, (((items s).map key).toList).Nodup)
    (hkey : ∀ a b, key a = key b → child.render a = child.render b) :
    View.DomClean (V.forEach tag items key child attrs sigPrefix) := by
  dsimp only [V.forEach]
  have hnotDirect : V.isDirectTmpl child = false := by
    cases child with
    | element _ _ _ => simp [V.isDirectTmpl, hdyn, hdynOn]
    | _ => rfl
  split
  · intro s
    simp only [Html.DomClean, ha.1 s, ha.2.1 s, Bool.not_false, Bool.true_and, Array.toList_map]
    exact Html.DomCleanList_map _ _ fun a _ => by simp [Html.DomClean_withKey, hcl a]
  · simp only [hnotDirect, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ha, ?_, ?_, ?_, ?_⟩
    · intro s
      dsimp only
      have h1 : disambiguateKeys ((items s).map key) = (items s).map key := disambiguateKeys_of_nodup (by simpa using hnd s)
      rw [h1]
      simp [List.length_map, List.length_zipIdx]
    · intro s
      dsimp only
      have hde : child.collectDyn = [] := List.isEmpty_iff.1 hdyn
      have hdo : child.collectDynOn = [] := List.isEmpty_iff.1 hdynOn
      exact Html.DomCleanList_map _ _ fun p _ => by
        simp [Html.DomClean_withKey, renderSig_of_collectDyn_empty child hde hdo p.1, hcl p.1]
    · intro s r hr
      dsimp only at hr
      rcases List.mem_map.1 hr with ⟨p, _, rfl⟩
      rw [Html.textOf?_withKey, renderSig_of_collectDyn_empty child (List.isEmpty_iff.1 hdyn) (List.isEmpty_iff.1 hdynOn)]
      exact htxt p.1
    · intro s₁ s₂ i j hi hj hkeq
      dsimp only at hi hj hkeq ⊢
      have hde : child.collectDyn = [] := List.isEmpty_iff.1 hdyn
      have hdo : child.collectDynOn = [] := List.isEmpty_iff.1 hdynOn
      have hu1 : disambiguateKeys ((items s₁).map key) = (items s₁).map key := disambiguateKeys_of_nodup (by simpa using hnd s₁)
      have hu2 : disambiguateKeys ((items s₂).map key) = (items s₂).map key := disambiguateKeys_of_nodup (by simpa using hnd s₂)
      have hi' : i < (items s₁).size := by simpa [hu1] using hi
      have hj' : j < (items s₂).size := by simpa [hu2] using hj
      have hkaEq : key (items s₁)[i] = key (items s₂)[j] := by simpa [hu1, hu2] using hkeq
      rw [getElem?_map_zipIdx _ (items s₁).toList 0 i, getElem?_map_zipIdx _ (items s₂).toList 0 j]
      simp only [Nat.zero_add, Array.getElem?_toList, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hj', Option.map_some]
      rw [renderSig_of_collectDyn_empty child hde hdo, renderSig_of_collectDyn_empty child hde hdo]
      have hd1 : (disambiguateKeys ((items s₁).map key)).getD i (key (items s₁)[i]) = key (items s₁)[i] := by simp [hu1, Array.getD, hi']
      have hd2 : (disambiguateKeys ((items s₂).map key)).getD j (key (items s₂)[j]) = key (items s₂)[j] := by simp [hu2, Array.getD, hj']
      rw [hd1, hd2, hkaEq, hkey _ _ hkaEq]

/-! ## 6. Compiled Row-Template & Prefix/Suffix/Swap Fast-Path Soundness -/

theorem prefixMatchLen_bound (oldMarks newMarks : Array USize) :
    ∀ i, i ≤ oldMarks.size → i ≤ newMarks.size →
      prefixMatchLen oldMarks newMarks i ≤ oldMarks.size ∧
      prefixMatchLen oldMarks newMarks i ≤ newMarks.size := by
  intro i
  induction hrem : oldMarks.size - i generalizing i with
  | zero =>
      intro ho hn; unfold prefixMatchLen; split
      · omega
      · exact ⟨ho, hn⟩
  | succ r ih =>
      intro ho hn; unfold prefixMatchLen; split
      · rename_i h
        dsimp only
        split
        · exact ih (i + 1) (by omega) (by omega) (by omega)
        · exact ⟨ho, hn⟩
      · exact ⟨ho, hn⟩

theorem prefixMatchLen_sound (oldMarks newMarks : Array USize) :
    ∀ i k, i ≤ k → k < prefixMatchLen oldMarks newMarks i →
      ∃ (ho : k < oldMarks.size) (hn : k < newMarks.size),
        newMarks[k]'hn ≠ 0 ∧ oldMarks[k]'ho = newMarks[k]'hn := by
  intro i
  induction hrem : oldMarks.size - i generalizing i with
  | zero =>
      intro k hik hklt
      unfold prefixMatchLen at hklt
      split at hklt <;> omega
  | succ r ih =>
      intro k hik hklt
      unfold prefixMatchLen at hklt
      split at hklt
      · rename_i h
        dsimp only at hklt
        split at hklt
        · rename_i hm
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
          by_cases heq : k = i
          · subst heq; exact ⟨h.1, h.2, hm.1, hm.2⟩
          · exact ih (i + 1) (by omega) k (by omega) hklt
        · omega
      · omega

theorem suffixMatchLen_sound (oldMarks newMarks : Array USize) (p : Nat) :
    ∀ q j, q ≤ j → j < suffixMatchLen oldMarks newMarks p q →
      p + j < oldMarks.size ∧ p + j < newMarks.size ∧
      ∃ (ho : oldMarks.size - 1 - j < oldMarks.size) (hn : newMarks.size - 1 - j < newMarks.size),
        newMarks[newMarks.size - 1 - j]'hn ≠ 0 ∧
        oldMarks[oldMarks.size - 1 - j]'ho = newMarks[newMarks.size - 1 - j]'hn := by
  intro q
  induction hrem : oldMarks.size - (p + q) generalizing q with
  | zero =>
      intro j hqj hjlt
      unfold suffixMatchLen at hjlt
      split at hjlt <;> omega
  | succ r ih =>
      intro j hqj hjlt
      unfold suffixMatchLen at hjlt
      split at hjlt
      · rename_i h
        dsimp only at hjlt
        split at hjlt
        · rename_i hm
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
          by_cases heq : j = q
          · subst heq; exact ⟨h.1, h.2, by omega, by omega, hm.1, hm.2⟩
          · exact ih (q + 1) (by omega) j (by omega) hjlt
        · omega
      · omega

private theorem mem_collectChangedMarksLoop_of_mem (oldMarks newMarks : Array USize) :
    ∀ i (acc : Array Nat) x, x ∈ acc.toList → x ∈ (collectChangedMarksLoop oldMarks newMarks i acc).toList := by
  intro i
  induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro acc x hx; unfold collectChangedMarksLoop
      split
      · omega
      · exact hx
  | succ r ih =>
      intro acc x hx; unfold collectChangedMarksLoop
      split
      · rename_i h
        apply ih (i + 1) (by omega)
        split
        · exact hx
        · rw [Array.toList_push]; exact List.mem_append_left _ hx
      · exact hx

theorem collectChangedMarksLoop_sound (oldMarks newMarks : Array USize) :
    ∀ i (acc : Array Nat) k (hk : k < newMarks.size),
      i ≤ k → k ∉ (collectChangedMarksLoop oldMarks newMarks i acc).toList →
      newMarks[k]'hk ≠ 0 ∧ oldMarks[k]? = some (newMarks[k]'hk) := by
  intro i
  induction hrem : newMarks.size - i generalizing i with
  | zero => intro _ k hk hik _; omega
  | succ r ih =>
      intro acc k hk hik hnot
      unfold collectChangedMarksLoop at hnot
      simp only [show i < newMarks.size by omega, ↓reduceDIte] at hnot
      by_cases heq : k = i
      · subst heq
        by_cases hm : (newMarks[k]'hk != 0 && oldMarks[k]? == some (newMarks[k]'hk)) = true
        · simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hm
        · have hmf : (newMarks[k]'hk != 0 && oldMarks[k]? == some (newMarks[k]'hk)) = false := Bool.eq_false_iff.2 hm
          simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hnot
          have hmem : k ∈ (collectChangedMarksLoop oldMarks newMarks (k + 1) (acc.push k)).toList :=
            mem_collectChangedMarksLoop_of_mem oldMarks newMarks (k + 1) (acc.push k) k (by rw [Array.toList_push]; simp)
          exact False.elim (hnot hmem)
      · exact ih (i + 1) (by omega) _ k hk (by omega) hnot

theorem patchNodeSlotAt_nextId {msg : Type} (a : DomArena msg) (n : Dom.Node)
    (path : List Nat) (attrName val : String) :
    (patchNodeSlotAt a n path attrName val).nextId = a.nextId := by
  induction path generalizing n with
  | nil =>
      dsimp only [patchNodeSlotAt]
      split
      · rfl
      · split <;> rfl
  | cons idx rest ih =>
      dsimp only [patchNodeSlotAt]
      cases a.get n with
      | element _ _ _ _ cs =>
          dsimp only
          cases cs[idx]? with
          | none => rfl
          | some child => exact ih child
      | _ => rfl

theorem patchNodeSlotAt_text_root {msg : Type} (a : DomArena msg) (n : Dom.Node) (old val : String)
    (hget : a.get n = .text old) :
    (patchNodeSlotAt a n [] "" val).get n = .text val ∧
    ∀ m, m ≠ n → (patchNodeSlotAt a n [] "" val).get m = a.get m := by
  refine ⟨?_, ?_⟩
  · simp [patchNodeSlotAt, DomArena.modify, hget]
  · intro m hm; simp [patchNodeSlotAt, DomArena.modify, hm]

end Qed
