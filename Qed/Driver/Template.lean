import Qed.Driver.Vdom

namespace Qed

inductive VState (σ : Type) (msg : Type) where
  | text (node : Dom.Node)
  | dyn (node : Dom.Node) (last : String)
  | elem (node : Dom.Node) (kids : List (VState σ msg))
  | cond (wasYes : Bool) (inner : VState σ msg)
  | list (node : Dom.Node) (keys : Array String) (sigs : Array (Array (String × String))) (rows : List (Html msg)) (marks : Array USize) (inst : String)
  | tlist (node : Dom.Node) (tmplId : UInt32) (evSlot : UInt32) (keys : Array String) (hasDups : Bool) (live : Array Dom.Node) (vals : Array (Array String)) (marks : Array USize)
  | stat (node : Dom.Node)
  | dynNode (node : Dom.Node) (last : Html msg)
  | memo (node : Dom.Node) (lastKey : String) (lastHtml : Html msg)

instance : Inhabited (VState σ msg) := ⟨.text 0⟩

/-! ## Bare-Array `O(N)` Key Index & Certifying `O(N log N)` LIS Minimal-Moves Reconciler -/

def kpLookupList (k : String) : List (String × Nat) → Option Nat
  | [] => none | (k', v) :: rest => if k' == k then some v else kpLookupList k rest
@[inline] def keyIndexGet (buckets : @& Array (List (String × Nat))) (mask : USize) (k : String) : Option Nat :=
  if h : 0 < buckets.size then kpLookupList k (buckets[strBucketIdx k mask buckets.size]'(strBucketIdx_lt k mask buckets.size h)) else none
def buildKeyIndexLoop (keys : @& Array String) (i : Nat) (buckets : Array (List (String × Nat))) (mask : USize) : Array (List (String × Nat)) :=
  if h : i < keys.size then
    let k := keys[i]
    let buckets' := if hb : 0 < buckets.size then
        let bi := strBucketIdx k mask buckets.size; have hbi := strBucketIdx_lt k mask buckets.size hb
        buckets.set bi ((k, i) :: buckets[bi]) hbi
      else buckets
    buildKeyIndexLoop keys (i + 1) buckets' mask
  else buckets
termination_by keys.size - i
decreasing_by exact Nat.sub_succ_lt_self keys.size i h
def buildKeyIndex (keys : Array String) : Array (List (String × Nat)) × USize :=
  let cap := nextPow2Ge (keys.size * 2) 16 30; let mask := USize.ofNat (cap - 1)
  (buildKeyIndexLoop keys 0 (Array.replicate cap []) mask, mask)
def planKeyedLoop (newKeys : @& Array String) (oldBuckets : @& Array (List (String × Nat))) (mask : USize)
    (oldRows : @& Array (Html msg)) (oldMarks : @& Array USize) (oldSigs : @& Array (Array (String × String)))
    (fresh : Unit → Array (Html msg)) (freshCache : Option (Array (Html msg))) (i : Nat)
    (sources : Array (Option Nat)) (used : Array Bool) (rows : Array (Html msg)) (marks : Array USize) (sigs : Array (Array (String × String))) :
    Array (Option Nat) × Array Bool × Array (Html msg) × Array USize × Array (Array (String × String)) :=
  if h : i < newKeys.size then
    match keyIndexGet oldBuckets mask newKeys[i] with
    | some oi =>
        let used' := if ho : oi < used.size then used.set oi true ho else used
        planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh freshCache (i + 1)
          (sources.push (some oi)) used' (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
    | none =>
        let (fArr, fCache) := match freshCache with | some a => (a, some a) | none => let a := fresh (); (a, some a)
        planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh fCache (i + 1)
          (sources.push none) used (rows.push (fArr.getD i default)) (marks.push 0) (sigs.push #[])
  else (sources, used, rows, marks, sigs)
termination_by newKeys.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newKeys.size i h

private def computeLisRaw (sources : Array (Option Nat)) : Array Bool :=
  let n := sources.size
  let rec lb (tails : @& Array Nat) (x lo hi : Nat) : Nat :=
    if h : lo < hi then let mid := lo + (hi - lo) / 2; if tails.getD mid 0 < x then lb tails x (mid + 1) hi else lb tails x lo mid else lo
  termination_by hi - lo
  decreasing_by all_goals omega
  let (_, _, tailPos, prev) := sources.foldl (init := (0, Array.emptyWithCapacity n, Array.emptyWithCapacity n, Array.replicate n n))
    fun (i, tails, tailPos, prev) s? => match s? with
      | none => (i + 1, tails, tailPos, prev)
      | some oi =>
          let pos := lb tails oi 0 tails.size; let prev' := prev.setIfInBounds i (if pos > 0 then tailPos.getD (pos - 1) n else n)
          if hp : pos < tails.size then (i + 1, tails.set pos oi hp, tailPos.setIfInBounds pos i, prev')
          else (i + 1, tails.push oi, tailPos.push i, prev')
  let rec trace (cur : Nat) (fl : Array Bool) : Nat → Array Bool
    | 0 => fl
    | fuel + 1 => if h : cur < fl.size then
        let fl' := fl.set cur true h; let nxt := prev.getD cur n; if nxt < n then trace nxt fl' fuel else fl' else fl
  if h : 0 < tailPos.size then trace (tailPos[tailPos.size - 1]'(Nat.sub_lt h Nat.zero_lt_one)) (Array.replicate n false) n else Array.replicate n false
def isValidLisLoop (sources : @& Array (Option Nat)) (flags : @& Array Bool) (i : Nat) (last? : Option Nat) : Bool :=
  if h : i < sources.size then
    if flags.getD i false then match sources[i] with
      | some oi => match last? with
          | none => isValidLisLoop sources flags (i + 1) (some oi)
          | some prev => if prev < oi then isValidLisLoop sources flags (i + 1) (some oi) else false
      | none => false
    else isValidLisLoop sources flags (i + 1) last?
  else true
termination_by sources.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self sources.size i h
def verifiedLisFlags (sources : Array (Option Nat)) : Array Bool :=
  let raw := computeLisRaw sources
  if raw.size == sources.size && isValidLisLoop sources raw 0 none then raw else Array.replicate sources.size false
def removeUnusedM [MonadDom msg m] (node : Dom.Node) (live : Array Dom.Node) (used : Array Bool) (i : Nat) : m Unit :=
  if h : i < live.size then
    if used.getD i false then removeUnusedM node live used (i + 1)
    else do MonadDom.removeNode node live[i]; removeUnusedM node live used (i + 1)
  else pure ()
termination_by live.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self live.size i h
def reconcileLisBackM [MonadDom msg m] (node : Dom.Node) (childNs : String) (live : Array Dom.Node)
    (sources : Array (Option Nat)) (inLis : Array Bool) (newRows : Array (Html msg)) : Nat → Bool → Dom.Node → m Unit
  | 0, _, _ => pure ()
  | k + 1, hasAnchor, anchor =>
      match sources.getD k none with
      | some oi =>
          let child := live.getD oi 0
          if inLis.getD k false then reconcileLisBackM node childNs live sources inLis newRows k true child
          else do MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) child
                  reconcileLisBackM node childNs live sources inLis newRows k true child
      | none => do
          let cn ← buildDomM childNs (newRows.getD k default)
          MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) cn
          reconcileLisBackM node childNs live sources inLis newRows k true cn

-- Pure tail recursion so the JS backend trampolines it instead of overflowing the stack on 10k-row `IO` binds.
def diffRowSigs {msg : Type} (rowSig : Nat → Array (String × String)) (rowEv : Nat → Array (String × msg)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (i : Nat)
    (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) (accEv : Array (String × msg)) :
    Array (Array (String × String)) × Array (String × String) × Array (String × msg) :=
  if h : i < newMarks.size then
    let m := newMarks[i]
    if m != 0 && oldMarks[i]? == some m then
      diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs (i + 1) (accSigs.push (oldSigs[i]?.getD #[])) accEmit accEv
    else
      let rsig := rowSig i; let old := oldSigs[i]?.getD #[]
      let emit' := (rsig.foldl (init := (0, accEmit)) fun (j, acc) (nm, v) =>
        (j + 1, if old[j]?.map (·.2) == some v then acc else acc.push (inst ++ nm, v))).2
      let ev' := (rowEv i).foldl (init := accEv) fun acc (nm, ev) => acc.push (inst ++ nm, ev)
      diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs (i + 1) (accSigs.push rsig) emit' ev'
  else (accSigs, accEmit, accEv)
termination_by newMarks.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newMarks.size i h
def emitSignalsM [MonadDom msg m] : List (String × String) → m Unit
  | [] => pure () | (nm, v) :: rest => do MonadDom.setSignal nm v; emitSignalsM rest
def emitSignalOnsM [MonadDom msg m] : List (String × msg) → m Unit
  | [] => pure () | (nm, ev) :: rest => do MonadDom.setSignalOn nm ev; emitSignalOnsM rest
def seedRowsM [MonadDom msg m] (inst : String) (rowSig : Nat → Array (String × String)) (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) : m (Array (Array (String × String))) := do
  let (newSigs, toEmit, toEv) := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
  emitSignalsM toEmit.toList; emitSignalOnsM toEv.toList; return newSigs

/-! ## Compiled Row-Template Fast-Path Helpers -/
@[inline] private def disambiguateWithFlag (rawKs : Array String) : Array String × Bool :=
  let uKeys := disambiguateKeys rawKs; (uKeys, uKeys != rawKs)
private def mountFreshTmplRowsM [MonadDom msg m] (node : Dom.Node) (tmplId evSlot : UInt32) (uKeys : Array String)
    (hasDups : Bool) (rowVals : Nat → Array String) (count : Nat) (newMarks : Array USize) : m (VState σ msg) := do
  if count == 0 then return .tlist node tmplId evSlot #[] false #[] #[] #[]
  let newVals := Array.ofFn (n := count) fun i => rowVals i.1
  return .tlist node tmplId evSlot uKeys hasDups (← MonadDom.mountTmplRows node tmplId newVals) newVals newMarks
private def initRowTmplM [MonadDom msg m] (node : Dom.Node) (childNs : String) (tmpl : RowTmpl σ msg) (s : σ) : m (UInt32 × UInt32) := do
  let tmplId ← MonadDom.compileRowTmpl childNs tmpl.proto tmpl.slotPaths tmpl.slotAttrs tmpl.evPaths tmpl.evNames
  return (tmplId, ← if tmpl.evNames.isEmpty then pure 0 else MonadDom.allocRowEvSlot node (tmpl.rowEvAt s))
def collectChangedMarksLoop (oldMarks newMarks : @& Array USize) (i : Nat) (acc : Array Nat) : Array Nat :=
  if h : i < newMarks.size then
    let m := newMarks[i]
    collectChangedMarksLoop oldMarks newMarks (i + 1) (if m != 0 && oldMarks[i]? == some m then acc else acc.push i)
  else acc
termination_by newMarks.size - i
decreasing_by exact Nat.sub_succ_lt_self newMarks.size i h
def prefixMatchLen (oldMarks newMarks : @& Array USize) (i : Nat) : Nat :=
  if h : i < oldMarks.size ∧ i < newMarks.size then
    let m := newMarks[i]'h.2
    if m != 0 && oldMarks[i]'h.1 == m then prefixMatchLen oldMarks newMarks (i + 1) else i
  else i
termination_by oldMarks.size - i
decreasing_by exact Nat.sub_succ_lt_self oldMarks.size i h.1
def suffixMatchLen (oldMarks newMarks : @& Array USize) (p q : Nat) : Nat :=
  if h : p + q < oldMarks.size ∧ p + q < newMarks.size then
    let m := newMarks[newMarks.size - 1 - q]'(by omega)
    if m != 0 && oldMarks[oldMarks.size - 1 - q]'(by omega) == m then suffixMatchLen oldMarks newMarks p (q + 1) else q
  else q
termination_by oldMarks.size - (p + q)
decreasing_by exact Nat.sub_succ_lt_self oldMarks.size (p + q) h.1

private def patchTmplListM [MonadDom msg m] (node : Dom.Node) (attrs : List (VAttr σ msg)) (keys : σ → Array String)
    (marks : σ → Array USize) (tmpl : RowTmpl σ msg) (s : σ) (tmplId evSlot : UInt32) (oldKeys : Array String)
    (oldDups : Bool) (oldLive : Array Dom.Node) (oldVals : Array (Array String)) (oldMarks : Array USize) : m (VState σ msg) := do
  if !tmpl.evNames.isEmpty then MonadDom.setRowEvSlot evSlot (tmpl.rowEvAt s)
  applyDynAttrsM node attrs s
  let (newMarks, nOld, rowVals) := (marks s, oldMarks.size, tmpl.rowVals s); let nNew := newMarks.size
  let mk ks dups lv vs : VState σ msg := .tlist node tmplId evSlot ks dups lv vs newMarks
  let patchDirty (dst src : Nat) (rn : Dom.Node) : m (Array String) := do
    let ov := oldVals.getD src #[]; let m := newMarks.getD dst 0
    if m != 0 && oldMarks[src]? == some m then pure ov else do let v := rowVals dst; MonadDom.patchTmplRow rn tmplId v ov; pure v
  let patchIdxs (idxs : Array Nat) : m (Array (Array String)) :=
    idxs.foldlM (init := oldVals) fun acc idx => do
      let nv := rowVals idx; MonadDom.patchTmplRow (oldLive.getD idx 0) tmplId nv (acc.getD idx #[]); return acc.setIfInBounds idx nv
  if nNew == 0 then
    if nOld > 0 then MonadDom.clearChildren node
    return .tlist node tmplId evSlot #[] false #[] #[] #[]
  if nOld == 0 then let (uKeys, hasDups) := disambiguateWithFlag (keys s); return ← mountFreshTmplRowsM node tmplId evSlot uKeys hasDups rowVals nNew newMarks
  if !oldDups then
    if nOld == nNew then
      let changed := collectChangedMarksLoop oldMarks newMarks 0 #[]
      if changed.isEmpty then return mk oldKeys false oldLive oldVals
      if changed.all fun idx => tmpl.rowKey s idx == oldKeys.getD idx "" then return mk oldKeys false oldLive (← patchIdxs changed)
      if h2 : changed.size = 2 then
        let (a, b) := (changed[0]'(h2 ▸ Nat.zero_lt_two), changed[1]'(h2 ▸ Nat.one_lt_two))
        let (ka, kb) := (tmpl.rowKey s a, tmpl.rowKey s b)
        if ka == oldKeys.getD b "" && kb == oldKeys.getD a "" then
          let (nodeA, nodeB) := (oldLive.getD a 0, oldLive.getD b 0)
          MonadDom.insertBeforeRef node (some nodeA) nodeB
          if b != a + 1 then MonadDom.insertBeforeRef node (if b + 1 < nOld then some (oldLive.getD (b + 1) 0) else none) nodeA
          return mk ((oldKeys.set! a ka).set! b kb) false ((oldLive.set! a nodeB).set! b nodeA)
            ((oldVals.set! a (← patchDirty a b nodeB)).set! b (← patchDirty b a nodeA))
    else
      let p := prefixMatchLen oldMarks newMarks 0
      if p == nOld && nNew > nOld then
        let addCount := nNew - nOld; let tailVals := Array.ofFn (n := addCount) fun i => rowVals (nOld + i.1)
        let (uKeys, hasDups) := disambiguateWithFlag (oldKeys ++ Array.ofFn (n := addCount) fun i => tmpl.rowKey s (nOld + i.1))
        return mk uKeys hasDups (oldLive ++ (← MonadDom.mountTmplRows node tmplId tailVals)) (oldVals ++ tailVals)
      if nNew < nOld then
        let q := suffixMatchLen oldMarks newMarks p 0
        if p + q == nNew then
          (oldLive.extract p (nOld - q)).forM (MonadDom.removeNode node)
          let keep {α} (arr : Array α) := arr.extract 0 p ++ arr.extract (nOld - q) nOld
          return mk (keep oldKeys) false (keep oldLive) (keep oldVals)
  let (newKeys, hasDups) := disambiguateWithFlag (keys s)
  if newKeys == oldKeys then return mk oldKeys hasDups oldLive (← patchIdxs (collectChangedMarksLoop oldMarks newMarks 0 #[]))
  let (oldBuckets, mask) := buildKeyIndex oldKeys
  let (sources, used) := newKeys.foldl (init := (Array.emptyWithCapacity nNew, Array.replicate oldKeys.size false))
    fun (src, used) k => match keyIndexGet oldBuckets mask k with
      | some oi => (src.push (some oi), used.setIfInBounds oi true) | none => (src.push none, used)
  if !used.any id then MonadDom.clearChildren node; mountFreshTmplRowsM node tmplId evSlot newKeys hasDups rowVals nNew newMarks
  else
    removeUnusedM node oldLive used 0; let inLis := verifiedLisFlags sources
    let rec back : Nat → Bool → Dom.Node → Array Dom.Node → Array (Array String) → m (Array Dom.Node × Array (Array String))
      | 0, _, _, ol, ov => return (ol, ov)
      | k + 1, hasA, a, ol, ov => do
          let ref := if hasA then some a else none
          let (c, nv) ← match sources.getD k none with
            | some oi => do
                let c := oldLive.getD oi 0
                if !inLis.getD k false then MonadDom.insertBeforeRef node ref c
                pure (c, ← patchDirty k oi c)
            | none => do let v := rowVals k; let cn ← MonadDom.mountTmplRow tmplId v; MonadDom.insertBeforeRef node ref cn; pure (cn, v)
          back k true c (ol.setIfInBounds k c) (ov.setIfInBounds k nv)
    let (newLive, newVals) ← back nNew false 0 (Array.replicate nNew 0) (Array.replicate nNew #[])
    return mk newKeys hasDups newLive newVals

mutual
def buildViewM [MonadDom msg m] (ns : String) : View σ msg → σ → m (Dom.Node × VState σ msg)
  | .text s, _ => do let n ← MonadDom.createText s; return (n, .text n)
  | .dyn get, s => do let v := get s; let n ← MonadDom.createText v; return (n, .dyn n v)
  | .static html, _ => do let n ← buildDomM ns html; return (n, .stat n)
  | .element tag attrs kids, s => do
      let node ← MonadDom.createElement ns tag; applyAttrsM node (attrs.map (VAttr.eval s))
      return (node, .elem node (← buildViewKidsM (Dom.childNsOf ns tag) node kids s))
  | .ifElse cond yes no, s => do
      let b := cond s; let (n, inner) ← (if b then buildViewM ns yes s else buildViewM ns no s); return (n, .cond b inner)
  | .dynNode get, s => do let html := get s; let n ← buildDomM ns html; return (n, .dynNode n html)
  | .memo sm, s => do let k := sm.keyOf s; let html := sm.eval s; let n ← buildDomM ns html; return (n, .memo n k html)
  | .keyedList tag attrs keys marks _ _ _ (some tmpl), s => do
      let (uKeys, hasDups) := disambiguateWithFlag (keys s); let nMarks := marks s
      let node ← MonadDom.createElement ns tag; applyAttrsM node (attrs.map (VAttr.eval s))
      let (tmplId, evSlot) ← initRowTmplM node (Dom.childNsOf ns tag) tmpl s
      return (node, ← mountFreshTmplRowsM node tmplId evSlot uKeys hasDups (tmpl.rowVals s) nMarks.size nMarks)
  | .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s => do
      let uKeys := disambiguateKeys (keys s); let node ← MonadDom.createElement ns tag; applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"; let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s uKeys) (rowEv s uKeys) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      buildDomListM (Dom.childNsOf ns tag) node rs; return (node, .list node uKeys perRow rs nMarks inst)
def buildViewKidsM [MonadDom msg m] (ns : String) (parent : Dom.Node) : List (View σ msg) → σ → m (List (VState σ msg))
  | [], _ => return []
  | k :: rest, s => do let (kn, kst) ← buildViewM ns k s; MonadDom.appendChild parent kn; return kst :: (← buildViewKidsM ns parent rest s)
end

mutual
def patchViewM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) : View σ msg → σ → VState σ msg → m (VState σ msg)
  | .dyn get, s, .dyn node last => do
      let v := get s
      if v != last then MonadDom.setText node v
      return .dyn node v
  | .element _ attrs kids, s, .elem node kstates => do applyDynAttrsM node attrs s; return .elem node (← patchViewKidsM node 0 kids s kstates)
  | .ifElse cond yes no, s, .cond wasYes inner => do
      let now := cond s
      if now == wasYes then return .cond now (← if now then patchViewM parent index yes s inner else patchViewM parent index no s inner)
      else
        let ns ← MonadDom.childNamespace parent
        let (n, st) ← if now then buildViewM ns yes s else buildViewM ns no s
        MonadDom.replaceChild parent index n; return .cond now st
  | .dynNode get, s, .dynNode node last => do let newHtml := get s; return .dynNode (← patchHtmlSubtreeM parent index node last newHtml) newHtml
  | .memo sm, s, .memo node lastKey lastHtml => do
      let k := sm.keyOf s
      if k == lastKey then return .memo node lastKey lastHtml
      else let newHtml := sm.eval s; return .memo (← patchHtmlSubtreeM parent index node lastHtml newHtml) k newHtml
  | .keyedList _ attrs keys marks _ _ _ (some tmpl), s, .tlist node tmplId evSlot oldKeys oldDups oldLive oldVals oldMarks =>
      patchTmplListM node attrs keys marks tmpl s tmplId evSlot oldKeys oldDups oldLive oldVals oldMarks
  | .keyedList _ attrs keys marks rowSig rowEv rowsHtml none, s, .list node oldKeys oldSigs oldRowsL oldMarks inst => do
      let rawKeys := keys s; let newMarks := marks s
      if rawKeys == oldKeys then
        applyDynAttrsM node attrs s
        return .list node oldKeys (← seedRowsM inst (rowSig s oldKeys) (rowEv s oldKeys) newMarks oldMarks oldSigs) oldRowsL newMarks inst
      else
        let newKeys := disambiguateKeys rawKeys
        if newKeys == oldKeys then
          applyDynAttrsM node attrs s
          return .list node oldKeys (← seedRowsM inst (rowSig s oldKeys) (rowEv s oldKeys) newMarks oldMarks oldSigs) oldRowsL newMarks inst
        else if newKeys.isEmpty then
          applyDynAttrsM node attrs s; MonadDom.clearChildren node; return .list node #[] #[] [] #[] inst
        else if oldRowsL.isEmpty then
          applyDynAttrsM node attrs s
          let newSigs ← seedRowsM inst (rowSig s newKeys) (rowEv s newKeys) newMarks #[] #[]
          let newRows := (rowsHtml s).map (Html.prefixSignals inst)
          let childNs ← MonadDom.childNamespace node; let frag ← MonadDom.createFragment
          buildDomListM childNs frag newRows; MonadDom.appendChild node frag
          return .list node newKeys newSigs newRows newMarks inst
        else
          let (oldBuckets, mask) := buildKeyIndex oldKeys; let oldRows := oldRowsL.toArray; let n := newKeys.size
          let (sources, used, rowsArr, marksArr, sigsArr) :=
            planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs
              (fun _ => ((rowsHtml s).map (Html.prefixSignals inst)).toArray) none 0
              (Array.emptyWithCapacity n) (Array.replicate oldKeys.size false)
              (Array.emptyWithCapacity n) (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)
          let newSigs ← seedRowsM inst (rowSig s newKeys) (rowEv s newKeys) newMarks marksArr sigsArr
          applyDynAttrsM node attrs s; let childNs ← MonadDom.childNamespace node
          if !used.any id then
            MonadDom.clearChildren node; let newRows := rowsArr.toList; let frag ← MonadDom.createFragment
            buildDomListM childNs frag newRows; MonadDom.appendChild node frag
            return .list node newKeys newSigs newRows newMarks inst
          else
            let oldCount ← MonadDom.childCount node; let live ← snapshotChildrenM node 0 #[] oldCount.toNat
            removeUnusedM node live used 0
            reconcileLisBackM node childNs live sources (verifiedLisFlags sources) rowsArr n false 0
            return .list node newKeys newSigs rowsArr.toList newMarks inst
  | .text _, _, st@(.text _) | .static _, _, st@(.stat _) => return st
  | v, s, _ => do let (n, st) ← buildViewM (← MonadDom.childNamespace parent) v s; MonadDom.replaceChild parent index n; return st
def patchViewKidsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) : List (View σ msg) → σ → List (VState σ msg) → m (List (VState σ msg))
  | [], _, _ => return []
  | k :: rest, s, kst :: restSt => return (← patchViewM node i k s kst) :: (← patchViewKidsM node (i + 1) rest s restSt)
  | k :: rest, s, []            => return (← patchViewM node i k s default) :: (← patchViewKidsM node (i + 1) rest s [])
end

def View.textOf? (s : σ) : View σ msg → Option String
  | .text str => some str | .dyn get => some (get s)
  | .ifElse cond yes no => if cond s then View.textOf? s yes else View.textOf? s no
  | .static html => html.textOf? | .dynNode get => (get s).textOf? | .memo sm => (sm.eval s).textOf?
  | .element .. | .keyedList .. => none
def hasMoreViewText (s : σ) : List (View σ msg) → Bool
  | [] => false | k :: cs => match k.textOf? s with | some "" => hasMoreViewText s cs | some _ => true | none => false
def hydrateListRowsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) : List (Html msg) → m Unit
  | [] => pure () | r :: rs => do hydrateDomM r (← MonadDom.childAt node i); hydrateListRowsM node (i + 1) rs

mutual
def hydrateViewM [MonadDom msg m] : View σ msg → σ → Dom.Node → m (VState σ msg)
  | .text _, _, node => return .text node
  | .dyn get, s, node => return .dyn node (get s)
  | .static html, _, node => do hydrateDomM html node; return .stat node
  | .element _ attrs kids, s, node => do
      MonadDom.clearHandlers node; applyAttrsM node (attrs.map (VAttr.eval s)); return .elem node (← hydrateViewKidsM node s 0 false kids)
  | .ifElse cond yes no, s, node => do let b := cond s; return .cond b (← if b then hydrateViewM yes s node else hydrateViewM no s node)
  | .dynNode get, s, node => do let html := get s; hydrateDomM html node; return .dynNode node html
  | .memo sm, s, node => do let k := sm.keyOf s; let html := sm.eval s; hydrateDomM html node; return .memo node k html
  | .keyedList _ attrs keys marks _ _ _ (some tmpl), s, node => do
      let (uKeys, hasDups) := disambiguateWithFlag (keys s); let nMarks := marks s; let n := nMarks.size
      MonadDom.clearHandlers node; applyAttrsM node (attrs.map (VAttr.eval s))
      let (tmplId, evSlot) ← initRowTmplM node (← MonadDom.childNamespace node) tmpl s
      let live ← snapshotChildrenM node 0 (Array.emptyWithCapacity n) n; live.forM (MonadDom.hydrateTmplRow · tmplId)
      return .tlist node tmplId evSlot uKeys hasDups live (Array.ofFn (n := n) fun i => tmpl.rowVals s i.1) nMarks
  | .keyedList _ attrs keys marks rowSig rowEv rowsHtml none, s, node => do
      let uKeys := disambiguateKeys (keys s); MonadDom.clearHandlers node; applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"; let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s uKeys) (rowEv s uKeys) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      hydrateListRowsM node 0 rs; return .list node uKeys perRow rs nMarks inst
def hydrateViewKidsM [MonadDom msg m] (node : Dom.Node) (s : σ) (i : UInt32) (inTextRun : Bool) : List (View σ msg) → m (List (VState σ msg))
  | [] => return []
  | k :: rest => do
      let (kn, nextRun) ← match k.textOf? s with
        | some str => hydrateTextSlotM node i inTextRun str (fun () => hasMoreViewText s rest)
        | none     => do pure (← MonadDom.childAt node i, false)
      return (← hydrateViewM k s kn) :: (← hydrateViewKidsM node s (i + 1) nextRun rest)
end

@[noinline] def buildView (h : Handlers msg) (ns : String) (v : View σ msg) (s : σ) : IO (Dom.Node × VState σ msg) := ReaderT.run (buildViewM (m := DomM msg) ns v s) h
@[noinline] def patchView (h : Handlers msg) (parent : Dom.Node) (index : UInt32) (v : View σ msg) (s : σ) (st : VState σ msg) : IO (VState σ msg) := ReaderT.run (patchViewM (m := DomM msg) parent index v s st) h
@[noinline] def hydrateView (h : Handlers msg) (v : View σ msg) (s : σ) (node : Dom.Node) : IO (VState σ msg) := ReaderT.run (hydrateViewM (m := DomM msg) v s node) h
end Qed
