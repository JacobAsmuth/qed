import Qed.Driver.Vdom

namespace Qed

inductive VState (σ : Type) (msg : Type) where
  | text (node : Dom.Node)
  | dyn (node : Dom.Node) (last : String)
  | elem (node : Dom.Node) (kids : List (VState σ msg))
  | cond (wasYes : Bool) (inner : VState σ msg)
  | list (node : Dom.Node) (keys : Array String)
      (sigs : Array (Array (String × String))) (rows : List (Html msg))
      (marks : Array USize) (inst : String)
  | tlist (node : Dom.Node) (tmplId : UInt32) (evSlot : UInt32)
      (keys : Array String) (hasDups : Bool) (live : Array Dom.Node)
      (vals : Array (Array String)) (marks : Array USize)
  | stat (node : Dom.Node)
  | dynNode (node : Dom.Node) (last : Html msg)
  | memo (node : Dom.Node) (lastKey : String) (lastHtml : Html msg)

instance : Inhabited (VState σ msg) := ⟨.text 0⟩

/-! ## Bare-Array `O(N)` Key Index & Certifying `O(N log N)` LIS Minimal-Moves Reconciler -/

def kpLookupList (k : String) : List (String × Nat) → Option Nat
  | [] => none
  | (k', v) :: rest => if k' == k then some v else kpLookupList k rest

@[inline] def keyIndexGet (buckets : @& Array (List (String × Nat))) (mask : USize) (k : String) : Option Nat :=
  if h : 0 < buckets.size then
    kpLookupList k (buckets[strBucketIdx k mask buckets.size]'(strBucketIdx_lt k mask buckets.size h))
  else none

def buildKeyIndexLoop (keys : @& Array String) (i : Nat)
    (buckets : Array (List (String × Nat))) (mask : USize) : Array (List (String × Nat)) :=
  if h : i < keys.size then
    let k := keys[i]
    let buckets' :=
      if hb : 0 < buckets.size then
        let bi := strBucketIdx k mask buckets.size
        have hbi : bi < buckets.size := strBucketIdx_lt k mask buckets.size hb
        let cur := buckets[bi]
        buckets.set bi ((k, i) :: cur) hbi
      else buckets
    buildKeyIndexLoop keys (i + 1) buckets' mask
  else buckets
termination_by keys.size - i
decreasing_by exact Nat.sub_succ_lt_self keys.size i h

def buildKeyIndex (keys : Array String) : Array (List (String × Nat)) × USize :=
  let cap := nextPow2Ge (keys.size * 2) 16 30
  let mask := USize.ofNat (cap - 1)
  (buildKeyIndexLoop keys 0 (Array.replicate cap []) mask, mask)

def planKeyedLoop (newKeys : @& Array String)
    (oldBuckets : @& Array (List (String × Nat))) (mask : USize)
    (oldRows : @& Array (Html msg)) (oldMarks : @& Array USize)
    (oldSigs : @& Array (Array (String × String)))
    (fresh : Unit → Array (Html msg)) (freshCache : Option (Array (Html msg)))
    (i : Nat)
    (sources : Array (Option Nat)) (used : Array Bool)
    (rows : Array (Html msg)) (marks : Array USize) (sigs : Array (Array (String × String))) :
    Array (Option Nat) × Array Bool × Array (Html msg) × Array USize × Array (Array (String × String)) :=
  if h : i < newKeys.size then
    match keyIndexGet oldBuckets mask newKeys[i] with
    | some oi =>
        let used' := if ho : oi < used.size then used.set oi true ho else used
        planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh freshCache (i + 1)
          (sources.push (some oi)) used'
          (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
    | none =>
        let (fArr, fCache) := match freshCache with
          | some a => (a, some a)
          | none   => let a := fresh (); (a, some a)
        planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh fCache (i + 1)
          (sources.push none) used
          (rows.push (fArr.getD i default)) (marks.push 0) (sigs.push #[])
  else (sources, used, rows, marks, sigs)
termination_by newKeys.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newKeys.size i h

private theorem lisLowerBound_dec1 {lo hi : Nat} (h : lo < hi) :
    hi - (lo + (hi - lo) / 2 + 1) < hi - lo := by
  have h1 : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (Nat.sub_pos_of_lt h) (by decide)
  have h2 : lo + (hi - lo) / 2 < hi := by
    have := Nat.add_lt_add_left h1 lo
    rwa [Nat.add_sub_of_le (Nat.le_of_lt h)] at this
  exact Nat.sub_lt_sub_left h (Nat.lt_succ_of_le (Nat.le_add_right lo _))

private theorem lisLowerBound_dec2 {lo hi : Nat} (h : lo < hi) :
    lo + (hi - lo) / 2 - lo < hi - lo := by
  rw [Nat.add_sub_cancel_left]
  exact Nat.div_lt_self (Nat.sub_pos_of_lt h) (by decide)

private def lisLowerBound (tails : @& Array Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if tails.getD mid 0 < x then
      lisLowerBound tails x (mid + 1) hi
    else
      lisLowerBound tails x lo mid
  else lo
termination_by hi - lo
decreasing_by
  · exact lisLowerBound_dec1 h
  · exact lisLowerBound_dec2 h

private def lisBuildLoop (sources : @& Array (Option Nat)) (i : Nat)
    (tails : Array Nat) (tailPos : Array Nat) (prev : Array Nat) :
    Array Nat × Array Nat × Array Nat :=
  if h : i < sources.size then
    match sources[i] with
    | none => lisBuildLoop sources (i + 1) tails tailPos prev
    | some oi =>
        let pos := lisLowerBound tails oi 0 tails.size
        let prevIdx := if pos > 0 then tailPos.getD (pos - 1) sources.size else sources.size
        let prev' := if hi : i < prev.size then prev.set i prevIdx hi else prev
        if hp : pos < tails.size then
          let tails' := tails.set pos oi hp
          let tailPos' := if htp : pos < tailPos.size then tailPos.set pos i htp else tailPos
          lisBuildLoop sources (i + 1) tails' tailPos' prev'
        else
          lisBuildLoop sources (i + 1) (tails.push oi) (tailPos.push i) prev'
  else (tails, tailPos, prev)
termination_by sources.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self sources.size i h

private def lisTraceLoop (prev : @& Array Nat) (sentinel : Nat) (cur : Nat)
    (flags : Array Bool) : Nat → Array Bool
  | 0 => flags
  | fuel + 1 =>
      if h : cur < flags.size then
        let flags' := flags.set cur true h
        let nxt := prev.getD cur sentinel
        if nxt < sentinel then lisTraceLoop prev sentinel nxt flags' fuel else flags'
      else flags

def computeLisRaw (sources : Array (Option Nat)) : Array Bool :=
  let n := sources.size
  let (_, tailPos, prev) :=
    lisBuildLoop sources 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n) (Array.replicate n n)
  let initFlags := Array.replicate n false
  if h : 0 < tailPos.size then
    lisTraceLoop prev n (tailPos[tailPos.size - 1]'(Nat.sub_lt h Nat.zero_lt_one)) initFlags n
  else initFlags

def isValidLisLoop (sources : @& Array (Option Nat)) (flags : @& Array Bool)
    (i : Nat) (last? : Option Nat) : Bool :=
  if h : i < sources.size then
    if flags.getD i false then
      match sources[i] with
      | some oi =>
          match last? with
          | none => isValidLisLoop sources flags (i + 1) (some oi)
          | some prev => if prev < oi then isValidLisLoop sources flags (i + 1) (some oi) else false
      | none => false
    else
      isValidLisLoop sources flags (i + 1) last?
  else true
termination_by sources.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self sources.size i h

def verifiedLisFlags (sources : Array (Option Nat)) : Array Bool :=
  let raw := computeLisRaw sources
  if raw.size == sources.size && isValidLisLoop sources raw 0 none then raw
  else Array.replicate sources.size false

def removeUnusedM [MonadDom msg m] (node : Dom.Node) (live : Array Dom.Node)
    (used : Array Bool) (i : Nat) : m Unit :=
  if h : i < live.size then
    if used.getD i false then
      removeUnusedM node live used (i + 1)
    else do
      MonadDom.removeNode node live[i]
      removeUnusedM node live used (i + 1)
  else pure ()
termination_by live.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self live.size i h

def reconcileLisBackM [MonadDom msg m] (node : Dom.Node) (childNs : String)
    (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (newRows : Array (Html msg)) :
    Nat → Bool → Dom.Node → m Unit
  | 0, _, _ => pure ()
  | k + 1, hasAnchor, anchor =>
      match sources.getD k none with
      | some oi =>
          let child := live.getD oi 0
          if inLis.getD k false then
            reconcileLisBackM node childNs live sources inLis newRows k true child
          else do
            MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) child
            reconcileLisBackM node childNs live sources inLis newRows k true child
      | none => do
          let cn ← buildDomM childNs (newRows.getD k default)
          MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) cn
          reconcileLisBackM node childNs live sources inLis newRows k true cn

def collectChanged (inst : String) (old new : Array (String × String)) (j : Nat)
    (acc : Array (String × String)) : Array (String × String) :=
  if h : j < new.size then
    let (nm, v) := new[j]
    let acc := if old[j]?.map (·.2) == some v then acc else acc.push (inst ++ nm, v)
    collectChanged inst old new (j + 1) acc
  else acc
termination_by new.size - j
decreasing_by exact Nat.sub_succ_lt_self new.size j h

def collectEvs {msg : Type} (inst : String) (evs : Array (String × msg)) (j : Nat)
    (acc : Array (String × msg)) : Array (String × msg) :=
  if h : j < evs.size then
    let (nm, m) := evs[j]
    collectEvs inst evs (j + 1) (acc.push (inst ++ nm, m))
  else acc
termination_by evs.size - j
decreasing_by exact Nat.sub_succ_lt_self evs.size j h

-- Pure tail recursion so the JS backend trampolines it instead of overflowing the stack on 10k-row `IO` binds.
def diffRowSigs {msg : Type} (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (i : Nat) (accSigs : Array (Array (String × String)))
    (accEmit : Array (String × String)) (accEv : Array (String × msg)) :
    Array (Array (String × String)) × Array (String × String) × Array (String × msg) :=
  if h : i < newMarks.size then
    let m := newMarks[i]
    if m != 0 && oldMarks[i]? == some m then
      diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs (i + 1) (accSigs.push (oldSigs[i]?.getD #[])) accEmit accEv
    else
      let rsig := rowSig i
      let accEmit := collectChanged inst (oldSigs[i]?.getD #[]) rsig 0 accEmit
      let accEv := collectEvs inst (rowEv i) 0 accEv
      diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs (i + 1) (accSigs.push rsig) accEmit accEv
  else (accSigs, accEmit, accEv)
termination_by newMarks.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newMarks.size i h

def emitSignalsM [MonadDom msg m] : List (String × String) → m Unit
  | []            => pure ()
  | (nm, v) :: rest => do
      MonadDom.setSignal nm v
      emitSignalsM rest

def emitSignalOnsM [MonadDom msg m] : List (String × msg) → m Unit
  | []            => pure ()
  | (nm, ev) :: rest => do
      MonadDom.setSignalOn nm ev
      emitSignalOnsM rest

def seedRowsM [MonadDom msg m] (inst : String) (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) :
    m (Array (Array (String × String))) := do
  let (newSigs, toEmit, toEv) := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
  emitSignalsM toEmit.toList
  emitSignalOnsM toEv.toList
  return newSigs

/-! ## Compiled Row-Template Fast-Path Helpers -/

def collectTmplValsLoop (rowVals : Nat → Array String) (start count : Nat)
    (acc : Array (Array String)) : Array (Array String) :=
  match count with
  | 0 => acc
  | n + 1 => collectTmplValsLoop rowVals (start + 1) n (acc.push (rowVals start))

def collectTmplKeysLoop (rowKey : Nat → String) (start count : Nat)
    (acc : Array String) : Array String :=
  match count with
  | 0 => acc
  | n + 1 => collectTmplKeysLoop rowKey (start + 1) n (acc.push (rowKey start))

def collectChangedMarksLoop (oldMarks newMarks : @& Array USize) (i : Nat)
    (acc : Array Nat) : Array Nat :=
  if h : i < newMarks.size then
    let m := newMarks[i]
    let acc' := if m != 0 && oldMarks[i]? == some m then acc else acc.push i
    collectChangedMarksLoop oldMarks newMarks (i + 1) acc'
  else acc
termination_by newMarks.size - i
decreasing_by exact Nat.sub_succ_lt_self newMarks.size i h

def allChangedKeysMatch (rowKey : Nat → String) (oldKeys : @& Array String)
    (changed : @& Array Nat) (k : Nat) : Bool :=
  if h : k < changed.size then
    let idx := changed[k]
    if rowKey idx == oldKeys.getD idx "" then
      allChangedKeysMatch rowKey oldKeys changed (k + 1)
    else false
  else true
termination_by changed.size - k
decreasing_by exact Nat.sub_succ_lt_self changed.size k h

def prefixMatchLen (oldMarks newMarks : @& Array USize) (i : Nat) : Nat :=
  if h : i < oldMarks.size ∧ i < newMarks.size then
    let m := newMarks[i]'h.2
    if m != 0 && oldMarks[i]'h.1 == m then prefixMatchLen oldMarks newMarks (i + 1) else i
  else i
termination_by oldMarks.size - i
decreasing_by exact Nat.sub_succ_lt_self oldMarks.size i h.1

private theorem sub_one_sub_lt {n p q : Nat} (h : p + q < n) : n - 1 - q < n :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h) Nat.zero_lt_one)

def suffixMatchLen (oldMarks newMarks : @& Array USize) (p q : Nat) : Nat :=
  if h : p + q < oldMarks.size ∧ p + q < newMarks.size then
    let oi := oldMarks.size - 1 - q
    let ni := newMarks.size - 1 - q
    let m := newMarks[ni]'(sub_one_sub_lt h.2)
    if m != 0 && oldMarks[oi]'(sub_one_sub_lt h.1) == m then
      suffixMatchLen oldMarks newMarks p (q + 1)
    else q
  else q
termination_by oldMarks.size - (p + q)
decreasing_by exact Nat.sub_succ_lt_self oldMarks.size (p + q) h.1

def planTmplLoop (newKeys : @& Array String) (oldBuckets : @& Array (List (String × Nat)))
    (mask : USize) (i : Nat) (sources : Array (Option Nat)) (used : Array Bool) :
    Array (Option Nat) × Array Bool :=
  if h : i < newKeys.size then
    match keyIndexGet oldBuckets mask newKeys[i] with
    | some oi =>
        let used' := if ho : oi < used.size then used.set oi true ho else used
        planTmplLoop newKeys oldBuckets mask (i + 1) (sources.push (some oi)) used'
    | none =>
        planTmplLoop newKeys oldBuckets mask (i + 1) (sources.push none) used
  else (sources, used)
termination_by newKeys.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newKeys.size i h

def patchChangedRowsM [MonadDom msg m] (tmplId : UInt32) (live : Array Dom.Node)
    (rowVals : Nat → Array String) (changed : Array Nat) (k : Nat)
    (vals : Array (Array String)) : m (Array (Array String)) := do
  if hk : k < changed.size then
    let idx := changed[k]
    let nv := rowVals idx
    let ov := vals.getD idx #[]
    MonadDom.patchTmplRow (live.getD idx 0) tmplId nv ov
    let vals' := if hi : idx < vals.size then vals.set idx nv hi else vals
    patchChangedRowsM tmplId live rowVals changed (k + 1) vals'
  else return vals
termination_by changed.size - k
decreasing_by exact Nat.sub_succ_lt_self changed.size k hk

def patchDirtyRowsM [MonadDom msg m] (tmplId : UInt32) (live : Array Dom.Node)
    (oldMarks newMarks : Array USize) (rowVals : Nat → Array String)
    (i : Nat) (vals : Array (Array String)) : m (Array (Array String)) := do
  if hi : i < newMarks.size then
    let m := newMarks[i]
    if m != 0 && oldMarks[i]? == some m then
      patchDirtyRowsM tmplId live oldMarks newMarks rowVals (i + 1) vals
    else
      let nv := rowVals i
      MonadDom.patchTmplRow (live.getD i 0) tmplId nv (vals.getD i #[])
      let vals' := if hv : i < vals.size then vals.set i nv hv else vals
      patchDirtyRowsM tmplId live oldMarks newMarks rowVals (i + 1) vals'
  else return vals
termination_by newMarks.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self newMarks.size i hi

def removeRangeM [MonadDom msg m] (node : Dom.Node) (live : Array Dom.Node)
    (i stop : Nat) : m Unit := do
  if h : i < stop then
    MonadDom.removeNode node (live.getD i 0)
    removeRangeM node live (i + 1) stop
termination_by stop - i
decreasing_by exact Nat.sub_succ_lt_self stop i h

def reconcileTmplBackM [MonadDom msg m] (node : Dom.Node) (tmplId : UInt32)
    (oldLive : Array Dom.Node) (oldVals : Array (Array String)) (oldMarks : Array USize)
    (rowVals : Nat → Array String) (newMarks : Array USize)
    (sources : Array (Option Nat)) (inLis : Array Bool) :
    Nat → Bool → Dom.Node → Array Dom.Node → Array (Array String) →
    m (Array Dom.Node × Array (Array String))
  | 0, _, _, outLive, outVals => return (outLive, outVals)
  | k + 1, hasAnchor, anchor, outLive, outVals =>
      match sources.getD k none with
      | some oi => do
          let child := oldLive.getD oi 0
          if !inLis.getD k false then
            MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) child
          let ov := oldVals.getD oi #[]
          let m := newMarks.getD k 0
          let nv ←
            if m != 0 && oldMarks[oi]? == some m then
              pure ov
            else do
              let v := rowVals k
              MonadDom.patchTmplRow child tmplId v ov
              pure v
          let outLive' := if hl : k < outLive.size then outLive.set k child hl else outLive
          let outVals' := if hv : k < outVals.size then outVals.set k nv hv else outVals
          reconcileTmplBackM node tmplId oldLive oldVals oldMarks rowVals newMarks sources inLis
            k true child outLive' outVals'
      | none => do
          let nv := rowVals k
          let cn ← MonadDom.mountTmplRow tmplId nv
          MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) cn
          let outLive' := if hl : k < outLive.size then outLive.set k cn hl else outLive
          let outVals' := if hv : k < outVals.size then outVals.set k nv hv else outVals
          reconcileTmplBackM node tmplId oldLive oldVals oldMarks rowVals newMarks sources inLis
            k true cn outLive' outVals'

def hydrateTmplRowsM [MonadDom msg m] (node : Dom.Node) (tmplId : UInt32)
    (i count : Nat) (acc : Array Dom.Node) : m (Array Dom.Node) := do
  match count with
  | 0 => return acc
  | n + 1 =>
      let child ← MonadDom.childAt node (UInt32.ofNat i)
      MonadDom.hydrateTmplRow child tmplId
      hydrateTmplRowsM node tmplId (i + 1) n (acc.push child)

def patchTmplListGeneralM [MonadDom msg m] (node : Dom.Node) (tmplId evSlot : UInt32)
    (keys : σ → Array String) (tmpl : RowTmpl σ msg) (s : σ)
    (oldKeys : Array String) (oldLive : Array Dom.Node)
    (oldVals : Array (Array String)) (oldMarks newMarks : Array USize) :
    m (VState σ msg) := do
  let rawKs := keys s
  let newKeys := disambiguateKeys rawKs
  let hasDups := newKeys != rawKs
  let nNew := newKeys.size
  if newKeys == oldKeys then
    let vals' ← patchDirtyRowsM tmplId oldLive oldMarks newMarks (tmpl.rowVals s) 0 oldVals
    return .tlist node tmplId evSlot oldKeys hasDups oldLive vals' newMarks
  else
    let (oldBuckets, mask) := buildKeyIndex oldKeys
    let (sources, used) :=
      planTmplLoop newKeys oldBuckets mask 0
        (Array.emptyWithCapacity nNew) (Array.replicate oldKeys.size false)
    if !used.any id then
      MonadDom.clearChildren node
      let newVals := collectTmplValsLoop (tmpl.rowVals s) 0 nNew (Array.emptyWithCapacity nNew)
      let newLive ← MonadDom.mountTmplRows node tmplId newVals
      return .tlist node tmplId evSlot newKeys hasDups newLive newVals newMarks
    else
      removeUnusedM node oldLive used 0
      let inLis := verifiedLisFlags sources
      let (newLive, newVals) ← reconcileTmplBackM node tmplId oldLive oldVals oldMarks
        (tmpl.rowVals s) newMarks sources inLis nNew false 0
        (Array.replicate nNew 0) (Array.replicate nNew #[])
      return .tlist node tmplId evSlot newKeys hasDups newLive newVals newMarks

def patchTmplListM [MonadDom msg m] (node : Dom.Node) (attrs : List (VAttr σ msg))
    (keys : σ → Array String) (marks : σ → Array USize) (tmpl : RowTmpl σ msg) (s : σ)
    (tmplId evSlot : UInt32) (oldKeys : Array String) (oldDups : Bool)
    (oldLive : Array Dom.Node) (oldVals : Array (Array String)) (oldMarks : Array USize) :
    m (VState σ msg) := do
  if !tmpl.evNames.isEmpty then
    MonadDom.setRowEvSlot evSlot (tmpl.rowEvAt s)
  applyDynAttrsM node attrs s
  let newMarks := marks s
  let nOld := oldMarks.size
  let nNew := newMarks.size
  if nNew == 0 then
    if nOld > 0 then MonadDom.clearChildren node
    return .tlist node tmplId evSlot #[] false #[] #[] #[]
  else if nOld == 0 then
    let rawKs := keys s
    let uKeys := disambiguateKeys rawKs
    let hasDups := uKeys != rawKs
    let newVals := collectTmplValsLoop (tmpl.rowVals s) 0 nNew (Array.emptyWithCapacity nNew)
    let newLive ← MonadDom.mountTmplRows node tmplId newVals
    return .tlist node tmplId evSlot uKeys hasDups newLive newVals newMarks
  else if !oldDups && nOld == nNew then
    let changed := collectChangedMarksLoop oldMarks newMarks 0 #[]
    if changed.isEmpty then
      return .tlist node tmplId evSlot oldKeys false oldLive oldVals newMarks
    else if allChangedKeysMatch (tmpl.rowKey s) oldKeys changed 0 then
      let vals' ← patchChangedRowsM tmplId oldLive (tmpl.rowVals s) changed 0 oldVals
      return .tlist node tmplId evSlot oldKeys false oldLive vals' newMarks
    else if h2 : changed.size = 2 then
      let a := changed[0]'(h2 ▸ Nat.zero_lt_two)
      let b := changed[1]'(h2 ▸ Nat.one_lt_two)
      let ka := tmpl.rowKey s a
      let kb := tmpl.rowKey s b
      if ka == oldKeys.getD b "" && kb == oldKeys.getD a "" then
        let nodeA := oldLive.getD a 0
        let nodeB := oldLive.getD b 0
        if b == a + 1 then
          MonadDom.insertBeforeRef node (some nodeA) nodeB
        else
          let afterB := if b + 1 < nOld then some (oldLive.getD (b + 1) 0) else none
          MonadDom.insertBeforeRef node (some nodeA) nodeB
          MonadDom.insertBeforeRef node afterB nodeA
        let ovA := oldVals.getD b #[]
        let ovB := oldVals.getD a #[]
        let nvA ←
          if newMarks.getD a 0 != 0 && oldMarks[b]? == some (newMarks.getD a 0) then pure ovA
          else do let v := tmpl.rowVals s a; MonadDom.patchTmplRow nodeB tmplId v ovA; pure v
        let nvB ←
          if newMarks.getD b 0 != 0 && oldMarks[a]? == some (newMarks.getD b 0) then pure ovB
          else do let v := tmpl.rowVals s b; MonadDom.patchTmplRow nodeA tmplId v ovB; pure v
        let keys' := (oldKeys.set! a ka).set! b kb
        let live' := (oldLive.set! a nodeB).set! b nodeA
        let vals' := (oldVals.set! a nvA).set! b nvB
        return .tlist node tmplId evSlot keys' false live' vals' newMarks
      else
        patchTmplListGeneralM node tmplId evSlot keys tmpl s oldKeys oldLive oldVals oldMarks newMarks
    else
      patchTmplListGeneralM node tmplId evSlot keys tmpl s oldKeys oldLive oldVals oldMarks newMarks
  else if !oldDups then
    let p := prefixMatchLen oldMarks newMarks 0
    if p == nOld && nNew > nOld then
      let addCount := nNew - nOld
      let tailVals := collectTmplValsLoop (tmpl.rowVals s) nOld addCount (Array.emptyWithCapacity addCount)
      let tailKeys := collectTmplKeysLoop (tmpl.rowKey s) nOld addCount (Array.emptyWithCapacity addCount)
      let rawKs := oldKeys ++ tailKeys
      let uKeys := disambiguateKeys rawKs
      let hasDups := uKeys != rawKs
      let tailLive ← MonadDom.mountTmplRows node tmplId tailVals
      return .tlist node tmplId evSlot uKeys hasDups (oldLive ++ tailLive) (oldVals ++ tailVals) newMarks
    else if nNew < nOld then
      let q := suffixMatchLen oldMarks newMarks p 0
      if p + q == nNew then
        removeRangeM node oldLive p (nOld - q)
        let keys' := oldKeys.extract 0 p ++ oldKeys.extract (nOld - q) nOld
        let live' := oldLive.extract 0 p ++ oldLive.extract (nOld - q) nOld
        let vals' := oldVals.extract 0 p ++ oldVals.extract (nOld - q) nOld
        return .tlist node tmplId evSlot keys' false live' vals' newMarks
      else
        patchTmplListGeneralM node tmplId evSlot keys tmpl s oldKeys oldLive oldVals oldMarks newMarks
    else
      patchTmplListGeneralM node tmplId evSlot keys tmpl s oldKeys oldLive oldVals oldMarks newMarks
  else
    patchTmplListGeneralM node tmplId evSlot keys tmpl s oldKeys oldLive oldVals oldMarks newMarks

mutual
def buildViewM [MonadDom msg m] (ns : String) :
    View σ msg → σ → m (Dom.Node × VState σ msg)
  | .text s, _ => do
      let n ← MonadDom.createText s
      return (n, .text n)
  | .dyn get, s => do
      let v := get s
      let n ← MonadDom.createText v
      return (n, .dyn n v)
  | .static html, _ => do
      let n ← buildDomM ns html
      return (n, .stat n)
  | .element tag attrs kids, s => do
      let node ← MonadDom.createElement ns tag
      applyAttrsM node (attrs.map (VAttr.eval s))
      let ks ← buildViewKidsM (Dom.childNsOf ns tag) node kids s
      return (node, .elem node ks)
  | .ifElse cond yes no, s => do
      let b := cond s
      let (n, inner) ← if b then buildViewM ns yes s else buildViewM ns no s
      return (n, .cond b inner)
  | .dynNode get, s => do
      let html := get s
      let n ← buildDomM ns html
      return (n, .dynNode n html)
  | .memo sm, s => do
      let k := sm.keyOf s
      let html := sm.eval s
      let n ← buildDomM ns html
      return (n, .memo n k html)
  | .keyedList tag attrs keys marks _ _ _ (some tmpl), s => do
      let rawKs := keys s
      let uKeys := disambiguateKeys rawKs
      let hasDups := uKeys != rawKs
      let node ← MonadDom.createElement ns tag
      applyAttrsM node (attrs.map (VAttr.eval s))
      let tmplId ← MonadDom.compileRowTmpl (Dom.childNsOf ns tag) tmpl.proto tmpl.slotPaths tmpl.slotAttrs tmpl.evPaths tmpl.evNames
      let evSlot ← if tmpl.evNames.isEmpty then pure 0 else MonadDom.allocRowEvSlot node (tmpl.rowEvAt s)
      let nMarks := marks s
      let n := nMarks.size
      if n == 0 then
        return (node, .tlist node tmplId evSlot #[] false #[] #[] #[])
      else
        let newVals := collectTmplValsLoop (tmpl.rowVals s) 0 n (Array.emptyWithCapacity n)
        let newLive ← MonadDom.mountTmplRows node tmplId newVals
        return (node, .tlist node tmplId evSlot uKeys hasDups newLive newVals nMarks)
  | .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s => do
      let uKeys := disambiguateKeys (keys s)
      let node ← MonadDom.createElement ns tag
      applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s uKeys) (rowEv s uKeys) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      buildDomListM (Dom.childNsOf ns tag) node rs
      return (node, .list node uKeys perRow rs nMarks inst)

def buildViewKidsM [MonadDom msg m] (ns : String) (parent : Dom.Node) :
    List (View σ msg) → σ → m (List (VState σ msg))
  | [], _ => return []
  | k :: rest, s => do
      let (kn, kst) ← buildViewM ns k s
      MonadDom.appendChild parent kn
      let restSt ← buildViewKidsM ns parent rest s
      return kst :: restSt
end

mutual
def patchViewM [MonadDom msg m]
    (parent : Dom.Node) (index : UInt32) :
    View σ msg → σ → VState σ msg → m (VState σ msg)
  | .dyn get, s, .dyn node last => do
      let v := get s
      if v != last then MonadDom.setText node v
      return .dyn node v
  | .element _ attrs kids, s, .elem node kstates => do
      applyDynAttrsM node attrs s
      let ks' ← patchViewKidsM node 0 kids s kstates
      return .elem node ks'
  | .ifElse cond yes no, s, .cond wasYes inner => do
      let now := cond s
      if now == wasYes then
        let inner' ← if now then patchViewM parent index yes s inner
                     else patchViewM parent index no s inner
        return .cond now inner'
      else
        let ns ← MonadDom.childNamespace parent
        let (n, st) ← if now then buildViewM ns yes s else buildViewM ns no s
        MonadDom.replaceChild parent index n
        return .cond now st
  | .dynNode get, s, .dynNode node last => do
      let newHtml := get s
      let n' ← patchHtmlSubtreeM parent index node last newHtml
      return .dynNode n' newHtml
  | .memo sm, s, .memo node lastKey lastHtml => do
      let k := sm.keyOf s
      if k == lastKey then
        return .memo node lastKey lastHtml
      else
        let newHtml := sm.eval s
        let n' ← patchHtmlSubtreeM parent index node lastHtml newHtml
        return .memo n' k newHtml
  | .keyedList _ attrs keys marks _ _ _ (some tmpl), s,
    .tlist node tmplId evSlot oldKeys oldDups oldLive oldVals oldMarks =>
      patchTmplListM node attrs keys marks tmpl s tmplId evSlot oldKeys oldDups oldLive oldVals oldMarks
  | .keyedList _ attrs keys marks rowSig rowEv rowsHtml none, s,
    .list node oldKeys oldSigs oldRowsL oldMarks inst => do
      let rawKeys  := keys s
      let newMarks := marks s
      if rawKeys == oldKeys then
        applyDynAttrsM node attrs s
        let newSigs ← seedRowsM inst (rowSig s oldKeys) (rowEv s oldKeys) newMarks oldMarks oldSigs
        return .list node oldKeys newSigs oldRowsL newMarks inst
      else
        let newKeys := disambiguateKeys rawKeys
        if newKeys == oldKeys then
          applyDynAttrsM node attrs s
          let newSigs ← seedRowsM inst (rowSig s oldKeys) (rowEv s oldKeys) newMarks oldMarks oldSigs
          return .list node oldKeys newSigs oldRowsL newMarks inst
        else if newKeys.isEmpty then
          applyDynAttrsM node attrs s
          MonadDom.clearChildren node
          return .list node #[] #[] [] #[] inst
        else if oldRowsL.isEmpty then
          applyDynAttrsM node attrs s
          let newSigs ← seedRowsM inst (rowSig s newKeys) (rowEv s newKeys) newMarks #[] #[]
          let newRows := (rowsHtml s).map (Html.prefixSignals inst)
          let childNs ← MonadDom.childNamespace node
          let frag ← MonadDom.createFragment
          buildDomListM childNs frag newRows
          MonadDom.appendChild node frag
          return .list node newKeys newSigs newRows newMarks inst
        else
          let (oldBuckets, mask) := buildKeyIndex oldKeys
          let oldRows := oldRowsL.toArray
          let n := newKeys.size
          let (sources, used, rowsArr, marksArr, sigsArr) :=
            planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs
              (fun _ => ((rowsHtml s).map (Html.prefixSignals inst)).toArray) none 0
              (Array.emptyWithCapacity n) (Array.replicate oldKeys.size false)
              (Array.emptyWithCapacity n) (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)
          let newSigs ← seedRowsM inst (rowSig s newKeys) (rowEv s newKeys) newMarks marksArr sigsArr
          applyDynAttrsM node attrs s
          let childNs ← MonadDom.childNamespace node
          if !used.any id then
            MonadDom.clearChildren node
            let newRows := rowsArr.toList
            let frag ← MonadDom.createFragment
            buildDomListM childNs frag newRows
            MonadDom.appendChild node frag
            return .list node newKeys newSigs newRows newMarks inst
          else
            let oldCount ← MonadDom.childCount node
            let live ← snapshotChildrenM node 0 #[] oldCount.toNat
            removeUnusedM node live used 0
            let inLis := verifiedLisFlags sources
            reconcileLisBackM node childNs live sources inLis rowsArr n false 0
            return .list node newKeys newSigs rowsArr.toList newMarks inst
  | .text _,   _, st@(.text _) => return st
  | .static _, _, st@(.stat _) => return st
  | v, s, _ => do
      let (n, st) ← buildViewM (← MonadDom.childNamespace parent) v s
      MonadDom.replaceChild parent index n
      return st

def patchViewKidsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) :
    List (View σ msg) → σ → List (VState σ msg) → m (List (VState σ msg))
  | [], _, _ => return []
  | k :: rest, s, kst :: restSt => do
      let kst' ← patchViewM node i k s kst
      let restSt' ← patchViewKidsM node (i + 1) rest s restSt
      return kst' :: restSt'
  | k :: rest, s, [] => do
      let kst' ← patchViewM node i k s default
      let restSt' ← patchViewKidsM node (i + 1) rest s []
      return kst' :: restSt'
end

def View.textOf? (s : σ) : View σ msg → Option String
  | .text str                   => some str
  | .dyn get                    => some (get s)
  | .ifElse cond yes no         => if cond s then View.textOf? s yes else View.textOf? s no
  | .static html                => html.textOf?
  | .dynNode get                => (get s).textOf?
  | .memo sm                    => (sm.eval s).textOf?
  | .element .. | .keyedList .. => none

def hasMoreViewText (s : σ) : List (View σ msg) → Bool
  | []      => false
  | k :: cs =>
      match k.textOf? s with
      | some "" => hasMoreViewText s cs
      | some _  => true
      | none    => false

def hydrateListRowsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) : List (Html msg) → m Unit
  | []      => pure ()
  | r :: rs => do
      let child ← MonadDom.childAt node i
      hydrateDomM r child
      hydrateListRowsM node (i + 1) rs

mutual
def hydrateViewM [MonadDom msg m] :
    View σ msg → σ → Dom.Node → m (VState σ msg)
  | .text _,      _, node => return .text node
  | .dyn get,     s, node => return .dyn node (get s)
  | .static html, _, node => do hydrateDomM html node; return .stat node
  | .element _ attrs kids, s, node => do
      MonadDom.clearHandlers node
      applyAttrsM node (attrs.map (VAttr.eval s))
      let ks ← hydrateViewKidsM node s 0 false kids
      return .elem node ks
  | .ifElse cond yes no, s, node => do
      let b := cond s
      let cst ← if b then hydrateViewM yes s node else hydrateViewM no s node
      return .cond b cst
  | .dynNode get, s, node => do
      let html := get s
      hydrateDomM html node
      return .dynNode node html
  | .memo sm, s, node => do
      let k := sm.keyOf s
      let html := sm.eval s
      hydrateDomM html node
      return .memo node k html
  | .keyedList _ attrs keys marks _ _ _ (some tmpl), s, node => do
      let rawKs := keys s
      let uKeys := disambiguateKeys rawKs
      let hasDups := uKeys != rawKs
      MonadDom.clearHandlers node
      applyAttrsM node (attrs.map (VAttr.eval s))
      let childNs ← MonadDom.childNamespace node
      let tmplId ← MonadDom.compileRowTmpl childNs tmpl.proto tmpl.slotPaths tmpl.slotAttrs tmpl.evPaths tmpl.evNames
      let evSlot ← if tmpl.evNames.isEmpty then pure 0 else MonadDom.allocRowEvSlot node (tmpl.rowEvAt s)
      let nMarks := marks s
      let n := nMarks.size
      let newVals := collectTmplValsLoop (tmpl.rowVals s) 0 n (Array.emptyWithCapacity n)
      let live ← hydrateTmplRowsM node tmplId 0 n (Array.emptyWithCapacity n)
      return .tlist node tmplId evSlot uKeys hasDups live newVals nMarks
  | .keyedList _ attrs keys marks rowSig rowEv rowsHtml none, s, node => do
      let uKeys := disambiguateKeys (keys s)
      MonadDom.clearHandlers node
      applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s uKeys) (rowEv s uKeys) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      hydrateListRowsM node 0 rs
      return .list node uKeys perRow rs nMarks inst

def hydrateViewKidsM [MonadDom msg m] (node : Dom.Node)
    (s : σ) (i : UInt32) (inTextRun : Bool) :
    List (View σ msg) → m (List (VState σ msg))
  | [] => return []
  | k :: rest => do
      let (kn, nextRun) ← match k.textOf? s with
        | some str => hydrateTextSlotM node i inTextRun str (fun () => hasMoreViewText s rest)
        | none     => do let cn ← MonadDom.childAt node i; pure (cn, false)
      let kst ← hydrateViewM k s kn
      let restSt ← hydrateViewKidsM node s (i + 1) nextRun rest
      return kst :: restSt
end

@[inline] def buildView (h : Handlers msg) (ns : String) (v : View σ msg) (s : σ) :
    IO (Dom.Node × VState σ msg) :=
  ReaderT.run (buildViewM (m := DomM msg) ns v s) h

@[inline] def patchView (h : Handlers msg) (parent : Dom.Node) (index : UInt32)
    (v : View σ msg) (s : σ) (st : VState σ msg) : IO (VState σ msg) :=
  ReaderT.run (patchViewM (m := DomM msg) parent index v s st) h

@[inline] def hydrateView (h : Handlers msg) (v : View σ msg) (s : σ) (node : Dom.Node) :
    IO (VState σ msg) :=
  ReaderT.run (hydrateViewM (m := DomM msg) v s node) h

end Qed
