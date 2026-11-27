import Qed.Render
import Qed.Style.Core
import Qed.Notation
import Std.Data.HashSet

namespace Qed

@[specialize 2] def pickFreshKeyLoopWith (k : String) (has : String → Bool) (maxLen : Nat) : Nat → Nat → String
  | _, 0 => k ++ String.ofList (List.replicate (maxLen + 1) '~')
  | i, fuel + 1 => let cand := k ++ "~~dup" ++ Nat.repr i; if !has cand then cand else pickFreshKeyLoopWith k has maxLen (i + 1) fuel

def pickFreshKey (k : String) (seen : Std.HashSet String) (maxLen : Nat) : String :=
  if !seen.contains k then k else pickFreshKeyLoopWith k seen.contains maxLen 1 seen.size

private theorem pickFreshKeyLoop_not_mem (k : String) (seen : Std.HashSet String) (maxLen : Nat)
    (hmax : ∀ s, s ∈ seen → s.length ≤ maxLen) : ∀ (i fuel : Nat), pickFreshKeyLoopWith k seen.contains maxLen i fuel ∉ seen
  | _, 0 => fun hmem => by
      have hle := hmax _ hmem
      have hlen : (k ++ String.ofList (List.replicate (maxLen + 1) '~')).length = k.length + (maxLen + 1) := by simp [String.length_append]
      unfold pickFreshKeyLoopWith at hle; omega
  | i, fuel + 1 => by
      simp only [pickFreshKeyLoopWith]; split
      · rename_i hc; exact fun hmem => by simp [Std.HashSet.contains_iff_mem.2 hmem] at hc
      · exact pickFreshKeyLoop_not_mem k seen maxLen hmax (i + 1) fuel

private theorem pickFreshKey_not_mem (k : String) (seen : Std.HashSet String) (maxLen : Nat)
    (hmax : ∀ s, s ∈ seen → s.length ≤ maxLen) : pickFreshKey k seen maxLen ∉ seen := by
  unfold pickFreshKey; split
  · rename_i hc; exact fun hmem => by simp [Std.HashSet.contains_iff_mem.2 hmem] at hc
  · exact pickFreshKeyLoop_not_mem k seen maxLen hmax 1 seen.size

def disambiguateKeysTR (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String) : List String → Array String
  | [] => acc
  | k :: rest => let k' := pickFreshKey k seen maxLen; disambiguateKeysTR (seen.insert k') (Nat.max maxLen k'.length) (acc.push k') rest

def disambiguateKeys (keys : Array String) : Array String := disambiguateKeysTR ∅ 0 #[] keys.toList

private theorem maxLen_insert {seen : Std.HashSet String} {maxLen : Nat} (hmax : ∀ s, s ∈ seen → s.length ≤ maxLen) (k' : String) :
    ∀ s, s ∈ seen.insert k' → s.length ≤ Nat.max maxLen k'.length := fun s hs =>
  (Std.HashSet.mem_insert.1 hs).elim (fun h => eq_of_beq h ▸ Nat.le_max_right _ _) (fun h => Nat.le_trans (hmax s h) (Nat.le_max_left _ _))

private theorem disambiguateKeysTR_nodup :
    ∀ (ks : List String) (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      (∀ s, s ∈ seen → s.length ≤ maxLen) → (∀ s, s ∈ acc.toList → s ∈ seen) → acc.toList.Nodup → (disambiguateKeysTR seen maxLen acc ks).toList.Nodup
  | [], _, _, _, _, _, hnd => hnd
  | k :: rest, seen, maxLen, acc, hmax, hsub, hnd => by
      let k' := pickFreshKey k seen maxLen; have hnot : k' ∉ seen := pickFreshKey_not_mem k seen maxLen hmax
      refine disambiguateKeysTR_nodup rest (seen.insert k') (Nat.max maxLen k'.length) (acc.push k') (maxLen_insert hmax k') ?_ ?_
      · intro s hs; rw [Array.toList_push, List.mem_append] at hs
        exact Std.HashSet.mem_insert.2 <| hs.elim (fun h1 => .inr (hsub s h1)) (fun h2 => by rcases List.mem_singleton.1 h2 with rfl; exact .inl (beq_self_eq_true _))
      · rw [Array.toList_push, List.nodup_append]
        exact ⟨hnd, List.pairwise_singleton _ _, fun b hb _ hc heq => hnot (List.mem_singleton.1 hc ▸ heq ▸ hsub b hb)⟩

theorem disambiguateKeys_nodup (keys : Array String) : (disambiguateKeys keys).toList.Nodup :=
  disambiguateKeysTR_nodup keys.toList ∅ 0 #[] (fun _ h => by simp at h) (fun _ h => by simp at h) List.Pairwise.nil

private theorem disambiguateKeysTR_size : ∀ (ks : List String) (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
    (disambiguateKeysTR seen maxLen acc ks).size = acc.size + ks.length
  | [], _, _, _ => by simp [disambiguateKeysTR]
  | _ :: rest, seen, maxLen, acc => by simp only [disambiguateKeysTR, disambiguateKeysTR_size rest, Array.size_push, List.length_cons]; omega

theorem disambiguateKeys_size (keys : Array String) : (disambiguateKeys keys).size = keys.size := by
  simpa [disambiguateKeys] using disambiguateKeysTR_size keys.toList ∅ 0 #[]

private theorem disambiguateKeysTR_of_nodup :
    ∀ (ks : List String) (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      (∀ k ∈ ks, k ∉ seen) → ks.Nodup → (disambiguateKeysTR seen maxLen acc ks).toList = acc.toList ++ ks
  | [], _, _, _, _, _ => by simp [disambiguateKeysTR]
  | k :: rest, seen, maxLen, acc, hdisj, hnd => by
      rcases List.nodup_cons.1 hnd with ⟨hkrest, hndRest⟩
      have hkc : seen.contains k = false := Bool.eq_false_iff.2 fun hc => hdisj k List.mem_cons_self (Std.HashSet.contains_iff_mem.1 hc)
      simp only [disambiguateKeysTR, show pickFreshKey k seen maxLen = k by simp [pickFreshKey, hkc]]
      rw [disambiguateKeysTR_of_nodup rest (seen.insert k) (Nat.max maxLen k.length) (acc.push k)
        (fun x hx hm => (Std.HashSet.mem_insert.1 hm).elim (fun h => hkrest (eq_of_beq h ▸ hx)) (hdisj x (List.mem_cons_of_mem k hx))) hndRest]
      simp [Array.toList_push]

theorem disambiguateKeys_of_nodup {keys : Array String} (hnd : keys.toList.Nodup) : disambiguateKeys keys = keys :=
  Array.ext' (by simpa [disambiguateKeys] using disambiguateKeysTR_of_nodup keys.toList ∅ 0 #[] (fun _ _ h => by simp at h) hnd)

def nextPow2Ge (target cur : Nat) : Nat → Nat
  | 0 => cur | fuel' + 1 => if cur ≥ target then cur else nextPow2Ge target (cur * 2) fuel'

theorem nextPow2Ge_pos (target : Nat) : ∀ (cur fuel : Nat), 0 < cur → 0 < nextPow2Ge target cur fuel
  | _, 0, h => h | cur, fuel + 1, h => by unfold nextPow2Ge; split; exact h; exact nextPow2Ge_pos target (cur * 2) fuel (by omega)

@[inline] def strBucketIdx (k : String) (mask : USize) (sz : Nat) : Nat := let idx := ((hash k).toUSize &&& mask).toNat; if idx < sz then idx else 0
theorem strBucketIdx_lt (k : String) (mask : USize) (sz : Nat) (hsz : 0 < sz) : strBucketIdx k mask sz < sz := by unfold strBucketIdx; dsimp only; split <;> assumption

@[inline] private def bucketContains (buckets : @& Array (List String)) (mask : USize) (k : String) : Bool :=
  if h : 0 < buckets.size then (buckets[strBucketIdx k mask buckets.size]'(strBucketIdx_lt k mask buckets.size h)).contains k else false

private def disambiguateKeysFastLoop (keys : @& Array String) (i : Nat)
    (buckets : Array (List String)) (mask : USize) (maxLen : Nat) (acc : Array String) : Array String :=
  if h : i < keys.size then
    let k := keys[i]
    let k' := if !bucketContains buckets mask k then k else pickFreshKeyLoopWith k (bucketContains buckets mask) maxLen 1 i
    let buckets' :=
      if hb : 0 < buckets.size then
        let bi := strBucketIdx k' mask buckets.size
        have hbi : bi < buckets.size := strBucketIdx_lt k' mask buckets.size hb
        buckets.set bi (k' :: buckets[bi]) hbi
      else buckets
    disambiguateKeysFastLoop keys (i + 1) buckets' mask (Nat.max maxLen k'.length) (acc.push k')
  else acc
termination_by keys.size - i

/-- Bare-array `O(N)` key disambiguator (`@[csimp]` replacement for `disambiguateKeys`). -/
def disambiguateKeysFast (keys : Array String) : Array String :=
  let cap := nextPow2Ge (keys.size * 2) 16 30
  disambiguateKeysFastLoop keys 0 (Array.replicate cap []) (USize.ofNat (cap - 1)) 0 (Array.emptyWithCapacity keys.size)

private def BucketsMatch (buckets : Array (List String)) (mask : USize) (seen : Std.HashSet String) : Prop :=
  0 < buckets.size ∧ ∀ s : String, bucketContains buckets mask s = seen.contains s

private theorem pickFreshKeyLoopWith_congr (k : String) {f g : String → Bool} (hfg : ∀ s, f s = g s) (maxLen : Nat) :
    ∀ i fuel, pickFreshKeyLoopWith k f maxLen i fuel = pickFreshKeyLoopWith k g maxLen i fuel
  | _, 0 => rfl | i, fuel + 1 => by simp only [pickFreshKeyLoopWith, hfg]; split <;> first | rfl | exact pickFreshKeyLoopWith_congr k hfg maxLen (i + 1) fuel

private theorem bucketsMatch_insert {buckets : Array (List String)} {mask : USize} {seen : Std.HashSet String}
    (hm : BucketsMatch buckets mask seen) (k' : String) :
    let bi := strBucketIdx k' mask buckets.size; let hbi : bi < buckets.size := strBucketIdx_lt k' mask buckets.size hm.1
    BucketsMatch (buckets.set bi (k' :: buckets[bi]) hbi) mask (seen.insert k') := by
  intro bi hbi; refine ⟨by simp only [Array.size_set, hm.1], fun s => ?_⟩
  have hprev : (buckets[strBucketIdx s mask buckets.size]'(strBucketIdx_lt s mask buckets.size hm.1)).contains s = seen.contains s := by simpa [bucketContains, hm.1] using hm.2 s
  simp only [bucketContains, Array.size_set, hm.1, ↓reduceDIte, Array.getElem_set, Std.HashSet.contains_insert]
  by_cases heq : k' = s
  · subst heq; simp [bi]
  · have hks : (k' == s) = false := beq_eq_false_iff_ne.2 heq; have hsk : (s == k') = false := beq_eq_false_iff_ne.2 (Ne.symm heq)
    split
    · rename_i h; simp only [h, List.contains_cons, hks, hsk, hprev, Bool.false_or]
    · simp only [hks, hprev, Bool.false_or]

private theorem disambiguateKeysFastLoop_eq (keys : Array String) (mask : USize) :
    ∀ (i : Nat) (buckets : Array (List String)) (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      i ≤ keys.size → BucketsMatch buckets mask seen → (∀ s, s ∈ seen → s.length ≤ maxLen) → seen.size = i →
      disambiguateKeysFastLoop keys i buckets mask maxLen acc = disambiguateKeysTR seen maxLen acc (keys.toList.drop i) := by
  intro i; induction hrem : keys.size - i generalizing i with
  | zero =>
      intro _ _ _ _ hle _ _ _; obtain rfl : i = keys.size := by omega
      have hdrop : keys.toList.drop keys.size = [] := List.drop_of_length_le (by simp)
      unfold disambiguateKeysFastLoop; simp [hdrop, disambiguateKeysTR]
  | succ _ ih =>
      intro buckets seen maxLen acc hle hm hmax hsz; have hlt : i < keys.size := by omega
      rw [show keys.toList.drop i = keys[i] :: keys.toList.drop (i + 1) by rw [List.drop_eq_getElem_cons (by simpa using hlt)]; rfl]
      unfold disambiguateKeysFastLoop; simp only [hlt, ↓reduceDIte, hm.1, disambiguateKeysTR]
      have hpk : (if !bucketContains buckets mask keys[i] then keys[i] else pickFreshKeyLoopWith keys[i] (bucketContains buckets mask) maxLen 1 i) = pickFreshKey keys[i] seen maxLen := by
        simp only [pickFreshKey, hm.2, hsz.symm, pickFreshKeyLoopWith_congr _ hm.2]
      simp only [hpk]; let k' := pickFreshKey keys[i] seen maxLen; have hnot : k' ∉ seen := pickFreshKey_not_mem keys[i] seen maxLen hmax
      exact ih (i + 1) (by omega) _ (seen.insert k') (Nat.max maxLen k'.length) (acc.push k')
        (by omega) (bucketsMatch_insert hm k') (maxLen_insert hmax k') (by simp [Std.HashSet.size_insert, hnot, hsz])

@[csimp] theorem disambiguateKeys_eq_fast : @disambiguateKeys = @disambiguateKeysFast := by
  funext keys; unfold disambiguateKeys disambiguateKeysFast
  let cap := nextPow2Ge (keys.size * 2) 16 30; have hcap : 0 < cap := nextPow2Ge_pos _ 16 30 (by omega)
  simpa using (disambiguateKeysFastLoop_eq keys (USize.ofNat (cap - 1)) 0 (Array.replicate cap []) ∅ 0
    (Array.emptyWithCapacity keys.size) (Nat.zero_le _) ⟨by simp [hcap], fun s => by simp [bucketContains, hcap]⟩ (fun _ h => by simp at h) (by simp)).symm

structure SoundMemo (σ : Type) (msg : Type) where
  keyOf : σ → String
  eval  : σ → Html msg
  sound : ∀ s s', keyOf s = keyOf s' → eval s = eval s'

def SoundMemo.mapScope (f : σ' → σ) (sm : SoundMemo σ msg) : SoundMemo σ' msg :=
  ⟨sm.keyOf ∘ f, sm.eval ∘ f, fun s₁ s₂ h => sm.sound (f s₁) (f s₂) h⟩
def SoundMemo.ofLawful {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) : SoundMemo σ msg :=
  ⟨LawfulKey.toKey ∘ proj, f ∘ proj, fun s₁ s₂ h => congrArg f (LawfulKey.injective (proj s₁) (proj s₂) h)⟩

inductive VAttr (σ : Type) (msg : Type) where
  | stat (a : Attr msg) | bind (get : σ → Attr msg) | dynVal (attr : String) (get : σ → String) | dynOn (event : String) (get : σ → msg)

structure RowTmpl (σ msg : Type) where
  proto     : Html msg
  slotPaths : Array (Array UInt32)
  slotAttrs : Array String
  evPaths   : Array (Array UInt32)
  evNames   : Array String
  rowKey    : σ → Nat → String
  rowVals   : σ → Nat → Array String
  rowEvAt   : σ → Nat → Nat → Option msg

def RowTmpl.mapScope (f : σ' → σ) (t : RowTmpl σ msg) : RowTmpl σ' msg :=
  { t with rowKey := t.rowKey ∘ f, rowVals := t.rowVals ∘ f, rowEvAt := t.rowEvAt ∘ f }

def applyHtmlSlotAt {msg : Type} (path : List Nat) (attrName val : String) : Html msg → Html msg
  | .text s => if path.isEmpty && attrName.isEmpty then .text val else .text s
  | .element tag attrs kids => match path with
      | [] => .element tag (attrs.map fun | .attr k v => if k == attrName then .attr k val else .attr k v | other => other) kids
      | i :: rest => .element tag attrs (kids.modify i (applyHtmlSlotAt rest attrName val))

def applyRowSlotsLoop {msg : Type} (slotPaths : Array (Array UInt32)) (slotAttrs vals : Array String) (i : Nat) (h : Html msg) : Html msg :=
  if hi : i < slotPaths.size then
    applyRowSlotsLoop slotPaths slotAttrs vals (i + 1) (applyHtmlSlotAt (slotPaths[i].toList.map UInt32.toNat) (slotAttrs.getD i "") (vals.getD i "") h)
  else h
termination_by slotPaths.size - i

def applyRowSlots {msg : Type} (proto : Html msg) (slotPaths : Array (Array UInt32)) (slotAttrs vals : Array String) : Html msg :=
  applyRowSlotsLoop slotPaths slotAttrs vals 0 proto

inductive View (σ : Type) (msg : Type) where
  | text (s : String)
  | dyn (get : σ → String)
  | element (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg))
  | ifElse (cond : σ → Bool) (yes no : View σ msg)
  | keyedList (tag : String) (attrs : List (VAttr σ msg)) (keys : σ → Array String)
      (marks : σ → Array USize) (rowSig : σ → Array String → Nat → Array (String × String))
      (rowEv : σ → Array String → Nat → Array (String × msg)) (rowsHtml : σ → List (Html msg))
      (tmpl? : Option (RowTmpl σ msg) := none)
  | static (html : Html msg)
  | dynNode (get : σ → Html msg)
  | memo (sm : SoundMemo σ msg)

def View.showIf (cond : σ → Bool) (child : View σ msg) : View σ msg := .ifElse cond child (.text "")

-- Transpiler emits `$.refMark` (ids ≥ 1); pure `0` never matches a real stamp so native evaluation never skips.
@[noinline] def refMark {α : Type} (a : α) : USize := (fun _ => 0) a

def VAttr.eval (s : σ) : VAttr σ msg → Attr msg
  | .stat a => a | .bind f => f s | .dynVal attr get => .attr attr (get s) | .dynOn ev get => .on ev (get s)

@[simp] theorem VAttr.eval_stat (s : σ) (a : Attr msg) : VAttr.eval s (.stat a) = a := rfl
@[simp] theorem VAttr.eval_bind (s : σ) (f : σ → Attr msg) : VAttr.eval s (.bind f) = f s := rfl
@[simp] theorem VAttr.eval_dynVal {msg : Type} (s : σ) (k : String) (g : σ → String) : (VAttr.dynVal k g : VAttr σ msg).eval s = .attr k (g s) := rfl
@[simp] theorem VAttr.eval_dynOn {msg : Type} (s : σ) (e : String) (g : σ → msg) : (VAttr.dynOn e g : VAttr σ msg).eval s = .on e (g s) := rfl

def VAttr.mapScope (f : σ' → σ) : VAttr σ msg → VAttr σ' msg
  | .stat a => .stat a | .bind g => .bind (g ∘ f) | .dynVal a g => .dynVal a (g ∘ f) | .dynOn e g => .dynOn e (g ∘ f)

@[simp] theorem VAttr.eval_mapScope (f : σ' → σ) (s' : σ') (va : VAttr σ msg) : VAttr.eval s' (va.mapScope f) = VAttr.eval (f s') va := by cases va <;> rfl

def withKey (k : String) : Html msg → Html msg | .element t as cs => .element t (.key k :: as) cs | h => h
@[simp] theorem Html.validIn_withKey (ctx : HtmlCtx) (k : String) (h : Html msg) : Html.validIn ctx (withKey k h) = Html.validIn ctx h := by cases h <;> simp [withKey, Html.validIn, Attr.valid]
@[simp] theorem Html.canonical_withKey (k : String) (h : Html msg) : Html.canonical (withKey k h) = Html.canonical h := by cases h <;> simp [withKey, Html.canonical, mkCanonicalElem, List.filterMap_cons, Attr.canonical]

mutual
  def View.mapScope (f : σ' → σ) : View σ msg → View σ' msg
    | .text s => .text s | .dyn get => .dyn (get ∘ f) | .static h => .static h | .dynNode get => .dynNode (get ∘ f) | .memo sm => .memo (sm.mapScope f)
    | .element t as ks => .element t (as.map (VAttr.mapScope f)) (View.mapScopeEach f ks)
    | .ifElse cond y n => .ifElse (cond ∘ f) (y.mapScope f) (n.mapScope f)
    | .keyedList t as keys marks rs re rh tmpl? =>
        .keyedList t (as.map (VAttr.mapScope f)) (keys ∘ f) (marks ∘ f) (rs ∘ f) (re ∘ f) (rh ∘ f) (tmpl?.map (RowTmpl.mapScope f))
  def View.mapScopeEach (f : σ' → σ) : List (View σ msg) → List (View σ' msg) | [] => [] | k :: ks => k.mapScope f :: View.mapScopeEach f ks
end

mutual
  def View.render : View σ msg → σ → Html msg
    | .text s, _ => .text s | .dyn get, s => .text (get s) | .static h, _ => h | .dynNode get, s => get s | .memo sm, s => sm.eval s
    | .element t as ks, s => .element t (as.map (VAttr.eval s)) (View.renderEach ks s)
    | .ifElse cond y n, s => if cond s then View.render y s else View.render n s
    | .keyedList tag as _ _ _ _ rowsHtml _, s => .element tag (as.map (VAttr.eval s)) (rowsHtml s)
  def View.renderEach : List (View σ msg) → σ → List (Html msg) | [], _ => [] | k :: ks, s => View.render k s :: View.renderEach ks s
end

@[simp] theorem View.renderEach_isEmpty : ∀ (ks : List (View σ msg)) (s : σ), (View.renderEach ks s).isEmpty = ks.isEmpty | [], _ | _ :: _, _ => rfl

mutual
  @[simp] theorem View.render_mapScope (f : σ' → σ) (v : View σ msg) (s' : σ') : View.render (v.mapScope f) s' = View.render v (f s') := by
    cases v with
    | element _ _ ks => simp only [View.mapScope, View.render, List.map_map, Function.comp_def, VAttr.eval_mapScope, View.renderEach_mapScopeEach f ks s']
    | ifElse _ y n => simp only [View.mapScope, View.render, Function.comp_def, View.render_mapScope f y s', View.render_mapScope f n s']
    | keyedList _ _ _ _ _ _ _ _ => simp only [View.mapScope, View.render, List.map_map, Function.comp_def, VAttr.eval_mapScope]
    | text _ | dyn _ | static _ | dynNode _ | memo _ => rfl
  @[simp] theorem View.renderEach_mapScopeEach (f : σ' → σ) (vs : List (View σ msg)) (s' : σ') :
      View.renderEach (View.mapScopeEach f vs) s' = View.renderEach vs (f s') := by
    cases vs with | nil => rfl | cons k ks => show View.render (k.mapScope f) s' :: _ = _; rw [View.render_mapScope, View.renderEach_mapScopeEach]; rfl
end

instance : CoeFun (View σ msg) (fun _ => σ → Html msg) := ⟨View.render⟩

@[simp] theorem View.renderEach_map {α σ msg : Type} (xs : List α) (f : α → View σ msg) (s : σ) :
    View.renderEach (xs.map f) s = xs.map (fun a => View.render (f a) s) := by induction xs <;> simp [View.renderEach, *]
@[simp] theorem View.render_ite {σ msg : Type} (c : Prop) [Decidable c] (a b : View σ msg) (s : σ) :
    View.render (if c then a else b) s = (if c then View.render a s else View.render b s) := by split <;> rfl

theorem View.validIn_render_ifElse {σ msg : Type} (ctx : HtmlCtx) (cond : σ → Bool) (y n : View σ msg) (s : σ)
    (hy : cond s = true → Html.validIn ctx (View.render y s) = true) (hn : cond s = false → Html.validIn ctx (View.render n s) = true) :
    Html.validIn ctx (View.render (.ifElse cond y n) s) = true := by simp only [View.render]; cases hc : cond s <;> simp [hc, hy, hn]
theorem View.validIn_render_showIf {σ msg : Type} (ctx : HtmlCtx) (cond : σ → Bool) (child : View σ msg) (s : σ)
    (hy : cond s = true → Html.validIn ctx (View.render child s) = true) : Html.validIn ctx (View.render (.showIf cond child) s) = true :=
  View.validIn_render_ifElse ctx cond child (.text "") s hy (fun _ => by simp [View.render, Html.validIn])

theorem View.validIn_render_element_intro {σ msg : Type} (ctx childCtx : HtmlCtx)
    (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg)) (s : σ)
    (hstep : stepHtmlCtx ctx tag = some childCtx) (hattrs : Attr.validList (attrs.map (VAttr.eval s)) = true)
    (hvoid : (!isVoidTag tag || kids.isEmpty) = true) (hcell : (!Attr.hasLocalCell (attrs.map (VAttr.eval s)) || kids.isEmpty) = true)
    (hkids : Html.validListIn childCtx (View.renderEach kids s) = true) : Html.validIn ctx (View.render (.element tag attrs kids) s) = true :=
  Html.validIn_element_intro ctx childCtx tag (attrs.map (VAttr.eval s)) (View.renderEach kids s) hstep hattrs
    (by simpa [View.renderEach_isEmpty] using hvoid) (by simpa [View.renderEach_isEmpty] using hcell) hkids

theorem View.validListIn_renderEach_nil {σ msg : Type} (ctx : HtmlCtx) (s : σ) : Html.validListIn ctx (View.renderEach ([] : List (View σ msg)) s) = true := rfl
theorem View.validListIn_renderEach_cons {σ msg : Type} (ctx : HtmlCtx) (k : View σ msg) (ks : List (View σ msg)) (s : σ)
    (hk : Html.validIn ctx (View.render k s) = true) (hks : Html.validListIn ctx (View.renderEach ks s) = true) : Html.validListIn ctx (View.renderEach (k :: ks) s) = true := Html.validListIn_cons_intro ctx _ _ hk hks
theorem View.validListIn_renderEach_map_intro {α σ msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → View σ msg) (s : σ) (hf : ∀ a, Html.validIn ctx (View.render (f a) s) = true) :
    Html.validListIn ctx (View.renderEach (xs.map f) s) = true := (View.renderEach_map xs f s).symm ▸ Html.validListIn_map_intro ctx xs (fun a => View.render (f a) s) hf
theorem View.validIn_render_mapScope_intro {σ' σ msg : Type} (ctx : HtmlCtx) (f : σ' → σ) (v : View σ msg) (s' : σ') (hv : Html.validIn ctx (View.render v (f s')) = true) :
    Html.validIn ctx (View.render (v.mapScope f) s') = true := (View.render_mapScope f v s').symm ▸ hv
theorem View.validListIn_renderEach_mapScopeEach_intro {σ' σ msg : Type} (ctx : HtmlCtx) (f : σ' → σ) (vs : List (View σ msg)) (s' : σ') (hvs : Html.validListIn ctx (View.renderEach vs (f s')) = true) :
    Html.validListIn ctx (View.renderEach (View.mapScopeEach f vs) s') = true := (View.renderEach_mapScopeEach f vs s').symm ▸ hvs
theorem View.validIn_render_ite_intro {σ msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : View σ msg) (s : σ)
    (ht : c → Html.validIn ctx (View.render a s) = true) (hf : ¬ c → Html.validIn ctx (View.render b s) = true) :
    Html.validIn ctx (View.render (if c then a else b) s) = true := (View.render_ite c a b s).symm ▸ Html.validIn_ite_intro ctx c _ _ ht hf

theorem Html.validIn_withKey_intro {msg : Type} (ctx : HtmlCtx) (k : String) (h : Html msg) (hh : Html.validIn ctx h = true) : Html.validIn ctx (withKey k h) = true := (Html.validIn_withKey ctx k h).trans hh
theorem Html.validIn_map_intro {α β : Type} (ctx : HtmlCtx) (f : α → β) (h : Html α) (hh : Html.validIn ctx h = true) : Html.validIn ctx (h.map f) = true := (Html.validIn_map ctx f h).trans hh
theorem Html.validListIn_mapChildren_intro {α β : Type} (ctx : HtmlCtx) (f : α → β) (hs : List (Html α)) (hh : Html.validListIn ctx hs = true) : Html.validListIn ctx (Html.mapChildren f hs) = true := (Html.validListIn_mapChildren ctx f hs).trans hh
theorem Html.validIn_prefixSignals_intro {msg : Type} (ctx : HtmlCtx) (p : String) (h : Html msg) (hh : Html.validIn ctx h = true) : Html.validIn ctx (h.prefixSignals p) = true := (Html.validIn_prefixSignals ctx p h).trans hh
theorem Html.validListIn_prefixSignalsList_intro {msg : Type} (ctx : HtmlCtx) (p : String) (hs : List (Html msg)) (hh : Html.validListIn ctx hs = true) : Html.validListIn ctx (Html.prefixSignalsList p hs) = true := (Html.validListIn_prefixSignalsList ctx p hs).trans hh

def View.ofHtml (f : σ → Html msg) : View σ msg := .dynNode f
def dynValGets (attrs : List (VAttr σ msg)) : List (σ → String) := attrs.filterMap fun | .dynVal _ get => some get | _ => none
def dynOnGets (attrs : List (VAttr σ msg)) : List (σ → msg) := attrs.filterMap fun | .dynOn _ get => some get | _ => none

mutual
  def View.collectDyn : View σ msg → List (σ → String)
    | .dyn get => [get] | .element _ attrs kids => dynValGets attrs ++ View.collectDynList kids | .ifElse _ y no => View.collectDyn y ++ View.collectDyn no | _ => []
  def View.collectDynList : List (View σ msg) → List (σ → String) | [] => [] | k :: ks => View.collectDyn k ++ View.collectDynList ks
end

mutual
  def View.collectDynOn : View σ msg → List (σ → msg)
    | .element _ attrs kids => dynOnGets attrs ++ View.collectDynOnList kids | .ifElse _ y no => View.collectDynOn y ++ View.collectDynOn no | _ => []
  def View.collectDynOnList : List (View σ msg) → List (σ → msg) | [] => [] | k :: ks => View.collectDynOn k ++ View.collectDynOnList ks
end

def tagBlocksDirectSpan (tag : String) : Bool :=
  tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" || tag == "colgroup" || tag == "thead" || tag == "tbody" || tag == "tfoot" || tag == "tr"
def tagBlocksSpanSubtree (tag : String) : Bool :=
  tag == "select" || tag == "optgroup" || tag == "option" || tag == "textarea" || tag == "style" || tag == "svg"

mutual
  def View.hasOpaque : View σ msg → Bool
    | .text _ | .dyn _ | .static _ => false
    | .element tag attrs kids =>
        attrs.any (fun | .bind _ => true | _ => false) || (tagBlocksDirectSpan tag && kids.any (fun | .dyn _ => true | _ => false)) ||
        (tagBlocksSpanSubtree tag && !(View.collectDynList kids).isEmpty) || View.hasOpaqueList kids
    | _ => true
  def View.hasOpaqueList : List (View σ msg) → Bool | [] => false | k :: ks => k.hasOpaque || View.hasOpaqueList ks
end

def renderSigAttrs (s : σ) (pre : String) : List (VAttr σ msg) → Nat → Nat → List (Attr msg) × Nat × Nat
  | [], n, en => ([], n, en)
  | va :: rest, n, en =>
      let (a, n1, en1) := match va with
        | .dynVal attr get => (Attr.signalAttr s!"{pre}#{n}" attr (get s), n + 1, en)
        | .dynOn ev get => (Attr.signalOn s!"{pre}#e{en}" ev (get s), n, en + 1)
        | other => (VAttr.eval s other, n, en)
      let (as, n2, en2) := renderSigAttrs s pre rest n1 en1; (a :: as, n2, en2)

@[simp] theorem Attr.validList_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), Attr.validList (renderSigAttrs s pre attrs n en).1 = Attr.validList (attrs.map (VAttr.eval s))
  | [], _, _ => rfl | va :: rest, _, _ => by cases va <;> exact congrArg (_ && ·) (Attr.validList_renderSigAttrs s pre rest _ _)

@[simp] theorem Attr.hasLocalCell_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), Attr.hasLocalCell (renderSigAttrs s pre attrs n en).1 = Attr.hasLocalCell (attrs.map (VAttr.eval s))
  | [], _, _ => rfl | va :: rest, _, _ => by cases va <;> exact congrArg (_ || ·) (Attr.hasLocalCell_renderSigAttrs s pre rest _ _)

mutual
  def View.renderSig : View σ msg → σ → String → Nat → (en : Nat := 0) → Html msg × Nat × Nat
    | .text s, _, _, n, en => (.text s, n, en)
    | .dyn get, s, pre, n, en => (.element "span" [.signalBind s!"{pre}#{n}"] [.text (get s)], n + 1, en)
    | .element tag attrs kids, s, pre, n, en =>
        let (attrs', n1, en1) := renderSigAttrs s pre attrs n en
        let (cs, n2, en2) := View.renderSigList kids s pre n1 en1; (.element tag attrs' cs, n2, en2)
    | .ifElse cond y no, s, pre, n, en =>
        if cond s then let (h, n1, en1) := View.renderSig y s pre n en; (h, n1 + (View.collectDyn no).length, en1 + (View.collectDynOn no).length)
        else View.renderSig no s pre (n + (View.collectDyn y).length) (en + (View.collectDynOn y).length)
    | .keyedList tag as _ _ _ _ rowsHtml _, s, _, n, en => (.element tag (as.map (VAttr.eval s)) (rowsHtml s), n, en)
    | .static h, _, _, n, en => (h, n, en) | .dynNode get, s, _, n, en => (get s, n, en) | .memo sm, s, _, n, en => (sm.eval s, n, en)
  def View.renderSigList : List (View σ msg) → σ → String → Nat → (en : Nat := 0) → List (Html msg) × Nat × Nat
    | [], _, _, n, en => ([], n, en)
    | k :: ks, s, pre, n, en => let (h, n', en') := View.renderSig k s pre n en; let (hs, n'', en'') := View.renderSigList ks s pre n' en'; (h :: hs, n'', en'')
end

@[simp] theorem View.renderSigList_isEmpty : ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n en : Nat), (View.renderSigList ks s pre n en).1.isEmpty = ks.isEmpty
  | [], _, _, _, _ | _ :: _, _, _, _, _ => rfl

@[simp] theorem renderSigAttrs_canonical (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), (renderSigAttrs s pre attrs n en).1.filterMap Attr.canonical = (attrs.map (VAttr.eval s)).filterMap Attr.canonical
  | [], _, _ => rfl
  | va :: rest, n, en => by
      cases va with
      | stat _ | bind _ => dsimp only [renderSigAttrs, List.map, VAttr.eval, List.filterMap]; cases Attr.canonical _ <;> simp only [renderSigAttrs_canonical s pre rest n en]
      | dynVal a g => exact congrArg (Attr.attr a (g s) :: ·) (renderSigAttrs_canonical s pre rest (n + 1) en)
      | dynOn e g => exact congrArg (Attr.on e (g s) :: ·) (renderSigAttrs_canonical s pre rest n (en + 1))

@[simp] theorem onlySignalBind_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), onlySignalBind (renderSigAttrs s pre attrs n en).1 = onlySignalBind (attrs.map (VAttr.eval s))
  | [], _, _ => rfl | [va], _, _ => by cases va <;> rfl
  | va1 :: va2 :: rest, n, en => by
      cases va1 with
      | stat a => cases a <;> first | rfl | exact onlySignalBind_renderSigAttrs s pre (va2 :: rest) n en
      | bind f => dsimp only [renderSigAttrs, List.map, VAttr.eval]; cases f s <;> first | rfl | exact onlySignalBind_renderSigAttrs s pre (va2 :: rest) n en
      | dynVal _ _ | dynOn _ _ => rfl

mutual
  @[simp] theorem View.canonical_renderSig :
      ∀ (v : View σ msg) (s : σ) (pre : String) (n en : Nat), Html.canonical (View.renderSig v s pre n en).1 = Html.canonical (View.render v s)
    | .element tag attrs kids, s, pre, n, en => by
        show mkCanonicalElem tag (renderSigAttrs s pre attrs n en).1 (Html.canonicalList (View.renderSigList kids s pre _ _).1) = _
        unfold mkCanonicalElem; rw [onlySignalBind_renderSigAttrs, renderSigAttrs_canonical, View.canonicalList_renderSigList kids s pre]; rfl
    | .ifElse cond y no, s, pre, n, en => by
        dsimp only [View.renderSig, View.render]; cases cond s
        · exact View.canonical_renderSig no s pre _ _
        · exact View.canonical_renderSig y s pre n en
    | .text _, _, _, _, _ | .dyn _, _, _, _, _ | .keyedList .., _, _, _, _ | .static _, _, _, _, _ | .dynNode _, _, _, _, _ | .memo _, _, _, _, _ => rfl
  @[simp] theorem View.canonicalList_renderSigList :
      ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n en : Nat), Html.canonicalList (View.renderSigList ks s pre n en).1 = Html.canonicalList (View.renderEach ks s)
    | [], _, _, _, _ => rfl
    | k :: ks, s, pre, n, en => by show Html.canonical _ :: Html.canonicalList _ = _; rw [View.canonical_renderSig k s pre n en, View.canonicalList_renderSigList ks s pre]; rfl
end

@[simp] theorem View.render_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) : (View.showIf cond child).render s = (if cond s then child.render s else .text "") := rfl
@[simp] theorem View.collectDyn_showIf (cond : σ → Bool) (child : View σ msg) : (View.showIf cond child).collectDyn = child.collectDyn := List.append_nil _
@[simp] theorem View.renderSig_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) (pre : String) (n en : Nat) :
    (View.showIf cond child).renderSig s pre n en = (if cond s then child.renderSig s pre n en else (.text "", n + child.collectDyn.length, en + child.collectDynOn.length)) := by
  dsimp only [View.showIf, View.renderSig, View.collectDyn, View.collectDynOn, List.length]; cases cond s <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]

def View.isDyn : View σ msg → Bool | .dyn _ => true | _ => false

namespace V

instance : Coe (Attr msg) (VAttr σ msg) := ⟨.stat⟩
instance : Coe Style (VAttr σ msg) := ⟨fun s => .stat (.cls s.className)⟩
instance : Coe String (View σ msg) := ⟨.text⟩
instance : Coe String (List (View σ msg)) := ⟨([.text ·])⟩

def text (s : String) : View σ msg := .text s
def dyn (get : σ → String) : View σ msg := .dyn get
def bindAttr (get : σ → Attr msg) : VAttr σ msg := .bind get
def dynAttr (name : String) (get : σ → String) : VAttr σ msg := .dynVal name get
def onClick' (get : σ → msg) : VAttr σ msg := .dynOn "click" get
def onInput' (get : σ → String → msg) : VAttr σ msg := .bind (fun s => .onValue "input" (get s))
def onCheck' (get : σ → Bool → msg) : VAttr σ msg := .bind (fun s => .onValue "change" (fun str => get s (str == "true")))
def static (h : Html msg) : View σ msg := .static h
def el (tag : String) (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := .element tag attrs kids
def showIf (cond : σ → Bool) (child : View σ msg) : View σ msg := .showIf cond child
def ifElse (cond : σ → Bool) (yes no : View σ msg) : View σ msg := .ifElse cond yes no
def dynNode (get : σ → Html msg) : View σ msg := .dynNode get
def memo {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) : View σ msg := .memo (SoundMemo.ofLawful f proj)
@[simp] theorem render_memo {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) (s : σ) : (memo f proj : View σ msg).render s = f (proj s) := rfl

private def isDirectStaticAttr : Attr msg → Bool | .cls _ | .attr _ _ | .flag _ _ | .key _ => true | _ => false
private def vattrDirectKey? : VAttr α msg → Option String
  | .stat (.cls _) => some "class" | .stat (.attr k _) | .stat (.flag k _) | .dynVal k _ => some k | _ => none

private def directTmplAttrsOk (attrs : List (VAttr α msg)) : Bool :=
  let allKeys := attrs.filterMap vattrDirectKey?
  let evNames := attrs.filterMap fun | .dynOn e _ => some e | _ => none
  attrs.all (fun | .stat a => isDirectStaticAttr a | .dynVal k _ => k != "checked" | .dynOn _ _ => true | .bind _ => false) &&
  (attrs.filterMap fun | .dynVal k _ => some k | _ => none).all (fun k => (allKeys.filter (· == k)).length == 1) &&
  evNames.all (fun e => (evNames.filter (· == e)).length == 1)

mutual
  private def isDirectTmplBody : View α msg → Bool
    | .text s => !s.isEmpty
    | .static h => Html.fold (!·.isEmpty) (fun _ attrs _ r => attrs.all isDirectStaticAttr && r) true (· && ·) h
    | .element _ attrs kids => directTmplAttrsOk attrs && match kids with | [.dyn _] => true | _ => isDirectTmplList kids
    | _ => false
  private def isDirectTmplList : List (View α msg) → Bool | [] => true | k :: ks => isDirectTmplBody k && isDirectTmplList ks
end

def isDirectTmpl : View α msg → Bool
  | v@(.element ..) => (!(View.collectDyn v).isEmpty || !(View.collectDynOn v).isEmpty) && isDirectTmplBody v | _ => false

private structure TmplAcc (α msg : Type) where
  slotPaths : Array (Array UInt32) := #[]
  slotAttrs : Array String := #[]
  slotFns   : Array (α → String) := #[]
  evPaths   : Array (Array UInt32) := #[]
  evNames   : Array String := #[]
  evFns     : Array (α → msg) := #[]

private def pushSlot (p : Array UInt32) (a : String) (g : α → String) : StateM (TmplAcc α msg) Unit :=
  modify fun s => { s with slotPaths := s.slotPaths.push p, slotAttrs := s.slotAttrs.push a, slotFns := s.slotFns.push g }

private def compileTmplAttrs (path : Array UInt32) : List (VAttr α msg) → StateM (TmplAcc α msg) (List (Attr msg))
  | [] => pure [] | .stat a :: r => return a :: (← compileTmplAttrs path r) | .bind _ :: r => compileTmplAttrs path r
  | .dynVal k g :: r => do pushSlot path k g; return .attr k "" :: (← compileTmplAttrs path r)
  | .dynOn e g :: r => do modify fun s => { s with evPaths := s.evPaths.push path, evNames := s.evNames.push e, evFns := s.evFns.push g }; compileTmplAttrs path r

mutual
  private def compileTmplNode (path : Array UInt32) : View α msg → StateM (TmplAcc α msg) (Html msg)
    | .text s => pure (.text s) | .static h => pure h
    | .dyn g => do pushSlot path "" g; pure (.text "")
    | .element tag attrs kids => return .element tag (← compileTmplAttrs path attrs) (← compileTmplKids path 0 kids)
    | _ => pure (.text "")
  private def compileTmplKids (p : Array UInt32) (i : Nat) : List (View α msg) → StateM (TmplAcc α msg) (List (Html msg))
    | [] => pure [] | k :: ks => return (← compileTmplNode (p.push (UInt32.ofNat i)) k) :: (← compileTmplKids p (i + 1) ks)
end

private def mkRowTmpl {α σ msg : Type} (child : View α msg) (items : σ → Array α) (key : α → String) : RowTmpl σ msg :=
  let (proto, c) := (compileTmplNode #[] child).run {}
  let evalRow : α → Array String := match c.slotFns.toList with
    | [] => fun _ => #[] | [f0] => fun a => #[f0 a] | [f0, f1] => fun a => #[f0 a, f1 a]
    | [f0, f1, f2] => fun a => #[f0 a, f1 a, f2 a] | [f0, f1, f2, f3] => fun a => #[f0 a, f1 a, f2 a, f3 a]
    | _ => fun a => c.slotFns.map (· a)
  { proto, slotPaths := c.slotPaths, slotAttrs := c.slotAttrs, evPaths := c.evPaths, evNames := c.evNames
    rowKey := fun s i => ((items s)[i]?.map key).getD "", rowVals := fun s i => ((items s)[i]?.map evalRow).getD #[]
    rowEvAt := fun s i j => do return (← c.evFns[j]?) (← (items s)[i]?) }

@[reducible] def forEachBlocked {α msg : Type} (tag : String) (child : View α msg) : Bool :=
  child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) || (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))

def forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg) := []) (sigPrefix : String := "") : View σ msg :=
  let renderPlain (s : σ) := ((items s).map fun a => withKey (key a) (child.render a)).toList
  if forEachBlocked tag child then .dynNode fun s => .element tag (attrs.map (VAttr.eval s)) (renderPlain s)
  else
    let rawKeys (s : σ) := (items s).map key; let marks (s : σ) := (items s).map Qed.refMark
    if isDirectTmpl child then
      .keyedList tag attrs rawKeys marks (fun _ _ _ => #[]) (fun _ _ _ => #[]) renderPlain (some (mkRowTmpl child items key))
    else
      let mkSigRow {β : Type} (sep : String) (ps : List (α → β)) (s : σ) (uKeys : Array String) (i : Nat) : Array (String × β) :=
        match (items s)[i]? with
        | some a => let sk := sigPrefix ++ uKeys.getD i (key a); (ps.mapIdx fun j p => (s!"{sk}{sep}{j}", p a)).toArray | none => #[]
      .keyedList tag attrs rawKeys marks (mkSigRow "#" (View.collectDyn child)) (mkSigRow "#e" (View.collectDynOn child))
        (fun s => let ks := disambiguateKeys (rawKeys s); (items s).toList.zipIdx.map fun (a, i) =>
          let uk := ks.getD i (key a); withKey uk (View.renderSig child a (sigPrefix ++ uk) 0).1) none

@[simp] theorem render_forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String) (s : σ) :
    (forEach tag items key child attrs sigPrefix).render s =
      .element tag (attrs.map (VAttr.eval s))
        (if forEachBlocked tag child || isDirectTmpl child
         then ((items s).map fun a => withKey (key a) (child.render a)).toList
         else let ks := disambiguateKeys ((items s).map key); (items s).toList.zipIdx.map fun (a, i) =>
           let uk := ks.getD i (key a); withKey uk (View.renderSig child a (sigPrefix ++ uk) 0).1) := by
  dsimp only [forEach]; cases forEachBlocked tag child
  · cases isDirectTmpl child <;> rfl
  · rfl

private theorem zipIdx_map_fst {α β : Type _} (g : α → β) : ∀ (xs : List α) (k : Nat), (xs.zipIdx k).map (fun p => g p.1) = xs.map g
  | [], _ => rfl | _ :: xs, k => by simp [List.zipIdx, zipIdx_map_fst g xs (k + 1)]

@[simp] theorem canonical_render_forEach {α : Type} (tag : String) (items : σ → Array α)
    (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String) (s : σ) :
    Html.canonical ((forEach tag items key child attrs sigPrefix).render s) =
      mkCanonicalElem tag (attrs.map (VAttr.eval s)) ((items s).toList.map fun a => Html.canonical (child.render a)) := by
  rw [render_forEach, Html.canonical_element]; cases (forEachBlocked tag child || isDirectTmpl child)
  · simp; rw [zipIdx_map_fst (fun a => (child.render a).canonical) (items s).toList 0]
  · simp [Array.toList_map]

mutual
  def View.sigSafeIn {σ msg : Type} (ctx : HtmlCtx) : View σ msg → Bool
    | .text _ | .static _ => true | .dyn _ => ctx.mode == .normal || ctx.mode == .svg
    | .element tag _ kids => match stepHtmlCtx ctx tag with | some childCtx => View.sigSafeListIn childCtx kids | none => false
    | _ => false
  def View.sigSafeListIn {σ msg : Type} (ctx : HtmlCtx) : List (View σ msg) → Bool | [] => true | k :: ks => View.sigSafeIn ctx k && View.sigSafeListIn ctx ks
end

private theorem stepHtmlCtx_span_of_mode {ctx : HtmlCtx} (hm : (ctx.mode == .normal || ctx.mode == .svg) = true) :
    stepHtmlCtx ctx "span" = some ctx := by
  rcases ctx with ⟨m, inP, inter, inForm⟩; cases m <;> simp at hm <;> cases inP <;> cases inter <;> cases inForm <;> rfl

private theorem validTextIn_of_mode {ctx : HtmlCtx} (hm : (ctx.mode == .normal || ctx.mode == .svg) = true) (s : String) :
    validTextIn ctx s = true := by rcases ctx with ⟨m, _, _, _⟩; cases m <;> simp at hm <;> rfl

mutual
  theorem View.validIn_renderSig_of_sigSafe {σ msg : Type} (ctx : HtmlCtx) :
      ∀ (v : View σ msg) (s : σ) (pre : String) (n en : Nat),
        View.sigSafeIn ctx v = true → Html.validIn ctx (View.render v s) = true → Html.validIn ctx (View.renderSig v s pre n en).1 = true
    | .text _, _, _, _, _, _, hvalid | .static _, _, _, _, _, _, hvalid => hvalid
    | .dyn _, _, _, _, _, hsafe, _ => by
        show (true && (!isVoidTag "span" || false) && true && match stepHtmlCtx ctx "span" with | some c => validTextIn c _ && true | none => false) = true
        rw [stepHtmlCtx_span_of_mode hsafe]; dsimp only; rw [validTextIn_of_mode hsafe, show isVoidTag "span" = false from rfl]; rfl
    | .element tag attrs kids, s, pre, n, en, hsafe, hvalid => by
        simp only [View.sigSafeIn] at hsafe
        simp only [View.render, View.renderSig, Html.validIn, View.renderEach_isEmpty, Attr.validList_renderSigAttrs, Attr.hasLocalCell_renderSigAttrs, View.renderSigList_isEmpty] at hvalid ⊢
        cases hstep : stepHtmlCtx ctx tag with
        | none => simp [hstep] at hsafe
        | some childCtx => simp only [hstep, Bool.and_eq_true] at hsafe hvalid ⊢; exact ⟨hvalid.1, View.validListIn_renderSigList_of_sigSafe childCtx kids s pre _ _ hsafe hvalid.2⟩
    | .ifElse .., _, _, _, _, hsafe, _ | .keyedList .., _, _, _, _, hsafe, _ | .dynNode .., _, _, _, _, hsafe, _ | .memo .., _, _, _, _, hsafe, _ => Bool.noConfusion hsafe
  theorem View.validListIn_renderSigList_of_sigSafe {σ msg : Type} (ctx : HtmlCtx) :
      ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n en : Nat),
        View.sigSafeListIn ctx ks = true → Html.validListIn ctx (View.renderEach ks s) = true → Html.validListIn ctx (View.renderSigList ks s pre n en).1 = true
    | [], _, _, _, _, _, _ => rfl
    | k :: ks, s, pre, n, en, hsafe, hvalid =>
        let hs := Bool.and_eq_true_iff.1 hsafe; let hv := Bool.and_eq_true_iff.1 hvalid
        Bool.and_eq_true_iff.2 ⟨View.validIn_renderSig_of_sigSafe ctx k s pre n en hs.1 hv.1, View.validListIn_renderSigList_of_sigSafe ctx ks s pre _ _ hs.2 hv.2⟩
end

theorem validIn_render_forEach {α σ msg : Type} (ctx childCtx : HtmlCtx) (tag : String)
    (items : σ → Array α) (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String) (s : σ)
    (hstep : stepHtmlCtx ctx tag = some childCtx) (hvoid : isVoidTag tag = false)
    (hcell : (!Attr.hasLocalCell (attrs.map (VAttr.eval s))) = true) (hattrs : Attr.validList (attrs.map (VAttr.eval s)) = true)
    (hchild : ∀ a, Html.validIn childCtx (child.render a) = true) (hsig : (forEachBlocked tag child || View.sigSafeIn childCtx child) = true) :
    Html.validIn ctx ((forEach tag items key child attrs sigPrefix).render s) = true := by
  rw [render_forEach]; simp only [Html.validIn, hstep, hattrs, hvoid, hcell, Bool.not_false, Bool.true_or, Bool.true_and]
  cases hc : (forEachBlocked tag child || isDirectTmpl child)
  · have hsafe : View.sigSafeIn childCtx child = true := by simpa [(Bool.or_eq_false_iff.1 hc).1] using hsig
    simp only [Bool.false_eq_true, ↓reduceIte, Html.validListIn_map, List.all_eq_true]
    rintro ⟨a, _⟩ _; dsimp only; rw [Html.validIn_withKey]; exact View.validIn_renderSig_of_sigSafe childCtx child a _ 0 0 hsafe (hchild a)
  · simp only [↓reduceIte, Html.validListIn_toList_map, List.all_eq_true]; intro a _; rw [Html.validIn_withKey]; exact hchild a

end V

class ForEachItems (c : Type) (α : outParam Type) where
  toList  : c → List α
  toArray : c → Array α

@[reducible] instance : ForEachItems (Array α) α := ⟨Array.toList, id⟩
@[reducible] instance : ForEachItems (List α) α := ⟨id, List.toArray⟩

@[simp] theorem ForEachItems.toList_array {α : Type} (a : Array α) : ForEachItems.toList a = a.toList := rfl
@[simp] theorem ForEachItems.toList_list {α : Type} (l : List α) : ForEachItems.toList l = l := rfl
@[simp] theorem ForEachItems.toArray_array_toList {α : Type} (a : Array α) : (ForEachItems.toArray a).toList = a.toList := rfl
@[simp] theorem ForEachItems.toArray_list_toList {α : Type} (l : List α) : (ForEachItems.toArray l).toList = l := by simp [ForEachItems.toArray]

@[reducible] def mapList {α β : Type} (l : List α) (f : α → β) : List β := l.map f
@[simp] theorem mapList_eq {α β : Type} (l : List α) (f : α → β) : mapList l f = l.map f := rfl

end Qed
