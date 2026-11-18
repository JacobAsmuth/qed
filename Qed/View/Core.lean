import Qed.Render
import Qed.Diff
import Qed.Style
import Qed.Notation
import Std.Data.HashSet

namespace Qed

def pickFreshKeyLoop (k : String) (seen : Std.HashSet String) (maxLen : Nat) : Nat → Nat → String
  | _, 0 => k ++ String.ofList (List.replicate (maxLen + 1) '~')
  | i, fuel + 1 =>
      let cand := k ++ "~~dup" ++ Nat.repr i
      if !seen.contains cand then cand
      else pickFreshKeyLoop k seen maxLen (i + 1) fuel

def pickFreshKey (k : String) (seen : Std.HashSet String) (maxLen : Nat) : String :=
  if !seen.contains k then k
  else pickFreshKeyLoop k seen maxLen 1 seen.size

theorem pickFreshKeyLoop_not_mem (k : String) (seen : Std.HashSet String) (maxLen : Nat)
    (hmax : ∀ s, s ∈ seen → s.length ≤ maxLen) :
    ∀ (i fuel : Nat), pickFreshKeyLoop k seen maxLen i fuel ∉ seen
  | _, 0 => by
      intro hmem
      have hle := hmax _ hmem
      have hlen : (k ++ String.ofList (List.replicate (maxLen + 1) '~')).length = k.length + (maxLen + 1) := by
        simp [String.length_append]
      unfold pickFreshKeyLoop at hle
      omega
  | i, fuel + 1 => by
      simp only [pickFreshKeyLoop]
      split
      · rename_i hc
        intro hmem
        have hc' : seen.contains (k ++ "~~dup" ++ Nat.repr i) = true := Std.HashSet.contains_iff_mem.2 hmem
        simp [hc'] at hc
      · exact pickFreshKeyLoop_not_mem k seen maxLen hmax (i + 1) fuel

theorem pickFreshKey_not_mem (k : String) (seen : Std.HashSet String) (maxLen : Nat)
    (hmax : ∀ s, s ∈ seen → s.length ≤ maxLen) :
    pickFreshKey k seen maxLen ∉ seen := by
  unfold pickFreshKey
  split
  · rename_i hc
    intro hmem
    have hc' : seen.contains k = true := Std.HashSet.contains_iff_mem.2 hmem
    simp [hc'] at hc
  · exact pickFreshKeyLoop_not_mem k seen maxLen hmax 1 seen.size

def disambiguateKeysTR (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String) :
    List String → Array String
  | [] => acc
  | k :: rest =>
      let k' := pickFreshKey k seen maxLen
      disambiguateKeysTR (seen.insert k') (Nat.max maxLen k'.length) (acc.push k') rest

def disambiguateKeys (keys : Array String) : Array String :=
  disambiguateKeysTR ∅ 0 #[] keys.toList

private theorem nodup_append_singleton {α : Type} {xs : List α} {a : α}
    (hnd : xs.Nodup) (ha : a ∉ xs) : (xs ++ [a]).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons x rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨hx, hrest⟩
      refine List.nodup_cons.2 ⟨?_, ih hrest (fun h => ha (List.mem_cons_of_mem x h))⟩
      intro hm
      rcases List.mem_append.1 hm with h1 | h2
      · exact hx h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact ha (List.mem_cons_self ..)

private theorem disambiguateKeysTR_nodup (ks : List String) :
    ∀ (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      (∀ s, s ∈ seen → s.length ≤ maxLen) →
      (∀ s, s ∈ acc.toList → s ∈ seen) →
      acc.toList.Nodup →
      (disambiguateKeysTR seen maxLen acc ks).toList.Nodup := by
  induction ks with
  | nil => intros _ _ _ _ _ hnd; exact hnd
  | cons k rest ih =>
      intro seen maxLen acc hmax hsub hnd
      let k' := pickFreshKey k seen maxLen
      have hnot : k' ∉ seen := pickFreshKey_not_mem k seen maxLen hmax
      have hnotAcc : k' ∉ acc.toList := fun hm => hnot (hsub k' hm)
      refine ih (seen.insert k') (Nat.max maxLen k'.length) (acc.push k') ?_ ?_ ?_
      · intro s hs
        rcases Std.HashSet.mem_insert.1 hs with heq | hmem
        · have : k' = s := eq_of_beq heq
          subst this
          exact Nat.le_max_right _ _
        · exact Nat.le_trans (hmax s hmem) (Nat.le_max_left _ _)
      · intro s hs
        rw [Array.toList_push, List.mem_append] at hs
        rcases hs with h1 | h2
        · exact Std.HashSet.mem_insert.2 (.inr (hsub s h1))
        · simp only [List.mem_singleton] at h2
          subst h2
          exact Std.HashSet.mem_insert.2 (.inl (beq_self_eq_true _))
      · rw [Array.toList_push]
        exact nodup_append_singleton hnd hnotAcc

theorem disambiguateKeys_nodup (keys : Array String) :
    (disambiguateKeys keys).toList.Nodup := by
  refine disambiguateKeysTR_nodup keys.toList ∅ 0 #[] ?_ ?_ List.Pairwise.nil
  · intro s hs; simp at hs
  · intro s hs; simp at hs

private theorem disambiguateKeysTR_size (ks : List String) :
    ∀ (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      (disambiguateKeysTR seen maxLen acc ks).size = acc.size + ks.length := by
  induction ks with
  | nil => intros; simp [disambiguateKeysTR]
  | cons k rest ih =>
      intros seen maxLen acc
      simp only [disambiguateKeysTR, ih, Array.size_push, List.length_cons]
      omega

theorem disambiguateKeys_size (keys : Array String) :
    (disambiguateKeys keys).size = keys.size := by
  simpa [disambiguateKeys] using disambiguateKeysTR_size keys.toList ∅ 0 #[]

private theorem disambiguateKeysTR_of_nodup (ks : List String) :
    ∀ (seen : Std.HashSet String) (maxLen : Nat) (acc : Array String),
      (∀ k ∈ ks, k ∉ seen) →
      ks.Nodup →
      (disambiguateKeysTR seen maxLen acc ks).toList = acc.toList ++ ks := by
  induction ks with
  | nil => intros; simp [disambiguateKeysTR]
  | cons k rest ih =>
      intro seen maxLen acc hdisj hnd
      rcases List.nodup_cons.1 hnd with ⟨hkrest, hndRest⟩
      have hkseen : k ∉ seen := hdisj k (List.mem_cons_self ..)
      have hkc : seen.contains k = false := by
        cases hc : seen.contains k with
        | false => rfl
        | true  => exact False.elim (hkseen (Std.HashSet.contains_iff_mem.1 hc))
      have hpk : pickFreshKey k seen maxLen = k := by simp [pickFreshKey, hkc]
      simp only [disambiguateKeysTR, hpk]
      rw [ih (seen.insert k) (Nat.max maxLen k.length) (acc.push k)]
      · simp [Array.toList_push]
      · intro x hx hm
        rcases Std.HashSet.mem_insert.1 hm with heq | hmem
        · have : k = x := eq_of_beq heq
          subst this
          exact hkrest hx
        · exact hdisj x (List.mem_cons_of_mem k hx) hmem
      · exact hndRest

theorem disambiguateKeys_of_nodup {keys : Array String} (hnd : keys.toList.Nodup) :
    disambiguateKeys keys = keys := by
  apply Array.ext'
  simpa [disambiguateKeys] using
    disambiguateKeysTR_of_nodup keys.toList ∅ 0 #[] (fun _ _ hm => by simp at hm) hnd

/-- A congruence-verified memoized HTML fragment: whenever two projections produce
    equal string keys, they are kernel-proven to produce identical `Html` trees. -/
structure SoundMemo (σ : Type) (msg : Type) where
  keyOf : σ → String
  eval  : σ → Html msg
  sound : ∀ s s', keyOf s = keyOf s' → eval s = eval s'

def SoundMemo.mapScope (f : σ' → σ) (sm : SoundMemo σ msg) : SoundMemo σ' msg where
  keyOf s' := sm.keyOf (f s')
  eval  s' := sm.eval (f s')
  sound s₁ s₂ h := sm.sound (f s₁) (f s₂) h

def SoundMemo.ofLawful {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) :
    SoundMemo σ msg where
  keyOf s := LawfulKey.toKey (proj s)
  eval  s := f (proj s)
  sound s₁ s₂ h := by rw [LawfulKey.injective (proj s₁) (proj s₂) h]

inductive VAttr (σ : Type) (msg : Type) where
  | stat (a : Attr msg)
  | bind (get : σ → Attr msg)
  | dynVal (attr : String) (get : σ → String)

inductive View (σ : Type) (msg : Type) where
  | text (s : String)
  | dyn (get : σ → String)
  | element (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg))
  | ifElse (cond : σ → Bool) (yes no : View σ msg)
  | keyedList (tag : String) (attrs : List (VAttr σ msg))
      (keys : σ → Array String)
      (marks : σ → Array USize) (rowSig : σ → Nat → Array (String × String))
      (rowsHtml : σ → List (Html msg))
  | static (html : Html msg)
  | dynNode (get : σ → Html msg)
  | memo (sm : SoundMemo σ msg)

def View.showIf (cond : σ → Bool) (child : View σ msg) : View σ msg :=
  .ifElse cond child (.text "")

-- Transpiler emits `$.refMark` (ids ≥ 1); pure `0` never matches a real stamp so native evaluation never skips.
@[noinline] def refMark {α : Type} (a : α) : USize := (fun _ => 0) a

def VAttr.eval (s : σ) : VAttr σ msg → Attr msg
  | .stat a          => a
  | .bind f          => f s
  | .dynVal attr get => .attr attr (get s)

@[simp] theorem VAttr.eval_stat (s : σ) (a : Attr msg) : VAttr.eval s (.stat a) = a := rfl
@[simp] theorem VAttr.eval_bind (s : σ) (f : σ → Attr msg) : VAttr.eval s (.bind f) = f s := rfl
@[simp] theorem VAttr.eval_dynVal {msg : Type} (s : σ) (k : String) (g : σ → String) :
    (VAttr.dynVal k g : VAttr σ msg).eval s = .attr k (g s) := rfl

def VAttr.mapScope (f : σ' → σ) : VAttr σ msg → VAttr σ' msg
  | .stat a          => .stat a
  | .bind g          => .bind (fun s' => g (f s'))
  | .dynVal attr get => .dynVal attr (fun s' => get (f s'))

@[simp] theorem VAttr.eval_mapScope (f : σ' → σ) (s' : σ') (va : VAttr σ msg) :
    VAttr.eval s' (va.mapScope f) = VAttr.eval (f s') va := by
  cases va <;> rfl

def withKey (k : String) : Html msg → Html msg
  | .element t as cs => .element t (.key k :: as) cs
  | h                => h

@[simp] theorem Html.validIn_withKey (ctx : HtmlCtx) (k : String) (h : Html msg) :
    Html.validIn ctx (withKey k h) = Html.validIn ctx h := by
  cases h <;> simp [withKey, Html.validIn, Attr.valid]

@[simp] theorem Html.canonical_withKey (k : String) (h : Html msg) :
    Html.canonical (withKey k h) = Html.canonical h := by
  cases h with
  | text _ => rfl
  | element t as cs => simp [withKey, Html.canonical, mkCanonicalElem, Attr.canonical]

mutual
  def View.mapScope (f : σ' → σ) : View σ msg → View σ' msg
    | .text s                          => .text s
    | .dyn get                         => .dyn (fun s' => get (f s'))
    | .element t as ks                 => .element t (as.map (VAttr.mapScope f)) (View.mapScopeEach f ks)
    | .ifElse cond y n                 => .ifElse (fun s' => cond (f s')) (y.mapScope f) (n.mapScope f)
    | .keyedList t as keys marks rs rh =>
        .keyedList t (as.map (VAttr.mapScope f)) (fun s' => keys (f s'))
          (fun s' => marks (f s')) (fun s' => rs (f s')) (fun s' => rh (f s'))
    | .static h                        => .static h
    | .dynNode get                     => .dynNode (fun s' => get (f s'))
    | .memo sm                         => .memo (sm.mapScope f)
  def View.mapScopeEach (f : σ' → σ) : List (View σ msg) → List (View σ' msg)
    | []      => []
    | k :: ks => k.mapScope f :: View.mapScopeEach f ks
end

mutual
  def View.render : View σ msg → σ → Html msg
    | .text s,          _ => .text s
    | .dyn get,         s => .text (get s)
    | .element t as ks, s => .element t (as.map (VAttr.eval s)) (View.renderEach ks s)
    | .ifElse cond y n, s => if cond s then View.render y s else View.render n s
    | .keyedList tag as _ _ _ rowsHtml, s => .element tag (as.map (VAttr.eval s)) (rowsHtml s)
    | .static h,        _ => h
    | .dynNode get,     s => get s
    | .memo sm,         s => sm.eval s
  def View.renderEach : List (View σ msg) → σ → List (Html msg)
    | [],      _ => []
    | k :: ks, s => View.render k s :: View.renderEach ks s
end

@[simp] theorem View.renderEach_isEmpty :
    ∀ (ks : List (View σ msg)) (s : σ), (View.renderEach ks s).isEmpty = ks.isEmpty
  | [], _ => rfl
  | _ :: _, _ => rfl

mutual
  @[simp] theorem View.render_mapScope (f : σ' → σ) (v : View σ msg) (s' : σ') :
      View.render (v.mapScope f) s' = View.render v (f s') := by
    cases v with
    | text _ => rfl
    | dyn _ => rfl
    | element t as ks =>
        simp [View.mapScope, View.render, List.map_map, Function.comp_def, View.renderEach_mapScopeEach f ks s']
    | ifElse cond y n =>
        simp [View.mapScope, View.render, View.render_mapScope f y s', View.render_mapScope f n s']
    | keyedList t as _ _ _ rh =>
        simp [View.mapScope, View.render, List.map_map, Function.comp_def]
    | static _ => rfl
    | dynNode _ => rfl
    | memo _ => rfl

  @[simp] theorem View.renderEach_mapScopeEach (f : σ' → σ) (vs : List (View σ msg)) (s' : σ') :
      View.renderEach (View.mapScopeEach f vs) s' = View.renderEach vs (f s') := by
    cases vs with
    | nil => rfl
    | cons k ks =>
        simp [View.mapScopeEach, View.renderEach, View.render_mapScope f k s', View.renderEach_mapScopeEach f ks s']
end

instance : CoeFun (View σ msg) (fun _ => σ → Html msg) := ⟨View.render⟩

@[simp] theorem View.renderEach_map {α σ msg : Type} (xs : List α) (f : α → View σ msg) (s : σ) :
    View.renderEach (xs.map f) s = xs.map (fun a => View.render (f a) s) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [View.renderEach, ih]

@[simp] theorem View.render_ite {σ msg : Type} (c : Prop) [Decidable c] (a b : View σ msg) (s : σ) :
    View.render (if c then a else b) s = (if c then View.render a s else View.render b s) := by
  by_cases hc : c <;> simp [hc]

theorem View.validIn_render_ifElse {σ msg : Type} (ctx : HtmlCtx) (cond : σ → Bool)
    (y n : View σ msg) (s : σ)
    (hy : cond s = true → Html.validIn ctx (View.render y s) = true)
    (hn : cond s = false → Html.validIn ctx (View.render n s) = true) :
    Html.validIn ctx (View.render (.ifElse cond y n) s) = true := by
  simp only [View.render]
  cases hc : cond s
  · exact hn hc
  · exact hy hc

theorem View.validIn_render_showIf {σ msg : Type} (ctx : HtmlCtx) (cond : σ → Bool)
    (child : View σ msg) (s : σ)
    (hy : cond s = true → Html.validIn ctx (View.render child s) = true) :
    Html.validIn ctx (View.render (.showIf cond child) s) = true :=
  View.validIn_render_ifElse ctx cond child (.text "") s hy (fun _ => by
    simp [View.render, Html.validIn, validTextIn_empty])

theorem View.validIn_render_element_intro {σ msg : Type} (ctx childCtx : HtmlCtx)
    (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg)) (s : σ)
    (hstep : stepHtmlCtx ctx tag = some childCtx)
    (hattrs : Attr.validList (attrs.map (VAttr.eval s)) = true)
    (hvoid : (!isVoidTag tag || kids.isEmpty) = true)
    (hcell : (!Attr.hasLocalCell (attrs.map (VAttr.eval s)) || kids.isEmpty) = true)
    (hkids : Html.validListIn childCtx (View.renderEach kids s) = true) :
    Html.validIn ctx (View.render (.element tag attrs kids) s) = true := by
  refine Html.validIn_element_intro ctx childCtx tag (attrs.map (VAttr.eval s))
    (View.renderEach kids s) hstep hattrs ?_ ?_ hkids
  · simpa [View.renderEach_isEmpty] using hvoid
  · simpa [View.renderEach_isEmpty] using hcell

theorem View.validListIn_renderEach_nil {σ msg : Type} (ctx : HtmlCtx) (s : σ) :
    Html.validListIn ctx (View.renderEach ([] : List (View σ msg)) s) = true := rfl

theorem View.validListIn_renderEach_cons {σ msg : Type} (ctx : HtmlCtx)
    (k : View σ msg) (ks : List (View σ msg)) (s : σ)
    (hk : Html.validIn ctx (View.render k s) = true)
    (hks : Html.validListIn ctx (View.renderEach ks s) = true) :
    Html.validListIn ctx (View.renderEach (k :: ks) s) = true :=
  Html.validListIn_cons_intro ctx (View.render k s) (View.renderEach ks s) hk hks

theorem View.validListIn_renderEach_map_intro {α σ msg : Type} (ctx : HtmlCtx)
    (xs : List α) (f : α → View σ msg) (s : σ)
    (hf : ∀ a, Html.validIn ctx (View.render (f a) s) = true) :
    Html.validListIn ctx (View.renderEach (xs.map f) s) = true := by
  rw [View.renderEach_map]
  exact Html.validListIn_map_intro ctx xs (fun a => View.render (f a) s) hf

theorem View.validIn_render_mapScope_intro {σ' σ msg : Type} (ctx : HtmlCtx)
    (f : σ' → σ) (v : View σ msg) (s' : σ')
    (hv : Html.validIn ctx (View.render v (f s')) = true) :
    Html.validIn ctx (View.render (v.mapScope f) s') = true := by
  rw [View.render_mapScope]; exact hv

theorem View.validListIn_renderEach_mapScopeEach_intro {σ' σ msg : Type} (ctx : HtmlCtx)
    (f : σ' → σ) (vs : List (View σ msg)) (s' : σ')
    (hvs : Html.validListIn ctx (View.renderEach vs (f s')) = true) :
    Html.validListIn ctx (View.renderEach (View.mapScopeEach f vs) s') = true := by
  rw [View.renderEach_mapScopeEach]; exact hvs

theorem View.validIn_render_ite_intro {σ msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a b : View σ msg) (s : σ)
    (ht : c → Html.validIn ctx (View.render a s) = true)
    (hf : ¬ c → Html.validIn ctx (View.render b s) = true) :
    Html.validIn ctx (View.render (if c then a else b) s) = true := by
  rw [View.render_ite]
  exact Html.validIn_ite_intro ctx c (View.render a s) (View.render b s) ht hf

theorem Html.validIn_withKey_intro {msg : Type} (ctx : HtmlCtx) (k : String) (h : Html msg)
    (hh : Html.validIn ctx h = true) :
    Html.validIn ctx (withKey k h) = true := by
  rw [Html.validIn_withKey]; exact hh

theorem Html.validIn_map_intro {α β : Type} (ctx : HtmlCtx) (f : α → β) (h : Html α)
    (hh : Html.validIn ctx h = true) :
    Html.validIn ctx (h.map f) = true := by
  rw [Html.validIn_map]; exact hh

theorem Html.validListIn_mapChildren_intro {α β : Type} (ctx : HtmlCtx) (f : α → β)
    (cs : List (Html α)) (hcs : Html.validListIn ctx cs = true) :
    Html.validListIn ctx (Html.mapChildren f cs) = true := by
  rw [Html.validListIn_mapChildren]; exact hcs

theorem Html.validIn_prefixSignals_intro {msg : Type} (ctx : HtmlCtx) (pfx : String) (h : Html msg)
    (hh : Html.validIn ctx h = true) :
    Html.validIn ctx (h.prefixSignals pfx) = true := by
  rw [Html.validIn_prefixSignals]; exact hh

theorem Html.validListIn_prefixSignalsList_intro {msg : Type} (ctx : HtmlCtx) (pfx : String)
    (cs : List (Html msg)) (hcs : Html.validListIn ctx cs = true) :
    Html.validListIn ctx (Html.prefixSignalsList pfx cs) = true := by
  rw [Html.validListIn_prefixSignalsList]; exact hcs

def View.ofHtml (f : σ → Html msg) : View σ msg := .dynNode f

mutual
  def applyValues : View σ msg → σ → Html msg → Html msg
    | .dyn get,              s', _                      => .text (get s')
    | .element _ attrs kids, s', .element tag _ oldKids =>
        .element tag (attrs.map (VAttr.eval s')) (applyValuesList kids s' oldKids)
    | .ifElse cond y n,      s', old                    => if cond s' then applyValues y s' old else applyValues n s' old
    | _,                     _,  old                    => old
  def applyValuesList : List (View σ msg) → σ → List (Html msg) → List (Html msg)
    | k :: ks, s', o :: os => applyValues k s' o :: applyValuesList ks s' os
    | _,       _,  _       => []
end

mutual
  def stable : View σ msg → σ → σ → Bool
    | .element _ _ kids, s, s' => stableList kids s s'
    | .ifElse cond y n,  s, s' => (cond s == cond s') && (if cond s then stable y s s' else stable n s s')
    | .keyedList ..,     _, _  => false
    | .dynNode _,        _, _  => false
    | .memo sm,          s, s' => sm.keyOf s == sm.keyOf s'
    | _,                 _, _  => true
  def stableList : List (View σ msg) → σ → σ → Bool
    | k :: ks, s, s' => stable k s s' && stableList ks s s'
    | [],      _, _  => true
end

mutual
  theorem applyValues_render (t : View σ msg) (s s' : σ) :
      stable t s s' = true → applyValues t s' (View.render t s) = View.render t s' := by
    intro h
    cases t with
    | element tag attrs kids =>
        simp only [View.render, applyValues]
        rw [applyValuesList_render kids s s' (by simpa [stable] using h)]
    | ifElse cond y no =>
        cases h₁ : cond s <;> cases h₂ : cond s' <;>
          simp_all [stable, View.render, applyValues, applyValues_render y s s', applyValues_render no s s']
    | memo sm =>
        simp only [stable, beq_iff_eq] at h
        simpa [View.render, applyValues] using sm.sound s s' h
    | _ => simp_all [stable, View.render, applyValues]
  theorem applyValuesList_render (ts : List (View σ msg)) (s s' : σ) :
      stableList ts s s' = true → applyValuesList ts s' (View.renderEach ts s) = View.renderEach ts s' := by
    cases ts with
    | nil => simp [View.renderEach, applyValuesList]
    | cons k ks =>
        simp only [stableList, Bool.and_eq_true, View.renderEach, applyValuesList]
        rintro ⟨hk, hks⟩
        rw [applyValues_render k s s' hk, applyValuesList_render ks s s' hks]
end

def patch (t : View σ msg) (s s' : σ) (old : Html msg) : Html msg :=
  if stable t s s' then applyValues t s' old else applyPatch (diff old (View.render t s')) old

theorem patch_render (t : View σ msg) (s s' : σ) :
    patch t s s' (View.render t s) = View.render t s' := by
  simp only [patch]
  split <;> simp_all [applyValues_render, diff_apply]

def dynValGets (attrs : List (VAttr σ msg)) : List (σ → String) :=
  attrs.filterMap fun | .dynVal _ get => some get | _ => none

mutual
  def View.collectDyn : View σ msg → List (σ → String)
    | .text _               => []
    | .dyn get              => [get]
    | .element _ attrs kids => dynValGets attrs ++ View.collectDynList kids
    | .ifElse _ y no        => View.collectDyn y ++ View.collectDyn no
    | .keyedList ..         => []
    | .static _             => []
    | .dynNode _            => []
    | .memo _               => []
  def View.collectDynList : List (View σ msg) → List (σ → String)
    | []      => []
    | k :: ks => View.collectDyn k ++ View.collectDynList ks
end

def tagBlocksDirectSpan (tag : String) : Bool :=
  tag == "ul" || tag == "ol" || tag == "dl" ||
  tag == "table" || tag == "colgroup" || tag == "thead" || tag == "tbody" || tag == "tfoot" || tag == "tr"

def tagBlocksSpanSubtree (tag : String) : Bool :=
  tag == "select" || tag == "optgroup" || tag == "option" ||
  tag == "textarea" || tag == "style" || tag == "svg"

mutual
  def View.hasOpaque : View σ msg → Bool
    | .text _                 => false
    | .dyn _                  => false
    | .element tag attrs kids =>
        attrs.any (fun | .bind _ => true | _ => false) ||
        (tagBlocksDirectSpan tag && kids.any (fun | .dyn _ => true | _ => false)) ||
        (tagBlocksSpanSubtree tag && !(View.collectDynList kids).isEmpty) ||
        View.hasOpaqueList kids
    | .ifElse ..              => true
    | .keyedList ..           => true
    | .static _               => false
    | .dynNode _              => true
    | .memo _                 => true
  def View.hasOpaqueList : List (View σ msg) → Bool
    | []      => false
    | k :: ks => k.hasOpaque || View.hasOpaqueList ks
end

mutual
  def View.collectShape : View σ msg → σ → String
    | .text _,          _ => ""
    | .dyn _,           _ => ""
    | .element _ _ kids, s => View.collectShapeList kids s
    | .ifElse cond y no, s =>
        if cond s then "1" ++ View.collectShape y s else "0" ++ View.collectShape no s
    | .keyedList tag as _ _ _ rowsHtml, s =>
        "{" ++ Html.render (.element tag (as.map (VAttr.eval s)) (rowsHtml s)) ++ "}"
    | .static _,        _ => ""
    | .dynNode get,     s => "<" ++ Html.render (get s) ++ ">"
    | .memo sm,         s => "<" ++ Html.render (sm.eval s) ++ ">"
  def View.collectShapeList : List (View σ msg) → σ → String
    | [],      _ => ""
    | k :: ks, s => View.collectShape k s ++ View.collectShapeList ks s
end

def renderSigAttrs (s : σ) (pre : String) : List (VAttr σ msg) → Nat → List (Attr msg) × Nat
  | [],        n => ([], n)
  | va :: rest, n =>
      let (a, n1) := match va with
        | .dynVal attr get => (Attr.signalAttr s!"{pre}#{n}" attr (get s), n + 1)
        | other            => (VAttr.eval s other, n)
      let (as, n2) := renderSigAttrs s pre rest n1
      (a :: as, n2)

@[simp] theorem Attr.validList_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n : Nat),
      Attr.validList (renderSigAttrs s pre attrs n).1 = Attr.validList (attrs.map (VAttr.eval s))
  | [], _ => rfl
  | va :: rest, n => by
      cases va <;> simp [renderSigAttrs, VAttr.eval, Attr.valid, Attr.validList_renderSigAttrs s pre rest]

@[simp] theorem Attr.hasLocalCell_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n : Nat),
      Attr.hasLocalCell (renderSigAttrs s pre attrs n).1 = Attr.hasLocalCell (attrs.map (VAttr.eval s))
  | [], _ => rfl
  | va :: rest, n => by
      cases va <;> simp [renderSigAttrs, VAttr.eval, Attr.hasLocalCell_renderSigAttrs s pre rest]

mutual
  def View.renderSig : View σ msg → σ → String → Nat → Html msg × Nat
    | .text s,          _, _,   n => (.text s, n)
    | .dyn get,         s, pre, n => (.element "span" [.signalBind s!"{pre}#{n}"] [.text (get s)], n + 1)
    | .element tag attrs kids, s, pre, n =>
        let (attrs', n1) := renderSigAttrs s pre attrs n
        let (cs, n2) := View.renderSigList kids s pre n1
        (.element tag attrs' cs, n2)
    | .ifElse cond y no, s, pre, n =>
        -- Reserve inactive branch's signal indices so leaf names stay aligned with `collectDyn` across flips.
        if cond s then
          let (h, n1) := View.renderSig y s pre n
          (h, n1 + (View.collectDyn no).length)
        else
          let (h, n2) := View.renderSig no s pre (n + (View.collectDyn y).length)
          (h, n2)
    | .keyedList tag as _ _ _ rowsHtml, s, _, n =>
        (.element tag (as.map (VAttr.eval s)) (rowsHtml s), n)
    | .static h,        _, _,   n => (h, n)
    | .dynNode get,     s, _,   n => (get s, n)
    | .memo sm,         s, _,   n => (sm.eval s, n)
  def View.renderSigList : List (View σ msg) → σ → String → Nat → List (Html msg) × Nat
    | [],      _, _,   n => ([], n)
    | k :: ks, s, pre, n =>
        let (h,  n')  := View.renderSig k s pre n
        let (hs, n'') := View.renderSigList ks s pre n'
        (h :: hs, n'')
end

@[simp] theorem View.renderSigList_isEmpty :
    ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n : Nat),
      (View.renderSigList ks s pre n).1.isEmpty = ks.isEmpty
  | [], _, _, _ => rfl
  | _ :: _, _, _, _ => rfl

@[simp] theorem renderSigAttrs_canonical (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n : Nat),
      (renderSigAttrs s pre attrs n).1.filterMap Attr.canonical =
        (attrs.map (VAttr.eval s)).filterMap Attr.canonical
  | [], _ => rfl
  | va :: rest, n => by
      cases va with
      | stat a =>
          simp only [renderSigAttrs, List.map, VAttr.eval, List.filterMap]
          cases Attr.canonical a <;> simp [renderSigAttrs_canonical s pre rest n]
      | bind f =>
          simp only [renderSigAttrs, List.map, VAttr.eval, List.filterMap]
          cases Attr.canonical (f s) <;> simp [renderSigAttrs_canonical s pre rest n]
      | dynVal attr get =>
          simp [renderSigAttrs, VAttr.eval, Attr.canonical,
                renderSigAttrs_canonical s pre rest (n + 1)]

@[simp] theorem onlySignalBind_renderSigAttrs (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n : Nat),
      onlySignalBind (renderSigAttrs s pre attrs n).1 =
        onlySignalBind (attrs.map (VAttr.eval s))
  | [], _ => rfl
  | [va], _ => by cases va <;> simp [renderSigAttrs, VAttr.eval, onlySignalBind]
  | va1 :: va2 :: rest, n => by
      cases va1 with
      | stat a =>
          simp only [renderSigAttrs, List.map, VAttr.eval]
          cases a with
          | key _ => exact onlySignalBind_renderSigAttrs s pre (va2 :: rest) n
          | _ => rfl
      | bind f =>
          simp only [renderSigAttrs, List.map, VAttr.eval]
          generalize f s = a
          cases a with
          | key _ => exact onlySignalBind_renderSigAttrs s pre (va2 :: rest) n
          | _ => rfl
      | dynVal _ _ => rfl

mutual
  @[simp] theorem View.canonical_renderSig :
      ∀ (v : View σ msg) (s : σ) (pre : String) (n : Nat),
        Html.canonical (View.renderSig v s pre n).1 = Html.canonical (View.render v s)
    | .text _, _, _, _ => rfl
    | .dyn _, _, _, _ => rfl
    | .element tag attrs kids, s, pre, n => by
        simp only [View.renderSig, View.render, Html.canonical, mkCanonicalElem,
              renderSigAttrs_canonical, onlySignalBind_renderSigAttrs,
              View.canonicalList_renderSigList kids s pre]
    | .ifElse cond y no, s, pre, n => by
        by_cases h : cond s = true <;>
          simp [View.renderSig, View.render, h, View.canonical_renderSig]
    | .keyedList .., _, _, _ => rfl
    | .static _, _, _, _ => rfl
    | .dynNode _, _, _, _ => rfl
    | .memo _, _, _, _ => rfl

  @[simp] theorem View.canonicalList_renderSigList :
      ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n : Nat),
        Html.canonicalList (View.renderSigList ks s pre n).1 = Html.canonicalList (View.renderEach ks s)
    | [], _, _, _ => rfl
    | k :: ks, s, pre, n => by
        simp [View.renderSigList, View.renderEach,
              View.canonical_renderSig k s pre n,
              View.canonicalList_renderSigList ks s pre]
end

@[simp] theorem View.render_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) :
    (View.showIf cond child).render s = (if cond s then child.render s else .text "") := rfl

theorem View.stable_showIf_hidden (cond : σ → Bool) (child : View σ msg) (s s' : σ)
    (h : cond s = false) (h' : cond s' = false) :
    stable (View.showIf cond child) s s' = true := by
  simp [View.showIf, stable, h, h']

@[simp] theorem View.collectShape_showIf (cond : σ → Bool) (child : View σ msg) (s : σ) :
    (View.showIf cond child).collectShape s =
      (if cond s then "1" ++ child.collectShape s else "0") := by
  simp [View.showIf, View.collectShape]

@[simp] theorem View.collectDyn_showIf (cond : σ → Bool) (child : View σ msg) :
    (View.showIf cond child).collectDyn = child.collectDyn := by
  simp [View.showIf, View.collectDyn]

@[simp] theorem View.renderSig_showIf (cond : σ → Bool) (child : View σ msg)
    (s : σ) (pre : String) (n : Nat) :
    (View.showIf cond child).renderSig s pre n =
      (if cond s then child.renderSig s pre n else (.text "", n + child.collectDyn.length)) := by
  simp [View.showIf, View.renderSig, View.collectDyn]

def View.isDyn : View σ msg → Bool
  | .dyn _ => true
  | _      => false

namespace V

instance : Coe (Attr msg) (VAttr σ msg) := ⟨.stat⟩
instance : Coe Style (VAttr σ msg) := ⟨fun s => .stat (.cls s.className)⟩
instance : Coe String (View σ msg) := ⟨.text⟩
instance : Coe String (List (View σ msg)) := ⟨fun s => [.text s]⟩

def text (s : String) : View σ msg := .text s
def dyn (get : σ → String) : View σ msg := .dyn get
def bindAttr (get : σ → Attr msg) : VAttr σ msg := .bind get
def dynAttr (name : String) (get : σ → String) : VAttr σ msg := .dynVal name get
def onClick' (get : σ → msg) : VAttr σ msg := .bind (fun s => .on "click" (get s))
def onInput' (get : σ → String → msg) : VAttr σ msg := .bind (fun s => .onValue "input" (get s))
def onCheck' (get : σ → Bool → msg) : VAttr σ msg :=
  .bind (fun s => .onValue "change" (fun str => get s (str == "true")))
def static (h : Html msg) : View σ msg := .static h

def el (tag : String) (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) :
    View σ msg := .element tag attrs kids

def showIf (cond : σ → Bool) (child : View σ msg) : View σ msg := .showIf cond child
def ifElse (cond : σ → Bool) (yes no : View σ msg) : View σ msg := .ifElse cond yes no
def dynNode (get : σ → Html msg) : View σ msg := .dynNode get

def memo {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) : View σ msg :=
  .memo (SoundMemo.ofLawful f proj)

@[simp] theorem render_memo {α σ msg : Type} [LawfulKey α] (f : α → Html msg) (proj : σ → α) (s : σ) :
    (memo f proj : View σ msg).render s = f (proj s) := rfl

def forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg) := []) (sigPrefix : String := "") : View σ msg :=
  -- `hasOpaque` rows can change props/closures without changing signal leaves, so fall back to `dynNode` diff.
  let directDynBlocked :=
    (tagBlocksDirectSpan tag && child.isDyn) ||
    (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty)
  if child.hasOpaque || directDynBlocked then
    .dynNode fun s => .element tag (attrs.map (VAttr.eval s))
      (((items s).map fun a => withKey (key a) (child.render a)).toList)
  else
    let projs := View.collectDyn child
    let uKeys : σ → Array String := fun s => disambiguateKeys ((items s).map key)
    .keyedList tag attrs
      uKeys
      (fun s => (items s).map (fun a => Qed.refMark a))
      (fun s i => match (items s)[i]? with
        | some a =>
            let sk := sigPrefix ++ (uKeys s).getD i (key a)
            (projs.mapIdx fun j p => (s!"{sk}#{j}", p a)).toArray
        | none => #[])
      (fun s =>
        let ks := uKeys s
        (items s).toList.zipIdx.map fun (a, i) =>
          let uk := ks.getD i (key a)
          withKey uk (View.renderSig child a (sigPrefix ++ uk) 0).1)

@[simp] theorem render_forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String) (s : σ) :
    (forEach tag items key child attrs sigPrefix).render s =
      .element tag (attrs.map (VAttr.eval s))
        (if child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) ||
            (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))
         then ((items s).map fun a => withKey (key a) (child.render a)).toList
         else
           let ks := disambiguateKeys ((items s).map key)
           (items s).toList.zipIdx.map fun (a, i) =>
             let uk := ks.getD i (key a)
             withKey uk (View.renderSig child a (sigPrefix ++ uk) 0).1) := by
  dsimp only [forEach]
  split <;> rfl

private theorem zipIdx_map_fst {α β : Type _} (g : α → β) :
    ∀ (xs : List α) (k : Nat), (xs.zipIdx k).map (fun p => g p.1) = xs.map g
  | [], _ => rfl
  | _ :: xs, k => by simp [List.zipIdx, zipIdx_map_fst g xs (k + 1)]

@[simp] theorem canonical_render_forEach {α : Type} (tag : String) (items : σ → Array α)
    (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg))
    (sigPrefix : String) (s : σ) :
    Html.canonical ((forEach tag items key child attrs sigPrefix).render s) =
      mkCanonicalElem tag (attrs.map (VAttr.eval s))
        ((items s).toList.map fun a => Html.canonical (child.render a)) := by
  rw [render_forEach, Html.canonical_element]
  by_cases h : (child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) ||
      (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))) = true
  · simp [h, Array.toList_map]
  · have hf : (child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) ||
        (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))) = false := Bool.eq_false_iff.2 h
    simp [hf]
    rw [zipIdx_map_fst (fun a => (child.render a).canonical) (items s).toList 0]

mutual
  def View.sigSafeIn {σ msg : Type} (ctx : HtmlCtx) : View σ msg → Bool
    | .text _             => true
    | .dyn _              => ctx.mode == .normal || ctx.mode == .svg
    | .element tag _ kids =>
        match stepHtmlCtx ctx tag with
        | some childCtx => View.sigSafeListIn childCtx kids
        | none          => false
    | .static _           => true
    | _                   => false

  def View.sigSafeListIn {σ msg : Type} (ctx : HtmlCtx) : List (View σ msg) → Bool
    | []      => true
    | k :: ks => View.sigSafeIn ctx k && View.sigSafeListIn ctx ks
end

private theorem stepHtmlCtx_span_of_mode {ctx : HtmlCtx}
    (hm : (ctx.mode == .normal || ctx.mode == .svg) = true) :
    stepHtmlCtx ctx "span" = some ctx := by
  rcases ctx with ⟨mode, inP, inter, inForm⟩
  cases mode <;> simp at hm
  · simp [stepHtmlCtx, isSafeTagName, isForbiddenTag, isContextOnlyTag, closesPTag, isInteractiveTag, isHeadingTag]
  · simp [stepHtmlCtx, isSafeTagName, isForbiddenTag]

private theorem validTextIn_of_mode {ctx : HtmlCtx}
    (hm : (ctx.mode == .normal || ctx.mode == .svg) = true) (s : String) :
    validTextIn ctx s = true := by
  rcases ctx with ⟨mode, inP, inter, inForm⟩
  cases mode <;> simp at hm <;> rfl

mutual
  theorem View.validIn_renderSig_of_sigSafe {σ msg : Type} (ctx : HtmlCtx) :
      ∀ (v : View σ msg) (s : σ) (pre : String) (n : Nat),
        View.sigSafeIn ctx v = true →
        Html.validIn ctx (View.render v s) = true →
        Html.validIn ctx (View.renderSig v s pre n).1 = true
    | .text _, _, _, _, _, hvalid => hvalid
    | .dyn _, _, _, _, hsafe, _ => by
        simp only [View.sigSafeIn] at hsafe
        simp only [View.renderSig, Html.validIn, Attr.validList, Attr.valid,
                   Attr.hasLocalCell, Attr.isLocalCell, List.isEmpty, isVoidTag, voidTags]
        rw [stepHtmlCtx_span_of_mode hsafe]
        simp [Html.validListIn, Html.validIn, validTextIn_of_mode hsafe]
    | .element tag attrs kids, s, pre, n, hsafe, hvalid => by
        simp only [View.sigSafeIn] at hsafe
        simp only [View.render, Html.validIn, View.renderEach_isEmpty] at hvalid
        simp only [View.renderSig, Html.validIn, Attr.validList_renderSigAttrs,
                   Attr.hasLocalCell_renderSigAttrs, View.renderSigList_isEmpty]
        cases hstep : stepHtmlCtx ctx tag with
        | none =>
            rw [hstep] at hvalid
            simp at hvalid
        | some childCtx =>
            rw [hstep] at hsafe hvalid
            simp only [Bool.and_eq_true] at hvalid
            rcases hvalid with ⟨⟨⟨hattrs, hvoid⟩, hcell⟩, hkids⟩
            simp only [hattrs, hvoid, hcell, Bool.true_and, View.validListIn_renderSigList_of_sigSafe childCtx kids s pre _ hsafe hkids]
    | .static _, _, _, _, _, hvalid => hvalid
    | .ifElse .., _, _, _, hsafe, _ => by simp [View.sigSafeIn] at hsafe
    | .keyedList .., _, _, _, hsafe, _ => by simp [View.sigSafeIn] at hsafe
    | .dynNode .., _, _, _, hsafe, _ => by simp [View.sigSafeIn] at hsafe
    | .memo .., _, _, _, hsafe, _ => by simp [View.sigSafeIn] at hsafe

  theorem View.validListIn_renderSigList_of_sigSafe {σ msg : Type} (ctx : HtmlCtx) :
      ∀ (ks : List (View σ msg)) (s : σ) (pre : String) (n : Nat),
        View.sigSafeListIn ctx ks = true →
        Html.validListIn ctx (View.renderEach ks s) = true →
        Html.validListIn ctx (View.renderSigList ks s pre n).1 = true
    | [], _, _, _, _, _ => rfl
    | k :: ks, s, pre, n, hsafe, hvalid => by
        simp only [View.sigSafeListIn, Bool.and_eq_true] at hsafe
        simp only [View.renderEach, Html.validListIn, Bool.and_eq_true] at hvalid
        simp only [View.renderSigList, Html.validListIn, Bool.and_eq_true]
        exact ⟨View.validIn_renderSig_of_sigSafe ctx k s pre n hsafe.1 hvalid.1,
               View.validListIn_renderSigList_of_sigSafe ctx ks s pre _ hsafe.2 hvalid.2⟩
end

theorem validIn_render_forEach {α σ msg : Type} (ctx childCtx : HtmlCtx) (tag : String)
    (items : σ → Array α) (key : α → String) (child : View α msg)
    (attrs : List (VAttr σ msg)) (sigPrefix : String) (s : σ)
    (hstep : stepHtmlCtx ctx tag = some childCtx)
    (hvoid : isVoidTag tag = false)
    (hcell : (!Attr.hasLocalCell (attrs.map (VAttr.eval s))) = true)
    (hattrs : Attr.validList (attrs.map (VAttr.eval s)) = true)
    (hchild : ∀ a, Html.validIn childCtx (child.render a) = true)
    (hsig : (child.hasOpaque ||
              ((tagBlocksDirectSpan tag && child.isDyn) ||
               (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty)) ||
              View.sigSafeIn childCtx child) = true) :
    Html.validIn ctx ((forEach tag items key child attrs sigPrefix).render s) = true := by
  rw [render_forEach]
  simp only [Html.validIn, hstep, hattrs, hvoid, hcell, Bool.not_false, Bool.true_or, Bool.true_and]
  by_cases hc : (child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) ||
      (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))) = true
  · simp only [hc, ↓reduceIte, Html.validListIn_toList_map, List.all_eq_true]
    intro a _
    rw [Html.validIn_withKey]
    exact hchild a
  · have hfalse : (child.hasOpaque || ((tagBlocksDirectSpan tag && child.isDyn) ||
        (tagBlocksSpanSubtree tag && !(View.collectDyn child).isEmpty))) = false := Bool.eq_false_iff.2 hc
    have hsafe : View.sigSafeIn childCtx child = true := by
      simpa [hfalse] using hsig
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte, Html.validListIn_map, List.all_eq_true]
    rintro ⟨a, i⟩ _
    dsimp only
    rw [Html.validIn_withKey]
    exact View.validIn_renderSig_of_sigSafe childCtx child a _ 0 hsafe (hchild a)

end V

class ForEachItems (c : Type) (α : outParam Type) where
  toList  : c → List α
  toArray : c → Array α

@[reducible] instance : ForEachItems (Array α) α where
  toList  := Array.toList
  toArray := id

@[reducible] instance : ForEachItems (List α) α where
  toList  := id
  toArray := List.toArray

@[simp] theorem ForEachItems.toList_array {α : Type} (a : Array α) :
    ForEachItems.toList a = a.toList := rfl

@[simp] theorem ForEachItems.toList_list {α : Type} (l : List α) :
    ForEachItems.toList l = l := rfl

@[simp] theorem ForEachItems.toArray_array_toList {α : Type} (a : Array α) :
    (ForEachItems.toArray a).toList = a.toList := rfl

@[simp] theorem ForEachItems.toArray_list_toList {α : Type} (l : List α) :
    (ForEachItems.toArray l).toList = l := by simp [ForEachItems.toArray]

@[reducible] def mapList {α β : Type} (l : List α) (f : α → β) : List β := l.map f

@[simp] theorem mapList_eq {α β : Type} (l : List α) (f : α → β) :
    mapList l f = l.map f := rfl

end Qed
