import Qed.Html
import Qed.Json

namespace Qed

structure LocalMsg where
  run : String → String × Option String

structure LocalDef where
  id         : String
  init       : String
  view       : String → Html LocalMsg
  viewProps  : Option (String → String → Html LocalMsg) := none
  valid_view : (∀ s, Html.valid (view s) = true) ∧
               match viewProps with
               | none   => True
               | some f => ∀ p s, Html.valid (f p s) = true

def LocalDef.viewForProps (ldef : LocalDef) (props : String) : String → Html LocalMsg :=
  (ldef.viewProps.map (· props)).getD ldef.view

def LocalDef.dedupe (ds : List LocalDef) : List LocalDef :=
  (ds.foldl (fun (acc : Array LocalDef) d =>
    if acc.any (·.id == d.id) then acc else acc.push d) #[]).toList

def Attr.localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) : Attr msg :=
  match a with
  | .localCell k c i _ b => .localCell k c i (Json.render (toJson props)) b
  | x => x

def localMount (component key : String) : Attr msg :=
  .localCell key component none "" (fun _ => none)

def localMountWith {O msg : Type} [FromJson O] (component key : String)
    (onOut : O → Option msg) : Attr msg :=
  .localCell key component none "" fun s =>
    (((Json.parse s).bind FromJson.fromJson : Except String O)).toOption.bind onOut

def Attr.localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : Attr msg :=
  match a with
  | .localCell k comp _ p bubble => .localCell k comp (some (Json.render (ToJson.toJson init))) p bubble
  | x => x

@[simp] theorem Attr.localProps_localCell {msg P : Type} [ToJson P]
    (k c : String) (i : Option String) (p0 : String) (b : String → Option msg) (props : P) :
    (Attr.localCell k c i p0 b).localProps props = .localCell k c i (Json.render (toJson props)) b := rfl

@[simp] theorem Attr.localInit_localCell {msg S : Type} [ToJson S]
    (k c : String) (i0 : Option String) (p : String) (b : String → Option msg) (init : S) :
    (Attr.localCell k c i0 p b).localInit init = .localCell k c (some (Json.render (ToJson.toJson init))) p b := rfl

@[simp] theorem Attr.valid_localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) :
    (a.localProps props).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.valid_localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) :
    (a.localInit init).valid = a.valid := by
  cases a <;> rfl

theorem Attr.valid_localProps_intro {msg P : Type} [ToJson P] (a : Attr msg) (props : P)
    (ha : a.valid = true) : (a.localProps props).valid = true := by
  rw [Attr.valid_localProps]; exact ha

theorem Attr.valid_localInit_intro {msg S : Type} [ToJson S] (a : Attr msg) (init : S)
    (ha : a.valid = true) : (a.localInit init).valid = true := by
  rw [Attr.valid_localInit]; exact ha

@[simp] theorem Attr.valid_localMount (component key : String) :
    (localMount component key : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_localMountWith {O msg : Type} [FromJson O]
    (component key : String) (onOut : O → Option msg) :
    (localMountWith component key onOut).valid = true := rfl

/-! ## `LocalDef` View Validity, Deduplication & `LawfulJson` Round-Trip Theorems -/

theorem LocalDef.valid_viewForProps (ldef : LocalDef) (props s : String) :
    Html.valid (ldef.viewForProps props s) = true := by
  unfold LocalDef.viewForProps
  have ⟨hv, hvp⟩ := ldef.valid_view
  cases h : ldef.viewProps with
  | none => simpa [h] using hv s
  | some f =>
      simp only [h] at hvp
      simpa using hvp props s

theorem LocalDef.dedupe_mem {d : LocalDef} {ds : List LocalDef} (hm : d ∈ LocalDef.dedupe ds) :
    d ∈ ds := by
  unfold LocalDef.dedupe at hm
  have hgen : ∀ (xs : List LocalDef) (acc : Array LocalDef),
      (∀ x ∈ acc.toList, x ∈ ds) →
      (∀ x ∈ xs, x ∈ ds) →
      ∀ x ∈ (xs.foldl (fun (acc : Array LocalDef) d =>
        if acc.any (·.id == d.id) then acc else acc.push d) acc).toList, x ∈ ds := by
    intro xs
    induction xs with
    | nil => intro acc hacc _ x hx; exact hacc x hx
    | cons y ys ih =>
        intro acc hacc hys x hx
        apply ih _ _ (fun z hz => hys z (List.mem_cons_of_mem y hz)) x hx
        intro z hz
        dsimp only at hz
        split at hz
        · exact hacc z hz
        · rw [Array.toList_push, List.mem_append] at hz
          rcases hz with h1 | h2
          · exact hacc z h1
          · simp only [List.mem_singleton] at h2
            subst h2
            exact hys z (List.mem_cons_self ..)
  exact hgen ds #[] (fun _ h => nomatch h) (fun _ h => h) d hm

theorem LocalDef.dedupe_ids_nodup (ds : List LocalDef) :
    ((LocalDef.dedupe ds).map (·.id)).Nodup := by
  unfold LocalDef.dedupe
  have hgen : ∀ (xs : List LocalDef) (acc : Array LocalDef),
      (acc.toList.map (·.id)).Nodup →
      ((xs.foldl (fun (acc : Array LocalDef) d =>
        if acc.any (·.id == d.id) then acc else acc.push d) acc).toList.map (·.id)).Nodup := by
    intro xs
    induction xs with
    | nil => intro acc hnd; exact hnd
    | cons y ys ih =>
        intro acc hnd
        apply ih
        dsimp only
        by_cases hany : acc.any (·.id == y.id) = true
        · simp [hany, hnd]
        · have hanyF : acc.any (·.id == y.id) = false := Bool.eq_false_iff.2 hany
          simp only [hanyF, Bool.false_eq_true, ↓reduceIte, Array.toList_push, List.map_append,
            List.map_singleton]
          have hnotMem : y.id ∉ acc.toList.map (·.id) := by
            intro hm
            rcases List.mem_map.1 hm with ⟨d, hd, hid⟩
            obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hd
            have hidxA : idx < acc.size := by rw [← Array.length_toList]; exact hidx
            have hanyT : acc.any (·.id == y.id) = true :=
              Array.any_iff_exists.2 ⟨idx, hidxA, Nat.zero_le _, hidxA, by
                have hgetA : acc[idx]'hidxA = d := hget
                simp [hgetA, hid]⟩
            simp [hanyT] at hanyF
          rw [List.nodup_iff_pairwise_ne] at hnd ⊢
          exact List.pairwise_append.2 ⟨hnd, List.pairwise_singleton _ _,
            fun a ha b hb => by
              simp only [List.mem_singleton] at hb
              subst hb
              intro heq; subst heq; exact hnotMem ha⟩
  exact hgen ds #[] List.Pairwise.nil

theorem LocalDef.decode_toJson_eq {S : Type} [LawfulJson S] (s init : S)
    (hdepth : LawfulJson.depthBound S ≤ 64) :
    ((Json.parse (Json.render (toJson s))).bind FromJson.fromJson).toOption.getD init = s := by
  rw [LawfulJson.parse_render_toJson s hdepth]
  rfl

end Qed
