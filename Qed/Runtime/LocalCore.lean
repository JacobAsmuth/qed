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

private def dedupeStep (acc : Array LocalDef) (d : LocalDef) : Array LocalDef :=
  if acc.any (·.id == d.id) then acc else acc.push d

def LocalDef.dedupe (ds : List LocalDef) : List LocalDef :=
  (ds.foldl dedupeStep #[]).toList

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
    (ha : a.valid = true) : (a.localProps props).valid = true :=
  Attr.valid_localProps a props ▸ ha

theorem Attr.valid_localInit_intro {msg S : Type} [ToJson S] (a : Attr msg) (init : S)
    (ha : a.valid = true) : (a.localInit init).valid = true :=
  Attr.valid_localInit a init ▸ ha

@[simp] theorem Attr.valid_localMount (component key : String) :
    (localMount component key : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_localMountWith {O msg : Type} [FromJson O]
    (component key : String) (onOut : O → Option msg) :
    (localMountWith component key onOut).valid = true := rfl

/-! ## `LocalDef` View Validity, Deduplication & `LawfulJson` Round-Trip Theorems -/

theorem LocalDef.valid_viewForProps (ldef : LocalDef) (props s : String) :
    Html.valid (ldef.viewForProps props s) = true := by
  rcases ldef with ⟨_, _, _, vp, hv, hvp⟩
  cases vp <;> simp [LocalDef.viewForProps, hv, hvp]

private theorem foldl_dedupe_inv (P : Array LocalDef → Prop) (xs : List LocalDef)
    (acc : Array LocalDef) (h0 : P acc) (hstep : ∀ a d, d ∈ xs → P a → P (dedupeStep a d)) :
    P (xs.foldl dedupeStep acc) := by
  induction xs generalizing acc with
  | nil => exact h0
  | cons y ys ih =>
      exact ih _ (hstep acc y (List.mem_cons_self ..) h0)
        fun a d hd => hstep a d (List.mem_cons_of_mem y hd)

theorem LocalDef.dedupe_mem {d : LocalDef} {ds : List LocalDef} (hm : d ∈ LocalDef.dedupe ds) :
    d ∈ ds :=
  foldl_dedupe_inv (fun a => ∀ x ∈ a.toList, x ∈ ds) ds #[] (fun _ h => nomatch h)
    (fun a y hy ha x hx => by
      unfold dedupeStep at hx
      split at hx
      · exact ha x hx
      · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        exact hx.elim (ha x) (· ▸ hy))
    d hm

theorem LocalDef.dedupe_ids_nodup (ds : List LocalDef) :
    ((LocalDef.dedupe ds).map (·.id)).Nodup :=
  foldl_dedupe_inv (fun a => (a.toList.map (·.id)).Nodup) ds #[] List.Pairwise.nil
    fun a y _ hnd => by
      unfold dedupeStep
      by_cases hany : a.any (·.id == y.id) = true
      · simp [hany, hnd]
      · have hnotMem : y.id ∉ a.toList.map (·.id) := by
          intro hm
          rcases List.mem_map.1 hm with ⟨d, hd, hid⟩
          obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hd
          have hi' : i < a.size := by simpa using hi
          have hgetA : a[i]'hi' = d := hget
          exact hany (Array.any_iff_exists.2 ⟨i, hi', Nat.zero_le _, hi', by simp [hgetA, hid]⟩)
        simp only [Bool.eq_false_iff.2 hany, Bool.false_eq_true, ↓reduceIte,
          Array.toList_push, List.map_append, List.map_singleton]
        exact List.nodup_append.2 ⟨hnd, List.pairwise_singleton _ _,
          fun x hx _ hz hxz => hnotMem (List.mem_singleton.1 hz ▸ hxz ▸ hx)⟩

theorem LocalDef.decode_toJson_eq {S : Type} [LawfulJson S] (s init : S)
    (hdepth : LawfulJson.depthBound S ≤ 64) :
    ((Json.parse (Json.render (toJson s))).bind FromJson.fromJson).toOption.getD init = s := by
  rw [LawfulJson.parse_render_toJson s hdepth]; rfl

end Qed
