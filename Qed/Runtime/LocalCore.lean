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
  valid_view : (∀ s, Html.valid (view s) = true) ∧ match viewProps with | none => True | some f => ∀ p s, Html.valid (f p s) = true

def LocalDef.viewForProps (ldef : LocalDef) (props : String) : String → Html LocalMsg := (ldef.viewProps.map (· props)).getD ldef.view
private def dedupeStep (acc : Array LocalDef) (d : LocalDef) : Array LocalDef := if acc.any (·.id == d.id) then acc else acc.push d
def LocalDef.dedupe (ds : List LocalDef) : List LocalDef := (ds.foldl dedupeStep #[]).toList

def Attr.localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) : Attr msg :=
  match a with | .localCell k c i _ b => .localCell k c i (Json.render (toJson props)) b | x => x
def localMount (component key : String) : Attr msg := .localCell key component none "" (fun _ => none)
def localMountWith {O msg : Type} [FromJson O] (component key : String) (onOut : O → Option msg) : Attr msg :=
  .localCell key component none "" fun s => (((Json.parse s).bind FromJson.fromJson : Except String O)).toOption.bind onOut
def Attr.localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : Attr msg :=
  match a with | .localCell k c _ p b => .localCell k c (some (Json.render (ToJson.toJson init))) p b | x => x

@[simp] theorem Attr.localProps_localCell {msg P : Type} [ToJson P] (k c : String) (i : Option String) (p0 : String) (b : String → Option msg) (props : P) :
    (Attr.localCell k c i p0 b).localProps props = .localCell k c i (Json.render (toJson props)) b := rfl
@[simp] theorem Attr.localInit_localCell {msg S : Type} [ToJson S] (k c : String) (i0 : Option String) (p : String) (b : String → Option msg) (init : S) :
    (Attr.localCell k c i0 p b).localInit init = .localCell k c (some (Json.render (ToJson.toJson init))) p b := rfl
@[simp] theorem Attr.valid_localProps {msg P : Type} [ToJson P] (a : Attr msg) (props : P) : (a.localProps props).valid = a.valid := by cases a <;> rfl
@[simp] theorem Attr.valid_localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : (a.localInit init).valid = a.valid := by cases a <;> rfl
theorem Attr.valid_localProps_intro {msg P : Type} [ToJson P] (a : Attr msg) (props : P) (ha : a.valid = true) : (a.localProps props).valid = true := Attr.valid_localProps a props ▸ ha
theorem Attr.valid_localInit_intro {msg S : Type} [ToJson S] (a : Attr msg) (init : S) (ha : a.valid = true) : (a.localInit init).valid = true := Attr.valid_localInit a init ▸ ha
@[simp] theorem Attr.valid_localMount (component key : String) : (localMount component key : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_localMountWith {O msg : Type} [FromJson O] (component key : String) (onOut : O → Option msg) : (localMountWith component key onOut).valid = true := rfl

theorem LocalDef.valid_viewForProps (ldef : LocalDef) (props s : String) : Html.valid (ldef.viewForProps props s) = true := by
  rcases ldef with ⟨_, _, _, vp, hv, hvp⟩; cases vp <;> simp [LocalDef.viewForProps, hv, hvp]

private theorem foldl_dedupe_inv (P : Array LocalDef → Prop) : ∀ (xs : List LocalDef) (acc : Array LocalDef),
    P acc → (∀ a d, d ∈ xs → P a → P (dedupeStep a d)) → P (xs.foldl dedupeStep acc)
  | [], _, h0, _ => h0 | y :: ys, acc, h0, hs => foldl_dedupe_inv P ys _ (hs acc y (.head _) h0) fun a d hd => hs a d (.tail _ hd)

theorem LocalDef.dedupe_mem {d : LocalDef} {ds : List LocalDef} (hm : d ∈ LocalDef.dedupe ds) : d ∈ ds :=
  foldl_dedupe_inv (fun a => ∀ x ∈ a.toList, x ∈ ds) ds #[] (fun _ h => nomatch h)
    (fun _ _ hy ha x hx => by
      unfold dedupeStep at hx; split at hx; exact ha x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx; exact hx.elim (ha x) (· ▸ hy)) d hm

theorem LocalDef.dedupe_ids_nodup (ds : List LocalDef) : ((LocalDef.dedupe ds).map (·.id)).Nodup :=
  foldl_dedupe_inv (fun a => (a.toList.map (·.id)).Nodup) ds #[] .nil fun a y _ hnd => by
    unfold dedupeStep; by_cases hany : a.any (·.id == y.id) = true
    · simp [hany, hnd]
    · have hnot : y.id ∉ a.toList.map (·.id) := fun hm => by
        rcases List.mem_map.1 hm with ⟨d, hd, hid⟩; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
        exact hany (Array.any_iff_exists.2 ⟨i, hi, Nat.zero_le _, hi, beq_iff_eq.2 (by simpa [Array.getElem_toList] using hid)⟩)
      simp only [Bool.eq_false_iff.2 hany, Bool.false_eq_true, ↓reduceIte, Array.toList_push, List.map_append, List.map_singleton]
      exact List.nodup_append.2 ⟨hnd, List.pairwise_singleton _ _, fun _ hx _ hz hxz => hnot (List.mem_singleton.1 hz ▸ hxz ▸ hx)⟩

theorem LocalDef.decode_toJson_eq {S : Type} [LawfulJson S] (s init : S) (hdepth : LawfulJson.depthBound S ≤ 64) :
    ((Json.parse (Json.render (toJson s))).bind FromJson.fromJson).toOption.getD init = s := by rw [LawfulJson.parse_render_toJson s hdepth]; rfl

end Qed
