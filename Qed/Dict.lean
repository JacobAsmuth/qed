import Qed.Json.Lawful
import Qed.Proto.Lawful

namespace Qed

structure Dict (K V : Type) where
  entriesList : List (K × V)
deriving Inhabited, DecidableEq, Repr

namespace Dict
section Ops
variable {K V : Type}

def empty : Dict K V := ⟨[]⟩
private def getAux [BEq K] (k : K) : List (K × V) → Option V | [] => none | (k', v) :: xs => if k' == k then some v else getAux k xs
def get [BEq K] (d : Dict K V) (k : K) : Option V := getAux k d.entriesList
def contains [BEq K] (d : Dict K V) (k : K) : Bool := (d.get k).isSome
private def setAux [BEq K] (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)] | (k', v') :: xs => if k' == k then (k, v) :: xs else (k', v') :: setAux k v xs
def set [BEq K] (d : Dict K V) (k : K) (v : V) : Dict K V := ⟨setAux k v d.entriesList⟩
def remove [BEq K] (d : Dict K V) (k : K) : Dict K V := ⟨d.entriesList.filter fun p => !(p.1 == k)⟩
def ofList [BEq K] (ps : List (K × V)) : Dict K V := ps.foldl (fun acc (k, v) => acc.set k v) empty
def size (d : Dict K V) : Nat := d.entriesList.length
def isEmpty (d : Dict K V) : Bool := d.entriesList.isEmpty
def keys (d : Dict K V) : Array K := (d.entriesList.map Prod.fst).toArray
def values (d : Dict K V) : Array V := (d.entriesList.map Prod.snd).toArray
def entries (d : Dict K V) : Array (K × V) := d.entriesList.toArray
def mapValues {W : Type} (d : Dict K V) (f : V → W) : Dict K W := ⟨d.entriesList.map fun (k, v) => (k, f v)⟩
def filter (d : Dict K V) (p : K → V → Bool) : Dict K V := ⟨d.entriesList.filter fun (k, v) => p k v⟩

instance : EmptyCollection (Dict K V) := ⟨Dict.empty⟩
instance [BEq K] : GetElem (Dict K V) K (Option V) (fun _ _ => True) where getElem d k _ := d.get k
instance {m : Type u → Type v} [Monad m] : ForIn m (Dict K V) (K × V) where forIn d := forIn d.entriesList
instance [ToString K] [ToString V] : ToString (Dict K V) where toString d := "{" ++ String.intercalate ", " (d.entriesList.map fun (k, v) => s!"{k}: {v}") ++ "}"

@[simp] theorem emptyCollection_eq_empty : ({} : Dict K V) = Dict.empty := rfl
@[simp] theorem getElem_eq_get [BEq K] (d : Dict K V) (k : K) : d[k] = d.get k := rfl
@[simp] theorem get_empty [BEq K] (k : K) : (Dict.empty : Dict K V).get k = none := rfl
@[simp] theorem contains_empty [BEq K] (k : K) : (Dict.empty : Dict K V).contains k = false := rfl
@[simp] theorem size_empty : (Dict.empty : Dict K V).size = 0 := rfl
@[simp] theorem isEmpty_empty : (Dict.empty : Dict K V).isEmpty = true := rfl

private theorem getAux_setAux [BEq K] [LawfulBEq K] (k k' : K) (v : V) :
    ∀ xs : List (K × V), getAux k' (setAux k v xs) = if k == k' then some v else getAux k' xs
  | [] => rfl
  | (_, _) :: xs => by
      unfold setAux; split <;> rename_i h0
      · cases eq_of_beq h0; unfold getAux; cases (k == k') <;> rfl
      · unfold getAux; split <;> rename_i h1
        · cases eq_of_beq h1; rw [if_neg fun h => h0 (by rw [eq_of_beq h, beq_self_eq_true])]
        · exact getAux_setAux k k' v xs

@[simp] theorem get_set [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) (v : V) : (d.set k v).get k' = if k == k' then some v else d.get k' := getAux_setAux k k' v d.entriesList
@[simp] theorem get_set_self [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) (v : V) : (d.set k v).get k = some v := by simp
theorem get_set_ne [BEq K] [LawfulBEq K] (d : Dict K V) {k k' : K} (h : k ≠ k') (v : V) : (d.set k v).get k' = d.get k' := by simp [beq_false_of_ne h]
@[simp] theorem contains_set [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) (v : V) : (d.set k v).contains k' = (k == k' || d.contains k') := by unfold contains; rw [get_set]; cases (k == k') <;> simp
@[simp] theorem contains_set_self [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) (v : V) : (d.set k v).contains k = true := by simp

private theorem getAux_filter_ne [BEq K] [LawfulBEq K] (k k' : K) :
    ∀ xs : List (K × V), getAux k' (xs.filter fun p => !(p.1 == k)) = if k == k' then none else getAux k' xs
  | [] => by simp [getAux]
  | (k0, _) :: xs => by
      simp only [List.filter_cons]; cases h0 : (k0 == k)
      · simp only [Bool.not_false, ↓reduceIte, getAux]; split <;> rename_i h1
        · rw [if_neg fun heq => by rw [eq_of_beq h1, eq_of_beq heq, beq_self_eq_true] at h0; cases h0]
        · exact getAux_filter_ne k k' xs
      · cases eq_of_beq h0; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, getAux_filter_ne k k' xs, getAux]; cases (k == k') <;> rfl

@[simp] theorem get_remove [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) : (d.remove k).get k' = if k == k' then none else d.get k' := getAux_filter_ne k k' d.entriesList
@[simp] theorem get_remove_self [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) : (d.remove k).get k = none := by simp
theorem get_remove_ne [BEq K] [LawfulBEq K] (d : Dict K V) {k k' : K} (h : k ≠ k') : (d.remove k).get k' = d.get k' := by simp [beq_false_of_ne h]
@[simp] theorem contains_remove [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) : (d.remove k).contains k' = (!(k == k') && d.contains k') := by unfold contains; rw [get_remove]; cases (k == k') <;> simp
@[simp] theorem contains_remove_self [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) : (d.remove k).contains k = false := by simp

private theorem length_setAux [BEq K] (k : K) (v : V) : ∀ xs : List (K × V), (setAux k v xs).length = if (getAux k xs).isSome then xs.length else xs.length + 1
  | [] => rfl
  | (k0, _) :: xs => by
      simp only [setAux, getAux]; by_cases h : (k0 == k) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, List.length_cons, length_setAux k v xs]; cases (getAux k xs).isSome <;> rfl

@[simp] theorem size_set [BEq K] (d : Dict K V) (k : K) (v : V) : (d.set k v).size = if d.contains k then d.size else d.size + 1 := length_setAux k v d.entriesList
theorem size_set_of_contains [BEq K] (d : Dict K V) (k : K) (v : V) (h : d.contains k = true) : (d.set k v).size = d.size := by simp [h]
theorem size_set_of_not_contains [BEq K] (d : Dict K V) (k : K) (v : V) (h : d.contains k = false) : (d.set k v).size = d.size + 1 := by simp [h]
theorem size_set_le [BEq K] (d : Dict K V) (k : K) (v : V) : (d.set k v).size ≤ d.size + 1 := by rw [size_set]; cases d.contains k <;> simp
@[simp] theorem size_remove_le [BEq K] (d : Dict K V) (k : K) : (d.remove k).size ≤ d.size := List.length_filter_le _ d.entriesList
@[simp] theorem isEmpty_iff_size (d : Dict K V) : d.isEmpty = decide (d.size = 0) := by cases d with | mk xs => cases xs <;> rfl
end Ops

instance (priority := high) {V : Type} [ToJson V] : ToJson (Dict String V) := ⟨fun d => .obj (d.entriesList.map fun p => (p.1, toJson p.2))⟩
instance (priority := high) {V : Type} [FromJson V] : FromJson (Dict String V) := ⟨fun
  | .obj fs => (fs.mapM (m := Except String) fun p => (fromJson p.2 : Except String V).map (p.1, ·)).map Dict.mk
  | _ => .error "expected JSON object for dictionary"⟩
instance (priority := high) {V : Type} [LawfulJson V] : LawfulJson (Dict String V) where
  depthBound := 1 + LawfulJson.depthBound V
  depth_toJson d := Nat.add_le_add_left (Json.maxObj_le_iff.2 fun _ hp => by rcases List.mem_map.1 hp with ⟨q, _, rfl⟩; exact LawfulJson.depth_toJson q.2) 1
  fromJson_toJson := fun ⟨ps⟩ => by
    change ((ps.map fun (p : String × V) => (p.1, toJson p.2)).mapM (m := Except String) (fun (p : String × Json) => (fromJson p.2 : Except String V).map (p.1, ·))).map Dict.mk = .ok ⟨ps⟩
    rw [list_mapM_map_ok _ _ fun ⟨_, v⟩ => by simp [Except.map]]; rfl
instance (priority := high) {V : Type} [ToJson V] : NonNullJson (Dict String V) := ⟨nofun⟩

qed_equiv_codec% jsonLow [K, V] (Dict K V, Dict.entriesList, Dict.mk, fun ⟨_⟩ => rfl)
qed_equiv_codec% proto   [K, V] (Dict K V, Dict.entriesList, Dict.mk, fun ⟨_⟩ => rfl)

end Dict
end Qed
