import Qed.Json.Lawful
import Qed.Proto.Lawful

namespace Qed

/-! ## Verified Typed Dictionary (`Qed.Dict K V` / `{K: V}`)
    Pure, total, insertion-order-preserving dictionary with:
    - Total `d[k] : Option V` indexing (never panics)
    - `k in d` / `k not in d` membership via `QedMem` / `QedMemProp`
    - Kernel-verified `@[simp]` laws for `get`, `contains`, `set`, `remove`, `size`
    - `LawfulJson` (real JSON objects for `{String: V}`, pair arrays for non-`String` keys)
    - `LawfulProto` (full binary Protobuf round-trip proof for RPCs & WebSockets)
    - Direct JS compilation through `qedjs` with zero extra runtime externs -/

structure Dict (K V : Type) where
  entriesList : List (K × V)
deriving Inhabited, DecidableEq, Repr

namespace Dict

def empty {K V : Type} : Dict K V := ⟨[]⟩

private def getAux {K V : Type} [BEq K] (k : K) : List (K × V) → Option V
  | []             => none
  | (k', v) :: xs  => if k' == k then some v else getAux k xs

def get {K V : Type} [BEq K] (d : Dict K V) (k : K) : Option V :=
  getAux k d.entriesList

def contains {K V : Type} [BEq K] (d : Dict K V) (k : K) : Bool :=
  (d.get k).isSome

private def setAux {K V : Type} [BEq K] (k : K) (v : V) : List (K × V) → List (K × V)
  | []              => [(k, v)]
  | (k', v') :: xs  => if k' == k then (k, v) :: xs else (k', v') :: setAux k v xs

def set {K V : Type} [BEq K] (d : Dict K V) (k : K) (v : V) : Dict K V :=
  ⟨setAux k v d.entriesList⟩

private def removeAux {K V : Type} [BEq K] (k : K) : List (K × V) → List (K × V)
  | []              => []
  | (k', v') :: xs  => if k' == k then removeAux k xs else (k', v') :: removeAux k xs

def remove {K V : Type} [BEq K] (d : Dict K V) (k : K) : Dict K V :=
  ⟨removeAux k d.entriesList⟩

def ofList {K V : Type} [BEq K] (ps : List (K × V)) : Dict K V :=
  ps.foldl (fun acc (k, v) => acc.set k v) empty

def size {K V : Type} (d : Dict K V) : Nat :=
  d.entriesList.length

def isEmpty {K V : Type} (d : Dict K V) : Bool :=
  d.entriesList.isEmpty

def keys {K V : Type} (d : Dict K V) : Array K :=
  (d.entriesList.map Prod.fst).toArray

def values {K V : Type} (d : Dict K V) : Array V :=
  (d.entriesList.map Prod.snd).toArray

def entries {K V : Type} (d : Dict K V) : Array (K × V) :=
  d.entriesList.toArray

def mapValues {K V W : Type} (d : Dict K V) (f : V → W) : Dict K W :=
  ⟨d.entriesList.map fun (k, v) => (k, f v)⟩

def filter {K V : Type} (d : Dict K V) (p : K → V → Bool) : Dict K V :=
  ⟨d.entriesList.filter fun (k, v) => p k v⟩

/-! ### Standard Instances (`EmptyCollection`, `GetElem`, `QedMem`, `ForIn`, `ToString`) -/

instance {K V : Type} : EmptyCollection (Dict K V) := ⟨Dict.empty⟩

instance {K V : Type} [BEq K] : GetElem (Dict K V) K (Option V) (fun _ _ => True) where
  getElem d k _ := d.get k

instance {m : Type u → Type v} [Monad m] {K V : Type} : ForIn m (Dict K V) (K × V) where
  forIn d init f := forIn d.entriesList init f

instance {K V : Type} [ToString K] [ToString V] : ToString (Dict K V) where
  toString d :=
    let parts := d.entriesList.map fun (k, v) => s!"{k}: {v}"
    "{" ++ String.intercalate ", " parts ++ "}"

/-! ### Kernel-Verified Proof Laws (`@[simp]`) -/

@[simp] theorem emptyCollection_eq_empty {K V : Type} :
    ({} : Dict K V) = Dict.empty := rfl

@[simp] theorem getElem_eq_get {K V : Type} [BEq K] (d : Dict K V) (k : K) :
    d[k] = d.get k := rfl

@[simp] theorem get_empty {K V : Type} [BEq K] (k : K) :
    (Dict.empty : Dict K V).get k = none := rfl

@[simp] theorem contains_empty {K V : Type} [BEq K] (k : K) :
    (Dict.empty : Dict K V).contains k = false := rfl

@[simp] theorem size_empty {K V : Type} :
    (Dict.empty : Dict K V).size = 0 := rfl

@[simp] theorem isEmpty_empty {K V : Type} :
    (Dict.empty : Dict K V).isEmpty = true := rfl

private theorem getAux_setAux {K V : Type} [BEq K] [LawfulBEq K] (k k' : K) (v : V) :
    ∀ xs : List (K × V), getAux k' (setAux k v xs) = if k == k' then some v else getAux k' xs
  | [] => by simp only [setAux, getAux]
  | (k0, _) :: xs => by
      simp only [setAux]
      by_cases h0 : k0 = k <;> by_cases h1 : k0 = k'
      · subst h0; subst h1; simp [getAux]
      · subst h0; simp [getAux, beq_false_of_ne h1]
      · subst h1; simp [getAux, beq_false_of_ne h0, beq_false_of_ne (Ne.symm h0)]
      · simp [getAux, beq_false_of_ne h0, beq_false_of_ne h1, getAux_setAux k k' v xs]

@[simp] theorem get_set {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) (v : V) :
    (d.set k v).get k' = if k == k' then some v else d.get k' :=
  getAux_setAux k k' v d.entriesList

@[simp] theorem get_set_self {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) (v : V) :
    (d.set k v).get k = some v := by
  simp

theorem get_set_ne {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) {k k' : K} (h : k ≠ k') (v : V) :
    (d.set k v).get k' = d.get k' := by
  simp [beq_false_of_ne h]

@[simp] theorem contains_set {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) (v : V) :
    (d.set k v).contains k' = (k == k' || d.contains k') := by
  unfold contains
  rw [get_set]
  cases h : (k == k') <;> simp

@[simp] theorem contains_set_self {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) (v : V) :
    (d.set k v).contains k = true := by
  simp

private theorem getAux_removeAux {K V : Type} [BEq K] [LawfulBEq K] (k k' : K) :
    ∀ xs : List (K × V), getAux k' (removeAux k xs) = if k == k' then none else getAux k' xs
  | [] => by simp [removeAux, getAux]
  | (k0, _) :: xs => by
      simp only [removeAux]
      by_cases h0 : k0 = k <;> by_cases h1 : k0 = k'
      · subst h0; subst h1; simp [getAux_removeAux k0 k0 xs]
      · subst h0; simp [getAux, beq_false_of_ne h1, getAux_removeAux k0 k' xs]
      · subst h1; simp [getAux, beq_false_of_ne h0, beq_false_of_ne (Ne.symm h0)]
      · simp [getAux, beq_false_of_ne h0, beq_false_of_ne h1, getAux_removeAux k k' xs]

@[simp] theorem get_remove {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) :
    (d.remove k).get k' = if k == k' then none else d.get k' :=
  getAux_removeAux k k' d.entriesList

@[simp] theorem get_remove_self {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) :
    (d.remove k).get k = none := by
  simp

theorem get_remove_ne {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) {k k' : K} (h : k ≠ k') :
    (d.remove k).get k' = d.get k' := by
  simp [beq_false_of_ne h]

@[simp] theorem contains_remove {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k k' : K) :
    (d.remove k).contains k' = (!(k == k') && d.contains k') := by
  unfold contains
  rw [get_remove]
  cases h : (k == k') <;> simp

@[simp] theorem contains_remove_self {K V : Type} [BEq K] [LawfulBEq K] (d : Dict K V) (k : K) :
    (d.remove k).contains k = false := by
  simp

private theorem length_setAux {K V : Type} [BEq K] (k : K) (v : V) :
    ∀ xs : List (K × V), (setAux k v xs).length = if (getAux k xs).isSome then xs.length else xs.length + 1
  | [] => by simp [setAux, getAux]
  | (k0, v0) :: xs => by
      simp only [setAux, getAux]
      by_cases h : (k0 == k) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, List.length_cons, length_setAux k v xs]
        cases (getAux k xs).isSome <;> rfl

@[simp] theorem size_set {K V : Type} [BEq K] (d : Dict K V) (k : K) (v : V) :
    (d.set k v).size = if d.contains k then d.size else d.size + 1 :=
  length_setAux k v d.entriesList

theorem size_set_of_contains {K V : Type} [BEq K] (d : Dict K V) (k : K) (v : V)
    (h : d.contains k = true) : (d.set k v).size = d.size := by
  simp [h]

theorem size_set_of_not_contains {K V : Type} [BEq K] (d : Dict K V) (k : K) (v : V)
    (h : d.contains k = false) : (d.set k v).size = d.size + 1 := by
  simp [h]

theorem size_set_le {K V : Type} [BEq K] (d : Dict K V) (k : K) (v : V) :
    (d.set k v).size ≤ d.size + 1 := by
  rw [size_set]
  cases d.contains k <;> simp

private theorem length_removeAux_le {K V : Type} [BEq K] (k : K) :
    ∀ xs : List (K × V), (removeAux k xs).length ≤ xs.length
  | [] => Nat.le_refl 0
  | (k0, _) :: xs => by
      have ih := length_removeAux_le k xs
      simp only [removeAux]; split <;> simp <;> omega

@[simp] theorem size_remove_le {K V : Type} [BEq K] (d : Dict K V) (k : K) :
    (d.remove k).size ≤ d.size :=
  length_removeAux_le k d.entriesList

@[simp] theorem isEmpty_iff_size {K V : Type} (d : Dict K V) :
    d.isEmpty = decide (d.size = 0) := by
  cases d with
  | mk xs => cases xs <;> rfl

/-! ### Verified JSON Codecs (`LawfulJson` & `NonNullJson`) -/

/-- `{String: V}` serializes as a standard JSON object `{"k1": v1, ...}`. -/
instance (priority := high) {V : Type} [ToJson V] : ToJson (Dict String V) where
  toJson d := .obj (d.entriesList.map fun (p : String × V) => (p.1, toJson p.2))

instance (priority := high) {V : Type} [FromJson V] : FromJson (Dict String V) where
  fromJson
    | .obj fs =>
        (fs.mapM (m := Except String) fun (p : String × Json) =>
          (fromJson p.2 : Except String V).map (p.1, ·)).map Dict.mk
    | _ => .error "expected JSON object for dictionary"

instance (priority := high) {V : Type} [LawfulJson V] : LawfulJson (Dict String V) where
  depthBound := 1 + LawfulJson.depthBound V
  depth_toJson d := Nat.add_le_add_left (Json.maxObj_le_iff.2 fun p hp => by
    rcases List.mem_map.1 hp with ⟨q, _, rfl⟩; exact LawfulJson.depth_toJson q.2) 1
  fromJson_toJson := fun ⟨ps⟩ => by
    change ((ps.map fun (p : String × V) => (p.1, toJson p.2)).mapM (m := Except String)
      (fun (p : String × Json) => (fromJson p.2 : Except String V).map (p.1, ·))).map Dict.mk = .ok ⟨ps⟩
    rw [list_mapM_map_ok _ _ fun ⟨_, v⟩ => by simp [Except.map]]
    rfl

instance (priority := high) {V : Type} [ToJson V] : NonNullJson (Dict String V) := ⟨nofun⟩

-- Non-`String`-keyed dictionaries `{K: V}` serialize as JSON arrays of `[k, v]` pairs.
qed_equiv_codec% jsonLow [K, V] (Dict K V, Dict.entriesList, Dict.mk, fun ⟨_⟩ => rfl)

/-! ### Verified Binary Protobuf Codecs (`LawfulProto`) -/

qed_equiv_codec% proto [K, V] (Dict K V, Dict.entriesList, Dict.mk, fun ⟨_⟩ => rfl)

end Dict
end Qed
