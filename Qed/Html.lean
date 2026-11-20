-- Avoids `String.Slice` from Lean ≥ 4.30 `trimAscii` so JS bundles stay free of `Slice` primitives.
def String.trimmed (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

namespace Qed

@[inline] def isSafeUrlChar (c : Char) : Bool :=
  c.toNat > 0x20 && c.toNat != 0x7F

def hasSafeUrlPrefix : List Char → Bool
  | ['/']                                                           => true
  | '/' :: c :: _                                                   => c != '/' && c != '\\'
  | '#' :: _                                                        => true
  | '?' :: _                                                        => true
  | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: c :: _ => c != '/' && c != '\\'
  | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: c :: _        => c != '/' && c != '\\'
  | 'm' :: 'a' :: 'i' :: 'l' :: 't' :: 'o' :: ':' :: c :: _        => c != '/' && c != '\\'
  | 't' :: 'e' :: 'l' :: ':' :: c :: _                             => c != '/' && c != '\\'
  | _                                                               => false

def isSafeUrl (s : String) : Bool :=
  let cs := s.toList
  hasSafeUrlPrefix cs && cs.all isSafeUrlChar

structure Url where
  raw  : String
  safe : isSafeUrl raw = true
deriving DecidableEq, Repr

namespace Url

def root : Url := ⟨"/", rfl⟩

instance : Inhabited Url := ⟨root⟩
instance : ToString Url := ⟨Url.raw⟩

@[simp] theorem isSafe (u : Url) : isSafeUrl u.raw = true := u.safe

def parse? (s : String) : Option Url :=
  if h : isSafeUrl s = true then some ⟨s, h⟩ else none

@[simp] theorem parse?_isSome (s : String) : (parse? s).isSome = isSafeUrl s := by
  unfold parse?
  by_cases h : isSafeUrl s = true <;> simp [h]

end Url

def containsCloseSeqLoop (afterLt : Bool) : List Char → Bool
  | []      => false
  | c :: cs => (afterLt && c == '/') || containsCloseSeqLoop (c == '<') cs

def containsCloseSeq (cs : List Char) : Bool := containsCloseSeqLoop false cs

def escapeCloseSeqLoop (afterLt : Bool) : List Char → List Char
  | []      => []
  | c :: cs =>
      if afterLt && c == '/' then
        '\\' :: '/' :: escapeCloseSeqLoop false cs
      else
        c :: escapeCloseSeqLoop (c == '<') cs

def escapeRawText (s : String) : String :=
  if !containsCloseSeq s.toList then s
  else String.ofList (escapeCloseSeqLoop false s.toList)

theorem containsCloseSeqLoop_escapeCloseSeqLoop (cs : List Char) :
    ∀ (b : Bool), containsCloseSeqLoop b (escapeCloseSeqLoop b cs) = false := by
  induction cs with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro b
      simp only [escapeCloseSeqLoop]
      cases h : (b && c == '/')
      · simpa [containsCloseSeqLoop, h] using ih (c == '<')
      · simpa [containsCloseSeqLoop] using ih false

@[simp] theorem containsCloseSeq_escapeRawText (s : String) :
    containsCloseSeq (escapeRawText s).toList = false := by
  unfold escapeRawText containsCloseSeq
  by_cases h : containsCloseSeqLoop false s.toList
  · simp [h, containsCloseSeqLoop_escapeCloseSeqLoop]
  · simp [h]

@[specialize 2] def hasAsciiByteLoop (s : String) (p : UInt8 → Bool) (sz : Nat) (hsz : sz = s.utf8ByteSize) (i : Nat) : Bool :=
  if h : i < sz then
    if p (s.getUTF8Byte ⟨i⟩ (show i < s.utf8ByteSize by omega)) then true else hasAsciiByteLoop s p sz hsz (i + 1)
  else false
termination_by sz - i

@[inline] def hasAsciiByte (s : String) (p : UInt8 → Bool) : Bool :=
  hasAsciiByteLoop s p s.utf8ByteSize rfl 0

private theorem list_toByteArray_loop_data (bs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bs acc).data.toList = acc.data.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih => simp only [List.toByteArray.loop, ih]; simp [ByteArray.push, List.append_assoc]

private theorem list_toByteArray_data (bs : List UInt8) : bs.toByteArray.data.toList = bs := by
  have h := list_toByteArray_loop_data bs ByteArray.empty
  have hem : ByteArray.empty.data.toList = [] := rfl
  rw [hem, List.nil_append] at h; exact h

private theorem string_toByteArray_data (s : String) :
    s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  have h1 : s.toByteArray = s.toList.utf8Encode := by
    rw [← String.toByteArray_ofList, String.ofList_toList]
  rw [h1, List.utf8Encode, list_toByteArray_data]

private theorem utf8EncodeChar_le_127 (c : Char) (hc : c.toNat ≤ 127) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  have hc' : c.val.toNat ≤ 127 := hc
  simp only [hc', ↓reduceIte]; rfl

private theorem utf8EncodeChar_gt_127 (c : Char) (h : c.toNat > 127) :
    ∀ b ∈ String.utf8EncodeChar c, b.toNat ≥ 128 := by
  unfold String.utf8EncodeChar
  have h1 : ¬(c.val.toNat ≤ 127) := by change ¬(c.toNat ≤ 127); omega
  simp only [h1, ↓reduceIte]
  split
  · intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> (change (_ % 256) ≥ 128; omega)
  · split
    · intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> (change (_ % 256) ≥ 128; omega)
    · intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> (change (_ % 256) ≥ 128; omega)

private theorem utf8EncodeChar_ne_nil (c : Char) : String.utf8EncodeChar c ≠ [] := by
  unfold String.utf8EncodeChar; dsimp only
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem hasAsciiByteLoop_eq (s : String) (p : UInt8 → Bool) (i : Nat) :
    hasAsciiByteLoop s p s.utf8ByteSize rfl i = (s.toByteArray.data.toList.drop i).any p := by
  fun_induction hasAsciiByteLoop s p s.utf8ByteSize rfl i with
  | case1 i h hp =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact h
      rw [List.drop_eq_getElem_cons hlt, List.any_cons]
      have hget : s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h := rfl
      rw [hget, hp]; rfl
  | case2 i h hp ih =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact h
      rw [List.drop_eq_getElem_cons hlt, List.any_cons]
      have hget : s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h := rfl
      have hpf : p (s.getUTF8Byte ⟨i⟩ h) = false := Bool.eq_false_iff.2 hp
      rw [hget, hpf, Bool.false_or, ih]
  | case3 i h =>
      have hge : s.toByteArray.data.toList.length ≤ i := by
        rw [Array.length_toList]
        have h' : ¬(i < s.toByteArray.size) := by rw [String.size_toByteArray]; exact h
        exact Nat.le_of_not_lt h'
      rw [List.drop_eq_nil_of_le hge]; rfl

theorem hasAsciiByte_eq_any (s : String) (p : UInt8 → Bool) (q : Char → Bool)
    (hhi : ∀ b : UInt8, b.toNat ≥ 128 → p b = false)
    (hlo : ∀ c : Char, c.toNat ≤ 127 → p (UInt8.ofNat c.toNat) = q c)
    (hqhi : ∀ c : Char, c.toNat > 127 → q c = false) :
    hasAsciiByte s p = s.toList.any q := by
  have hgo : hasAsciiByte s p = s.toByteArray.data.toList.any p := by
    simpa [hasAsciiByte] using hasAsciiByteLoop_eq s p 0
  rw [hgo, string_toByteArray_data, List.any_flatMap]
  congr 1
  funext c
  by_cases hc : c.toNat ≤ 127
  · rw [utf8EncodeChar_le_127 c hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    exact hlo c hc
  · have hgt : c.toNat > 127 := by omega
    rw [hqhi c hgt]
    rw [List.any_eq_false]
    intro b hb
    simp [hhi b (utf8EncodeChar_gt_127 c hgt b hb)]

private def escapeCloseSeqBytesSpec (afterLt : Bool) : List UInt8 → List UInt8
  | []      => []
  | b :: bs =>
      if afterLt && b == 47 then 92 :: 47 :: escapeCloseSeqBytesSpec false bs
      else b :: escapeCloseSeqBytesSpec (b == 60) bs

theorem asciiByte_beq_char (c : Char) (hc : c.toNat ≤ 127) (target : Char) (ht : target.toNat ≤ 127) :
    (UInt8.ofNat c.toNat == UInt8.ofNat target.toNat) = (c == target) := by
  cases heq : (c == target)
  · rw [beq_eq_false_iff_ne] at heq ⊢
    intro h; apply heq
    have hnat : c.toNat = target.toNat := by
      have h1 : (UInt8.ofNat c.toNat).toNat = (UInt8.ofNat target.toNat).toNat := congrArg UInt8.toNat h
      change c.toNat % 256 = target.toNat % 256 at h1
      omega
    exact Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat))
  · rw [beq_iff_eq] at heq; subst heq; simp

private theorem escapeCloseSeqBytes_hi (xs ys : List UInt8) (hhi : ∀ b ∈ xs, b.toNat ≥ 128) (hne : xs ≠ []) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (xs ++ ys) = xs ++ escapeCloseSeqBytesSpec false ys := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
      intro afterLt
      have hb : b.toNat ≥ 128 := hhi b (by simp)
      have hb47 : (b == 47) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; subst heq; exact absurd hb (by decide)
      have hb60 : (b == 60) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; subst heq; exact absurd hb (by decide)
      simp only [List.cons_append, escapeCloseSeqBytesSpec, hb47, hb60, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      cases bs with
      | nil => rfl
      | cons b' bs' => rw [ih (fun x hx => hhi x (by simp [hx])) (by simp) false]

private theorem escapeCloseSeqBytes_flatMap (cs : List Char) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (cs.flatMap String.utf8EncodeChar) =
      (escapeCloseSeqLoop afterLt cs).flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro afterLt
      simp only [List.flatMap_cons, escapeCloseSeqLoop]
      by_cases hc : c.toNat ≤ 127
      · have h1 := utf8EncodeChar_le_127 c hc
        have h47 : (UInt8.ofNat c.toNat == 47) = (c == '/') := asciiByte_beq_char c hc '/' (by decide)
        have h60 : (UInt8.ofNat c.toNat == 60) = (c == '<') := asciiByte_beq_char c hc '<' (by decide)
        rw [h1, List.singleton_append, escapeCloseSeqBytesSpec, h47, h60]
        split
        · simp [List.flatMap_cons, ih]; rfl
        · simp [List.flatMap_cons, h1, ih]
      · have hgt : c.toNat > 127 := by omega
        have hc47 : (c == '/') = false := by
          rw [beq_eq_false_iff_ne]; intro h; subst h; exact absurd hgt (by decide)
        have hc60 : (c == '<') = false := by
          rw [beq_eq_false_iff_ne]; intro h; subst h; exact absurd hgt (by decide)
        rw [escapeCloseSeqBytes_hi _ _ (utf8EncodeChar_gt_127 c hgt) (utf8EncodeChar_ne_nil c) afterLt]
        simp [hc47, hc60, List.flatMap_cons, ih]

private theorem escapeCloseSeqLoop_noop (cs : List Char) (afterLt : Bool)
    (h : containsCloseSeqLoop afterLt cs = false) :
    escapeCloseSeqLoop afterLt cs = cs := by
  induction cs generalizing afterLt with
  | nil => rfl
  | cons c cs ih =>
      simp only [containsCloseSeqLoop, Bool.or_eq_false_iff] at h
      simp only [escapeCloseSeqLoop, h.1, Bool.false_eq_true, ↓reduceIte]
      rw [ih (c == '<') h.2]

private theorem escapeRawText_eq_always (s : String) :
    escapeRawText s = String.ofList (escapeCloseSeqLoop false s.toList) := by
  unfold escapeRawText containsCloseSeq
  cases h : containsCloseSeqLoop false s.toList
  · simp [escapeCloseSeqLoop_noop s.toList false h]
  · simp

@[inline] private def copySliceAppend (src : ByteArray) (segStart stop : Nat) (acc : ByteArray) : ByteArray :=
  src.copySlice segStart acc acc.size (stop - segStart) false

private theorem copySliceAppend_data (src : ByteArray) (segStart stop : Nat) (acc : ByteArray)
    (hle : segStart ≤ stop) :
    (copySliceAppend src segStart stop acc).data.toList =
      acc.data.toList ++ (src.data.toList.drop segStart).take (stop - segStart) := by
  unfold copySliceAppend ByteArray.copySlice
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  have hlen : acc.size = acc.data.toList.length := Array.length_toList.symm
  have h1 : (acc.data.toList.drop 0).take (acc.size - 0) = acc.data.toList := by
    rw [List.drop_zero, Nat.sub_zero, hlen, List.take_length]
  have h2 : acc.data.toList.drop (acc.size + min (stop - segStart) (src.data.size - segStart)) = [] :=
    List.drop_eq_nil_of_le (by rw [← hlen]; omega)
  have h3 : segStart + (stop - segStart) - segStart = stop - segStart := by omega
  rw [h1, h2, h3, List.take_nil, List.append_nil]

private def hasCloseSeqStrLoop (s : String) (i : Nat) (afterLt : Bool) : Bool :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if afterLt && b == 47 then true
    else hasCloseSeqStrLoop s (i + 1) (b == 60)
  else false
termination_by s.utf8ByteSize - i

private theorem hasCloseSeqStrLoop_false_eq (s : String) (i : Nat) (afterLt : Bool)
    (hfalse : hasCloseSeqStrLoop s i afterLt = false) :
    escapeCloseSeqBytesSpec afterLt (s.toByteArray.data.toList.drop i) = s.toByteArray.data.toList.drop i := by
  fun_induction hasCloseSeqStrLoop s i afterLt with
  | case1 i afterLt hi b hhit => cases hfalse
  | case2 i afterLt hi b hmiss ih =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact hi
      rw [List.drop_eq_getElem_cons hlt, escapeCloseSeqBytesSpec]
      have hget : s.toByteArray.data.toList[i] = b := rfl
      rw [hget, if_neg hmiss, ih hfalse]
  | case3 i afterLt hge =>
      have : s.toByteArray.data.toList.length ≤ i := by
        rw [Array.length_toList]
        have h' : ¬(i < s.toByteArray.size) := by rw [String.size_toByteArray]; exact hge
        exact Nat.le_of_not_lt h'
      rw [List.drop_eq_nil_of_le this]; rfl

private def escapeRawBytesLoop (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray) : ByteArray :=
  if h : i < ba.size then
    let b := ba[i]
    if afterLt && b == 47 then
      let acc' := (copySliceAppend ba segStart i acc).push 92
      escapeRawBytesLoop ba i (i + 1) false acc'
    else
      escapeRawBytesLoop ba segStart (i + 1) (b == 60) acc
  else
    copySliceAppend ba segStart ba.size acc
termination_by ba.size - i

private theorem escapeRawBytesLoop_data (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray)
    (hle : segStart ≤ i) (hi : i ≤ ba.size) :
    (escapeRawBytesLoop ba segStart i afterLt acc).data.toList =
      acc.data.toList ++ (ba.data.toList.drop segStart).take (i - segStart) ++
      escapeCloseSeqBytesSpec afterLt (ba.data.toList.drop i) := by
  fun_induction escapeRawBytesLoop ba segStart i afterLt acc with
  | case1 segStart i afterLt acc hlt b hhit acc' ih =>
      have hi_lt : i < ba.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hget : ba.data.toList[i] = b := rfl
      have h47 : b = 47 := beq_iff_eq.1 ((Bool.and_eq_true _ _).mp hhit).2
      rw [ih (by omega) (by omega)]
      simp only [acc', ByteArray.push, Array.toList_push]
      rw [copySliceAppend_data ba segStart i acc hle]
      rw [List.drop_eq_getElem_cons hi_lt, hget]
      rw [escapeCloseSeqBytesSpec, if_pos hhit]
      have htake1 : (b :: ba.data.toList.drop (i + 1)).take (i + 1 - i) = [47] := by
        rw [show i + 1 - i = 1 by omega, h47]; rfl
      rw [htake1]
      simp [List.append_assoc]
  | case2 segStart i afterLt acc hlt b hmiss ih =>
      have hi_lt : i < ba.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hget : ba.data.toList[i] = b := rfl
      rw [ih (by omega) (by omega)]
      rw [List.drop_eq_getElem_cons hi_lt, hget, escapeCloseSeqBytesSpec, if_neg hmiss]
      have hlen : i - segStart < (ba.data.toList.drop segStart).length := by
        rw [List.length_drop, Array.length_toList]; change i - segStart < ba.size - segStart; omega
      have htake : (ba.data.toList.drop segStart).take (i + 1 - segStart) =
          (ba.data.toList.drop segStart).take (i - segStart) ++ [b] := by
        rw [show i + 1 - segStart = (i - segStart) + 1 by omega, List.take_succ_eq_append_getElem hlen]
        simp [List.getElem_drop, show segStart + (i - segStart) = i by omega]; rfl
      rw [htake]
      simp [List.append_assoc]
  | case3 segStart i afterLt acc hge =>
      have heq : i = ba.size := by omega
      subst heq
      rw [copySliceAppend_data ba segStart ba.size acc hle]
      have hnil : ba.data.toList.drop ba.size = [] := by
        apply List.drop_eq_nil_of_le; rw [Array.length_toList]; exact Nat.le_refl _
      rw [hnil]; simp [escapeCloseSeqBytesSpec]

private theorem escapeRawBytes_eq_spec (s : String) :
    escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)) =
      (String.ofList (escapeCloseSeqLoop false s.toList)).toByteArray := by
  apply ByteArray.ext; apply Array.ext'
  unfold String.toUTF8
  rw [escapeRawBytesLoop_data s.toByteArray 0 0 false _ (Nat.le_refl _) (Nat.zero_le _)]
  have hem : (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)).data.toList = [] := rfl
  rw [hem, String.toByteArray_ofList, List.utf8Encode, list_toByteArray_data,
      ← escapeCloseSeqBytes_flatMap, ← string_toByteArray_data]
  simp

private def escapeRawTextFast (s : String) : String :=
  if !hasCloseSeqStrLoop s 0 false then s
  else
    String.fromUTF8
      (escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)))
      (by rw [escapeRawBytes_eq_spec]; exact (String.ofList (escapeCloseSeqLoop false s.toList)).isValidUTF8)

@[csimp] theorem escapeRawText_eq_fast : @escapeRawText = @escapeRawTextFast := by
  funext s
  rw [escapeRawText_eq_always]
  unfold escapeRawTextFast
  cases h : hasCloseSeqStrLoop s 0 false
  · simp only [Bool.not_false, ↓reduceIte]
    have h1 := hasCloseSeqStrLoop_false_eq s 0 false h
    simp only [List.drop_zero] at h1
    apply (String.toByteArray_inj).1
    apply ByteArray.ext; apply Array.ext'
    rw [String.toByteArray_ofList, List.utf8Encode, list_toByteArray_data,
        ← escapeCloseSeqBytes_flatMap, ← string_toByteArray_data, h1]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply (String.toByteArray_inj).1
    exact (escapeRawBytes_eq_spec s).symm

private def escapeRawBytesLoopU (ba : ByteArray) (sz : USize) (hsz : sz.toNat ≤ ba.size)
    (segStart i : USize) (afterLt : Bool) (acc : ByteArray) : ByteArray :=
  if h : i < sz then
    let b := ba.uget i (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.1 h) hsz)
    if afterLt && b == 47 then
      let acc' := (copySliceAppend ba segStart.toNat i.toNat acc).push 92
      escapeRawBytesLoopU ba sz hsz i (i + 1) false acc'
    else
      escapeRawBytesLoopU ba sz hsz segStart (i + 1) (b == 60) acc
  else
    copySliceAppend ba segStart.toNat sz.toNat acc
termination_by sz.toNat - i.toNat
decreasing_by
  all_goals
    have hlt : i.toNat < sz.toNat := USize.lt_iff_toNat_lt.1 h
    have hlt2 : i.toNat + 1 < 2 ^ System.Platform.numBits := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt) sz.toBitVec.isLt
    have hadd : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt hlt2
    omega

/-- Appends the UTF-8 bytes of `escapeRawText s` directly into `acc` in a single unboxed `USize`
    pass without intermediate `String` allocations or UTF-8 re-validation. -/
def escapeRawTextBytesInto (acc : ByteArray) (s : String) : ByteArray :=
  let ba := s.toUTF8
  let sz := ba.usize
  if h : sz.toNat = ba.size then
    escapeRawBytesLoopU ba sz (Nat.le_of_eq h) 0 0 false acc
  else
    escapeRawBytesLoop ba 0 0 false acc

inductive Attr (msg : Type) where
  | cls (name : String)
  | attr (key value : String)
  | flag (key : String) (present : Bool)
  | key (k : String)
  | on (event : String) (m : msg)
  | onValue (event : String) (decode : String → msg)
  | localCell (key component : String) (init? : Option String) (props : String) (bubble : String → Option msg)
  | signalBind (name : String)
  | signalAttr (name attr value : String)
  | signalOn (name event : String) (m : msg)

inductive Html (msg : Type) where
  | text (content : String)
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))

def Attr.empty : Attr msg := .cls ""

abbrev Html.empty : Html msg := .text ""

def Html.ofOption : Option (Html msg) → Html msg
  | some h => h
  | none   => .text ""

@[simp] theorem toString_string (s : String) : toString s = s := rfl

def Attr.isSignalBind : Attr msg → Bool
  | .signalBind _ => true
  | _             => false

def Attr.canonical : Attr msg → Option (Attr msg)
  | .key _            => none
  | .signalBind _     => none
  | .signalAttr _ k v => some (.attr k v)
  | .signalOn _ e m   => some (.on e m)
  | .cls name         => some (.attr "class" name)
  | a                 => some a

@[simp] theorem Attr.isSignalBind_ite (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.isSignalBind (if c then a else b) = if c then Attr.isSignalBind a else Attr.isSignalBind b := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Attr.canonical_ite (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.canonical (if c then a else b) = if c then Attr.canonical a else Attr.canonical b := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Option.ite_some {α : Type _} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem List.filterMap_ite {α β : Type _} (f : α → Option β) (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else b).filterMap f = if c then a.filterMap f else b.filterMap f := by
  by_cases hc : c <;> simp [hc]

instance : Inhabited (Attr msg) := ⟨.cls ""⟩
instance : Inhabited (Html msg) := ⟨.text ""⟩

instance : Coe String (Html msg) := ⟨.text⟩
instance : Coe String (List (Html msg)) := ⟨([·])⟩
instance : Coe Nat (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe Int (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe Float (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe (Option (Html msg)) (Html msg) := ⟨Html.ofOption⟩
instance : Coe (Array (Html msg)) (List (Html msg)) := ⟨Array.toList⟩

def Attr.map (f : α → β) : Attr α → Attr β
  | .cls n               => .cls n
  | .attr k v            => .attr k v
  | .flag k present      => .flag k present
  | .key k               => .key k
  | .on e m              => .on e (f m)
  | .onValue e h         => .onValue e (fun s => f (h s))
  | .localCell k c i p b => .localCell k c i p (fun s => (b s).map f)
  | .signalBind name     => .signalBind name
  | .signalAttr n a v    => .signalAttr n a v
  | .signalOn n e m      => .signalOn n e (f m)

mutual
  def Html.map (f : α → β) : Html α → Html β
    | .text s => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.map f)) (Html.mapChildren f children)
  def Html.mapChildren (f : α → β) : List (Html α) → List (Html β)
    | []      => []
    | c :: cs => Html.map f c :: Html.mapChildren f cs
end

def Attr.prefixSignal (pfx : String) : Attr msg → Attr msg
  | .signalBind n     => .signalBind (pfx ++ n)
  | .signalAttr n a v => .signalAttr (pfx ++ n) a v
  | .signalOn n e m   => .signalOn (pfx ++ n) e m
  | other             => other

mutual
  def Html.prefixSignals (pfx : String) : Html msg → Html msg
    | .text s => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.prefixSignal pfx)) (Html.prefixSignalsList pfx children)
  def Html.prefixSignalsList (pfx : String) : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs => Html.prefixSignals pfx c :: Html.prefixSignalsList pfx cs
end

@[inline] def isKeyChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'

def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def asciiLower (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

def hasOnPrefix : List Char → Bool
  | 'o' :: 'n' :: _ => true
  | _               => false

def isSafeRenderedKey (k : String) : Bool :=
  !k.isEmpty && !hasOnPrefix (k.toList.map asciiLowerChar) && asciiLower k != "srcdoc"

def isSafeAttrName (k : String) : Bool :=
  k.toList.all isKeyChar && isSafeRenderedKey k

def isUrlAttrName (k : String) : Bool :=
  let kl := asciiLower k
  kl == "href" || kl == "src" || kl == "action" || kl == "formaction" ||
  kl == "xlink:href" || kl == "poster" || kl == "data" || kl == "cite" || kl == "srcset"

def Attr.validKeyValue (k v : String) : Bool :=
  isSafeAttrName k && (!isUrlAttrName k || isSafeUrl v)

def Attr.valid : Attr msg → Bool
  | .cls _            => true
  | .attr k v         => Attr.validKeyValue k v
  | .flag k _         => isSafeAttrName k
  | .key _            => true
  | .on event _       => isSafeAttrName event
  | .onValue event _  => isSafeAttrName event
  | .localCell ..     => true
  | .signalBind _     => true
  | .signalAttr _ a v => Attr.validKeyValue a v
  | .signalOn _ e _   => isSafeAttrName e

@[simp] theorem Attr.valid_cls (n : String) : (Attr.cls n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_attr (k v : String) : (Attr.attr k v : Attr msg).valid = Attr.validKeyValue k v := rfl
@[simp] theorem Attr.valid_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).valid = isSafeAttrName k := rfl
@[simp] theorem Attr.valid_key (n : String) : (Attr.key n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_on (e : String) (m : msg) : (Attr.on e m).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.valid_onValue (e : String) (f : String → msg) : (Attr.onValue e f).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.valid_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) :
    (Attr.localCell k c i p b).valid = true := rfl
@[simp] theorem Attr.valid_signalBind (n : String) : (Attr.signalBind n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_signalAttr (n a v : String) :
    (Attr.signalAttr n a v : Attr msg).valid = Attr.validKeyValue a v := rfl
@[simp] theorem Attr.valid_signalOn (n e : String) (m : msg) :
    (Attr.signalOn n e m).valid = isSafeAttrName e := rfl

def Attr.validList : List (Attr msg) → Bool
  | []      => true
  | a :: as => a.valid && Attr.validList as

def Attr.isLocalCell : Attr msg → Bool
  | .localCell .. => true
  | _             => false

@[simp] theorem Attr.isLocalCell_cls (n : String) : (Attr.cls n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_attr (k v : String) : (Attr.attr k v : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_key (n : String) : (Attr.key n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_on (e : String) (m : msg) : (Attr.on e m).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_onValue (e : String) (f : String → msg) : (Attr.onValue e f).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) :
    (Attr.localCell k c i p b).isLocalCell = true := rfl
@[simp] theorem Attr.isLocalCell_signalBind (n : String) : (Attr.signalBind n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_signalAttr (n a v : String) :
    (Attr.signalAttr n a v : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_signalOn (n e : String) (m : msg) :
    (Attr.signalOn n e m).isLocalCell = false := rfl

def Attr.hasLocalCell : List (Attr msg) → Bool
  | []        => false
  | a :: rest => a.isLocalCell || Attr.hasLocalCell rest

def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]

def isVoidTag (tag : String) : Bool := voidTags.contains tag

private def isVoidTagFast (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 2 => tag == "br" || tag == "hr"
  | 3 => tag == "col" || tag == "img" || tag == "wbr"
  | 4 => tag == "area" || tag == "base" || tag == "link" || tag == "meta"
  | 5 => tag == "embed" || tag == "input" || tag == "track"
  | 6 => tag == "source"
  | _ => false

@[csimp] theorem isVoidTag_eq_fast : @isVoidTag = @isVoidTagFast := by
  funext tag
  unfold isVoidTag voidTags isVoidTagFast
  simp only [List.contains, List.elem]
  by_cases h1 : tag == "area"; · rw [beq_iff_eq.1 h1]; rfl
  by_cases h2 : tag == "base"; · rw [beq_iff_eq.1 h2]; rfl
  by_cases h3 : tag == "br"; · rw [beq_iff_eq.1 h3]; rfl
  by_cases h4 : tag == "col"; · rw [beq_iff_eq.1 h4]; rfl
  by_cases h5 : tag == "embed"; · rw [beq_iff_eq.1 h5]; rfl
  by_cases h6 : tag == "hr"; · rw [beq_iff_eq.1 h6]; rfl
  by_cases h7 : tag == "img"; · rw [beq_iff_eq.1 h7]; rfl
  by_cases h8 : tag == "input"; · rw [beq_iff_eq.1 h8]; rfl
  by_cases h9 : tag == "link"; · rw [beq_iff_eq.1 h9]; rfl
  by_cases h10 : tag == "meta"; · rw [beq_iff_eq.1 h10]; rfl
  by_cases h11 : tag == "source"; · rw [beq_iff_eq.1 h11]; rfl
  by_cases h12 : tag == "track"; · rw [beq_iff_eq.1 h12]; rfl
  by_cases h13 : tag == "wbr"; · rw [beq_iff_eq.1 h13]; rfl
  simp only [Bool.eq_false_iff.2 h1, Bool.eq_false_iff.2 h2, Bool.eq_false_iff.2 h3,
    Bool.eq_false_iff.2 h4, Bool.eq_false_iff.2 h5, Bool.eq_false_iff.2 h6,
    Bool.eq_false_iff.2 h7, Bool.eq_false_iff.2 h8, Bool.eq_false_iff.2 h9,
    Bool.eq_false_iff.2 h10, Bool.eq_false_iff.2 h11, Bool.eq_false_iff.2 h12,
    Bool.eq_false_iff.2 h13, Bool.false_or]
  split <;> rfl

def isSafeTagName (tag : String) : Bool :=
  let cs := tag.toList
  !cs.isEmpty && cs.all (fun c => c.isAlphanum || c == '-')

def isForbiddenTag (tag : String) : Bool :=
  tag == "script" || tag == "base" || tag == "applet" || tag == "object" || tag == "embed"

def isHeadingTag (tag : String) : Bool :=
  tag == "h1" || tag == "h2" || tag == "h3" || tag == "h4" || tag == "h5" || tag == "h6"

def closesPTag (tag : String) : Bool :=
  tag == "address" || tag == "article" || tag == "aside" || tag == "blockquote" ||
  tag == "details" || tag == "div" || tag == "dl" || tag == "fieldset" ||
  tag == "figcaption" || tag == "figure" || tag == "footer" || tag == "form" ||
  isHeadingTag tag || tag == "header" || tag == "hgroup" || tag == "hr" ||
  tag == "main" || tag == "menu" || tag == "nav" || tag == "ol" || tag == "p" ||
  tag == "pre" || tag == "search" || tag == "section" || tag == "table" || tag == "ul"

def isInteractiveTag (tag : String) : Bool :=
  tag == "a" || tag == "button" || tag == "input" || tag == "select" ||
  tag == "textarea" || tag == "details" || tag == "summary"

def isContextOnlyTag (tag : String) : Bool :=
  tag == "li" || tag == "dt" || tag == "dd" ||
  tag == "caption" || tag == "colgroup" || tag == "col" ||
  tag == "thead" || tag == "tbody" || tag == "tfoot" ||
  tag == "tr" || tag == "td" || tag == "th" ||
  tag == "option" || tag == "optgroup"

inductive TagMode where
  | normal
  | ulOl
  | dl
  | table
  | colgroup
  | tableSection
  | tableRow
  | select
  | optgroup
  | option
  | rawStyle
  | textarea
  | svg
deriving DecidableEq, Repr

structure HtmlCtx where
  mode        : TagMode := .normal
  inP         : Bool := false
  interactive : Bool := false
  inForm      : Bool := false
deriving DecidableEq, Repr

def stepHtmlCtx (ctx : HtmlCtx) (tag : String) : Option HtmlCtx :=
  if !isSafeTagName tag || isForbiddenTag tag then none
  else
    match ctx.mode with
    | .svg =>
        if tag == "foreignObject" then some {}
        else some { ctx with mode := .svg }
    | .option | .textarea | .rawStyle => none
    | .ulOl =>
        if tag == "li" then some { ctx with mode := .normal, inP := false } else none
    | .dl =>
        if tag == "dt" || tag == "dd" then some { ctx with mode := .normal, inP := false } else none
    | .table =>
        if tag == "caption" then some { ctx with mode := .normal, inP := false }
        else if tag == "colgroup" then some { ctx with mode := .colgroup, inP := false }
        else if tag == "thead" || tag == "tbody" || tag == "tfoot" then
          some { ctx with mode := .tableSection, inP := false }
        else none
    | .colgroup =>
        if tag == "col" then some { ctx with mode := .normal } else none
    | .tableSection =>
        if tag == "tr" then some { ctx with mode := .tableRow, inP := false } else none
    | .tableRow =>
        if tag == "td" || tag == "th" then some { ctx with mode := .normal, inP := false } else none
    | .select =>
        if tag == "option" then some { ctx with mode := .option }
        else if tag == "optgroup" then some { ctx with mode := .optgroup }
        else none
    | .optgroup =>
        if tag == "option" then some { ctx with mode := .option } else none
    | .normal =>
        if isContextOnlyTag tag then none
        else if ctx.inP && closesPTag tag then none
        else if ctx.interactive && (isInteractiveTag tag || tag == "label" || tag == "form") then none
        else if ctx.inForm && tag == "form" then none
        else if tag == "svg" then some { ctx with mode := .svg }
        else if tag == "style" then some { ctx with mode := .rawStyle }
        else if tag == "textarea" then some { ctx with mode := .textarea, interactive := true }
        else if tag == "select" then some { ctx with mode := .select, interactive := true }
        else if tag == "ul" || tag == "ol" then some { ctx with mode := .ulOl }
        else if tag == "dl" then some { ctx with mode := .dl }
        else if tag == "table" then some { ctx with mode := .table }
        else
          some { mode        := .normal
                 inP         := ctx.inP || tag == "p" || isHeadingTag tag
                 interactive := ctx.interactive || tag == "a" || tag == "button" || tag == "details" || tag == "summary"
                 inForm      := ctx.inForm || tag == "form" }

def validTextIn (ctx : HtmlCtx) (s : String) : Bool :=
  match ctx.mode with
  | .normal | .option | .textarea | .svg => true
  | .rawStyle => !containsCloseSeq s.toList
  | .ulOl | .dl | .table | .colgroup | .tableSection | .tableRow | .select | .optgroup => s == ""

mutual
  def Html.validIn (ctx : HtmlCtx) : Html msg → Bool
    | .text s => validTextIn ctx s
    | .element tag attrs children =>
        Attr.validList attrs &&
        (!isVoidTag tag || children.isEmpty) &&
        (!Attr.hasLocalCell attrs || children.isEmpty) &&
        match stepHtmlCtx ctx tag with
        | some childCtx => Html.validListIn childCtx children
        | none          => false

  def Html.validListIn (ctx : HtmlCtx) : List (Html msg) → Bool
    | []      => true
    | c :: cs => Html.validIn ctx c && Html.validListIn ctx cs
end

def Html.valid (h : Html msg) : Bool := Html.validIn {} h

@[simp] theorem Attr.valid_empty : (Attr.empty : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.valid (if c then a else b) = (if c then a.valid else b.valid) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Attr.validList_nil : Attr.validList ([] : List (Attr msg)) = true := rfl
@[simp] theorem Attr.validList_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.validList (a :: as) = (a.valid && Attr.validList as) := rfl

@[simp] theorem Attr.validList_append (xs ys : List (Attr msg)) :
    Attr.validList (xs ++ ys) = (Attr.validList xs && Attr.validList ys) := by
  induction xs with
  | nil => simp [Attr.validList]
  | cons a rest ih => simp [Attr.validList, ih, Bool.and_assoc]

@[simp] theorem Attr.validList_filter_nonkey (xs : List (Attr msg)) :
    Attr.validList (xs.filter (fun | .key _ => false | _ => true)) = Attr.validList xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      cases a <;> simp [Attr.validList, Attr.valid, ih]

@[simp] theorem Attr.hasLocalCell_nil : Attr.hasLocalCell ([] : List (Attr msg)) = false := rfl
@[simp] theorem Attr.hasLocalCell_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.hasLocalCell (a :: as) = (a.isLocalCell || Attr.hasLocalCell as) := rfl

@[simp] theorem Attr.isLocalCell_empty : (Attr.empty : Attr msg).isLocalCell = false := rfl

@[simp] theorem Attr.isLocalCell_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.isLocalCell (if c then a else b) = (if c then a.isLocalCell else b.isLocalCell) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Attr.hasLocalCell_append (xs ys : List (Attr msg)) :
    Attr.hasLocalCell (xs ++ ys) = (Attr.hasLocalCell xs || Attr.hasLocalCell ys) := by
  induction xs with
  | nil => simp [Attr.hasLocalCell]
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, ih]

@[simp] theorem Attr.hasLocalCell_filter_nonkey (xs : List (Attr msg)) :
    Attr.hasLocalCell (xs.filter (fun | .key _ => false | _ => true)) = Attr.hasLocalCell xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, ih]

@[simp] theorem Attr.valid_map {α β : Type} (f : α → β) (a : Attr α) :
    (a.map f).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.validList_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.validList (as.map (Attr.map f)) = Attr.validList as := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp [Attr.validList, ih]

@[simp] theorem Attr.hasLocalCell_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.hasLocalCell (as.map (Attr.map f)) = Attr.hasLocalCell as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, Attr.map, ih]

@[simp] theorem Attr.valid_prefixSignal (pfx : String) (a : Attr msg) :
    (a.prefixSignal pfx).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.validList_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.validList (as.map (Attr.prefixSignal pfx)) = Attr.validList as := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp [Attr.validList, ih]

@[simp] theorem Attr.hasLocalCell_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.hasLocalCell (as.map (Attr.prefixSignal pfx)) = Attr.hasLocalCell as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, Attr.prefixSignal, ih]

@[simp] theorem Html.mapChildren_isEmpty {α β : Type} (f : α → β) (cs : List (Html α)) :
    (Html.mapChildren f cs).isEmpty = cs.isEmpty := by
  cases cs <;> rfl

@[simp] theorem Html.prefixSignalsList_isEmpty (pfx : String) (cs : List (Html msg)) :
    (Html.prefixSignalsList pfx cs).isEmpty = cs.isEmpty := by
  cases cs <;> rfl

mutual
  @[simp] theorem Html.validIn_map {α β : Type} (ctx : HtmlCtx) (f : α → β) :
      (h : Html α) → Html.validIn ctx (h.map f) = Html.validIn ctx h
    | .text _ => rfl
    | .element tag attrs children => by
        simp only [Html.map, Html.validIn, Attr.validList_map_attrMap,
                   Attr.hasLocalCell_map_attrMap, Html.mapChildren_isEmpty]
        cases stepHtmlCtx ctx tag with
        | none => rfl
        | some childCtx => simp [Html.validListIn_mapChildren childCtx f children]

  @[simp] theorem Html.validListIn_mapChildren {α β : Type} (ctx : HtmlCtx) (f : α → β) :
      (cs : List (Html α)) → Html.validListIn ctx (Html.mapChildren f cs) = Html.validListIn ctx cs
    | [] => rfl
    | c :: cs => by
        simp [Html.mapChildren, Html.validListIn, Html.validIn_map ctx f c,
              Html.validListIn_mapChildren ctx f cs]
end

mutual
  @[simp] theorem Html.validIn_prefixSignals (ctx : HtmlCtx) (pfx : String) :
      (h : Html msg) → Html.validIn ctx (h.prefixSignals pfx) = Html.validIn ctx h
    | .text _ => rfl
    | .element tag attrs children => by
        simp only [Html.prefixSignals, Html.validIn, Attr.validList_prefixSignal,
                   Attr.hasLocalCell_prefixSignal, Html.prefixSignalsList_isEmpty]
        cases stepHtmlCtx ctx tag with
        | none => rfl
        | some childCtx => simp [Html.validListIn_prefixSignalsList childCtx pfx children]

  @[simp] theorem Html.validListIn_prefixSignalsList (ctx : HtmlCtx) (pfx : String) :
      (cs : List (Html msg)) → Html.validListIn ctx (Html.prefixSignalsList pfx cs) = Html.validListIn ctx cs
    | [] => rfl
    | c :: cs => by
        simp [Html.prefixSignalsList, Html.validListIn, Html.validIn_prefixSignals ctx pfx c,
              Html.validListIn_prefixSignalsList ctx pfx cs]
end

@[simp] theorem Html.validListIn_nil (ctx : HtmlCtx) :
    Html.validListIn ctx ([] : List (Html msg)) = true := rfl

@[simp] theorem Html.validListIn_cons (ctx : HtmlCtx) (c : Html msg) (cs : List (Html msg)) :
    Html.validListIn ctx (c :: cs) = (Html.validIn ctx c && Html.validListIn ctx cs) := rfl

@[simp] theorem Html.validListIn_append (ctx : HtmlCtx) (xs ys : List (Html msg)) :
    Html.validListIn ctx (xs ++ ys) = (Html.validListIn ctx xs && Html.validListIn ctx ys) := by
  induction xs with
  | nil => simp [Html.validListIn]
  | cons c rest ih => simp [Html.validListIn, ih, Bool.and_assoc]

@[simp] theorem Html.validIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg) :
    Html.validIn ctx (if c then a else b) = (if c then Html.validIn ctx a else Html.validIn ctx b) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Html.validListIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : List (Html msg)) :
    Html.validListIn ctx (if c then a else b) = (if c then Html.validListIn ctx a else Html.validListIn ctx b) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Html.validIn_ofOption (ctx : HtmlCtx) (o : Option (Html msg)) :
    Html.validIn ctx (Html.ofOption o) =
      match o with | some h => Html.validIn ctx h | none => validTextIn ctx "" := by
  cases o <;> rfl

@[simp] theorem Html.validListIn_map {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f) = xs.all (fun a => Html.validIn ctx (f a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [ih]

@[simp] theorem Html.validListIn_toList_map {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f).toList = xs.toList.all (fun a => Html.validIn ctx (f a)) := by
  simp [Array.toList_map]

@[simp] theorem List.all_const_true {α : Type} (xs : List α) :
    xs.all (fun _ => true) = true := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp [ih]

@[simp] theorem validTextIn_normal (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.normal, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_option (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.option, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_textarea (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.textarea, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_svg (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.svg, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_rawStyle (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.rawStyle, inP, inter, inForm⟩ s = !containsCloseSeq s.toList := rfl

@[simp] theorem validTextIn_empty (ctx : HtmlCtx) :
    validTextIn ctx "" = true := by
  cases ctx with
  | mk mode _ _ _ => cases mode <;> simp [validTextIn, containsCloseSeq, containsCloseSeqLoop]

theorem Attr.validList_cons_intro {msg : Type} (a : Attr msg) (as : List (Attr msg))
    (ha : a.valid = true) (has : Attr.validList as = true) :
    Attr.validList (a :: as) = true := by
  simp [Attr.validList, ha, has]

theorem Attr.validList_append_intro {msg : Type} (xs ys : List (Attr msg))
    (hx : Attr.validList xs = true) (hy : Attr.validList ys = true) :
    Attr.validList (xs ++ ys) = true := by
  simp [Attr.validList_append, hx, hy]

theorem Attr.valid_ite_intro {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg)
    (ht : c → a.valid = true) (hf : ¬ c → b.valid = true) :
    Attr.valid (if c then a else b) = true := by
  by_cases hc : c <;> simp [hc, ht, hf]

theorem Attr.hasLocalCell_cons_eq_false {msg : Type} (a : Attr msg) (as : List (Attr msg))
    (ha : a.isLocalCell = false) (has : Attr.hasLocalCell as = false) :
    Attr.hasLocalCell (a :: as) = false := by
  simp [Attr.hasLocalCell, ha, has]

theorem Attr.hasLocalCell_append_eq_false {msg : Type} (xs ys : List (Attr msg))
    (hx : Attr.hasLocalCell xs = false) (hy : Attr.hasLocalCell ys = false) :
    Attr.hasLocalCell (xs ++ ys) = false := by
  simp [Attr.hasLocalCell_append, hx, hy]

theorem Attr.isLocalCell_ite_eq_false {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg)
    (ht : c → a.isLocalCell = false) (hf : ¬ c → b.isLocalCell = false) :
    Attr.isLocalCell (if c then a else b) = false := by
  by_cases hc : c <;> simp [hc, ht, hf]

theorem Bool.not_false_or (a b : Bool) (ha : a = false) : (!a || b) = true := by
  simp [ha]

theorem validTextIn_rawStyle_escape (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.rawStyle, inP, inter, inForm⟩ (escapeRawText s) = true := by
  simp [validTextIn, containsCloseSeq_escapeRawText]

theorem Html.validIn_element_intro {msg : Type} (ctx childCtx : HtmlCtx)
    (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))
    (hstep : stepHtmlCtx ctx tag = some childCtx)
    (hattrs : Attr.validList attrs = true)
    (hvoid : (!isVoidTag tag || children.isEmpty) = true)
    (hcell : (!Attr.hasLocalCell attrs || children.isEmpty) = true)
    (hkids : Html.validListIn childCtx children = true) :
    Html.validIn ctx (.element tag attrs children) = true := by
  simp [Html.validIn, hstep, hattrs, hvoid, hcell, hkids]

theorem Html.validListIn_cons_intro {msg : Type} (ctx : HtmlCtx) (c : Html msg) (cs : List (Html msg))
    (hc : Html.validIn ctx c = true) (hcs : Html.validListIn ctx cs = true) :
    Html.validListIn ctx (c :: cs) = true := by
  simp [Html.validListIn, hc, hcs]

theorem Html.validListIn_append_intro {msg : Type} (ctx : HtmlCtx) (xs ys : List (Html msg))
    (hx : Html.validListIn ctx xs = true) (hy : Html.validListIn ctx ys = true) :
    Html.validListIn ctx (xs ++ ys) = true := by
  simp [Html.validListIn_append, hx, hy]

theorem Html.validIn_ite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg)
    (ht : c → Html.validIn ctx a = true) (hf : ¬ c → Html.validIn ctx b = true) :
    Html.validIn ctx (if c then a else b) = true := by
  by_cases hc : c <;> simp [hc, ht, hf]

theorem Html.validIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a : c → Html msg) (b : ¬ c → Html msg)
    (ht : ∀ h : c, Html.validIn ctx (a h) = true) (hf : ∀ h : ¬ c, Html.validIn ctx (b h) = true) :
    Html.validIn ctx (if h : c then a h else b h) = true := by
  by_cases hc : c <;> simp [hc, ht, hf]

theorem Html.validListIn_ite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a b : List (Html msg))
    (ht : c → Html.validListIn ctx a = true) (hf : ¬ c → Html.validListIn ctx b = true) :
    Html.validListIn ctx (if c then a else b) = true := by
  by_cases hc : c <;> simp [hc, ht, hf]

theorem Html.validListIn_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg)
    (hf : ∀ a, Html.validIn ctx (f a) = true) :
    Html.validListIn ctx (xs.map f) = true := by
  simp only [Html.validListIn_map, List.all_eq_true]
  exact fun a _ => hf a

theorem Html.validListIn_toList_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg)
    (hf : ∀ a, Html.validIn ctx (f a) = true) :
    Html.validListIn ctx (xs.map f).toList = true := by
  simp only [Html.validListIn_toList_map, List.all_eq_true]
  exact fun a _ => hf a

def onlySignalBind : List (Attr msg) → Bool
  | [.signalBind _] => true
  | .key _ :: rest  => onlySignalBind rest
  | _               => false

def mkCanonicalElem (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) : Html msg :=
  if tag == "span" && onlySignalBind attrs then
    match cs with
    | [c] => c
    | _   => .element tag (attrs.filterMap Attr.canonical) cs
  else
    .element tag (attrs.filterMap Attr.canonical) cs

mutual
  def Html.canonical : Html msg → Html msg
    | .text s               => .text s
    | .element tag attrs cs => mkCanonicalElem tag attrs (Html.canonicalList cs)

  def Html.canonicalList : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs => Html.canonical c :: Html.canonicalList cs
end

@[simp] theorem onlySignalBind_signalBind (sig : String) :
    onlySignalBind ([.signalBind sig] : List (Attr msg)) = true := rfl

@[simp] theorem onlySignalBind_key (k : String) (rest : List (Attr msg)) :
    onlySignalBind (.key k :: rest) = onlySignalBind rest := rfl

@[simp] theorem mkCanonicalElem_signalBind (sig : String) (c : Html msg) :
    mkCanonicalElem "span" [.signalBind sig] [c] = c := rfl

@[simp] theorem mkCanonicalElem_not_signal (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg))
    (h : (tag == "span" && onlySignalBind attrs) = false) :
    mkCanonicalElem tag attrs cs = .element tag (attrs.filterMap Attr.canonical) cs := by
  simp [mkCanonicalElem, h]

@[simp] theorem Html.canonical_text (s : String) :
    Html.canonical (.text s : Html msg) = .text s := rfl

@[simp] theorem Html.canonical_element (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) :
    Html.canonical (.element tag attrs cs) = mkCanonicalElem tag attrs (Html.canonicalList cs) := rfl

@[simp] theorem Html.canonical_ite (c : Prop) [Decidable c] (a b : Html msg) :
    Html.canonical (if c then a else b) = if c then Html.canonical a else Html.canonical b := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Html.canonical_ofOption (o : Option (Html msg)) :
    Html.canonical (Html.ofOption o) = match o with | some h => Html.canonical h | none => .text "" := by
  cases o <;> rfl

@[simp] theorem Html.canonicalList_nil : Html.canonicalList ([] : List (Html msg)) = [] := rfl

@[simp] theorem Html.canonicalList_cons (c : Html msg) (cs : List (Html msg)) :
    Html.canonicalList (c :: cs) = Html.canonical c :: Html.canonicalList cs := rfl

@[simp] theorem Html.canonicalList_append (xs ys : List (Html msg)) :
    Html.canonicalList (xs ++ ys) = Html.canonicalList xs ++ Html.canonicalList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem Html.canonicalList_map {α : Type _} (xs : List α) (f : α → Html msg) :
    Html.canonicalList (xs.map f) = xs.map (fun x => Html.canonical (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem Html.canonicalList_eq_map (cs : List (Html msg)) :
    Html.canonicalList cs = cs.map Html.canonical := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

end Qed
