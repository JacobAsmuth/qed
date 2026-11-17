import Std.Data.String.ToNat
import Std.Data.String.ToInt
import Qed.Html
import Qed.Json
import Qed.Proto

namespace Qed

class RouteParam (α : Type) where
  toSeg      : α → String
  fromSeg    : String → Option α
  round_trip : ∀ a, fromSeg (toSeg a) = some a

attribute [simp] RouteParam.round_trip

instance : RouteParam String := ⟨id, some, fun _ => rfl⟩
instance : RouteParam Nat    := ⟨Nat.repr, String.toNat?, Nat.toNat?_repr⟩
instance : RouteParam Int    := ⟨Int.repr, String.toInt?, Int.toInt?_repr⟩

@[simp] theorem RouteParam.toSeg_string (s : String) : RouteParam.toSeg s = s := rfl

class Router (α : Type) where
  print      : α → List String
  parse      : List String → Option α
  round_trip : ∀ a, parse (print a) = some a

instance [Router R] : ToJson R := ⟨fun r => toJson (Router.print r)⟩
instance [Router R] : FromJson R := ⟨fun j => do
  let segs ← (fromJson j : Except String (List String))
  (Router.parse segs).elim (.error "invalid route") .ok⟩
instance [Router R] : LawfulJson R where
  depthBound := 1
  depth_toJson r := LawfulJson.depth_toJson (Router.print r)
  fromJson_toJson r := by
    change (fromJson (toJson (Router.print r)) : Except String (List String)).bind
      (fun segs => (Router.parse segs).elim (.error "invalid route") .ok) = .ok r
    rw [LawfulJson.fromJson_toJson (Router.print r)]
    change (Router.parse (Router.print r)).elim _ _ = _
    rw [Router.round_trip]; rfl

instance [Router R] : NonNullJson R := ⟨nofun⟩

instance [Router R] : ToProto R := .ofEquiv Router.print

private def decodeRouteSegs [Router R] (segs : List String) : Except String R :=
  (Router.parse segs).elim (.error "invalid route") .ok

instance [Router R] : FromProto R where
  fromProtoMsg fs := (FromProto.fromProtoMsg fs).bind decodeRouteSegs
  fromProtoVal w  := (FromProto.fromProtoVal w).bind decodeRouteSegs

instance [Router R] : LawfulProto R where
  msg_tags_pos r := LawfulProto.msg_tags_pos (Router.print r)
  fromProtoMsg_toProtoMsg r := by
    change (FromProto.fromProtoMsg (ToProto.toProtoMsg (Router.print r))).bind decodeRouteSegs = .ok r
    rw [LawfulProto.fromProtoMsg_toProtoMsg (Router.print r)]; simp [decodeRouteSegs, Router.round_trip, Except.bind]
  fromProtoVal_toProtoVal r := by
    change (FromProto.fromProtoVal (ToProto.toProtoVal (Router.print r))).bind decodeRouteSegs = .ok r
    rw [LawfulProto.fromProtoVal_toProtoVal (Router.print r)]; simp [decodeRouteSegs, Router.round_trip, Except.bind]

class LawfulKey (α : Type) where
  toKey     : α → String
  injective : ∀ a₁ a₂ : α, toKey a₁ = toKey a₂ → a₁ = a₂

instance : LawfulKey String where
  toKey := id
  injective _ _ h := h

instance : LawfulKey Nat where
  toKey := Nat.repr
  injective a₁ a₂ h := by
    have := congrArg String.toNat? h
    simpa [Nat.toNat?_repr] using this

instance : LawfulKey Int where
  toKey := Int.repr
  injective a₁ a₂ h := by
    have := congrArg String.toInt? h
    simpa [Int.toInt?_repr] using this

instance : LawfulKey Bool where
  toKey | true => "1" | false => "0"
  injective a₁ a₂ h := by cases a₁ <;> cases a₂ <;> simp_all

instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := by
    have h₁ := LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    have h₂ := LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    rw [h] at h₁
    rw [h₁] at h₂
    exact Except.ok.inj h₂

private def hexDigit (n : UInt8) : Char :=
  match n.toNat % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E'
  | _ => 'F'

private def isUnreserved (b : UInt8) : Bool :=
  let c := b.toNat
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
    || c == 45 || c == 95 || c == 46 || c == 126

@[inline] def isPctEncodedChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    n == 45 || n == 95 || n == 46 || n == 126 || n == 37

@[inline] private def isSafePathBodyChar (c : Char) : Bool :=
  isSafeUrlChar c && c.toNat != 92

private theorem isPctEncodedChar_hexDigit (n : UInt8) :
    isPctEncodedChar (hexDigit n) = true := by
  unfold hexDigit; split <;> rfl

private theorem isPctEncodedChar_unreserved {b : UInt8} (h : isUnreserved b = true) :
    isPctEncodedChar (Char.ofNat b.toNat) = true := by
  unfold isUnreserved at h
  have hb : b.toNat ≤ 126 ∧ b.toNat ≥ 45 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega
  have hv : b.toNat.isValidChar := by simp [Nat.isValidChar]; omega
  have htn : (Char.ofNat b.toNat).toNat = b.toNat := by simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
  unfold isPctEncodedChar; rw [htn]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢; omega

private def encodeUTF8Loop (bs : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < bs.size then
    let b := bs[i]
    let next := if isUnreserved b then acc.push (Char.ofNat b.toNat)
                else ((acc.push '%').push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0F))
    encodeUTF8Loop bs (i + 1) next
  else acc
termination_by bs.size - i

private theorem encodeUTF8Loop_pct (bs : ByteArray) :
    ∀ (i : Nat) (acc : String),
      acc.toList.all isPctEncodedChar = true →
      (encodeUTF8Loop bs i acc).toList.all isPctEncodedChar = true := by
  intro i
  induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc hacc; unfold encodeUTF8Loop
      have hnot : ¬ i < bs.size := by omega
      simp [hnot, hacc]
  | succ _ ih =>
      intro acc hacc; unfold encodeUTF8Loop
      have hlt : i < bs.size := by omega
      simp only [hlt, ↓reduceDIte]
      apply ih (i + 1) (by omega)
      by_cases hu : isUnreserved bs[i]
      · simp [hu, String.toList_push, hacc, isPctEncodedChar_unreserved hu]
      · have hpct : isPctEncodedChar '%' = true := rfl
        simp [hu, String.toList_push, hacc, hpct, isPctEncodedChar_hexDigit]

def encodeSeg (s : String) : String :=
  encodeUTF8Loop s.toUTF8 0 ""

theorem encodeSeg_pct (s : String) :
    (encodeSeg s).toList.all isPctEncodedChar = true :=
  encodeUTF8Loop_pct s.toUTF8 0 "" rfl

theorem encodeSeg_safe (s : String) :
    (encodeSeg s).toList.all isSafePathBodyChar = true := by
  have h := encodeSeg_pct s
  rw [List.all_eq_true] at h ⊢
  intro c hc; specialize h c hc
  unfold isPctEncodedChar at h; unfold isSafePathBodyChar isSafeUrlChar
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h ⊢
  omega

private def unhex (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (UInt8.ofNat (n - 48))
  else if 65 ≤ n && n ≤ 70 then some (UInt8.ofNat (n - 55))
  else if 97 ≤ n && n ≤ 102 then some (UInt8.ofNat (n - 87))
  else none

private def decodeBytes : List Char → ByteArray → ByteArray
  | '%' :: h :: l :: rest, acc =>
      match unhex h, unhex l with
      | some hi, some lo => decodeBytes rest (acc.push ((hi <<< 4) ||| lo))
      | _,       _       => decodeBytes (h :: l :: rest) (acc.push 37)
  | c :: rest, acc => decodeBytes rest (acc ++ c.toString.toUTF8)
  | [], acc => acc

def decodeSeg (s : String) : String :=
  (String.fromUTF8? (decodeBytes s.toList .empty)).getD s

private theorem unhex_hexDigit (n : UInt8) (hn : n.toNat < 16) :
    unhex (hexDigit n) = some n := by
  have h0 : n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨
            n.toNat = 4 ∨ n.toNat = 5 ∨ n.toNat = 6 ∨ n.toNat = 7 ∨
            n.toNat = 8 ∨ n.toNat = 9 ∨ n.toNat = 10 ∨ n.toNat = 11 ∨
            n.toNat = 12 ∨ n.toNat = 13 ∨ n.toNat = 14 ∨ n.toNat = 15 := by omega
  rcases h0 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · have hne : n = UInt8.ofNat n.toNat := (UInt8.ofNat_toNat).symm
      rw [hne]; simp [h, hexDigit, unhex]

private theorem bitvec8_recombine : ∀ x : BitVec 8, ((x >>> 4) <<< 4) ||| (x &&& 0x0F#8) = x := by
  decide

private theorem uint8_recombine (b : UInt8) :
    ((b >>> 4) <<< 4) ||| (b &&& 0x0F) = b :=
  UInt8.eq_of_toBitVec_eq (bitvec8_recombine b.toBitVec)

private theorem bitvec8_shiftRight4_lt : ∀ x : BitVec 8, (x >>> 4#8).toNat < 16 := by decide
private theorem bitvec8_and15_lt : ∀ x : BitVec 8, (x &&& 0x0F#8).toNat < 16 := by decide

private theorem uint8_shiftRight4_lt (b : UInt8) : (b >>> 4).toNat < 16 :=
  bitvec8_shiftRight4_lt b.toBitVec

private theorem uint8_and15_lt (b : UInt8) : (b &&& 0x0F).toNat < 16 :=
  bitvec8_and15_lt b.toBitVec

private theorem encodeUTF8Loop_toList (bs : ByteArray) :
    ∀ (i : Nat) (acc : String),
      (encodeUTF8Loop bs i acc).toList = acc.toList ++ (encodeUTF8Loop bs i "").toList := by
  intro i
  induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc
      have hnot : ¬ i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]
      simp [hnot]
  | succ _ ih =>
      intro acc
      have hlt : i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]
      simp only [hlt, ↓reduceDIte]
      by_cases hu : isUnreserved bs[i]
      · simp only [hu, ↓reduceIte]
        rw [ih (i + 1) (by omega) (acc.push (Char.ofNat bs[i].toNat))]
        rw [ih (i + 1) (by omega) ("".push (Char.ofNat bs[i].toNat))]
        simp [String.toList_push, List.append_assoc]
      · simp only [hu, Bool.false_eq_true, ↓reduceIte]
        rw [ih (i + 1) (by omega) (((acc.push '%').push (hexDigit (bs[i] >>> 4))).push (hexDigit (bs[i] &&& 0x0F)))]
        rw [ih (i + 1) (by omega) ((("".push '%').push (hexDigit (bs[i] >>> 4))).push (hexDigit (bs[i] &&& 0x0F)))]
        simp [String.toList_push, List.append_assoc]

private theorem isUnreserved_props {b : UInt8} (h : isUnreserved b = true) :
    b.toNat ≤ 126 ∧ b.toNat ≠ 37 := by
  unfold isUnreserved at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

private theorem asciiChar_toUTF8 (b : UInt8) (hle : b.toNat ≤ 127) :
    (Char.ofNat b.toNat).toString.toUTF8 = ByteArray.mk #[b] := by
  have hv : b.toNat.isValidChar := by simp [Nat.isValidChar]; omega
  have htn : (Char.ofNat b.toNat).val.toNat = b.toNat := by
    simp [Char.ofNat, hv, Char.ofNatAux]
  apply ByteArray.ext
  have hstr : (Char.ofNat b.toNat).toString = String.ofList [Char.ofNat b.toNat] := rfl
  rw [String.toUTF8, hstr, String.toByteArray_ofList, List.utf8Encode_singleton]
  simp [String.utf8EncodeChar, htn, hle]

private theorem byteArray_append_singleton (acc : ByteArray) (b : UInt8) :
    acc ++ ByteArray.mk #[b] = acc.push b := by
  apply ByteArray.ext
  simp

private theorem decodeBytes_nonPct (c : Char) (rest : List Char) (acc : ByteArray) (hne : c ≠ '%') :
    decodeBytes (c :: rest) acc = decodeBytes rest (acc ++ c.toString.toUTF8) := by
  cases rest with
  | nil => simp [decodeBytes]
  | cons c₁ r₁ =>
      cases r₁ with
      | nil => simp [decodeBytes]
      | cons c₂ r₂ => simp [decodeBytes, hne]

private theorem decodeBytes_encodeUTF8Loop (bs : ByteArray) :
    ∀ (i : Nat) (acc : ByteArray),
      i ≤ bs.size →
      (decodeBytes (encodeUTF8Loop bs i "").toList acc).data.toList =
        acc.data.toList ++ bs.data.toList.drop i := by
  intro i
  induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc hi
      have heq : i = bs.size := by omega
      subst heq
      rw [encodeUTF8Loop.eq_1]
      have hnot : ¬ bs.size < bs.size := Nat.lt_irrefl _
      have hdrop : bs.data.toList.drop bs.size = [] := by
        rw [List.drop_eq_nil_iff]
        exact Nat.le_refl _
      have hempty : "".toList = [] := rfl
      simp only [hnot, ↓reduceDIte, hdrop, hempty, List.append_nil]
      rw [decodeBytes.eq_def]
  | succ _ ih =>
      intro acc hi
      have hlt : i < bs.size := by omega
      have hltL : i < bs.data.toList.length := by
        rw [Array.length_toList]
        exact hlt
      have hdrop : bs.data.toList.drop i = bs[i] :: bs.data.toList.drop (i + 1) :=
        (List.getElem_cons_drop hltL).symm
      have hstep : encodeUTF8Loop bs i "" =
          encodeUTF8Loop bs (i + 1)
            (if isUnreserved bs[i] then "".push (Char.ofNat bs[i].toNat)
             else (("".push '%').push (hexDigit (bs[i] >>> 4))).push (hexDigit (bs[i] &&& 0x0F))) := by
        rw [encodeUTF8Loop.eq_1 (acc := "")]
        simp only [hlt, ↓reduceDIte]
        rfl
      rw [hstep, encodeUTF8Loop_toList]
      by_cases hu : isUnreserved bs[i]
      · have ⟨hle, hne37⟩ := isUnreserved_props hu
        have hnePct : Char.ofNat bs[i].toNat ≠ '%' := by
          intro hc
          have htn : (Char.ofNat bs[i].toNat).toNat = '%'.toNat := congrArg Char.toNat hc
          have hv : bs[i].toNat.isValidChar := by simp [Nat.isValidChar]; omega
          simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat] at htn
          exact hne37 htn
        have hlist : ("".push (Char.ofNat bs[i].toNat)).toList = [Char.ofNat bs[i].toNat] := by
          simp
        simp only [hu, ↓reduceIte, hlist, List.singleton_append]
        rw [decodeBytes_nonPct _ _ _ hnePct, asciiChar_toUTF8 _ (by omega), byteArray_append_singleton]
        have hih := ih (i + 1) (by omega) (acc.push bs[i]) (by omega)
        rw [hih]
        simp [hdrop, ByteArray.push, List.append_assoc]
      · have hlist : ((("".push '%').push (hexDigit (bs[i] >>> 4))).push (hexDigit (bs[i] &&& 0x0F))).toList =
            ['%', hexDigit (bs[i] >>> 4), hexDigit (bs[i] &&& 0x0F)] := by
          simp [String.toList_push]
        simp only [hu, Bool.false_eq_true, ↓reduceIte, hlist, List.cons_append, List.nil_append]
        have hhi := unhex_hexDigit (bs[i] >>> 4) (uint8_shiftRight4_lt bs[i])
        have hlo := unhex_hexDigit (bs[i] &&& 0x0F) (uint8_and15_lt bs[i])
        have hrec := uint8_recombine bs[i]
        rw [decodeBytes.eq_def]
        simp only [hhi, hlo, hrec]
        have hih := ih (i + 1) (by omega) (acc.push bs[i]) (by omega)
        rw [hih]
        simp [hdrop, ByteArray.push, List.append_assoc]

@[simp] theorem decodeSeg_encodeSeg (s : String) : decodeSeg (encodeSeg s) = s := by
  unfold decodeSeg encodeSeg
  have hdata := decodeBytes_encodeUTF8Loop s.toUTF8 0 .empty (Nat.zero_le _)
  simp only [List.drop_zero, ByteArray.empty] at hdata
  have hba : decodeBytes (encodeUTF8Loop s.toUTF8 0 "").toList .empty = s.toUTF8 := by
    apply ByteArray.ext
    exact congrArg List.toArray (by simpa using hdata)
  rw [hba, String.toUTF8, String.fromUTF8?]
  rw [dif_pos s.isValidUTF8]
  rfl

private def joinSlash : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ "/" ++ joinSlash ss

private theorem joinSlash_safe :
    ∀ (segs : List String),
      (∀ s ∈ segs, s.toList.all isSafePathBodyChar = true) →
      (joinSlash segs).toList.all isSafePathBodyChar = true
  | [], _ => rfl
  | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by
      have hslash : isSafePathBodyChar '/' = true := rfl
      have ih := joinSlash_safe (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      simp [joinSlash, String.toList_append, hs s₁ (by simp), hslash, ih]

private theorem dropWhile_slash_safe :
    ∀ (cs : List Char),
      cs.all isSafePathBodyChar = true →
      hasSafeUrlPrefix ('/' :: cs.dropWhile (· == '/')) = true ∧
      ('/' :: cs.dropWhile (· == '/')).all isSafeUrlChar = true
  | [], _ => ⟨rfl, rfl⟩
  | c :: rest, hcs => by
      simp only [List.all_cons, Bool.and_eq_true] at hcs
      rcases hcs with ⟨hc, hrest⟩
      by_cases hslash : (c == '/') = true
      · simpa [List.dropWhile, hslash] using dropWhile_slash_safe rest hrest
      · have hcf : (c == '/') = false := Bool.eq_false_iff.2 hslash
        simp only [List.dropWhile, hcf]
        unfold isSafePathBodyChar at hc
        rcases Bool.and_eq_true_iff.1 hc with ⟨hcUrl, hcNot92⟩
        have hnotBs : (c != '\\') = true := by
          rw [bne_iff_ne]
          intro heq; subst heq; simp at hcNot92
        have hnotSlash : (c != '/') = true := by
          rw [bne_iff_ne]
          intro heq; subst heq; simp at hcf
        have hrestUrl : rest.all isSafeUrlChar = true := by
          rw [List.all_eq_true] at hrest ⊢
          intro x hx
          exact (Bool.and_eq_true_iff.1 (hrest x hx)).1
        have hslashUrl : isSafeUrlChar '/' = true := rfl
        exact ⟨by simp [hasSafeUrlPrefix, hnotSlash, hnotBs],
               by simp [List.all_cons, hslashUrl, hcUrl, hrestUrl]⟩

def Router.toURL {α} [Router α] (a : α) : String :=
  String.ofList ('/' :: (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/'))

@[simp] theorem Router.isSafeUrl_toURL {α : Type} [Router α] (a : α) :
    isSafeUrl (Router.toURL a) = true := by
  unfold Router.toURL isSafeUrl
  rw [String.toList_ofList]
  have hbody : (joinSlash ((Router.print a).map encodeSeg)).toList.all isSafePathBodyChar = true := by
    apply joinSlash_safe
    intro s hs
    rcases List.mem_map.1 hs with ⟨raw, _, rfl⟩
    exact encodeSeg_safe raw
  have ⟨hpfx, hall⟩ := dropWhile_slash_safe _ hbody
  exact Bool.and_eq_true_iff.2 ⟨hpfx, hall⟩

def Router.toUrl {α : Type} [Router α] (a : α) : Url :=
  ⟨Router.toURL a, Router.isSafeUrl_toURL a⟩

def stripQueryAndHash (path : String) : String :=
  String.ofList (path.toList.takeWhile fun c => c != '#' && c != '?')

def splitSlashChars : List Char → List Char → List String
  | [],      acc => [String.ofList acc.reverse]
  | c :: cs, acc =>
      if c == '/' then String.ofList acc.reverse :: splitSlashChars cs []
      else splitSlashChars cs (c :: acc)

def splitSlash (s : String) : List String :=
  splitSlashChars s.toList []

def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse (((splitSlash (stripQueryAndHash path)).filter (· ≠ "")).map decodeSeg)

private theorem isPctEncodedChar_props {c : Char} (h : isPctEncodedChar c = true) :
    c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' := by
  unfold isPctEncodedChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> simp at h

private theorem encodeUTF8Loop_nonEmpty (bs : ByteArray) (i : Nat) (hlt : i < bs.size) :
    (encodeUTF8Loop bs i "").toList ≠ [] := by
  rw [encodeUTF8Loop.eq_1 (acc := "")]
  simp only [hlt, ↓reduceDIte]
  by_cases hu : isUnreserved bs[i]
  · simp only [hu, ↓reduceIte]
    rw [encodeUTF8Loop_toList]
    simp
  · simp only [hu, Bool.false_eq_true, ↓reduceIte]
    rw [encodeUTF8Loop_toList]
    simp

private theorem encodeSeg_nonEmpty {s : String} (hne : s ≠ "") : encodeSeg s ≠ "" := by
  intro heq
  have hsz : 0 < s.toUTF8.size := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hemp : s.toUTF8 = ByteArray.empty := by
      apply ByteArray.ext
      apply Array.ext'
      have hlen : s.toUTF8.data.toList.length = 0 := by
        rw [Array.length_toList]
        exact hz
      exact List.eq_nil_of_length_eq_zero hlen
    apply hne
    apply String.ext_iff.2
    simpa [String.toUTF8] using hemp
  have hneEnc := encodeUTF8Loop_nonEmpty s.toUTF8 0 hsz
  apply hneEnc
  change (encodeSeg s).toList = []
  rw [heq]; rfl

private theorem isPctOrSlash_props {c : Char} (h : (isPctEncodedChar c || c == '/') = true) :
    c ≠ '#' ∧ c ≠ '?' := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with hp | rfl
  · exact ⟨(isPctEncodedChar_props hp).2.2, (isPctEncodedChar_props hp).2.1⟩
  · exact ⟨by decide, by decide⟩

private theorem takeWhile_pctOrSlash {cs : List Char}
    (h : cs.all (fun c => isPctEncodedChar c || c == '/') = true) :
    cs.takeWhile (fun c => c != '#' && c != '?') = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have ⟨hh, hq⟩ := isPctOrSlash_props h.1
      have hpred : (c != '#' && c != '?') = true := by simp [bne_iff_ne, hh, hq]
      simp [List.takeWhile, hpred, ih h.2]

private theorem joinSlash_pctOrSlash :
    ∀ (segs : List String),
      (∀ s ∈ segs, s.toList.all isPctEncodedChar = true) →
      (joinSlash segs).toList.all (fun c => isPctEncodedChar c || c == '/') = true
  | [], _ => rfl
  | [s], hs => by
      have hp := hs s (by simp)
      rw [List.all_eq_true] at hp ⊢
      intro c hc; simp [hp c hc]
  | s₁ :: s₂ :: rest, hs => by
      have h1 := hs s₁ (by simp)
      have h2 := joinSlash_pctOrSlash (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      have h1' : s₁.toList.all (fun c => isPctEncodedChar c || c == '/') = true := by
        rw [List.all_eq_true] at h1 ⊢; intro c hc; simp [h1 c hc]
      simp [joinSlash, String.toList_append, h1', h2]

private theorem splitSlashChars_append_nonSlash (cs rest acc : List Char)
    (hno : cs.all (· != '/') = true) :
    splitSlashChars (cs ++ rest) acc = splitSlashChars rest (acc.reverse ++ cs).reverse := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hno
      have hcf : (c == '/') = false := beq_eq_false_iff_ne.2 hno.1
      simp only [List.cons_append, splitSlashChars, hcf, Bool.false_eq_true, ↓reduceIte]
      rw [ih (c :: acc) hno.2]
      simp [List.reverse_cons, List.append_assoc]

private theorem splitSlashChars_joinSlash :
    ∀ (segs : List String),
      (∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true) →
      (splitSlashChars (joinSlash segs).toList []).filter (· ≠ "") = segs
  | [], _ => rfl
  | [s], hs => by
      have ⟨hne, _⟩ := hs s (by simp)
      have hno : s.toList.all (· != '/') = true := by
        have hp := (hs s (by simp)).2
        rw [List.all_eq_true] at hp ⊢
        intro c hc
        exact bne_iff_ne.2 (isPctEncodedChar_props (hp c hc)).1
      have hsp := splitSlashChars_append_nonSlash s.toList [] [] hno
      simp only [List.append_nil] at hsp
      have hres : splitSlashChars s.toList [] = [s] := by
        simpa [splitSlashChars, String.ofList_toList] using hsp
      simp [joinSlash, hres, hne]
  | s₁ :: s₂ :: rest, hs => by
      have ⟨hne1, hpct1⟩ := hs s₁ (by simp)
      have hno : s₁.toList.all (· != '/') = true := by
        rw [List.all_eq_true] at hpct1 ⊢
        intro c hc
        exact bne_iff_ne.2 (isPctEncodedChar_props (hpct1 c hc)).1
      have hjoin : (joinSlash (s₁ :: s₂ :: rest)).toList =
          s₁.toList ++ ('/' :: (joinSlash (s₂ :: rest)).toList) := by
        simp [joinSlash, String.toList_append]
      rw [hjoin, splitSlashChars_append_nonSlash s₁.toList _ [] hno]
      simp only [List.reverse_nil, List.nil_append, List.reverse_reverse, splitSlashChars,
        beq_self_eq_true, ↓reduceIte, String.ofList_toList, List.filter_cons]
      rw [if_pos (decide_eq_true hne1)]
      congr 1
      exact splitSlashChars_joinSlash (s₂ :: rest) (fun x hx => hs x (by simp [hx]))

/-- End-to-end URL round-trip: whenever every printed path segment is non-empty,
    `Router.fromURL (Router.toURL a) = some a` (including UTF-8 percent-encoding/decoding
    of spaces, `/`, `?`, `#`, and arbitrary Unicode). -/
theorem Router.fromURL_toURL {α : Type} [Router α] (a : α)
    (hne : ∀ s ∈ Router.print a, s ≠ "") :
    Router.fromURL (Router.toURL a) = some a := by
  unfold Router.fromURL Router.toURL splitSlash stripQueryAndHash
  rw [String.toList_ofList]
  have hpct : ∀ s ∈ (Router.print a).map encodeSeg, s.toList.all isPctEncodedChar = true := by
    intro s hs
    rcases List.mem_map.1 hs with ⟨raw, _, rfl⟩
    exact encodeSeg_pct raw
  have hnonempty : ∀ s ∈ (Router.print a).map encodeSeg, s ≠ "" ∧ s.toList.all isPctEncodedChar = true := by
    intro s hs
    rcases List.mem_map.1 hs with ⟨raw, hraw, rfl⟩
    exact ⟨encodeSeg_nonEmpty (hne raw hraw), encodeSeg_pct raw⟩
  have hdrop : (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/') =
      (joinSlash ((Router.print a).map encodeSeg)).toList := by
    cases hxs : (Router.print a).map encodeSeg with
    | nil => rfl
    | cons x xs =>
        have hxne : x ≠ "" := (hnonempty x (by simp [hxs])).1
        have hxpct : x.toList.all isPctEncodedChar = true := (hnonempty x (by simp [hxs])).2
        cases hxl : x.toList with
        | nil =>
            exfalso; apply hxne
            have := congrArg String.ofList hxl
            simpa [String.ofList_toList] using this
        | cons c cs =>
            have hcPct : isPctEncodedChar c = true := by
              rw [hxl] at hxpct; simp at hxpct; exact hxpct.1
            have hcSlash : (c == '/') = false := beq_eq_false_iff_ne.2 (isPctEncodedChar_props hcPct).1
            have hj : (joinSlash (x :: xs)).toList = c :: (cs ++ match xs with
                | [] => []
                | y :: ys => '/' :: (joinSlash (y :: ys)).toList) := by
              cases xs with
              | nil => simp [joinSlash, hxl]
              | cons y ys => simp [joinSlash, String.toList_append, hxl]
            rw [hj, List.dropWhile_cons, if_neg (by simp [hcSlash]), ← hj]
  rw [hdrop, String.toList_ofList]
  have htw := takeWhile_pctOrSlash (joinSlash_pctOrSlash ((Router.print a).map encodeSeg) hpct)
  have hslashPred : ('/' != '#' && '/' != '?') = true := rfl
  rw [List.takeWhile_cons, if_pos hslashPred, htw]
  have hsplit : splitSlashChars ('/' :: (joinSlash ((Router.print a).map encodeSeg)).toList) [] =
      "" :: splitSlashChars (joinSlash ((Router.print a).map encodeSeg)).toList [] := rfl
  rw [hsplit]
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, splitSlashChars_joinSlash _ hnonempty]
  simp [List.map_map, Function.comp_def, decodeSeg_encodeSeg, Router.round_trip]

/-- Canonicality: any URL segment list parsed to `a` re-parses from `Router.print a` to `some a`. -/
theorem Router.canonical_reparse {α : Type} [Router α] (segs : List String) (a : α)
    (_h : Router.parse segs = some a) :
    Router.parse (Router.print a) = some a :=
  Router.round_trip a

class ToHref (α : Type) where
  toUrl : α → Url

def ToHref.toHref {α : Type} [ToHref α] (v : α) : String := (ToHref.toUrl v).raw

instance : ToHref Url := ⟨id⟩
instance [Router R] : ToHref R := ⟨Router.toUrl⟩

@[simp] theorem ToHref.toUrl_url (u : Url) : ToHref.toUrl u = u := rfl
@[simp] theorem ToHref.toHref_url (u : Url) : ToHref.toHref u = u.raw := rfl
@[simp] theorem ToHref.toHref_route {R : Type} [Router R] (r : R) :
    ToHref.toHref r = Router.toURL r := rfl
@[simp] theorem ToHref.isSafeUrl_toHref {α : Type} [ToHref α] (v : α) :
    isSafeUrl (ToHref.toHref v) = true := (ToHref.toUrl v).safe

syntax routeEnumAlt := ident (" => " str)?
syntax (name := routeEnumCmd) "route_enum " ident " where " sepBy1IndentSemicolon(routeEnumAlt) : command

open Lean in
macro_rules
  | `(route_enum $t:ident where $[$alts:routeEnumAlt]*) => do
      let toSegId   := mkIdent (t.getId ++ `toSeg)
      let fromSegId := mkIdent (t.getId ++ `fromSeg)
      let rtId      := mkIdent (t.getId ++ `round_trip)
      let mut ctors : Array (TSyntax `ident) := #[]
      let mut ctorPats : Array (TSyntax `term) := #[]
      let mut slugs : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      for alt in alts do
        let (c, seg) ← match alt with
          | `(routeEnumAlt| $c:ident $[=> $seg:str]?) => pure (c, seg)
          | _ => Macro.throwErrorAt alt "route_enum: expected constructor name with optional `=> \"slug\"`"
        let ctorId := mkIdent (t.getId ++ c.getId)
        let slugLit : TSyntax `term := match seg with
          | some s => ⟨s.raw⟩
          | none   => quote (toString c.getId)
        ctors     := ctors.push c
        ctorPats  := ctorPats.push ctorId
        slugs     := slugs.push slugLit
        parseRhss := parseRhss.push (← `(some $ctorId))
      let parsePatsAll := slugs.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      `(inductive $t:ident where
          $[| $ctors:ident]*
        deriving Repr, DecidableEq, Inhabited
        def $toSegId:ident (x : $t) : String :=
          match x with
          $[| $ctorPats:term => $slugs:term]*
        def $fromSegId:ident (s : String) : Option $t :=
          match s with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $fromSegId:ident ($toSegId:ident a) = some a := by
          intro a; cases a <;> rfl
        instance : RouteParam $t:ident := ⟨$toSegId, $fromSegId, $rtId⟩)

syntax routeBinder := "(" ident (" : " term)? ")"
syntax routeAlt := ("*")? ident (routeBinder)* (" => " str)?
syntax (name := routerCmd) "router " ident " where " sepBy1IndentSemicolon(routeAlt) : command

open Lean in
private def parseRouteBinder (b : TSyntax ``routeBinder) : MacroM (TSyntax `ident × TSyntax `term) := do
  match b with
  | `(routeBinder| ($id:ident : $ty:term)) => pure (id, ty)
  | `(routeBinder| ($id:ident))            => pure (id, ← `(String))
  | _ => Macro.throwErrorAt b "router: expected `(param)` or `(param : Type)`"

open Lean in
private def routePatternsOverlap (p₁ p₂ : Array (Option String)) : Bool :=
  p₁.size == p₂.size &&
  (List.range p₁.size).all fun i =>
    match p₁[i]!, p₂[i]! with
    | some a, some b => a == b
    | _, _           => true

open Lean in
macro_rules
  | `(router $t:ident where $[$alts:routeAlt]*) => do
      let printId := mkIdent (t.getId ++ `print)
      let parseId := mkIdent (t.getId ++ `parse)
      let rtId    := mkIdent (t.getId ++ `round_trip)
      let mut ctorNames : Array (TSyntax `ident) := #[]
      let mut ctorBs    : Array (Array (TSyntax `ident)) := #[]
      let mut ctorBts   : Array (Array (TSyntax `term))  := #[]
      let mut printPats : Array (TSyntax `term) := #[]
      let mut printRhss : Array (TSyntax `term) := #[]
      let mut parsePats : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      let mut patShapes : Array (TSyntax `ident × Array (Option String)) := #[]
      let mut markedCtor : Option (TSyntax `ident) := none
      for alt in alts do
        let (marked, c, rawBinders, seg) ← (match alt with
          | `(routeAlt| * $c:ident $[$rbs:routeBinder]* $[=> $seg:str]?) =>
              pure (true,  c, rbs, seg)
          | `(routeAlt| $c:ident $[$rbs:routeBinder]* $[=> $seg:str]?) =>
              pure (false, c, rbs, seg)
          | _ => Macro.throwErrorAt alt "router: couldn't read this route. Each one is a constructor name, then zero or more params like (slug : String) or (slug), then an optional path like \"/books/:id\"; mark the not-found fallback with a leading *.")
        let explicitBinders ← rawBinders.mapM parseRouteBinder
        let rawSegs : Array String := match seg with
          | some s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray
          | none   => #[toString c.getId]
        let hasPlaceholders := rawSegs.any (·.startsWith ":")
        let mut bs     : Array (TSyntax `ident) := #[]
        let mut btsArr : Array (TSyntax `term)  := #[]
        if hasPlaceholders then
          let mut seenPlaceholders : Array String := #[]
          for rs in rawSegs do
            if rs.startsWith ":" then
              let pname := String.ofList (rs.toList.drop 1)
              if pname.isEmpty then
                Macro.throwErrorAt alt "router: empty `:` parameter in route path"
              if seenPlaceholders.contains pname then
                Macro.throwErrorAt alt s!"router: duplicate `:{pname}` parameter in route path"
              seenPlaceholders := seenPlaceholders.push pname
              match explicitBinders.find? (fun (b, _) => toString b.getId == pname) with
              | some (b, bt) =>
                  bs     := bs.push b
                  btsArr := btsArr.push bt
              | none =>
                  bs     := bs.push (mkIdent (Name.mkSimple pname))
                  btsArr := btsArr.push (← `(String))
          for (b, _) in explicitBinders do
            unless seenPlaceholders.contains (toString b.getId) do
              Macro.throwErrorAt b s!"router: parameter `{b.getId}` is not referenced as `:{b.getId}` in the route path"
        else
          bs     := explicitBinders.map (·.1)
          btsArr := explicitBinders.map (·.2)
        let ctorId := mkIdent (t.getId ++ c.getId)
        let patShape : Array (Option String) :=
          if hasPlaceholders then
            rawSegs.map fun rs => if rs.startsWith ":" then none else some rs
          else
            rawSegs.map some ++ Array.replicate bs.size none
        for (prevC, prevPat) in patShapes do
          if routePatternsOverlap prevPat patShape then
            Macro.throwErrorAt c
              s!"router: route `{c.getId}` overlaps with earlier route `{prevC.getId}` (both match {patShape.size}-segment paths)"
        patShapes := patShapes.push (c, patShape)
        let (printSeg, parseSeg) ← if hasPlaceholders then do
          let mut pr : Array (TSyntax `term) := #[]
          let mut pa : Array (TSyntax `term) := #[]
          for rs in rawSegs do
            if rs.startsWith ":" then
              let pname := String.ofList (rs.toList.drop 1)
              let some bId := bs.find? (fun b => toString b.getId == pname)
                | Macro.throwErrorAt alt "router: internal missing param"
              let bTerm : TSyntax `term := ⟨bId.raw⟩
              pr := pr.push (← `(RouteParam.toSeg $bTerm))
              pa := pa.push bTerm
            else
              pr := pr.push (quote rs)
              pa := pa.push (quote rs)
          pure (pr, pa)
        else do
          let segs : Array (TSyntax `term) := rawSegs.map (quote ·)
          let printTerms ← bs.mapM fun b => do
            let bTerm : TSyntax `term := ⟨b.raw⟩
            `(RouteParam.toSeg $bTerm)
          pure (segs ++ printTerms, segs ++ bs.map (fun b => (⟨b.raw⟩ : TSyntax `term)))
        let mut parseBody : TSyntax `term ← `(some ($ctorId $bs*))
        for i in (List.range bs.size).reverse do
          let bTerm : TSyntax `term := ⟨bs[i]!.raw⟩
          let bt := btsArr[i]!
          parseBody ← `(match (RouteParam.fromSeg $bTerm : Option $bt) with | some $bTerm => $parseBody | none => none)
        if marked then
          if bs.size != 0 then
            Macro.throwErrorAt c "router: the not-found route (marked `*`) must take no arguments. It is the fallback for any unmatched URL, so there's nothing to parse into it."
          markedCtor := some c
        ctorNames := ctorNames.push c
        ctorBs    := ctorBs.push bs
        ctorBts   := ctorBts.push btsArr
        printPats := printPats.push (← `($ctorId $bs*))
        printRhss := printRhss.push (← `([$printSeg,*]))
        parsePats := parsePats.push (← `([$parseSeg,*]))
        parseRhss := parseRhss.push parseBody
      let parsePatsAll := parsePats.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      let inhCmd : TSyntax `command ← match markedCtor with
        | some mc => `(instance : Inhabited $t := ⟨$(mkIdent (t.getId ++ mc.getId))⟩)
        | none    => `(deriving instance Inhabited for $t)
      `(inductive $t:ident where
          $[| $ctorNames:ident $[($ctorBs:ident : $ctorBts:term)]*]*
        deriving Repr, DecidableEq
        $inhCmd:command
        def $printId:ident (r : $t) : List String :=
          match r with
          $[| $printPats:term => $printRhss:term]*
        def $parseId:ident (p : List String) : Option $t :=
          match p with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $parseId:ident ($printId:ident a) = some a := by
          intro a; cases a <;>
            (try simp only [$printId:ident, $parseId:ident, RouteParam.round_trip, RouteParam.toSeg_string]) <;>
            (try simp [$printId:ident, $parseId:ident, RouteParam.round_trip])
        instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩)

router Route where
  home => ""
  about
  post (slug : String) => "posts"
  user (name : String) => "users"

router TypedRoute where
  page (n : Nat) => "page"
  delta (i : Int) => "delta"
  item (slug : String) (n : Nat) => "items"

end Qed
