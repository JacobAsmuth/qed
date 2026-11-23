import Qed.Router.Basic
import Qed.Router.Macro
import Qed.Json
import Qed.Proto

namespace Qed

private def decodeRouteSegs [Router R] (segs : List String) : Except String R :=
  (Router.parse segs).elim (.error "invalid route") .ok

instance [Router R] : ToJson R := .ofEquiv Router.print
instance [Router R] : FromJson R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulJson R :=
  .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]
instance [Router R] : NonNullJson R := ⟨nofun⟩

instance [Router R] : ToProto R := .ofEquiv Router.print
instance [Router R] : FromProto R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulProto R :=
  .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]

instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := by
    have h₁ := LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    have h₂ := LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    rw [h] at h₁
    rw [h₁] at h₂
    exact Except.ok.inj h₂

private theorem unhex_hexDigit (n : UInt8) (hn : n.toNat < 16) : unhex (hexDigit n) = some n := by
  simp [unhex, hexDigit, unhexNat?_hexDigitUpper hn, UInt8.ofNat_toNat]

private theorem bitvec8_nibbles : ∀ x : BitVec 8,
    (((x >>> 4) <<< 4) ||| (x &&& 0x0F#8) = x) ∧ (x >>> 4#8).toNat < 16 ∧ (x &&& 0x0F#8).toNat < 16 := by
  decide

private theorem encodeUTF8Loop_toList (bs : ByteArray) :
    ∀ (i : Nat) (acc : String),
      (encodeUTF8Loop bs i acc).toList = acc.toList ++ (encodeUTF8Loop bs i "").toList := by
  intro i; induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc; have hnot : ¬ i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]; simp [hnot]
  | succ _ ih =>
      intro acc; have hlt : i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]
      simp only [hlt, ↓reduceDIte]
      by_cases hu : isUnreserved bs[i] <;>
        (first | rw [if_pos hu, if_pos hu] | rw [if_neg hu, if_neg hu]) <;>
        (conv => rhs; rw [ih (i + 1) (by omega)]
         rw [ih (i + 1) (by omega)]
         simp [String.toList_push, List.append_assoc])

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
    ∀ (i : Nat) (acc : ByteArray), i ≤ bs.size →
      (decodeBytes (encodeUTF8Loop bs i "").toList acc).data.toList =
        acc.data.toList ++ bs.data.toList.drop i := by
  intro i; induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc hi
      have heq : i = bs.size := by omega
      subst heq
      rw [encodeUTF8Loop.eq_1, dif_neg (Nat.lt_irrefl _)]
      simp [List.drop_eq_nil_iff, decodeBytes]
  | succ _ ih =>
      intro acc hi; have hlt : i < bs.size := by omega
      have hdrop : bs.data.toList.drop i = bs[i] :: bs.data.toList.drop (i + 1) :=
        (List.getElem_cons_drop (by simpa using hlt)).symm
      suffices h : decodeBytes (encodeUTF8Loop bs i "").toList acc =
          decodeBytes (encodeUTF8Loop bs (i + 1) "").toList (acc.push bs[i]) by
        rw [h, ih (i + 1) (by omega) (acc.push bs[i]) (by omega), hdrop]
        simp [ByteArray.push, List.append_assoc]
      rw [encodeUTF8Loop.eq_1 (acc := ""), dif_pos hlt, encodeUTF8Loop_toList]
      by_cases hu : isUnreserved bs[i]
      · have ⟨hle, hne37⟩ := isUnreserved_props hu
        have hnePct : Char.ofNat bs[i].toNat ≠ '%' := fun hc => hne37 (by
          have := congrArg Char.toNat hc
          have hv : bs[i].toNat.isValidChar := by simp [Nat.isValidChar]; omega
          simpa [Char.ofNat, hv, Char.ofNatAux, Char.toNat] using this)
        simp only [hu, ↓reduceIte, String.toList_push, String.toList_empty, List.nil_append, List.singleton_append]
        rw [decodeBytes_nonPct _ _ _ hnePct, asciiChar_toUTF8 _ (by omega), byteArray_append_singleton]
      · have ⟨hrecBV, hhiLt, hloLt⟩ := bitvec8_nibbles bs[i].toBitVec
        have hrec : ((bs[i] >>> 4) <<< 4) ||| (bs[i] &&& 0x0F) = bs[i] := UInt8.eq_of_toBitVec_eq hrecBV
        simp only [hu, Bool.false_eq_true, ↓reduceIte, String.toList_push, String.toList_empty,
          List.nil_append, List.cons_append]
        rw [decodeBytes.eq_def]
        simp only [unhex_hexDigit (bs[i] >>> 4) hhiLt, unhex_hexDigit (bs[i] &&& 0x0F) hloLt, hrec]

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

private theorem isPctEncodedChar_props {c : Char} (h : isPctEncodedChar c = true) :
    c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' := by
  unfold isPctEncodedChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> simp at h

private theorem encodeUTF8Loop_nonEmpty (bs : ByteArray) (i : Nat) (hlt : i < bs.size) :
    (encodeUTF8Loop bs i "").toList ≠ [] := by
  rw [encodeUTF8Loop.eq_1 (acc := "")]; simp only [hlt, ↓reduceDIte]
  split <;> (rw [encodeUTF8Loop_toList]; simp)

private theorem encodeSeg_nonEmpty {s : String} (hne : s ≠ "") : encodeSeg s ≠ "" := by
  have hsz : 0 < s.toUTF8.size := Nat.pos_of_ne_zero fun hz => hne (by
    have hemp : s.toUTF8 = ByteArray.empty :=
      ByteArray.ext (Array.ext' (List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact hz)))
    exact String.ext_iff.2 (by simpa [String.toUTF8] using hemp))
  intro heq; exact encodeUTF8Loop_nonEmpty s.toUTF8 0 hsz (by change (encodeSeg s).toList = []; rw [heq]; rfl)

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

private theorem pct_no_slash {s : String} (h : s.toList.all isPctEncodedChar = true) :
    s.toList.all (· != '/') = true :=
  List.all_eq_true.2 fun c hc => bne_iff_ne.2 (isPctEncodedChar_props (List.all_eq_true.1 h c hc)).1

private theorem splitSlashChars_joinSlash :
    ∀ (segs : List String),
      (∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true) →
      (splitSlashChars (joinSlash segs).toList []).filter (· ≠ "") = segs
  | [], _ => rfl
  | [s], hs => by
      have ⟨hne, hp⟩ := hs s (by simp)
      have hsp := splitSlashChars_append_nonSlash s.toList [] [] (pct_no_slash hp)
      simp only [List.append_nil] at hsp
      have hres : splitSlashChars s.toList [] = [s] := by simpa [splitSlashChars, String.ofList_toList] using hsp
      simp [joinSlash, hres, hne]
  | s₁ :: s₂ :: rest, hs => by
      have ⟨hne1, hp1⟩ := hs s₁ (by simp)
      have hjoin : (joinSlash (s₁ :: s₂ :: rest)).toList = s₁.toList ++ ('/' :: (joinSlash (s₂ :: rest)).toList) := by
        simp [joinSlash, String.toList_append]
      rw [hjoin, splitSlashChars_append_nonSlash s₁.toList _ [] (pct_no_slash hp1)]
      simp only [List.reverse_nil, List.nil_append, List.reverse_reverse, splitSlashChars,
        beq_self_eq_true, ↓reduceIte, String.ofList_toList, List.filter_cons, decide_eq_true hne1]
      congr 1; exact splitSlashChars_joinSlash (s₂ :: rest) (fun x hx => hs x (by simp [hx]))

/-- End-to-end URL round-trip: whenever every printed path segment is non-empty,
    `Router.fromURL (Router.toURL a) = some a` (including UTF-8 percent-encoding/decoding
    of spaces, `/`, `?`, `#`, and arbitrary Unicode). -/
theorem Router.fromURL_toURL {α : Type} [Router α] (a : α)
    (hne : ∀ s ∈ Router.print a, s ≠ "") :
    Router.fromURL (Router.toURL a) = some a := by
  unfold Router.fromURL Router.toURL splitSlash stripQueryAndHash
  rw [String.toList_ofList]
  have hnonempty : ∀ s ∈ (Router.print a).map encodeSeg, s ≠ "" ∧ s.toList.all isPctEncodedChar = true := by
    intro s hs; rcases List.mem_map.1 hs with ⟨raw, hraw, rfl⟩
    exact ⟨encodeSeg_nonEmpty (hne raw hraw), encodeSeg_pct raw⟩
  have hdrop : (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/') =
      (joinSlash ((Router.print a).map encodeSeg)).toList := by
    cases hxs : (Router.print a).map encodeSeg with
    | nil => rfl
    | cons x xs =>
        have ⟨hxne, hxpct⟩ := hnonempty x (by simp [hxs])
        cases hxl : x.toList with
        | nil => exact absurd (by simpa [String.ofList_toList] using congrArg String.ofList hxl) hxne
        | cons c cs =>
            have hcSlash : (c == '/') = false := by
              have h := pct_no_slash hxpct
              rw [hxl, List.all_cons, Bool.and_eq_true] at h
              exact beq_eq_false_iff_ne.2 (bne_iff_ne.1 h.1)
            cases xs <;> simp [joinSlash, String.toList_append, hxl, hcSlash]
  rw [hdrop, String.toList_ofList]
  have hall : (joinSlash ((Router.print a).map encodeSeg)).toList.all (fun c => c != '#' && c != '?') = true :=
    joinSlash_all _ rfl _ fun s hs => List.all_eq_true.2 fun c hc => by
      have ⟨_, hq, hh⟩ := isPctEncodedChar_props (List.all_eq_true.1 (hnonempty s hs).2 c hc)
      simp [bne_iff_ne, hq, hh]
  have htw : (joinSlash ((Router.print a).map encodeSeg)).toList.takeWhile (fun c => c != '#' && c != '?') = _ :=
    list_takeWhile_eq_self _ fun c hc => List.all_eq_true.1 hall c hc
  rw [List.takeWhile_cons, if_pos (by decide : ('/' != '#' && '/' != '?') = true), htw]
  change Router.parse (((("" :: splitSlashChars (joinSlash _).toList []).filter (· ≠ "")).map decodeSeg)) = _
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, splitSlashChars_joinSlash _ hnonempty]
  simp [List.map_map, Function.comp_def, decodeSeg_encodeSeg, Router.round_trip]

/-- Canonicality: any URL segment list parsed to `a` re-parses from `Router.print a` to `some a`. -/
theorem Router.canonical_reparse {α : Type} [Router α] (segs : List String) (a : α)
    (_h : Router.parse segs = some a) :
    Router.parse (Router.print a) = some a :=
  Router.round_trip a

end Qed
