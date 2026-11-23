import Qed.Router.Basic
import Qed.Router.Macro
import Qed.Json
import Qed.Proto

namespace Qed

private def decodeRouteSegs [Router R] (segs : List String) : Except String R := (Router.parse segs).elim (.error "invalid route") .ok
instance [Router R] : ToJson R := .ofEquiv Router.print
instance [Router R] : FromJson R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulJson R := .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]
instance [Router R] : NonNullJson R := ⟨nofun⟩
instance [Router R] : ToProto R := .ofEquiv Router.print
instance [Router R] : FromProto R := .ofRetract decodeRouteSegs
instance [Router R] : LawfulProto R := .ofRetract Router.print decodeRouteSegs fun r => by simp [decodeRouteSegs, Router.round_trip]
instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := Except.ok.inj <|
    (h ▸ LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)).symm.trans
      (LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _))

private theorem unhex_hexDigit (n : UInt8) (hn : n.toNat < 16) : unhex (hexDigit n) = some n := by
  simp only [unhex, hexDigit, Option.map_eq_some_iff]; exact ⟨n.toNat, unhexNat?_hexDigitUpper hn, UInt8.ofNat_toNat⟩
private theorem bitvec8_nibbles : ∀ x : BitVec 8,
    (((x >>> 4) <<< 4) ||| (x &&& 0x0F#8) = x) ∧ (x >>> 4#8).toNat < 16 ∧ (x &&& 0x0F#8).toNat < 16 := by decide
private theorem encodeUTF8Loop_toList (bs : ByteArray) (i : Nat) :
    ∀ acc, (encodeUTF8Loop bs i acc).toList = acc.toList ++ (encodeUTF8Loop bs i "").toList := by
  induction hfuel : bs.size - i generalizing i with
  | zero => intro acc; rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := "")]; simp [show ¬ i < bs.size by omega]
  | succ _ ih =>
      intro acc; have h : i < bs.size := by omega
      rw [encodeUTF8Loop.eq_1 (acc := acc), encodeUTF8Loop.eq_1 (acc := ""), dite_eq_left h, dite_eq_left h]
      by_cases hu : isUnreserved bs[i] <;>
        (simp only [hu, Bool.false_eq_true, ↓reduceIte]; conv => rhs; rw [ih (i + 1) (by omega)]
         rw [ih (i + 1) (by omega)]; simp [String.toList_push, List.append_assoc])
private theorem decodeBytes_unreserved {b : UInt8} (hu : isUnreserved b = true) (rest : List Char) (acc : ByteArray) :
    decodeBytes (Char.ofNat b.toNat :: rest) acc = decodeBytes rest (acc.push b) := by
  have ⟨hle, hne37, htn⟩ := unreserved_toNat hu
  have hne : Char.ofNat b.toNat ≠ '%' := fun h => hne37 (htn ▸ congrArg Char.toNat h)
  have hstep : decodeBytes (Char.ofNat b.toNat :: rest) acc = decodeBytes rest (acc ++ (Char.ofNat b.toNat).toString.toUTF8) := by
    cases rest with | nil => simp [decodeBytes] | cons _ r => cases r <;> simp [decodeBytes, hne]
  have hutf : (Char.ofNat b.toNat).toString.toUTF8 = ByteArray.mk #[b] := by
    apply ByteArray.ext; change (String.ofList [Char.ofNat b.toNat]).toByteArray.data = #[b]
    rw [String.toByteArray_ofList, List.utf8Encode_singleton, String.utf8EncodeChar]
    simp only [show (Char.ofNat b.toNat).val.toNat = b.toNat from htn, show b.toNat ≤ 127 by omega, ↓reduceIte, UInt8.ofNat_toNat]; rfl
  rw [hstep, hutf]; congr 1; exact ByteArray.ext (by simp [ByteArray.push])
private theorem decodeBytes_encodeUTF8Loop (bs : ByteArray) (i : Nat) :
    ∀ (acc : ByteArray), i ≤ bs.size →
      (decodeBytes (encodeUTF8Loop bs i "").toList acc).data.toList = acc.data.toList ++ bs.data.toList.drop i := by
  induction hfuel : bs.size - i generalizing i with
  | zero => intro acc hi; obtain rfl : i = bs.size := (by omega); rw [encodeUTF8Loop.eq_1, dite_eq_right (Nat.lt_irrefl _)]; simp [List.drop_eq_nil_iff, decodeBytes]
  | succ _ ih =>
      intro acc hi; have hlt : i < bs.size := (by omega)
      have hdrop : bs.data.toList.drop i = bs[i] :: bs.data.toList.drop (i + 1) := (List.getElem_cons_drop (by simpa using hlt)).symm
      suffices h : decodeBytes (encodeUTF8Loop bs i "").toList acc = decodeBytes (encodeUTF8Loop bs (i + 1) "").toList (acc.push bs[i]) by
        rw [h, ih (i + 1) (by omega) (acc.push bs[i]) (by omega), hdrop]; simp [ByteArray.push, List.append_assoc]
      rw [encodeUTF8Loop.eq_1 (acc := ""), dite_eq_left hlt, encodeUTF8Loop_toList]
      by_cases hu : isUnreserved bs[i]
      · simp only [hu, ↓reduceIte, String.toList_push, String.toList_empty, List.nil_append, List.singleton_append]; exact decodeBytes_unreserved hu _ _
      · have ⟨hrecBV, hhiLt, hloLt⟩ := bitvec8_nibbles bs[i].toBitVec
        simp only [hu, Bool.false_eq_true, ↓reduceIte, String.toList_push, String.toList_empty, List.nil_append, List.cons_append]
        rw [decodeBytes.eq_def]
        simp only [unhex_hexDigit (bs[i] >>> 4) hhiLt, unhex_hexDigit (bs[i] &&& 0x0F) hloLt]
        exact congrArg (fun x => decodeBytes _ (acc.push x)) (UInt8.eq_of_toBitVec_eq hrecBV)
@[simp] theorem decodeSeg_encodeSeg (s : String) : decodeSeg (encodeSeg s) = s := by
  have hdata := decodeBytes_encodeUTF8Loop s.toUTF8 0 .empty (Nat.zero_le _); simp only [List.drop_zero, ByteArray.empty] at hdata
  have hba : decodeBytes (encodeSeg s).toList .empty = s.toUTF8 := ByteArray.ext (congrArg List.toArray (by simpa [encodeSeg] using hdata))
  rw [decodeSeg, hba, String.toUTF8, String.fromUTF8?, dite_eq_left s.isValidUTF8]; rfl

private theorem isPctEncodedChar_props {c : Char} (h : isPctEncodedChar c = true) : c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' := by
  simp only [isPctEncodedChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> simp at h
private theorem splitSlashChars_append_pct (cs rest acc : List Char) (hp : cs.all isPctEncodedChar = true) :
    splitSlashChars (cs ++ rest) acc = splitSlashChars rest (acc.reverse ++ cs).reverse := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hp
      simp only [List.cons_append, splitSlashChars, beq_eq_false_iff_ne.2 (isPctEncodedChar_props hp.1).1, Bool.false_eq_true, ↓reduceIte]
      rw [ih (c :: acc) hp.2]; simp [List.reverse_cons, List.append_assoc]
private theorem splitSlashChars_joinSlash : ∀ (segs : List String),
    (∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true) → (splitSlashChars (joinSlash segs).toList []).filter (· ≠ "") = segs
  | [], _ => rfl
  | [s], hs => by
      have ⟨hne, hp⟩ := hs s (.head _)
      simp [joinSlash, show splitSlashChars s.toList [] = [s] by simpa [splitSlashChars, String.ofList_toList] using splitSlashChars_append_pct s.toList [] [] hp, hne]
  | s₁ :: s₂ :: rest, hs => by
      have ⟨hne1, hp1⟩ := hs s₁ (.head _)
      rw [show (joinSlash (s₁ :: s₂ :: rest)).toList = s₁.toList ++ ('/' :: (joinSlash (s₂ :: rest)).toList) by simp [joinSlash, String.toList_append],
        splitSlashChars_append_pct s₁.toList _ [] hp1]
      simp only [List.reverse_nil, List.nil_append, List.reverse_reverse, splitSlashChars, beq_self_eq_true, ↓reduceIte, String.ofList_toList, List.filter_cons, decide_eq_true hne1]
      exact congrArg (s₁ :: ·) (splitSlashChars_joinSlash (s₂ :: rest) fun x hx => hs x (.tail _ hx))
theorem Router.fromURL_toURL {α : Type} [Router α] (a : α) (hne : ∀ s ∈ Router.print a, s ≠ "") :
    Router.fromURL (Router.toURL a) = some a := by
  unfold Router.fromURL Router.toURL splitSlash stripQueryAndHash; rw [String.toList_ofList]
  let segs := (Router.print a).map encodeSeg
  have hnonempty : ∀ s ∈ segs, s ≠ "" ∧ s.toList.all isPctEncodedChar = true := fun s hs => by
    rcases List.mem_map.1 hs with ⟨raw, hraw, rfl⟩
    exact ⟨fun h => hne raw hraw (by rw [← decodeSeg_encodeSeg raw, h]; rfl), encodeSeg_pct raw⟩
  have hdrop : (joinSlash segs).toList.dropWhile (· == '/') = (joinSlash segs).toList := by
    cases hxs : segs with | nil => rfl | cons x xs =>
      have ⟨hxne, hxpct⟩ := hnonempty x (by simp [hxs])
      cases hxl : x.toList with
      | nil => exact absurd (by simpa [String.ofList_toList] using congrArg String.ofList hxl) hxne
      | cons c _ =>
          have hc := beq_eq_false_iff_ne.2 (isPctEncodedChar_props (List.all_eq_true.1 hxpct c (by simp [hxl]))).1
          cases xs <;> simp [joinSlash, String.toList_append, hxl, hc]
  have hall : (joinSlash segs).toList.all (fun c => c != '#' && c != '?') = true :=
    joinSlash_all _ rfl _ fun s hs => List.all_eq_true.2 fun c hc => by
      have ⟨_, hq, hh⟩ := isPctEncodedChar_props (List.all_eq_true.1 (hnonempty s hs).2 c hc); simp [bne_iff_ne, hq, hh]
  rw [hdrop, String.toList_ofList, List.takeWhile_cons, ite_eq_left (by decide : ('/' != '#' && '/' != '?') = true),
    list_takeWhile_eq_self _ fun c hc => List.all_eq_true.1 hall c hc]
  change Router.parse ((("" :: splitSlashChars (joinSlash segs).toList []).filter (· ≠ "")).map decodeSeg) = _
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, splitSlashChars_joinSlash _ hnonempty]
  simp [segs, List.map_map, Function.comp_def, decodeSeg_encodeSeg, Router.round_trip]
theorem Router.canonical_reparse {α : Type} [Router α] (segs : List String) (a : α) (_h : Router.parse segs = some a) :
    Router.parse (Router.print a) = some a := Router.round_trip a
end Qed
