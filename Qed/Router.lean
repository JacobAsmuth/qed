import Qed.Router.Basic
import Qed.Router.Macro
import Qed.Json
import Qed.Proto

namespace Qed

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

instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := by
    have h₁ := LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    have h₂ := LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    rw [h] at h₁
    rw [h₁] at h₂
    exact Except.ok.inj h₂

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

end Qed
