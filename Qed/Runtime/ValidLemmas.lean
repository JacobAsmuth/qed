import Qed.View.Core
import Lean

/-! ## Pre-proved O(1) HTML Validity Lemmas
Eliminates per-component UTF-8 `String` kernel reduction for common HTML5 tags and attributes. -/

namespace Qed.ValidLemmas

theorem not_isVoidTag_or (tag : String) (b : Bool) (h : isVoidTag tag = false) :
    (!isVoidTag tag || b) = true := by rw [h]; rfl

theorem attr_nonUrl {msg : Type} (k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.attr k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem signalAttr_nonUrl {msg : Type} (n k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.signalAttr n k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem flag_safe {msg : Type} (k : String) (p : Bool) (h : isSafeAttrName k = true) :
    (Attr.flag k p : Attr msg).valid = true := h

theorem on_safe {msg : Type} (e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.on e m).valid = true := h

theorem signalOn_safe {msg : Type} (n e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.signalOn n e m).valid = true := h

theorem onValue_safe {msg : Type} (e : String) (f : String → msg) (h : isSafeAttrName e = true) :
    (Attr.onValue e f).valid = true := h

theorem valid_attr_nonUrl {msg α : Type} [ToString α] (k : String) (v : α)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Qed.attr k v : Attr msg).valid = true :=
  attr_nonUrl k (toString v) h

theorem attr_valid_dite_intro {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).valid = true) (hb : ∀ h, (b h).valid = true) :
    (dite c a b).valid = true := by
  by_cases h : c <;> simp [h, ha, hb]

theorem attr_isLocalCell_dite_eq_false {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).isLocalCell = false) (hb : ∀ h, (b h).isLocalCell = false) :
    (dite c a b).isLocalCell = false := by
  by_cases h : c <;> simp [h, ha, hb]

theorem validListIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a : c → List (Html msg)) (b : ¬c → List (Html msg))
    (ha : ∀ h, Html.validListIn ctx (a h) = true) (hb : ∀ h, Html.validListIn ctx (b h) = true) :
    Html.validListIn ctx (dite c a b) = true := by
  by_cases h : c <;> simp [h, ha, hb]

/-! ### Fast Single-Pass UTF-8 Byte Decision Helpers
Avoids repeated kernel `String.decEq` and `String.toList`/`ofList` roundtrips while preserving
all public O(1) lemma signatures. -/

private theorem char_ofNat_val_toNat (n : Nat) (h : n ≤ 127) : (Char.ofNat n).val.toNat = n := by
  have hv : Nat.isValidChar n := Or.inl (by omega)
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux]
  rfl

private theorem list_toByteArray_loop_data (bs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bs acc).data.toList = acc.data.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih => simp only [List.toByteArray.loop, ih]; simp [ByteArray.push, List.append_assoc]

private theorem utf8Encode_ascii (bs : List UInt8) (h : bs.all (fun b => decide (b.toNat ≤ 127)) = true) :
    (String.ofList (bs.map fun b => Char.ofNat b.toNat)).toByteArray.data.toList = bs := by
  rw [String.toByteArray_ofList, List.utf8Encode]
  have hloop := list_toByteArray_loop_data
    ((bs.map fun b => Char.ofNat b.toNat).flatMap String.utf8EncodeChar) ByteArray.empty
  change (List.toByteArray.loop _ ByteArray.empty).data.toList = bs
  rw [hloop]
  have hem : ByteArray.empty.data.toList = [] := rfl
  rw [hem, List.nil_append]
  clear hloop hem
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.map_cons, List.flatMap_cons]
      have hchar : (Char.ofNat b.toNat).val.toNat = b.toNat := char_ofNat_val_toNat b.toNat h.1
      have henc : String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
        unfold String.utf8EncodeChar
        have h1 : (Char.ofNat b.toNat).val.toNat ≤ 127 := by omega
        simp only [h1, ↓reduceIte]
        have h2 : UInt8.ofNat (Char.ofNat b.toNat).val.toNat = b := by
          apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
          change (Char.ofNat b.toNat).val.toNat % 256 = b.toNat
          omega
        rw [h2]
      rw [henc, List.singleton_append, ih h.2]

private theorem str_eq_of_bytes {a b : String}
    (h : a.toByteArray.data.toList = b.toByteArray.data.toList) : a = b := by
  cases a with | ofByteArray ba ha => cases b with | ofByteArray bb hb =>
  cases ba with | mk da => cases bb with | mk db =>
  cases da; cases db; cases h; rfl

private theorem ascii_toList (s : String)
    (h : s.toByteArray.data.toList.all (fun b => decide (b.toNat ≤ 127)) = true) :
    s.toList = s.toByteArray.data.toList.map (fun b => Char.ofNat b.toNat) := by
  have heq : String.ofList (s.toByteArray.data.toList.map fun b => Char.ofNat b.toNat) = s :=
    str_eq_of_bytes (utf8Encode_ascii s.toByteArray.data.toList h)
  conv => lhs; rw [← heq]
  rw [String.toList_ofList]

private def isLowerTagByte (b : UInt8) : Bool :=
  let n := b.toNat
  (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) || n == 45

private theorem lowerTagByte_props (b : UInt8) (h : isLowerTagByte b = true) :
    b.toNat ≤ 127 ∧
    ((Char.ofNat b.toNat).isAlphanum || Char.ofNat b.toNat == '-') = true ∧
    isKeyChar (Char.ofNat b.toNat) = true ∧
    asciiLowerChar (Char.ofNat b.toNat) = Char.ofNat b.toNat := by
  unfold isLowerTagByte at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hle : b.toNat ≤ 127 := by omega
  have hval : (Char.ofNat b.toNat).val.toNat = b.toNat := char_ofNat_val_toNat b.toNat hle
  have halnum : ((Char.ofNat b.toNat).isAlphanum || Char.ofNat b.toNat == '-') = true := by
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h1
    · have : (Char.ofNat b.toNat).isLower = true := by
        unfold Char.isLower
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        change 97 ≤ (Char.ofNat b.toNat).val.toNat ∧ (Char.ofNat b.toNat).val.toNat ≤ 122
        omega
      simp [Char.isAlphanum, Char.isAlpha, this]
    · have : (Char.ofNat b.toNat).isDigit = true := by
        unfold Char.isDigit
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        change 48 ≤ (Char.ofNat b.toNat).val.toNat ∧ (Char.ofNat b.toNat).val.toNat ≤ 57
        omega
      simp [Char.isAlphanum, this]
    · have : Char.ofNat b.toNat = '-' := by
        apply Char.ext; apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
        change (Char.ofNat b.toNat).val.toNat = 45; omega
      simp [this]
  have hkey : isKeyChar (Char.ofNat b.toNat) = true := by
    unfold isKeyChar
    simp only [Bool.or_eq_true] at halnum ⊢
    rcases halnum with h1 | h2
    · exact .inl (.inl (.inl (.inl h1)))
    · exact .inl (.inl (.inl (.inr h2)))
  have hlow : asciiLowerChar (Char.ofNat b.toNat) = Char.ofNat b.toNat := by
    unfold asciiLowerChar
    have hnot : ('A' ≤ Char.ofNat b.toNat && Char.ofNat b.toNat ≤ 'Z') = false := by
      rw [Bool.and_eq_false_iff]
      simp only [decide_eq_false_iff_not]
      change ¬(65 ≤ (Char.ofNat b.toNat).val.toNat) ∨ ¬((Char.ofNat b.toNat).val.toNat ≤ 90)
      omega
    simp [hnot]
  exact ⟨hle, halnum, hkey, hlow⟩

private theorem lowerBytes_core (s : String)
    (hnon : (!s.toByteArray.data.toList.isEmpty) = true)
    (hall : s.toByteArray.data.toList.all isLowerTagByte = true) :
    isSafeTagName s = true ∧
    s.toList.all isKeyChar = true ∧
    (!s.isEmpty) = true ∧
    s.toList.map asciiLowerChar = s.toList ∧
    asciiLower s = s := by
  have hascii : s.toByteArray.data.toList.all (fun b => decide (b.toNat ≤ 127)) = true :=
    List.all_eq_true.2 fun b hb => decide_eq_true (lowerTagByte_props b (List.all_eq_true.1 hall b hb)).1
  have htl : s.toList = s.toByteArray.data.toList.map (fun b => Char.ofNat b.toNat) := ascii_toList s hascii
  have hne : (!s.toList.isEmpty) = true := by
    rw [htl]; cases h : s.toByteArray.data.toList with
    | nil => simp [h] at hnon
    | cons _ _ => rfl
  have hsafe : isSafeTagName s = true := by
    unfold isSafeTagName
    rw [Bool.and_eq_true]
    refine ⟨hne, ?_⟩
    rw [htl, List.all_map, List.all_eq_true]
    intro b hb
    exact (lowerTagByte_props b (List.all_eq_true.1 hall b hb)).2.1
  have hkey : s.toList.all isKeyChar = true := by
    rw [htl, List.all_map, List.all_eq_true]
    intro b hb
    exact (lowerTagByte_props b (List.all_eq_true.1 hall b hb)).2.2.1
  have hneStr : (!s.isEmpty) = true := by
    cases h : s.isEmpty with
    | false => rfl
    | true =>
        exfalso
        have hlen0 : s.utf8ByteSize = 0 := by simpa [String.isEmpty] using h
        have hsz : s.toByteArray.data.toList.length = 0 := by
          rw [Array.length_toList]; change s.toByteArray.size = 0; rw [String.size_toByteArray]; exact hlen0
        cases hl : s.toByteArray.data.toList with
        | nil => simp [hl] at hnon
        | cons _ _ => simp [hl] at hsz
  have hmap : s.toList.map asciiLowerChar = s.toList := by
    rw [htl, List.map_map]
    refine List.map_congr_left fun b hb => ?_
    exact (lowerTagByte_props b (List.all_eq_true.1 hall b hb)).2.2.2
  have hlow : asciiLower s = s := by
    unfold asciiLower; rw [hmap, String.ofList_toList]
  exact ⟨hsafe, hkey, hneStr, hmap, hlow⟩

private def isNotOnBytes : List UInt8 → Bool
  | 111 :: 110 :: _ => false
  | _               => true

private def isUrlAttrBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 97  => rest == [99, 116, 105, 111, 110] -- action
    | 99  => rest == [105, 116, 101] -- cite
    | 100 => rest == [97, 116, 97] -- data
    | 102 => rest == [111, 114, 109, 97, 99, 116, 105, 111, 110] -- formaction
    | 104 => rest == [114, 101, 102] -- href
    | 112 => rest == [111, 115, 116, 101, 114] -- poster
    | 115 => rest == [114, 99] || rest == [114, 99, 115, 101, 116] -- src, srcset
    | 120 => rest == [108, 105, 110, 107, 58, 104, 114, 101, 102] -- xlink:href
    | _   => false
  | [] => false

private def isSrcdocBytes : List UInt8 → Bool
  | [115, 114, 99, 100, 111, 99] => true
  | _ => false

private def checkSaBytes (bs : List UInt8) : Bool :=
  !bs.isEmpty && bs.all isLowerTagByte && isNotOnBytes bs && !isSrcdocBytes bs

private def checkSnuBytes (bs : List UInt8) : Bool :=
  checkSaBytes bs && !isUrlAttrBytes bs

private theorem byte_eq_of_char_ofNat {b : UInt8} {c : Char} (hle : b.toNat ≤ 127)
    (heq : Char.ofNat b.toNat = c) : b = UInt8.ofNat c.val.toNat := by
  have hv := char_ofNat_val_toNat b.toNat hle
  have hc : b.toNat = c.val.toNat := by rw [← hv, heq]
  apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change b.toNat = c.val.toNat % 256
  omega

private theorem mk_sa (k : String) (h : checkSaBytes k.toByteArray.data.toList = true) :
    isSafeAttrName k = true := by
  unfold checkSaBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨hnon, hall⟩, hnotOn⟩, hnotSrc⟩
  have ⟨_, hkey, hneStr, hmap, hlow⟩ := lowerBytes_core k (by simpa using hnon) hall
  have hascii : k.toByteArray.data.toList.all (fun b => decide (b.toNat ≤ 127)) = true :=
    List.all_eq_true.2 fun b hb => decide_eq_true (lowerTagByte_props b (List.all_eq_true.1 hall b hb)).1
  have htl := ascii_toList k hascii
  have hnoOn : hasOnPrefix (k.toList.map asciiLowerChar) = false := by
    cases hon : hasOnPrefix (k.toList.map asciiLowerChar) with
    | false => rfl
    | true =>
        exfalso
        rw [hmap, htl] at hon
        cases hb : k.toByteArray.data.toList with
        | nil => simp [hb, hasOnPrefix] at hon
        | cons b0 r0 =>
            cases r0 with
            | nil => simp [hb, hasOnPrefix] at hon
            | cons b1 r1 =>
                rw [hb] at hnotOn
                simp only [hb, List.map_cons, hasOnPrefix] at hon
                split at hon
                · rename_i rest heq
                  injection heq with hc0 hrest
                  injection hrest with hc1 _
                  have hle0 := (lowerTagByte_props b0 (List.all_eq_true.1 hall b0 (by simp [hb]))).1
                  have hle1 := (lowerTagByte_props b1 (List.all_eq_true.1 hall b1 (by simp [hb]))).1
                  have hb0 : b0 = 111 := byte_eq_of_char_ofNat hle0 hc0
                  have hb1 : b1 = 110 := byte_eq_of_char_ofNat hle1 hc1
                  subst hb0; subst hb1; exact Bool.noConfusion hnotOn
                · exact Bool.noConfusion hon
  have hns : (asciiLower k != "srcdoc") = true := by
    rw [hlow, bne_iff_ne]
    intro heq; subst heq; exact Bool.noConfusion hnotSrc
  simp only [isSafeAttrName, isSafeRenderedKey, hkey, hneStr, hnoOn, hns, Bool.not_false, Bool.and_self]

private theorem mk_snu (k : String) (h : checkSnuBytes k.toByteArray.data.toList = true) :
    isSafeAttrName k = true ∧ isUrlAttrName k = false := by
  unfold checkSnuBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hsa := mk_sa k h.1
  refine ⟨hsa, ?_⟩
  have h1 := h.1
  unfold checkSaBytes at h1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  have ⟨_, _, _, _, hlow⟩ := lowerBytes_core k (by simpa using h1.1.1.1) h1.1.1.2
  cases hu : isUrlAttrName k with
  | false => rfl
  | true =>
      exfalso
      unfold isUrlAttrName at hu
      rw [hlow] at hu
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h.2

theorem snu_dataRole     : isSafeAttrName "data-role" = true ∧ isUrlAttrName "data-role" = false := mk_snu "data-role" rfl
theorem snu_dataQedLink  : isSafeAttrName "data-qed-link" = true ∧ isUrlAttrName "data-qed-link" = false := mk_snu "data-qed-link" rfl
theorem snu_value        : isSafeAttrName "value" = true ∧ isUrlAttrName "value" = false := mk_snu "value" rfl
theorem snu_placeholder  : isSafeAttrName "placeholder" = true ∧ isUrlAttrName "placeholder" = false := mk_snu "placeholder" rfl
theorem snu_name         : isSafeAttrName "name" = true ∧ isUrlAttrName "name" = false := mk_snu "name" rfl
theorem snu_alt          : isSafeAttrName "alt" = true ∧ isUrlAttrName "alt" = false := mk_snu "alt" rfl
theorem snu_title        : isSafeAttrName "title" = true ∧ isUrlAttrName "title" = false := mk_snu "title" rfl
theorem snu_style        : isSafeAttrName "style" = true ∧ isUrlAttrName "style" = false := mk_snu "style" rfl
theorem snu_type         : isSafeAttrName "type" = true ∧ isUrlAttrName "type" = false := mk_snu "type" rfl
theorem snu_class        : isSafeAttrName "class" = true ∧ isUrlAttrName "class" = false := mk_snu "class" rfl
theorem snu_id           : isSafeAttrName "id" = true ∧ isUrlAttrName "id" = false := mk_snu "id" rfl
theorem snu_for          : isSafeAttrName "for" = true ∧ isUrlAttrName "for" = false := mk_snu "for" rfl
theorem snu_role         : isSafeAttrName "role" = true ∧ isUrlAttrName "role" = false := mk_snu "role" rfl
theorem snu_ariaLabel    : isSafeAttrName "aria-label" = true ∧ isUrlAttrName "aria-label" = false := mk_snu "aria-label" rfl
theorem snu_ariaInvalid  : isSafeAttrName "aria-invalid" = true ∧ isUrlAttrName "aria-invalid" = false := mk_snu "aria-invalid" rfl
theorem snu_ariaLive     : isSafeAttrName "aria-live" = true ∧ isUrlAttrName "aria-live" = false := mk_snu "aria-live" rfl
theorem snu_rows         : isSafeAttrName "rows" = true ∧ isUrlAttrName "rows" = false := mk_snu "rows" rfl
theorem snu_cols         : isSafeAttrName "cols" = true ∧ isUrlAttrName "cols" = false := mk_snu "cols" rfl
theorem snu_min          : isSafeAttrName "min" = true ∧ isUrlAttrName "min" = false := mk_snu "min" rfl
theorem snu_max          : isSafeAttrName "max" = true ∧ isUrlAttrName "max" = false := mk_snu "max" rfl
theorem snu_step         : isSafeAttrName "step" = true ∧ isUrlAttrName "step" = false := mk_snu "step" rfl
theorem snu_tabindex     : isSafeAttrName "tabindex" = true ∧ isUrlAttrName "tabindex" = false := mk_snu "tabindex" rfl
theorem snu_target       : isSafeAttrName "target" = true ∧ isUrlAttrName "target" = false := mk_snu "target" rfl
theorem snu_rel          : isSafeAttrName "rel" = true ∧ isUrlAttrName "rel" = false := mk_snu "rel" rfl
theorem snu_accept       : isSafeAttrName "accept" = true ∧ isUrlAttrName "accept" = false := mk_snu "accept" rfl
theorem snu_autocomplete : isSafeAttrName "autocomplete" = true ∧ isUrlAttrName "autocomplete" = false := mk_snu "autocomplete" rfl

theorem sa_click     : isSafeAttrName "click" = true := mk_sa "click" rfl
theorem sa_input     : isSafeAttrName "input" = true := mk_sa "input" rfl
theorem sa_change    : isSafeAttrName "change" = true := mk_sa "change" rfl
theorem sa_keydown   : isSafeAttrName "keydown" = true := mk_sa "keydown" rfl
theorem sa_keyup     : isSafeAttrName "keyup" = true := mk_sa "keyup" rfl
theorem sa_submit    : isSafeAttrName "submit" = true := mk_sa "submit" rfl
theorem sa_blur      : isSafeAttrName "blur" = true := mk_sa "blur" rfl
theorem sa_focus     : isSafeAttrName "focus" = true := mk_sa "focus" rfl
theorem sa_dblclick  : isSafeAttrName "dblclick" = true := mk_sa "dblclick" rfl
theorem sa_mousedown : isSafeAttrName "mousedown" = true := mk_sa "mousedown" rfl
theorem sa_mouseup   : isSafeAttrName "mouseup" = true := mk_sa "mouseup" rfl
theorem sa_disabled  : isSafeAttrName "disabled" = true := mk_sa "disabled" rfl
theorem sa_required  : isSafeAttrName "required" = true := mk_sa "required" rfl
theorem sa_checked   : isSafeAttrName "checked" = true := mk_sa "checked" rfl
theorem sa_readonly  : isSafeAttrName "readonly" = true := mk_sa "readonly" rfl
theorem sa_selected  : isSafeAttrName "selected" = true := mk_sa "selected" rfl
theorem sa_multiple  : isSafeAttrName "multiple" = true := mk_sa "multiple" rfl
theorem sa_hidden    : isSafeAttrName "hidden" = true := mk_sa "hidden" rfl

theorem valid_value {msg α : Type} [ToString α] (v : α) :
    (Qed.value v : Attr msg).valid = true :=
  attr_nonUrl "value" (toString v) snu_value

theorem valid_onCheck {msg : Type} (f : Bool → msg) :
    (Qed.onCheck f).valid = true := sa_change

theorem valid_vOnCheck {σ msg : Type} (s : σ) (f : σ → Bool → msg) :
    (VAttr.eval s (V.onCheck' f)).valid = true := sa_change

/-! ### Fast Tag Byte Classifiers for `stepHtmlCtx` and `isVoidTag` -/

private def isVoidTagBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 97  => rest == [114, 101, 97] -- area
    | 98  => rest == [97, 115, 101] || rest == [114] -- base, br
    | 99  => rest == [111, 108] -- col
    | 101 => rest == [109, 98, 101, 100] -- embed
    | 104 => rest == [114] -- hr
    | 105 => rest == [109, 103] || rest == [110, 112, 117, 116] -- img, input
    | 108 => rest == [105, 110, 107] -- link
    | 109 => rest == [101, 116, 97] -- meta
    | 115 => rest == [111, 117, 114, 99, 101] -- source
    | 116 => rest == [114, 97, 99, 107] -- track
    | 119 => rest == [98, 114] -- wbr
    | _   => false
  | [] => false

private theorem mk_nv (t : String) (h : isVoidTagBytes t.toByteArray.data.toList = false) :
    isVoidTag t = false := by
  cases hv : isVoidTag t with
  | false => rfl
  | true =>
      exfalso
      have hmem : t ∈ voidTags := List.mem_of_elem_eq_true hv
      unfold voidTags at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private def isForbiddenBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 97  => rest == [112, 112, 108, 101, 116] -- applet
    | 98  => rest == [97, 115, 101] -- base
    | 101 => rest == [109, 98, 101, 100] -- embed
    | 111 => rest == [98, 106, 101, 99, 116] -- object
    | 115 => rest == [99, 114, 105, 112, 116] -- script
    | _   => false
  | [] => false

private def isContextOnlyBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 99  => rest == [97, 112, 116, 105, 111, 110] || rest == [111, 108, 103, 114, 111, 117, 112] || rest == [111, 108]
    | 100 => rest == [116] || rest == [100]
    | 108 => rest == [105]
    | 111 => rest == [112, 116, 105, 111, 110] || rest == [112, 116, 103, 114, 111, 117, 112]
    | 116 => rest == [104, 101, 97, 100] || rest == [98, 111, 100, 121] || rest == [102, 111, 111, 116] ||
             rest == [114] || rest == [100] || rest == [104]
    | _   => false
  | [] => false

private def isInteractiveBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 97  => rest == [] -- a
    | 98  => rest == [117, 116, 116, 111, 110] -- button
    | 100 => rest == [101, 116, 97, 105, 108, 115] -- details
    | 105 => rest == [110, 112, 117, 116] -- input
    | 115 => rest == [101, 108, 101, 99, 116] || rest == [117, 109, 109, 97, 114, 121] -- select, summary
    | 116 => rest == [101, 120, 116, 97, 114, 101, 97] -- textarea
    | _   => false
  | [] => false

private def isHeadingBytes : List UInt8 → Bool
  | [104, b1] => 49 ≤ b1.toNat && b1.toNat ≤ 54 -- h1..h6
  | _         => false

private def closesPBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 97  => rest == [100, 100, 114, 101, 115, 115] || rest == [114, 116, 105, 99, 108, 101] || rest == [115, 105, 100, 101]
    | 98  => rest == [108, 111, 99, 107, 113, 117, 111, 116, 101]
    | 100 => rest == [101, 116, 97, 105, 108, 115] || rest == [105, 118] || rest == [108]
    | 102 => rest == [105, 101, 108, 100, 115, 101, 116] || rest == [105, 103, 99, 97, 112, 116, 105, 111, 110] ||
             rest == [105, 103, 117, 114, 101] || rest == [111, 111, 116, 101, 114] || rest == [111, 114, 109]
    | 104 => isHeadingBytes (b0 :: rest) || rest == [101, 97, 100, 101, 114] || rest == [103, 114, 111, 117, 112] || rest == [114]
    | 109 => rest == [97, 105, 110] || rest == [101, 110, 117]
    | 110 => rest == [97, 118]
    | 111 => rest == [108]
    | 112 => rest == [] || rest == [114, 101]
    | 115 => rest == [101, 97, 114, 99, 104] || rest == [101, 99, 116, 105, 111, 110]
    | 116 => rest == [97, 98, 108, 101]
    | 117 => rest == [108]
    | _   => false
  | [] => false

private def isOtherNormalSpecialBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 100 => rest == [108] -- dl
    | 102 => rest == [111, 114, 109] -- form
    | 108 => rest == [97, 98, 101, 108] -- label
    | 111 => rest == [108] -- ol
    | 112 => rest == [] -- p
    | 115 => rest == [118, 103] || rest == [116, 121, 108, 101] -- svg, style
    | 116 => rest == [97, 98, 108, 101] -- table
    | 117 => rest == [108] -- ul
    | _   => false
  | [] => false

private theorem isForbidden_false_of_bytes (t : String)
    (h : isForbiddenBytes t.toByteArray.data.toList = false) : isForbiddenTag t = false := by
  cases hv : isForbiddenTag t with
  | false => rfl
  | true =>
      exfalso; unfold isForbiddenTag at hv
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem isContextOnly_false_of_bytes (t : String)
    (h : isContextOnlyBytes t.toByteArray.data.toList = false) : isContextOnlyTag t = false := by
  cases hv : isContextOnlyTag t with
  | false => rfl
  | true =>
      exfalso; unfold isContextOnlyTag at hv
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem isInteractive_false_of_bytes (t : String)
    (h : isInteractiveBytes t.toByteArray.data.toList = false) : isInteractiveTag t = false := by
  cases hv : isInteractiveTag t with
  | false => rfl
  | true =>
      exfalso; unfold isInteractiveTag at hv
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem isHeading_false_of_bytes (t : String)
    (h : isHeadingBytes t.toByteArray.data.toList = false) : isHeadingTag t = false := by
  cases hv : isHeadingTag t with
  | false => rfl
  | true =>
      exfalso; unfold isHeadingTag at hv
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem closesP_false_of_bytes (t : String)
    (h : closesPBytes t.toByteArray.data.toList = false) : closesPTag t = false := by
  cases hv : closesPTag t with
  | false => rfl
  | true =>
      exfalso; unfold closesPTag isHeadingTag at hv
      simp only [Bool.or_eq_true, beq_iff_eq] at hv
      repeat (rcases hv with hv | hv <;> try (subst hv; exact Bool.noConfusion h))

private theorem otherNormal_false_of_bytes (t : String)
    (h : isOtherNormalSpecialBytes t.toByteArray.data.toList = false) :
    (t == "svg" || t == "style" || t == "ul" || t == "ol" || t == "dl" ||
     t == "table" || t == "p" || t == "label" || t == "form") = false := by
  cases hv : (t == "svg" || t == "style" || t == "ul" || t == "ol" || t == "dl" ||
              t == "table" || t == "p" || t == "label" || t == "form") with
  | false => rfl
  | true =>
      exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem isSafe_of_lower (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte) = true) :
    isSafeTagName tag = true := by
  rw [Bool.and_eq_true] at h
  exact (lowerBytes_core tag h.1 h.2).1

private theorem beq_false_of_bytes {a b : String}
    (h : (a.toByteArray.data.toList == b.toByteArray.data.toList) = false) : (a == b) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; subst heq; simp at h

private def checkPlainBlockBytes (bs : List UInt8) : Bool :=
  !bs.isEmpty && bs.all isLowerTagByte &&
  !isForbiddenBytes bs && !isContextOnlyBytes bs && !isInteractiveBytes bs &&
  !isHeadingBytes bs && !isOtherNormalSpecialBytes bs

private def checkPlainInlineBytes (bs : List UInt8) : Bool :=
  checkPlainBlockBytes bs && !closesPBytes bs

private theorem mk_plainBlock (tag : String)
    (h : checkPlainBlockBytes tag.toByteArray.data.toList = true)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := false, interactive, inForm } := by
  unfold checkPlainBlockBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hinter⟩, hhead⟩, hoth⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hi := isInteractive_false_of_bytes tag hinter
  have hh := isHeading_false_of_bytes tag hhead
  have ho := otherNormal_false_of_bytes tag hoth
  have hi' := hi
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, hsel⟩, hta⟩, hdet⟩, hsum⟩
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h14⟩, h15⟩
  simp only [stepHtmlCtx, hs, hf, hc, hi, hh, ha, hbtn, hsel, hta, hdet, hsum,
    h1, h2, h5, h6, h7, h8, h9, h14, h15, Bool.not_true, Bool.or_false,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private theorem mk_plainInline (tag : String)
    (h : checkPlainInlineBytes tag.toByteArray.data.toList = true)
    (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive, inForm } tag =
      some { mode := .normal, inP, interactive, inForm } := by
  unfold checkPlainInlineBytes checkPlainBlockBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hinter⟩, hhead⟩, hoth⟩, hcp⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hcp' := closesP_false_of_bytes tag hcp
  have hi := isInteractive_false_of_bytes tag hinter
  have hh := isHeading_false_of_bytes tag hhead
  have ho := otherNormal_false_of_bytes tag hoth
  have hi' := hi
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, hsel⟩, hta⟩, hdet⟩, hsum⟩
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h14⟩, h15⟩
  simp only [stepHtmlCtx, hs, hf, hc, hcp', hi, hh, ha, hbtn, hsel, hta, hdet, hsum,
    h1, h2, h5, h6, h7, h8, h9, h14, h15, Bool.not_true, Bool.or_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private theorem mk_heading (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !isInteractiveBytes tag.toByteArray.data.toList) = true)
    (hp : (tag == "p" || isHeadingTag tag) = true)
    (ho : (tag == "svg" || tag == "style" || tag == "ul" || tag == "ol" || tag == "dl" ||
           tag == "table" || tag == "label" || tag == "form") = false)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := true, interactive, inForm } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hinter⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hi := isInteractive_false_of_bytes tag hinter
  have hi' := hi
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, hsel⟩, hta⟩, hdet⟩, hsum⟩
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h5⟩, h6⟩, h7⟩, h8⟩, h14⟩, h15⟩
  simp only [stepHtmlCtx, hs, hf, hc, hi, hp, ha, hbtn, hsel, hta, hdet, hsum,
    h1, h2, h5, h6, h7, h8, h14, h15, Bool.not_true, Bool.false_or, Bool.or_false,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private def isHeadingNonSpecialBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 100 => rest == [108]
    | 102 => rest == [111, 114, 109]
    | 108 => rest == [97, 98, 101, 108]
    | 111 => rest == [108]
    | 115 => rest == [118, 103] || rest == [116, 121, 108, 101]
    | 116 => rest == [97, 98, 108, 101]
    | 117 => rest == [108]
    | _   => false
  | [] => false

private theorem headingNonSpecial_false (t : String)
    (h : isHeadingNonSpecialBytes t.toByteArray.data.toList = false) :
    (t == "svg" || t == "style" || t == "ul" || t == "ol" || t == "dl" ||
     t == "table" || t == "label" || t == "form") = false := by
  cases hv : (t == "svg" || t == "style" || t == "ul" || t == "ol" || t == "dl" ||
              t == "table" || t == "label" || t == "form") with
  | false => rfl
  | true =>
      exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem mk_heading_fast (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !isInteractiveBytes tag.toByteArray.data.toList && !isHeadingNonSpecialBytes tag.toByteArray.data.toList) = true)
    (hp : (tag == "p" || isHeadingTag tag) = true) (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := true, interactive, inForm } := by
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact mk_heading tag h.1 hp (headingNonSpecial_false tag h.2) interactive inForm

private def isInterOtherBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 100 => rest == [108] -- dl
    | 102 => rest == [111, 114, 109] -- form
    | 111 => rest == [108] -- ol
    | 112 => rest == [] -- p
    | 115 => rest == [118, 103] || rest == [116, 121, 108, 101] || rest == [101, 108, 101, 99, 116] -- svg, style, select
    | 116 => rest == [97, 98, 108, 101] || rest == [101, 120, 116, 97, 114, 101, 97] -- table, textarea
    | 117 => rest == [108] -- ul
    | _   => false
  | [] => false

private theorem interOther_false (t : String)
    (h : isInterOtherBytes t.toByteArray.data.toList = false) :
    (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
     t == "ul" || t == "ol" || t == "dl" || t == "table" ||
     t == "p" || t == "form") = false := by
  cases hv : (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
              t == "ul" || t == "ol" || t == "dl" || t == "table" ||
              t == "p" || t == "form") with
  | false => rfl
  | true =>
      exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem mk_interactive (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !closesPBytes tag.toByteArray.data.toList && !isHeadingBytes tag.toByteArray.data.toList &&
          !isInterOtherBytes tag.toByteArray.data.toList) = true)
    (hint : (tag == "a" || tag == "button" || tag == "details" || tag == "summary") = true)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := true, inForm } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hcp⟩, hhead⟩, hoth⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hcp' := closesP_false_of_bytes tag hcp
  have hh := isHeading_false_of_bytes tag hhead
  have ho := interOther_false tag hoth
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
  simp only [stepHtmlCtx, hs, hf, hc, hcp', hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    Bool.not_true, Bool.false_or, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, Bool.or_assoc]
  rw [show (tag == "a" || (tag == "button" || (tag == "details" || tag == "summary"))) = true by
    simpa [Bool.or_assoc] using hint]

private def isInputOtherBytes : List UInt8 → Bool
  | b0 :: rest =>
    isInterOtherBytes (b0 :: rest) ||
    match b0.toNat with
    | 97  => rest == []
    | 98  => rest == [117, 116, 116, 111, 110]
    | 100 => rest == [101, 116, 97, 105, 108, 115]
    | 115 => rest == [117, 109, 109, 97, 114, 121]
    | _   => false
  | [] => false

private theorem inputOther_false (t : String)
    (h : isInputOtherBytes t.toByteArray.data.toList = false) :
    (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
     t == "ul" || t == "ol" || t == "dl" || t == "table" ||
     t == "p" || t == "a" || t == "button" || t == "details" ||
     t == "summary" || t == "form") = false := by
  cases hv : (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
              t == "ul" || t == "ol" || t == "dl" || t == "table" ||
              t == "p" || t == "a" || t == "button" || t == "details" ||
              t == "summary" || t == "form") with
  | false => rfl
  | true =>
      exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact Bool.noConfusion h

private theorem mk_inputLike (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !closesPBytes tag.toByteArray.data.toList && !isHeadingBytes tag.toByteArray.data.toList &&
          !isInputOtherBytes tag.toByteArray.data.toList) = true)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := false, inForm } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hcp⟩, hhead⟩, hoth⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hcp' := closesP_false_of_bytes tag hcp
  have hh := isHeading_false_of_bytes tag hhead
  have ho := inputOther_false tag hoth
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
  simp only [stepHtmlCtx, hs, hf, hc, hcp', hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    Bool.not_true, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

private theorem mk_normalModeChange (tag : String) (m2 : TagMode)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !isInteractiveBytes tag.toByteArray.data.toList) = true)
    (hsvg : (tag == "svg") = false) (hsty : (tag == "style") = false)
    (hlab : (tag == "label") = false) (hfrm : (tag == "form") = false)
    (hstep : (if tag == "ul" || tag == "ol" then some TagMode.ulOl
              else if tag == "dl" then some TagMode.dl
              else if tag == "table" then some TagMode.table
              else none) = some m2)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := m2, inP := false, interactive, inForm } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hinter⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hi := isInteractive_false_of_bytes tag hinter
  have hi' := hi
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hsel⟩, hta⟩, _⟩, _⟩
  simp only [stepHtmlCtx, hs, hf, hc, hi, hsel, hta, hsvg, hsty, hlab, hfrm,
    Bool.not_true, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (tag == "ul" || tag == "ol") = true
  · rw [if_pos h1] at hstep ⊢; cases hstep; rfl
  · rw [if_neg h1] at hstep ⊢
    by_cases h2 : (tag == "dl") = true
    · rw [if_pos h2] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h2] at hstep ⊢
      by_cases h3 : (tag == "table") = true
      · rw [if_pos h3] at hstep ⊢; cases hstep; rfl
      · rw [if_neg h3] at hstep; cases hstep

private theorem mk_interModeChange (tag : String) (m2 : TagMode)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte &&
          !isForbiddenBytes tag.toByteArray.data.toList && !isContextOnlyBytes tag.toByteArray.data.toList &&
          !closesPBytes tag.toByteArray.data.toList) = true)
    (hsvg : (tag == "svg") = false) (hsty : (tag == "style") = false) (hfrm : (tag == "form") = false)
    (hstep : (if tag == "textarea" then some TagMode.textarea
              else if tag == "select" then some TagMode.select
              else none) = some m2)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := m2, inP, interactive := true, inForm } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hcp⟩
  have hs := (lowerBytes_core tag (by simpa using hnon) hall).1
  have hf := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hcp' := closesP_false_of_bytes tag hcp
  simp only [stepHtmlCtx, hs, hf, hc, hcp', hsvg, hsty, hfrm,
    Bool.not_true, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (tag == "textarea") = true
  · rw [if_pos h1] at hstep ⊢; cases hstep; rfl
  · rw [if_neg h1] at hstep ⊢
    by_cases h2 : (tag == "select") = true
    · rw [if_pos h2] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h2] at hstep; cases hstep

private theorem mk_modeStep (m1 m2 : TagMode) (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hstep : (match m1 with
      | .ulOl => if tag == "li" then some TagMode.normal else none
      | .table => if tag == "caption" then some TagMode.normal
                  else if tag == "colgroup" then some TagMode.colgroup
                  else if tag == "thead" || tag == "tbody" || tag == "tfoot" then some TagMode.tableSection
                  else none
      | .tableSection => if tag == "tr" then some TagMode.tableRow else none
      | .tableRow => if tag == "td" || tag == "th" then some TagMode.normal else none
      | _ => none) = some m2)
    (p i f : Bool) :
    stepHtmlCtx { mode := m1, inP := p, interactive := i, inForm := f } tag =
      some { mode := m2, inP := false, interactive := i, inForm := f } := by
  cases m1 <;>
    simp only [stepHtmlCtx, hs, hf, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hstep ⊢ <;>
    try cases hstep
  · by_cases h : (tag == "li") = true
    · rw [if_pos h] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h] at hstep; cases hstep
  · by_cases h1 : (tag == "caption") = true
    · rw [if_pos h1] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h1] at hstep ⊢
      by_cases h2 : (tag == "colgroup") = true
      · rw [if_pos h2] at hstep ⊢; cases hstep; rfl
      · rw [if_neg h2] at hstep ⊢
        by_cases h3 : (tag == "thead" || tag == "tbody" || tag == "tfoot") = true
        · rw [if_pos h3] at hstep ⊢; cases hstep; rfl
        · rw [if_neg h3] at hstep; cases hstep
  · by_cases h : (tag == "tr") = true
    · rw [if_pos h] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h] at hstep; cases hstep
  · by_cases h : (tag == "td" || tag == "th") = true
    · rw [if_pos h] at hstep ⊢; cases hstep; rfl
    · rw [if_neg h] at hstep; cases hstep

theorem step_div (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "div" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "div" rfl i f
theorem step_section (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "section" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "section" rfl i f
theorem step_article (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "article" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "article" rfl i f
theorem step_aside (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "aside" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "aside" rfl i f
theorem step_header (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "header" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "header" rfl i f
theorem step_footer (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "footer" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "footer" rfl i f
theorem step_main (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "main" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "main" rfl i f
theorem step_nav (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "nav" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "nav" rfl i f
theorem step_blockquote (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "blockquote" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "blockquote" rfl i f
theorem step_pre (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "pre" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "pre" rfl i f
theorem step_fieldset (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "fieldset" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "fieldset" rfl i f
theorem step_figure (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "figure" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "figure" rfl i f
theorem step_figcaption (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "figcaption" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "figcaption" rfl i f
theorem step_hr (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "hr" = some { mode := .normal, inP := false, interactive := i, inForm := f } := mk_plainBlock "hr" rfl i f

theorem step_span (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "span" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "span" rfl p i f
theorem step_strong (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "strong" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "strong" rfl p i f
theorem step_em (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "em" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "em" rfl p i f
theorem step_code (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "code" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "code" rfl p i f
theorem step_small (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "small" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "small" rfl p i f
theorem step_b (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "b" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "b" rfl p i f
theorem step_i (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "i" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "i" rfl p i f
theorem step_u (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "u" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "u" rfl p i f
theorem step_s (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "s" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "s" rfl p i f
theorem step_mark (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "mark" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "mark" rfl p i f
theorem step_time (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "time" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "time" rfl p i f
theorem step_kbd (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "kbd" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "kbd" rfl p i f
theorem step_img (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "img" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "img" rfl p i f
theorem step_br (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "br" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "br" rfl p i f
theorem step_legend (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } "legend" = some { mode := .normal, inP := p, interactive := i, inForm := f } := mk_plainInline "legend" rfl p i f

theorem step_p (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "p" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "p" rfl (by simp) i f
theorem step_h1 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h1" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h1" rfl (by simp [isHeadingTag]) i f
theorem step_h2 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h2" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h2" rfl (by simp [isHeadingTag]) i f
theorem step_h3 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h3" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h3" rfl (by simp [isHeadingTag]) i f
theorem step_h4 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h4" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h4" rfl (by simp [isHeadingTag]) i f
theorem step_h5 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h5" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h5" rfl (by simp [isHeadingTag]) i f
theorem step_h6 (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } "h6" = some { mode := .normal, inP := true, interactive := i, inForm := f } := mk_heading_fast "h6" rfl (by simp [isHeadingTag]) i f

theorem step_button (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } "button" = some { mode := .normal, inP := p, interactive := true, inForm := f } := mk_interactive "button" rfl (by simp) p f
theorem step_a (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } "a" = some { mode := .normal, inP := p, interactive := true, inForm := f } := mk_interactive "a" rfl (by simp) p f
theorem step_summary (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } "summary" = some { mode := .normal, inP := p, interactive := true, inForm := f } := mk_interactive "summary" rfl (by simp) p f

theorem step_input (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } "input" = some { mode := .normal, inP := p, interactive := false, inForm := f } := mk_inputLike "input" rfl p f
theorem step_label (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } "label" = some { mode := .normal, inP := p, interactive := false, inForm := f } := mk_inputLike "label" rfl p f

theorem step_form :
    stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
      some { mode := .normal, inP := false, interactive := false, inForm := true } := by
  have hs := isSafe_of_lower "form" rfl
  have hf := isForbidden_false_of_bytes "form" rfl
  have hc := isContextOnly_false_of_bytes "form" rfl
  have hh := isHeading_false_of_bytes "form" rfl
  have hi := isInteractive_false_of_bytes "form" rfl
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi
  rcases hi with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, hsel⟩, hta⟩, hdet⟩, hsum⟩
  have hsvg : ("form" == "svg") = false := beq_false_of_bytes rfl
  have hsty : ("form" == "style") = false := beq_false_of_bytes rfl
  have hul  : ("form" == "ul") = false := beq_false_of_bytes rfl
  have hol  : ("form" == "ol") = false := beq_false_of_bytes rfl
  have hdl  : ("form" == "dl") = false := beq_false_of_bytes rfl
  have htbl : ("form" == "table") = false := beq_false_of_bytes rfl
  have hp   : ("form" == "p") = false := beq_false_of_bytes rfl
  simp only [stepHtmlCtx, hs, hf, hc, hh, ha, hbtn, hsel, hta, hdet, hsum,
    hsvg, hsty, hul, hol, hdl, htbl, hp, beq_self_eq_true,
    Bool.not_true, Bool.or_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

theorem step_textarea (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "textarea" =
      some { mode := .textarea, inP, interactive := true, inForm } :=
  mk_interModeChange "textarea" .textarea rfl (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (beq_false_of_bytes rfl) (by simp) inP inForm

theorem step_select (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "select" =
      some { mode := .select, inP, interactive := true, inForm } :=
  mk_interModeChange "select" .select rfl (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (beq_false_of_bytes rfl) (by simp [beq_false_of_bytes (a := "select") (b := "textarea") rfl]) inP inForm

theorem step_ul (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ul" =
      some { mode := .ulOl, inP := false, interactive, inForm } :=
  mk_normalModeChange "ul" .ulOl rfl (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (beq_false_of_bytes rfl) (beq_false_of_bytes rfl) (by simp) interactive inForm

theorem step_ol (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ol" =
      some { mode := .ulOl, inP := false, interactive, inForm } :=
  mk_normalModeChange "ol" .ulOl rfl (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (beq_false_of_bytes rfl) (beq_false_of_bytes rfl) (by simp) interactive inForm

theorem step_table (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "table" =
      some { mode := .table, inP := false, interactive, inForm } :=
  mk_normalModeChange "table" .table rfl (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (beq_false_of_bytes rfl) (beq_false_of_bytes rfl)
    (by simp [beq_false_of_bytes (a := "table") (b := "ul") rfl,
              beq_false_of_bytes (a := "table") (b := "ol") rfl,
              beq_false_of_bytes (a := "table") (b := "dl") rfl]) interactive inForm

theorem step_li (p i f : Bool) : stepHtmlCtx { mode := .ulOl, inP := p, interactive := i, inForm := f } "li" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .ulOl .normal "li" (isSafe_of_lower "li" rfl) (isForbidden_false_of_bytes "li" rfl) (by simp) p i f
theorem step_thead (p i f : Bool) : stepHtmlCtx { mode := .table, inP := p, interactive := i, inForm := f } "thead" = some { mode := .tableSection, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .table .tableSection "thead" (isSafe_of_lower "thead" rfl) (isForbidden_false_of_bytes "thead" rfl)
    (by simp [beq_false_of_bytes (a := "thead") (b := "caption") rfl, beq_false_of_bytes (a := "thead") (b := "colgroup") rfl]) p i f
theorem step_tbody (p i f : Bool) : stepHtmlCtx { mode := .table, inP := p, interactive := i, inForm := f } "tbody" = some { mode := .tableSection, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .table .tableSection "tbody" (isSafe_of_lower "tbody" rfl) (isForbidden_false_of_bytes "tbody" rfl)
    (by simp [beq_false_of_bytes (a := "tbody") (b := "caption") rfl, beq_false_of_bytes (a := "tbody") (b := "colgroup") rfl]) p i f
theorem step_tr (p i f : Bool) : stepHtmlCtx { mode := .tableSection, inP := p, interactive := i, inForm := f } "tr" = some { mode := .tableRow, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableSection .tableRow "tr" (isSafe_of_lower "tr" rfl) (isForbidden_false_of_bytes "tr" rfl) (by simp) p i f
theorem step_td (p i f : Bool) : stepHtmlCtx { mode := .tableRow, inP := p, interactive := i, inForm := f } "td" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableRow .normal "td" (isSafe_of_lower "td" rfl) (isForbidden_false_of_bytes "td" rfl) (by simp) p i f
theorem step_th (p i f : Bool) : stepHtmlCtx { mode := .tableRow, inP := p, interactive := i, inForm := f } "th" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableRow .normal "th" (isSafe_of_lower "th" rfl) (isForbidden_false_of_bytes "th" rfl) (by simp) p i f

theorem step_option (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .select, inP, interactive, inForm } "option" =
      some { mode := .option, inP, interactive, inForm } := by
  have h1 := isSafe_of_lower "option" rfl
  have h2 := isForbidden_false_of_bytes "option" rfl
  simp only [stepHtmlCtx, h1, h2, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]

theorem nv_div : isVoidTag "div" = false := mk_nv "div" rfl
theorem nv_span : isVoidTag "span" = false := mk_nv "span" rfl
theorem nv_p : isVoidTag "p" = false := mk_nv "p" rfl
theorem nv_a : isVoidTag "a" = false := mk_nv "a" rfl
theorem nv_button : isVoidTag "button" = false := mk_nv "button" rfl
theorem nv_form : isVoidTag "form" = false := mk_nv "form" rfl
theorem nv_label : isVoidTag "label" = false := mk_nv "label" rfl
theorem nv_ul : isVoidTag "ul" = false := mk_nv "ul" rfl
theorem nv_ol : isVoidTag "ol" = false := mk_nv "ol" rfl
theorem nv_li : isVoidTag "li" = false := mk_nv "li" rfl
theorem nv_h1 : isVoidTag "h1" = false := mk_nv "h1" rfl
theorem nv_h2 : isVoidTag "h2" = false := mk_nv "h2" rfl
theorem nv_h3 : isVoidTag "h3" = false := mk_nv "h3" rfl
theorem nv_h4 : isVoidTag "h4" = false := mk_nv "h4" rfl
theorem nv_h5 : isVoidTag "h5" = false := mk_nv "h5" rfl
theorem nv_h6 : isVoidTag "h6" = false := mk_nv "h6" rfl
theorem nv_section : isVoidTag "section" = false := mk_nv "section" rfl
theorem nv_article : isVoidTag "article" = false := mk_nv "article" rfl
theorem nv_aside : isVoidTag "aside" = false := mk_nv "aside" rfl
theorem nv_header : isVoidTag "header" = false := mk_nv "header" rfl
theorem nv_footer : isVoidTag "footer" = false := mk_nv "footer" rfl
theorem nv_main : isVoidTag "main" = false := mk_nv "main" rfl
theorem nv_nav : isVoidTag "nav" = false := mk_nv "nav" rfl
theorem nv_blockquote : isVoidTag "blockquote" = false := mk_nv "blockquote" rfl
theorem nv_pre : isVoidTag "pre" = false := mk_nv "pre" rfl
theorem nv_code : isVoidTag "code" = false := mk_nv "code" rfl
theorem nv_strong : isVoidTag "strong" = false := mk_nv "strong" rfl
theorem nv_em : isVoidTag "em" = false := mk_nv "em" rfl
theorem nv_small : isVoidTag "small" = false := mk_nv "small" rfl
theorem nv_b : isVoidTag "b" = false := mk_nv "b" rfl
theorem nv_i : isVoidTag "i" = false := mk_nv "i" rfl
theorem nv_u : isVoidTag "u" = false := mk_nv "u" rfl
theorem nv_s : isVoidTag "s" = false := mk_nv "s" rfl
theorem nv_mark : isVoidTag "mark" = false := mk_nv "mark" rfl
theorem nv_time : isVoidTag "time" = false := mk_nv "time" rfl
theorem nv_kbd : isVoidTag "kbd" = false := mk_nv "kbd" rfl
theorem nv_table : isVoidTag "table" = false := mk_nv "table" rfl
theorem nv_thead : isVoidTag "thead" = false := mk_nv "thead" rfl
theorem nv_tbody : isVoidTag "tbody" = false := mk_nv "tbody" rfl
theorem nv_tr : isVoidTag "tr" = false := mk_nv "tr" rfl
theorem nv_td : isVoidTag "td" = false := mk_nv "td" rfl
theorem nv_th : isVoidTag "th" = false := mk_nv "th" rfl
theorem nv_select : isVoidTag "select" = false := mk_nv "select" rfl
theorem nv_option : isVoidTag "option" = false := mk_nv "option" rfl
theorem nv_textarea : isVoidTag "textarea" = false := mk_nv "textarea" rfl
theorem nv_fieldset : isVoidTag "fieldset" = false := mk_nv "fieldset" rfl
theorem nv_legend : isVoidTag "legend" = false := mk_nv "legend" rfl
theorem nv_figure : isVoidTag "figure" = false := mk_nv "figure" rfl
theorem nv_figcaption : isVoidTag "figcaption" = false := mk_nv "figcaption" rfl
theorem nv_summary : isVoidTag "summary" = false := mk_nv "summary" rfl

open Lean

private def mkStrMap (entries : Array (String × Name)) : Std.HashMap String Name :=
  entries.foldl (fun m (k, v) => m.insert k v) {}

def safeNonUrlAttrMap : Std.HashMap String Name := mkStrMap #[
  ("data-role", ``snu_dataRole), ("data-qed-link", ``snu_dataQedLink), ("value", ``snu_value),
  ("placeholder", ``snu_placeholder), ("name", ``snu_name), ("alt", ``snu_alt), ("title", ``snu_title),
  ("style", ``snu_style), ("type", ``snu_type), ("class", ``snu_class), ("id", ``snu_id), ("for", ``snu_for),
  ("role", ``snu_role), ("aria-label", ``snu_ariaLabel), ("aria-invalid", ``snu_ariaInvalid),
  ("aria-live", ``snu_ariaLive), ("rows", ``snu_rows), ("cols", ``snu_cols), ("min", ``snu_min),
  ("max", ``snu_max), ("step", ``snu_step), ("tabindex", ``snu_tabindex), ("target", ``snu_target),
  ("rel", ``snu_rel), ("accept", ``snu_accept), ("autocomplete", ``snu_autocomplete)]

def safeAttrMap : Std.HashMap String Name := mkStrMap #[
  ("click", ``sa_click), ("input", ``sa_input), ("change", ``sa_change), ("keydown", ``sa_keydown),
  ("keyup", ``sa_keyup), ("submit", ``sa_submit), ("blur", ``sa_blur), ("focus", ``sa_focus),
  ("dblclick", ``sa_dblclick), ("mousedown", ``sa_mousedown), ("mouseup", ``sa_mouseup),
  ("disabled", ``sa_disabled), ("required", ``sa_required), ("checked", ``sa_checked),
  ("readonly", ``sa_readonly), ("selected", ``sa_selected), ("multiple", ``sa_multiple), ("hidden", ``sa_hidden)]

def nonVoidTagMap : Std.HashMap String Name := mkStrMap #[
  ("div", ``nv_div), ("span", ``nv_span), ("p", ``nv_p), ("a", ``nv_a), ("button", ``nv_button),
  ("form", ``nv_form), ("label", ``nv_label), ("ul", ``nv_ul), ("ol", ``nv_ol), ("li", ``nv_li),
  ("h1", ``nv_h1), ("h2", ``nv_h2), ("h3", ``nv_h3), ("h4", ``nv_h4), ("h5", ``nv_h5), ("h6", ``nv_h6),
  ("section", ``nv_section), ("article", ``nv_article), ("aside", ``nv_aside), ("header", ``nv_header),
  ("footer", ``nv_footer), ("main", ``nv_main), ("nav", ``nv_nav), ("blockquote", ``nv_blockquote),
  ("pre", ``nv_pre), ("code", ``nv_code), ("strong", ``nv_strong), ("em", ``nv_em), ("small", ``nv_small),
  ("b", ``nv_b), ("i", ``nv_i), ("u", ``nv_u), ("s", ``nv_s), ("mark", ``nv_mark), ("time", ``nv_time),
  ("kbd", ``nv_kbd), ("table", ``nv_table), ("thead", ``nv_thead), ("tbody", ``nv_tbody), ("tr", ``nv_tr),
  ("td", ``nv_td), ("th", ``nv_th), ("select", ``nv_select), ("option", ``nv_option), ("textarea", ``nv_textarea),
  ("fieldset", ``nv_fieldset), ("legend", ``nv_legend), ("figure", ``nv_figure), ("figcaption", ``nv_figcaption),
  ("summary", ``nv_summary)]

private def stepBlockMap : Std.HashMap String Name := mkStrMap #[
  ("div", ``step_div), ("section", ``step_section), ("article", ``step_article), ("aside", ``step_aside),
  ("header", ``step_header), ("footer", ``step_footer), ("main", ``step_main), ("nav", ``step_nav),
  ("blockquote", ``step_blockquote), ("pre", ``step_pre), ("fieldset", ``step_fieldset),
  ("figure", ``step_figure), ("figcaption", ``step_figcaption), ("hr", ``step_hr),
  ("p", ``step_p), ("h1", ``step_h1), ("h2", ``step_h2), ("h3", ``step_h3), ("h4", ``step_h4),
  ("h5", ``step_h5), ("h6", ``step_h6), ("ul", ``step_ul), ("ol", ``step_ol), ("table", ``step_table)]

private def stepInlineMap : Std.HashMap String Name := mkStrMap #[
  ("span", ``step_span), ("strong", ``step_strong), ("em", ``step_em), ("code", ``step_code),
  ("small", ``step_small), ("b", ``step_b), ("i", ``step_i), ("u", ``step_u), ("s", ``step_s),
  ("mark", ``step_mark), ("time", ``step_time), ("kbd", ``step_kbd), ("img", ``step_img),
  ("br", ``step_br), ("legend", ``step_legend)]

private def stepNonInterMap : Std.HashMap String Name := mkStrMap #[
  ("button", ``step_button), ("a", ``step_a), ("summary", ``step_summary),
  ("input", ``step_input), ("label", ``step_label), ("textarea", ``step_textarea), ("select", ``step_select)]

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let bP := toExpr ctxV.inP
  let bI := toExpr ctxV.interactive
  let bF := toExpr ctxV.inForm
  match ctxV.mode with
  | .normal =>
      if !ctxV.inP then
        if let some lm := stepBlockMap[tagS]? then mkApp2 (mkConst lm) bI bF
        else if !ctxV.interactive && !ctxV.inForm && tagS == "form" then mkConst ``step_form
        else if !ctxV.interactive then
          if let some lm := stepNonInterMap[tagS]? then mkApp2 (mkConst lm) bP bF
          else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
          else rflStep childCtxE
        else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
        else rflStep childCtxE
      else if !ctxV.interactive then
        if let some lm := stepNonInterMap[tagS]? then mkApp2 (mkConst lm) bP bF
        else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
        else rflStep childCtxE
      else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
      else rflStep childCtxE
  | .ulOl         => if tagS == "li"     then mkApp3 (mkConst ``step_li) bP bI bF     else rflStep childCtxE
  | .table        => if tagS == "thead"  then mkApp3 (mkConst ``step_thead) bP bI bF
                     else if tagS == "tbody" then mkApp3 (mkConst ``step_tbody) bP bI bF else rflStep childCtxE
  | .tableSection => if tagS == "tr"     then mkApp3 (mkConst ``step_tr) bP bI bF     else rflStep childCtxE
  | .tableRow     => if tagS == "td"     then mkApp3 (mkConst ``step_td) bP bI bF
                     else if tagS == "th" then mkApp3 (mkConst ``step_th) bP bI bF    else rflStep childCtxE
  | .select       => if tagS == "option" then mkApp3 (mkConst ``step_option) bP bI bF else rflStep childCtxE
  | _             => rflStep childCtxE
where
  rflStep (childCtxE : Expr) : Expr :=
    mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
      (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) childCtxE)

private def qedAttrWrapperMap : Std.HashMap Name (Name × String × Name) :=
  #[
    (``Qed.role,          (``attr_nonUrl,  "data-role",   ``snu_dataRole)),
    (``Qed.placeholder,   (``attr_nonUrl,  "placeholder", ``snu_placeholder)),
    (``Qed.name,          (``attr_nonUrl,  "name",        ``snu_name)),
    (``Qed.alt,           (``attr_nonUrl,  "alt",         ``snu_alt)),
    (``Qed.title,         (``attr_nonUrl,  "title",       ``snu_title)),
    (``Qed.style,         (``attr_nonUrl,  "style",       ``snu_style)),
    (``Qed.type',         (``attr_nonUrl,  "type",        ``snu_type)),
    (``Qed.onClick,       (``on_safe,      "click",       ``sa_click)),
    (``Qed.onSubmit,      (``on_safe,      "submit",      ``sa_submit)),
    (``Qed.onBlur,        (``on_safe,      "blur",        ``sa_blur)),
    (``Qed.onFocus,       (``on_safe,      "focus",       ``sa_focus)),
    (``Qed.onDoubleClick, (``on_safe,      "dblclick",    ``sa_dblclick)),
    (``Qed.onMouseDown,   (``on_safe,      "mousedown",   ``sa_mousedown)),
    (``Qed.onMouseUp,     (``on_safe,      "mouseup",     ``sa_mouseup)),
    (``Qed.onInput,       (``onValue_safe, "input",       ``sa_input)),
    (``Qed.onChange,      (``onValue_safe, "input",       ``sa_input)),
    (``Qed.onKeydown,     (``onValue_safe, "keydown",     ``sa_keydown)),
    (``Qed.onKeyup,       (``onValue_safe, "keyup",       ``sa_keyup)),
    (``Qed.disabled,      (``flag_safe,    "disabled",    ``sa_disabled)),
    (``Qed.required,      (``flag_safe,    "required",    ``sa_required)),
    (``Qed.checked,       (``flag_safe,    "checked",     ``sa_checked)),
    (``Qed.readOnly,      (``flag_safe,    "readonly",    ``sa_readonly))
  ].foldl (fun m (k, v) => m.insert k v) {}

def fastAttrValidProof? (msgTy a : Expr) : Option Expr :=
  let a := a.consumeMData
  let args := a.getAppArgs
  let strLit? (e : Expr) : Option String := match e.consumeMData with | .lit (.strVal s) => some s | _ => none
  match a.getAppFn.constName? with
  | some fn =>
      if fn == ``VAttr.eval && args.size == 4 &&
          (args[3]!).consumeMData.getAppFn.constName? == some ``V.onCheck' then
        let vaArgs := args[3]!.consumeMData.getAppArgs
        if vaArgs.size == 3 then some (mkApp4 (mkConst ``valid_vOnCheck) args[0]! args[1]! args[2]! vaArgs[2]!)
        else none
      else if fn == ``Qed.value && args.size == 4 then
        some (mkApp4 (mkConst ``valid_value) args[0]! args[1]! args[2]! args[3]!)
      else if fn == ``Qed.onCheck && args.size == 2 then
        some (mkApp2 (mkConst ``valid_onCheck) args[0]! args[1]!)
      else if args.size == 2 then
        qedAttrWrapperMap[fn]?.map fun (comb, key, lem) =>
          mkApp4 (mkConst comb) msgTy (toExpr key) args[1]! (mkConst lem)
      else if fn == ``Attr.attr && args.size == 3 then
        (strLit? args[1]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``attr_nonUrl) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.signalAttr && args.size == 4 then
        (strLit? args[2]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``signalAttr_nonUrl) #[msgTy, args[1]!, args[2]!, args[3]!, mkConst lem]
      else if fn == ``Qed.attr && args.size == 5 then
        (strLit? args[3]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``valid_attr_nonUrl) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, mkConst lem]
      else if fn == ``Attr.flag && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``flag_safe) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.on && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``on_safe) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.signalOn && args.size == 4 then
        (strLit? args[2]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``signalOn_safe) #[msgTy, args[1]!, args[2]!, args[3]!, mkConst lem]
      else if fn == ``Attr.onValue && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``onValue_safe) msgTy args[1]! args[2]! (mkConst lem)
      else none
  | none => none

end Qed.ValidLemmas
