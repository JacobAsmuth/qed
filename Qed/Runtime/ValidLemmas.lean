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

private def mkStrMap (entries : Array (String × Lean.Name)) : Std.HashMap String Lean.Name :=
  entries.foldl (fun m (k, v) => m.insert k v) {}

local macro "genValidTable " kind:ident mapDef:ident " [" keys:str,* "]" : command => do
  let camel (pfx s : String) : String :=
    match s.splitOn "-" with
    | [] => pfx
    | h :: t => pfx ++ h ++ String.join (t.map fun p =>
        match p.toList with | [] => "" | c :: cs => String.ofList (c.toUpper :: cs))
  let mut cmds := #[]
  let mut entries : Array (Lean.TSyntax `term) := #[]
  let k := kind.getId.eraseMacroScopes.toString
  let mkRef (n : String) := Lean.mkIdentFrom kind (Lean.Name.mkSimple n)
  for sLit in keys.getElems do
    let s := sLit.getString
    let pfx := match k with
      | "snu" => "snu_" | "sa" => "sa_" | "nv" => "nv_" | _ => "step_"
    let thmStr := camel pfx s
    let thm := Lean.mkIdentFrom sLit (Lean.Name.mkSimple thmStr)
    let fullName := Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkSimple "Qed") "ValidLemmas") thmStr
    entries := entries.push (← `(($sLit, $(Lean.quote fullName))))
    let cmd ← match k with
      | "snu" => `(command| theorem $thm : isSafeAttrName $sLit = true ∧ isUrlAttrName $sLit = false := $(mkRef "mk_snu") $sLit rfl)
      | "sa"  => `(command| theorem $thm : isSafeAttrName $sLit = true := $(mkRef "mk_sa") $sLit rfl)
      | "nv"  => `(command| theorem $thm : isVoidTag $sLit = false := $(mkRef "mk_nv") $sLit rfl)
      | "block" =>
          `(command| theorem $thm (i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := false, interactive := i, inForm := f } := $(mkRef "mk_plainBlock") $sLit rfl i f)
      | "inline" =>
          `(command| theorem $thm (p i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := i, inForm := f } := $(mkRef "mk_plainInline") $sLit rfl p i f)
      | "heading" =>
          `(command| theorem $thm (i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := true, interactive := i, inForm := f } := $(mkRef "mk_heading") $sLit rfl (by simp [isHeadingTag]) i f)
      | "inter" =>
          `(command| theorem $thm (p f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := true, inForm := f } := $(mkRef "mk_interactive") $sLit rfl (by simp) p f)
      | "input" =>
          `(command| theorem $thm (p f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := false, inForm := f } := $(mkRef "mk_inputLike") $sLit rfl p f)
      | _ => Lean.Macro.throwUnsupported
    cmds := cmds.push cmd
  if k == "snu" || k == "sa" || k == "nv" || k == "inline" then
    cmds := cmds.push (← `(command| def $mapDef : Std.HashMap String Lean.Name := mkStrMap #[$entries,*]))
  else
    cmds := cmds.push (← `(command| private def $mapDef : Array (String × Lean.Name) := #[$entries,*]))
  return ⟨Lean.mkNullNode cmds⟩

genValidTable snu safeNonUrlAttrMap [
  "data-role", "data-qed-link", "value", "placeholder", "name", "alt", "title", "style", "type",
  "class", "id", "for", "role", "aria-label", "aria-invalid", "aria-live", "rows", "cols",
  "min", "max", "step", "tabindex", "target", "rel", "accept", "autocomplete"]

genValidTable sa safeAttrMap [
  "click", "input", "change", "keydown", "keyup", "submit", "blur", "focus", "dblclick",
  "mousedown", "mouseup", "disabled", "required", "checked", "readonly", "selected", "multiple", "hidden"]

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

local macro "bytes_false_by " e:term " using " h:ident " [" unf:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let simpT ← if unf.getElems.isEmpty then `(tactic| simp only [Bool.or_eq_true, beq_iff_eq] at hv)
              else `(tactic| simp only [$unf,*, Bool.or_eq_true, beq_iff_eq] at hv)
  `(tactic| (
    cases hv : $e with
    | false => rfl
    | true =>
        exfalso
        $simpT
        repeat (rcases hv with hv | hv <;> try (subst hv; exact Bool.noConfusion $h))))

private theorem mk_nv (t : String) (h : isVoidTagBytes t.toByteArray.data.toList = false) :
    isVoidTag t = false := by
  cases hv : isVoidTag t with
  | false => rfl
  | true =>
      exfalso
      have hmem : t ∈ voidTags := List.mem_of_elem_eq_true hv
      unfold voidTags at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      repeat (rcases hmem with rfl | hmem <;> try exact Bool.noConfusion h)

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

private def isModeChangeBytes : List UInt8 → Bool
  | b0 :: rest =>
    match b0.toNat with
    | 100 => rest == [108] -- dl
    | 111 => rest == [108] -- ol
    | 115 => rest == [118, 103] || rest == [116, 121, 108, 101] || rest == [101, 108, 101, 99, 116] -- svg, style, select
    | 116 => rest == [97, 98, 108, 101] || rest == [101, 120, 116, 97, 114, 101, 97] -- table, textarea
    | 117 => rest == [108] -- ul
    | _   => false
  | [] => false

private theorem isForbidden_false_of_bytes (t : String)
    (h : isForbiddenBytes t.toByteArray.data.toList = false) : isForbiddenTag t = false := by
  bytes_false_by (isForbiddenTag t) using h [isForbiddenTag]

private theorem isContextOnly_false_of_bytes (t : String)
    (h : isContextOnlyBytes t.toByteArray.data.toList = false) : isContextOnlyTag t = false := by
  bytes_false_by (isContextOnlyTag t) using h [isContextOnlyTag]

private theorem isInteractive_false_of_bytes (t : String)
    (h : isInteractiveBytes t.toByteArray.data.toList = false) : isInteractiveTag t = false := by
  bytes_false_by (isInteractiveTag t) using h [isInteractiveTag]

private theorem isHeading_false_of_bytes (t : String)
    (h : isHeadingBytes t.toByteArray.data.toList = false) : isHeadingTag t = false := by
  bytes_false_by (isHeadingTag t) using h [isHeadingTag]

private theorem closesP_false_of_bytes (t : String)
    (h : closesPBytes t.toByteArray.data.toList = false) : closesPTag t = false := by
  bytes_false_by (closesPTag t) using h [closesPTag, isHeadingTag]

private theorem modeChange_false (t : String)
    (h : isModeChangeBytes t.toByteArray.data.toList = false) :
    (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
     t == "ul" || t == "ol" || t == "dl" || t == "table") = false := by
  bytes_false_by (t == "svg" || t == "style" || t == "textarea" || t == "select" ||
                  t == "ul" || t == "ol" || t == "dl" || t == "table") using h []

private theorem isSafe_of_lower (tag : String)
    (h : (!tag.toByteArray.data.toList.isEmpty && tag.toByteArray.data.toList.all isLowerTagByte) = true) :
    isSafeTagName tag = true := by
  rw [Bool.and_eq_true] at h
  exact (lowerBytes_core tag h.1 h.2).1

private theorem beq_false_of_bytes {a b : String}
    (h : (a.toByteArray.data.toList == b.toByteArray.data.toList) = false) : (a == b) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; subst heq; simp at h

private theorem bne_bytes_false {a b : String}
    (h : (a.toByteArray.data.toList != b.toByteArray.data.toList) = true) : (a == b) = false :=
  beq_false_of_bytes (by simpa [bne] using h)

private theorem mk_normalSameMode (tag : String) (inP interactive inForm inP' interactive' inForm' : Bool)
    (hnon : (!tag.toByteArray.data.toList.isEmpty) = true)
    (hall : tag.toByteArray.data.toList.all isLowerTagByte = true)
    (hforb : isForbiddenBytes tag.toByteArray.data.toList = false)
    (hctx : isContextOnlyBytes tag.toByteArray.data.toList = false)
    (hmc : isModeChangeBytes tag.toByteArray.data.toList = false)
    (hp : (inP && closesPTag tag) = false)
    (hi : (interactive && (isInteractiveTag tag || tag == "label" || tag == "form")) = false)
    (hf : (inForm && tag == "form") = false)
    (hP' : (inP || tag == "p" || isHeadingTag tag) = inP')
    (hI' : (interactive || tag == "a" || tag == "button" || tag == "details" || tag == "summary") = interactive')
    (hF' : (inForm || tag == "form") = inForm') :
    stepHtmlCtx { mode := .normal, inP, interactive, inForm } tag =
      some { mode := .normal, inP := inP', interactive := interactive', inForm := inForm' } := by
  have hs := (lowerBytes_core tag hnon hall).1
  have hfb := isForbidden_false_of_bytes tag hforb
  have hc := isContextOnly_false_of_bytes tag hctx
  have hm := modeChange_false tag hmc
  simp only [Bool.or_eq_false_iff] at hm
  rcases hm with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  simp only [stepHtmlCtx, hs, hfb, hc, hp, hi, hf, h1, h2, h3, h4, h5, h6, h7, h8,
    hP', hI', hF', Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

private def checkNormalBaseBytes (bs : List UInt8) : Bool :=
  !bs.isEmpty && bs.all isLowerTagByte && !isForbiddenBytes bs && !isContextOnlyBytes bs && !isModeChangeBytes bs

private def checkPlainBlockBytes (bs : List UInt8) : Bool :=
  checkNormalBaseBytes bs && !isInteractiveBytes bs && !isHeadingBytes bs &&
  bs != [112] && bs != [108, 97, 98, 101, 108] && bs != [102, 111, 114, 109]

private def checkPlainInlineBytes (bs : List UInt8) : Bool :=
  checkPlainBlockBytes bs && !closesPBytes bs

private theorem mk_plainCore (tag : String) (inP interactive inForm : Bool)
    (h : checkPlainBlockBytes tag.toByteArray.data.toList = true)
    (hcp : (inP && closesPTag tag) = false) :
    stepHtmlCtx { mode := .normal, inP, interactive, inForm } tag =
      some { mode := .normal, inP, interactive, inForm } := by
  unfold checkPlainBlockBytes checkNormalBaseBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hmc⟩, hinter⟩, hhead⟩, hp⟩, hlab⟩, hfrm⟩
  have hi := isInteractive_false_of_bytes tag hinter
  have hh := isHeading_false_of_bytes tag hhead
  have hp' : (tag == "p") = false := bne_bytes_false hp
  have hl' : (tag == "label") = false := bne_bytes_false hlab
  have hf' : (tag == "form") = false := bne_bytes_false hfrm
  have hi' := hi; simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, _⟩, _⟩, hdet⟩, hsum⟩
  exact mk_normalSameMode tag inP interactive inForm inP interactive inForm
    (by simpa using hnon) hall hforb hctx hmc hcp
    (by simp [hi, hl', hf']) (by simp [hf'])
    (by simp [hp', hh]) (by simp [ha, hbtn, hdet, hsum]) (by simp [hf'])

private theorem mk_plainBlock (tag : String) (h : checkPlainBlockBytes tag.toByteArray.data.toList = true)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := false, interactive, inForm } :=
  mk_plainCore tag false interactive inForm h rfl

private theorem mk_plainInline (tag : String) (h : checkPlainInlineBytes tag.toByteArray.data.toList = true)
    (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive, inForm } tag =
      some { mode := .normal, inP, interactive, inForm } := by
  unfold checkPlainInlineBytes at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact mk_plainCore tag inP interactive inForm h.1 (by simp [closesP_false_of_bytes tag h.2])

private def checkHeadingBytes (bs : List UInt8) : Bool :=
  checkNormalBaseBytes bs && !isInteractiveBytes bs &&
  bs != [108, 97, 98, 101, 108] && bs != [102, 111, 114, 109]

private theorem mk_heading (tag : String) (h : checkHeadingBytes tag.toByteArray.data.toList = true)
    (hp : (tag == "p" || isHeadingTag tag) = true) (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := true, interactive, inForm } := by
  unfold checkHeadingBytes checkNormalBaseBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hmc⟩, hinter⟩, hlab⟩, hfrm⟩
  have hi := isInteractive_false_of_bytes tag hinter
  have hl' : (tag == "label") = false := bne_bytes_false hlab
  have hf' : (tag == "form") = false := bne_bytes_false hfrm
  have hi' := hi; simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, _⟩, _⟩, hdet⟩, hsum⟩
  exact mk_normalSameMode tag false interactive inForm true interactive inForm
    (by simpa using hnon) hall hforb hctx hmc rfl
    (by simp [hi, hl', hf']) (by simp [hf'])
    (by simpa using hp) (by simp [ha, hbtn, hdet, hsum]) (by simp [hf'])

private def checkInterBytes (bs : List UInt8) : Bool :=
  checkNormalBaseBytes bs && !closesPBytes bs && !isHeadingBytes bs &&
  bs != [112] && bs != [102, 111, 114, 109]

private theorem mk_interactive (tag : String) (h : checkInterBytes tag.toByteArray.data.toList = true)
    (hint : (tag == "a" || tag == "button" || tag == "details" || tag == "summary") = true)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := true, inForm } := by
  unfold checkInterBytes checkNormalBaseBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hmc⟩, hcp⟩, hhead⟩, hp⟩, hfrm⟩
  have hf' : (tag == "form") = false := bne_bytes_false hfrm
  exact mk_normalSameMode tag inP false inForm inP true inForm
    (by simpa using hnon) hall hforb hctx hmc
    (by simp [closesP_false_of_bytes tag hcp]) rfl (by simp [hf'])
    (by simp [bne_bytes_false hp (b := "p"), isHeading_false_of_bytes tag hhead])
    (by simpa [Bool.or_assoc] using hint) (by simp [hf'])

private def checkInputLikeBytes (bs : List UInt8) : Bool :=
  checkInterBytes bs &&
  bs != [97] && bs != [98, 117, 116, 116, 111, 110] &&
  bs != [100, 101, 116, 97, 105, 108, 115] && bs != [115, 117, 109, 109, 97, 114, 121]

private theorem mk_inputLike (tag : String) (h : checkInputLikeBytes tag.toByteArray.data.toList = true)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := false, inForm } := by
  unfold checkInputLikeBytes checkInterBytes checkNormalBaseBytes at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnon, hall⟩, hforb⟩, hctx⟩, hmc⟩, hcp⟩, hhead⟩, hp⟩, hfrm⟩, ha⟩, hbtn⟩, hdet⟩, hsum⟩
  have hf' : (tag == "form") = false := bne_bytes_false hfrm
  exact mk_normalSameMode tag inP false inForm inP false inForm
    (by simpa using hnon) hall hforb hctx hmc
    (by simp [closesP_false_of_bytes tag hcp]) rfl (by simp [hf'])
    (by simp [bne_bytes_false hp (b := "p"), isHeading_false_of_bytes tag hhead])
    (by simp [bne_bytes_false ha (b := "a"), bne_bytes_false hbtn (b := "button"),
              bne_bytes_false hdet (b := "details"), bne_bytes_false hsum (b := "summary")])
    (by simp [hf'])

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
  have hi' := hi; simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi'
  rcases hi' with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hsel⟩, hta⟩, _⟩, _⟩
  simp only [stepHtmlCtx, hs, hf, hc, hi, hsel, hta, hsvg, hsty, hlab, hfrm,
    Bool.not_true, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

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
  repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

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
    repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

genValidTable block stepPlainBlockEntries [
  "div", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "fieldset", "figure", "figcaption", "hr"]

genValidTable inline stepInlineMap [
  "span", "strong", "em", "code", "small", "b", "i", "u", "s", "mark", "time", "kbd", "img", "br", "legend"]

genValidTable heading stepHeadingEntries ["p", "h1", "h2", "h3", "h4", "h5", "h6"]

genValidTable inter stepInterEntries ["button", "a", "summary"]

genValidTable input stepInputEntries ["input", "label"]

theorem step_form :
    stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
      some { mode := .normal, inP := false, interactive := false, inForm := true } := by
  have hi := isInteractive_false_of_bytes "form" rfl
  simp only [isInteractiveTag, Bool.or_eq_false_iff] at hi
  rcases hi with ⟨⟨⟨⟨⟨⟨ha, hbtn⟩, _⟩, _⟩, _⟩, hdet⟩, hsum⟩
  exact mk_normalSameMode "form" false false false false false true rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [beq_false_of_bytes (a := "form") (b := "p") rfl, isHeading_false_of_bytes "form" rfl])
    (by simp [ha, hbtn, hdet, hsum]) (by simp)

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

genValidTable nv nonVoidTagMap [
  "div", "span", "p", "a", "button", "form", "label", "ul", "ol", "li",
  "h1", "h2", "h3", "h4", "h5", "h6", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "code", "strong", "em", "small", "b", "i", "u", "s", "mark", "time", "kbd",
  "table", "thead", "tbody", "tr", "td", "th", "select", "option", "textarea", "fieldset", "legend",
  "figure", "figcaption", "summary"]

open Lean

private def stepBlockMap : Std.HashMap String Name :=
  mkStrMap (stepPlainBlockEntries ++ stepHeadingEntries ++ #[("ul", ``step_ul), ("ol", ``step_ol), ("table", ``step_table)])

private def stepNonInterMap : Std.HashMap String Name :=
  mkStrMap (stepInterEntries ++ stepInputEntries ++ #[("textarea", ``step_textarea), ("select", ``step_select)])

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let bP := toExpr ctxV.inP
  let bI := toExpr ctxV.interactive
  let bF := toExpr ctxV.inForm
  match ctxV.mode with
  | .normal =>
      if !ctxV.inP then
        if let some lm := stepBlockMap[tagS]? then mkApp2 (mkConst lm) bI bF
        else if !ctxV.interactive && !ctxV.inForm && tagS == "form" then mkConst ``step_form
        else normalInlineOrInter bP bI bF
      else normalInlineOrInter bP bI bF
  | .ulOl         => if tagS == "li"     then mkApp3 (mkConst ``step_li) bP bI bF     else rflStep childCtxE
  | .table        => if tagS == "thead"  then mkApp3 (mkConst ``step_thead) bP bI bF
                     else if tagS == "tbody" then mkApp3 (mkConst ``step_tbody) bP bI bF else rflStep childCtxE
  | .tableSection => if tagS == "tr"     then mkApp3 (mkConst ``step_tr) bP bI bF     else rflStep childCtxE
  | .tableRow     => if tagS == "td"     then mkApp3 (mkConst ``step_td) bP bI bF
                     else if tagS == "th" then mkApp3 (mkConst ``step_th) bP bI bF    else rflStep childCtxE
  | .select       => if tagS == "option" then mkApp3 (mkConst ``step_option) bP bI bF else rflStep childCtxE
  | _             => rflStep childCtxE
where
  normalInlineOrInter (bP bI bF : Expr) : Expr :=
    if let some lm := if !ctxV.interactive then stepNonInterMap[tagS]? else none then mkApp2 (mkConst lm) bP bF
    else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
    else rflStep childCtxE
  rflStep (childCtxE : Expr) : Expr :=
    mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
      (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) childCtxE)

def qedAttrWrapperMap : Std.HashMap Name (Name × String × Name) :=
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
