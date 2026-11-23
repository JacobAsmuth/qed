import Qed.Html

namespace Qed

def localKey (component key : String) : String := component ++ "@" ++ key

@[inline] def isMarkupOrQuote (c : Char) : Bool := c == '<' || c == '>' || c == '"' || c == '\''
@[inline] def isHtmlSpecial (c : Char) : Bool := c == '&' || isMarkupOrQuote c

def escapeHtmlStep (acc : String) : Char → String
  | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '>' => acc ++ "&gt;" | '"' => acc ++ "&quot;" | '\'' => acc ++ "&#39;" | c => acc.push c

def escapeHtml (s : String) : String := let cs := s.toList; if !cs.any isHtmlSpecial then s else cs.foldl escapeHtmlStep ""

@[inline] private def isHtmlSpecialByte (b : UInt8) : Bool := b <= 62 && (b == 38 || b == 60 || b == 62 || b == 34 || b == 39)
def escapeHtmlAcc (acc s : String) : String := if !hasAsciiByte s isHtmlSpecialByte then acc ++ s else s.foldl escapeHtmlStep acc
def escapeHtmlFast (s : String) : String := escapeHtmlAcc "" s

private theorem push_eq_append_r (a : String) (c : Char) : a.push c = a ++ String.singleton c := by ext; simp

private theorem escapeHtmlStep_append (a b : String) (c : Char) : escapeHtmlStep (a ++ b) c = a ++ escapeHtmlStep b c := by
  unfold escapeHtmlStep; split
  all_goals first | exact String.append_assoc | rw [push_eq_append_r, push_eq_append_r, String.append_assoc]

private theorem foldl_escapeHtmlStep_append : ∀ (cs : List Char) (a b : String), cs.foldl escapeHtmlStep (a ++ b) = a ++ cs.foldl escapeHtmlStep b
  | [], _, _ => rfl
  | c :: cs, a, b => by simp only [List.foldl_cons, escapeHtmlStep_append]; exact foldl_escapeHtmlStep_append cs a (escapeHtmlStep b c)

private theorem escapeHtmlAcc_eq (acc s : String) : escapeHtmlAcc acc s = acc ++ escapeHtml s := by
  unfold escapeHtmlAcc escapeHtml; dsimp only
  have h1 : hasAsciiByte s isHtmlSpecialByte = s.toList.any isHtmlSpecial :=
    hasAsciiByte_eq_any s isHtmlSpecialByte isHtmlSpecial
      (fun b => (by decide : ∀ x : BitVec 8, x.toNat ≥ 128 → isHtmlSpecialByte ⟨x⟩ = false) b.toBitVec)
      (fun c hc => by simpa [Char.ofNat_toNat] using (by decide : ∀ n : Fin 128, isHtmlSpecialByte (UInt8.ofNat n.val) = isHtmlSpecial (Char.ofNat n.val)) ⟨c.toNat, by omega⟩)
      (fun c hgt => by simp only [isHtmlSpecial, isMarkupOrQuote, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; refine ⟨?_, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩ <;> (rintro rfl; exact absurd hgt (by decide)))
  rw [h1, show s.foldl escapeHtmlStep acc = s.toList.foldl escapeHtmlStep acc by simp]
  cases s.toList.any isHtmlSpecial
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; simpa using foldl_escapeHtmlStep_append s.toList acc ""

@[csimp] theorem escapeHtml_eq_escapeHtmlFast : @escapeHtml = @escapeHtmlFast := by funext s; simpa [escapeHtmlFast] using (escapeHtmlAcc_eq "" s).symm

private theorem escapeHtmlStep_safe (acc : String) (c : Char) (hacc : acc.toList.all (!isMarkupOrQuote ·) = true) :
    (escapeHtmlStep acc c).toList.all (!isMarkupOrQuote ·) = true := by
  unfold escapeHtmlStep; split
  all_goals first
    | (rw [String.toList_append, List.all_append, hacc]; decide)
    | (rw [String.toList_push, List.all_append, hacc]; simp_all [isMarkupOrQuote])

private theorem foldl_escapeHtmlStep_safe : ∀ (cs : List Char) (acc : String), acc.toList.all (!isMarkupOrQuote ·) = true → (cs.foldl escapeHtmlStep acc).toList.all (!isMarkupOrQuote ·) = true
  | [], _, hacc => hacc | c :: cs, acc, hacc => foldl_escapeHtmlStep_safe cs (escapeHtmlStep acc c) (escapeHtmlStep_safe acc c hacc)

/-- Every character emitted by `escapeHtml` is free of `<`, `>`, `"`, and `'`. -/
theorem escapeHtml_no_markup_or_quote (s : String) : ∀ c ∈ (escapeHtml s).toList, isMarkupOrQuote c = false := by
  unfold escapeHtml; dsimp only; cases h : s.toList.any isHtmlSpecial
  · simp only [Bool.not_false, ↓reduceIte]; rw [List.any_eq_false] at h
    exact fun c hc => (Bool.or_eq_false_iff.1 (Bool.eq_false_iff.2 (h c hc))).2
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact fun c hc => by simpa using List.all_eq_true.1 (foldl_escapeHtmlStep_safe s.toList "" (by decide)) c hc

def Attr.key? : Attr msg → Option String | .attr k _ | .flag k _ => some k | _ => none

def dedupAttrs : List (Attr msg) → List (Attr msg)
  | [] => []
  | a :: rest => match a.key? with
      | none => a :: dedupAttrs rest
      | some k => if rest.any (·.key? == some k) then dedupAttrs rest else a :: dedupAttrs rest

def normalizeAttrs (attrs : List (Attr msg)) : List (Attr msg) :=
  let classes := (attrs.filterMap fun | .cls c => some c | _ => none).filter (· != "")
  (if classes.isEmpty then [] else [Attr.cls (String.intercalate " " classes)]) ++ dedupAttrs (attrs.filter fun | .cls _ => false | _ => true)

def sanitizeKey (k : String) : String := let cs := k.toList; if cs.all isKeyChar then k else String.ofList (cs.filter isKeyChar)
def sanitizeKeyFast (k : String) : String :=
  if k.foldl (fun b c => b && isKeyChar c) true then k else k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) ""

private theorem foldl_and_eq_all_r (p : Char → Bool) (cs : List Char) (init : Bool) : cs.foldl (fun b c => b && p c) init = (init && cs.all p) := by
  induction cs generalizing init with | nil => simp | cons _ _ ih => simp [ih, Bool.and_assoc]

private theorem foldl_filterPush_eq (p : Char → Bool) (cs : List Char) (acc : String) :
    cs.foldl (fun a c => if p c then a.push c else a) acc = acc ++ String.ofList (cs.filter p) := by
  induction cs generalizing acc with | nil => simp | cons c _ ih => simp only [List.foldl_cons, List.filter_cons]; cases p c <;> simp [ih]; ext; simp

@[csimp] theorem sanitizeKey_eq_sanitizeKeyFast : @sanitizeKey = @sanitizeKeyFast := by
  funext k; unfold sanitizeKey sanitizeKeyFast
  have h1 : k.foldl (fun b c => b && isKeyChar c) true = k.toList.all isKeyChar := by
    rw [show k.foldl (fun b c => b && isKeyChar c) true = k.toList.foldl (fun b c => b && isKeyChar c) true by simp, foldl_and_eq_all_r, Bool.true_and]
  have h2 : k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" = String.ofList (k.toList.filter isKeyChar) := by
    rw [show k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" = k.toList.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" by simp, foldl_filterPush_eq]; simp
  rw [h1, h2]

theorem sanitizeKey_safe (k : String) : ∀ c ∈ (sanitizeKey k).toList, isKeyChar c = true := by
  unfold sanitizeKey; dsimp only; cases h : k.toList.all isKeyChar
  · intro c hc; simp only [Bool.false_eq_true, ↓reduceIte, String.toList_ofList] at hc; exact (List.mem_filter.1 hc).2
  · exact List.all_eq_true.1 h

def renderAttr (hs : Array msg) : Attr msg → String × Array msg
  | .cls c => (s!" class=\"{escapeHtml c}\"", hs)
  | .attr k v | .signalAttr _ k v =>
      let sk := sanitizeKey k; if !isSafeRenderedKey sk || (isUrlAttrName sk && !isSafeUrl v) then ("", hs) else (s!" {sk}=\"{escapeHtml v}\"", hs)
  | .flag k present => let sk := sanitizeKey k; if !present || !isSafeRenderedKey sk then ("", hs) else (s!" {sk}=\"{sk}\"", hs)
  | .key _ | .onValue _ _ => ("", hs)
  | .on event m | .signalOn _ event m => let ev := sanitizeKey event; if ev.isEmpty then ("", hs) else (s!" data-qed-on-{ev}=\"{hs.size}\"", hs.push m)
  | .localCell key comp _ _ _ => (s!" data-qed-local=\"{escapeHtml (localKey comp key)}\"", hs)
  | .signalBind name => (s!" data-qed-signal=\"{escapeHtml name}\"", hs)

theorem renderAttr_blocks_inline_handler (hs : Array msg) (k v : String) (hon : hasOnPrefix ((sanitizeKey k).toList.map asciiLowerChar) = true) :
    (renderAttr hs (.attr k v)).1 = "" := by simp [renderAttr, isSafeRenderedKey, hon]
theorem renderAttr_blocks_srcdoc (hs : Array msg) (k v : String) (hsd : asciiLower (sanitizeKey k) = "srcdoc") :
    (renderAttr hs (.attr k v)).1 = "" := by simp [renderAttr, isSafeRenderedKey, hsd]
theorem renderAttr_blocks_unsafe_url (hs : Array msg) (k v : String) (hurl : isUrlAttrName (sanitizeKey k) = true) (hbad : isSafeUrl v = false) :
    (renderAttr hs (.attr k v)).1 = "" := by simp [renderAttr, hurl, hbad]

def renderAttrs (hs : Array msg) : List (Attr msg) → String × Array msg
  | [] => ("", hs) | a :: as => let (s1, hs1) := renderAttr hs a; let (s2, hs2) := renderAttrs hs1 as; (s1 ++ s2, hs2)

def renderElement (renderKids : Array msg → String × Array msg) (hs : Array msg) (tag : String) (attrs : List (Attr msg)) (children : List (Html msg)) : String × Array msg :=
  let (attrStr, hs1) := renderAttrs hs (normalizeAttrs attrs)
  if tag == "style" || tag == "script" then (s!"<{tag}{attrStr}>{escapeRawText (String.join (children.map fun | .text s => s | _ => ""))}</{tag}>", hs1)
  else if isVoidTag tag then (s!"<{tag}{attrStr}>", hs1)
  else
    let (childStr, hs2) := renderKids hs1
    let body := if tag == "textarea" && childStr.front? == some '\n' then "\n" ++ childStr else childStr
    (s!"<{tag}{attrStr}>{body}</{tag}>", hs2)

mutual
  def renderNode (hs : Array msg) : Html msg → String × Array msg
    | .text s => (escapeHtml s, hs) | .element tag attrs children => renderElement (fun hs => renderChildren hs children) hs tag attrs children
  def renderChildren (hs : Array msg) : List (Html msg) → String × Array msg
    | [] => ("", hs) | c :: cs => let (s1, hs1) := renderNode hs c; let (s2, hs2) := renderChildren hs1 cs; (s1 ++ s2, hs2)
end

private def renderSafeAttrAcc (acc k v : String) : String :=
  let sk := sanitizeKey k
  if !isSafeRenderedKey sk || (isUrlAttrName sk && !isSafeUrl v) then acc else (escapeHtmlAcc (((acc.push ' ') ++ sk) ++ "=\"") v).push '"'

def renderAttrAcc (hs : Array msg) (acc : String) : Attr msg → String × Array msg
  | .cls c => ((escapeHtmlAcc (acc ++ " class=\"") c).push '"', hs)
  | .attr k v | .signalAttr _ k v => (renderSafeAttrAcc acc k v, hs)
  | .flag k present => let sk := sanitizeKey k; if !present || !isSafeRenderedKey sk then (acc, hs) else (((((acc.push ' ') ++ sk) ++ "=\"") ++ sk).push '"', hs)
  | .key _ | .onValue _ _ => (acc, hs)
  | .on event m | .signalOn _ event m => let ev := sanitizeKey event; if ev.isEmpty then (acc, hs) else (((((acc ++ " data-qed-on-") ++ ev) ++ "=\"") ++ toString hs.size).push '"', hs.push m)
  | .localCell key comp _ _ _ => ((escapeHtmlAcc (acc ++ " data-qed-local=\"") (localKey comp key)).push '"', hs)
  | .signalBind name => ((escapeHtmlAcc (acc ++ " data-qed-signal=\"") name).push '"', hs)

private theorem renderAttrAcc_eq (hs : Array msg) (acc : String) (a : Attr msg) : renderAttrAcc hs acc a = (acc ++ (renderAttr hs a).1, (renderAttr hs a).2) := by
  cases a <;> unfold renderAttrAcc renderAttr <;> dsimp only [renderSafeAttrAcc]
  all_goals (try split) <;> simp only [escapeHtmlAcc_eq, push_eq_append_r, show String.singleton '"' = "\"" from rfl, show String.singleton ' ' = " " from rfl, toString_string, String.append_assoc, String.append_empty]

def renderAttrsAcc (hs : Array msg) (acc : String) : List (Attr msg) → String × Array msg
  | [] => (acc, hs) | a :: as => let (acc1, hs1) := renderAttrAcc hs acc a; renderAttrsAcc hs1 acc1 as

private theorem renderAttrsAcc_eq (hs : Array msg) (acc : String) (as : List (Attr msg)) : renderAttrsAcc hs acc as = (acc ++ (renderAttrs hs as).1, (renderAttrs hs as).2) := by
  induction as generalizing hs acc with | nil => simp [renderAttrsAcc, renderAttrs] | cons _ _ ih => simp only [renderAttrsAcc, renderAttrAcc_eq, renderAttrs]; rw [ih, String.append_assoc]

@[inline] private def renderElemAttrsAcc (hs : Array msg) (acc : String) : List (Attr msg) → String × Array msg
  | [] | [.key _] => (acc, hs) | attrs => renderAttrsAcc hs acc (normalizeAttrs attrs)

private theorem renderElemAttrsAcc_eq (hs : Array msg) (acc : String) (attrs : List (Attr msg)) :
    renderElemAttrsAcc hs acc attrs = (acc ++ (renderAttrs hs (normalizeAttrs attrs)).1, (renderAttrs hs (normalizeAttrs attrs)).2) := by
  cases attrs with
  | nil => exact Prod.ext String.append_empty.symm rfl
  | cons a rest => cases a <;> cases rest <;> first | exact renderAttrsAcc_eq hs acc (normalizeAttrs _) | (change (acc, hs) = (acc ++ ("" ++ ""), hs); rw [String.append_empty, String.append_empty])

mutual
  def renderNodeAcc (hs : Array msg) (acc : String) : Html msg → String × Array msg
    | .text s => (escapeHtmlAcc acc s, hs)
    | .element tag attrs children =>
        let (acc1, hs1) := renderElemAttrsAcc hs ((acc.push '<') ++ tag) attrs
        if tag == "style" || tag == "script" then (((((acc1.push '>') ++ escapeRawText (String.join (children.map fun | .text s => s | _ => ""))) ++ "</") ++ tag).push '>', hs1)
        else if isVoidTag tag then (acc1.push '>', hs1)
        else if tag == "textarea" then
          let (childStr, hs2) := renderChildrenAcc hs1 "" children
          let acc2 := if childStr.front? == some '\n' then (acc1.push '>').push '\n' else acc1.push '>'
          ((((acc2 ++ childStr) ++ "</") ++ tag).push '>', hs2)
        else let (acc2, hs2) := renderChildrenAcc hs1 (acc1.push '>') children; (((acc2 ++ "</") ++ tag).push '>', hs2)
  def renderChildrenAcc (hs : Array msg) (acc : String) : List (Html msg) → String × Array msg
    | [] => (acc, hs) | c :: cs => let (acc', hs') := renderNodeAcc hs acc c; renderChildrenAcc hs' acc' cs
end

mutual
  theorem renderNodeAcc_eq (hs : Array msg) (acc : String) (h : Html msg) : renderNodeAcc hs acc h = (acc ++ (renderNode hs h).1, (renderNode hs h).2) := by
    cases h with
    | text _ => simp only [renderNodeAcc, renderNode, escapeHtmlAcc_eq]
    | element tag _ _ =>
        unfold renderNodeAcc renderNode renderElement; rw [renderElemAttrsAcc_eq]
        have hlt : String.singleton '<' = "<" := rfl; have hgt : String.singleton '>' = ">" := rfl; have hnl : String.singleton '\n' = "\n" := rfl
        cases (tag == "style" || tag == "script")
        · cases isVoidTag tag
          · cases (tag == "textarea")
            · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, renderChildrenAcc_eq, push_eq_append_r, hlt, hgt, toString_string, String.append_assoc]
            · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, renderChildrenAcc_eq, String.empty_append]
              split <;> simp only [push_eq_append_r, hlt, hgt, hnl, toString_string, String.append_assoc]
          · simp only [↓reduceIte, Bool.false_eq_true, push_eq_append_r, hlt, hgt, toString_string, String.append_assoc]
        · simp only [↓reduceIte, push_eq_append_r, hlt, hgt, toString_string, String.append_assoc]
  theorem renderChildrenAcc_eq (hs : Array msg) (acc : String) (cs : List (Html msg)) : renderChildrenAcc hs acc cs = (acc ++ (renderChildren hs cs).1, (renderChildren hs cs).2) := by
    cases cs with | nil => simp [renderChildrenAcc, renderChildren] | cons _ _ => simp only [renderChildrenAcc, renderNodeAcc_eq, renderChildren]; rw [renderChildrenAcc_eq, String.append_assoc]
end

def renderNodeFast (hs : Array msg) (h : Html msg) : String × Array msg := renderNodeAcc hs "" h
@[csimp] theorem renderNode_eq_renderNodeFast : @renderNode = @renderNodeFast := by funext _ hs h; simpa [renderNodeFast] using (renderNodeAcc_eq hs "" h).symm

def renderChildrenFast (hs : Array msg) (cs : List (Html msg)) : String × Array msg := renderChildrenAcc hs "" cs
@[csimp] theorem renderChildren_eq_renderChildrenFast : @renderChildren = @renderChildrenFast := by funext _ hs cs; simpa [renderChildrenFast] using (renderChildrenAcc_eq hs "" cs).symm

def Html.render (h : Html msg) : String := (renderNode #[] h).1
def Html.textOf? : Html msg → Option String | .text s => some s | _ => none

def restOfTextRun : List (Html msg) → String | [] => "" | c :: cs => match c.textOf? with | some s => s ++ restOfTextRun cs | none => ""
def hasMoreText : List (Html msg) → Bool | [] => false | c :: cs => match c.textOf? with | some "" => hasMoreText cs | some _ => true | none => false

mutual
  def coalesceTextRun : List (Html msg) → List (Html msg)
    | [] => [] | c :: cs => match c.textOf? with | some s => if s == "" then coalesceTextRun cs else .text (s ++ restOfTextRun cs) :: dropCurrentTextRun cs | none => c :: coalesceTextRun cs
  def dropCurrentTextRun : List (Html msg) → List (Html msg)
    | [] => [] | c :: cs => match c.textOf? with | some _ => dropCurrentTextRun cs | none => c :: coalesceTextRun cs
end

def hydrateChildrenSpec (inTextRun : Bool) : List (Html msg) → List (Html msg) → List (Html msg)
  | [], _ => []
  | c :: cs, dom => match c.textOf? with
      | some s => if s == "" then c :: hydrateChildrenSpec inTextRun cs dom else if inTextRun then c :: hydrateChildrenSpec true cs dom
                  else match dom with | _ :: domRest => c :: hydrateChildrenSpec true cs domRest | [] => []
      | none => match dom with | _ :: domRest => c :: hydrateChildrenSpec false cs domRest | [] => []

theorem hydrateChildrenSpec_roundtrip (cs : List (Html msg)) :
    hydrateChildrenSpec false cs (coalesceTextRun cs) = cs ∧ hydrateChildrenSpec true cs (dropCurrentTextRun cs) = cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c _ ih =>
      rcases ih with ⟨ihF, ihT⟩
      cases h : c.textOf? with
      | none => exact ⟨by simpa [hydrateChildrenSpec, coalesceTextRun, h] using ihF, by simpa [hydrateChildrenSpec, dropCurrentTextRun, h] using ihF⟩
      | some s => cases hs : (s == "") with
        | true  => exact ⟨by simpa [hydrateChildrenSpec, coalesceTextRun, h, hs] using ihF, by simpa [hydrateChildrenSpec, dropCurrentTextRun, h, hs] using ihT⟩
        | false => exact ⟨by simpa [hydrateChildrenSpec, coalesceTextRun, h, hs] using ihT, by simpa [hydrateChildrenSpec, dropCurrentTextRun, h, hs] using ihT⟩

theorem hydrate_coalesce (cs : List (Html msg)) : hydrateChildrenSpec false cs (coalesceTextRun cs) = cs := (hydrateChildrenSpec_roundtrip cs).1

/-! ## End-to-End Serialization & Valid-Attribute Preservation Closure -/

theorem sanitizeKey_of_safe {k : String} (hk : k.toList.all isKeyChar = true) : sanitizeKey k = k := by simp [sanitizeKey, hk]

theorem renderAttr_valid_attr (hs : Array msg) {k v : String} (hv : (Attr.attr k v : Attr msg).valid = true) :
    renderAttr hs (.attr k v) = (" " ++ k ++ "=\"" ++ escapeHtml v ++ "\"", hs) := by
  simp only [Attr.valid, Attr.validKeyValue, isSafeAttrName, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hv
  rcases hv with ⟨⟨hkc, hsafe⟩, hurl⟩
  have hnb : (!isSafeRenderedKey k || isUrlAttrName k && !isSafeUrl v) = false := by cases hu : isUrlAttrName k <;> rcases hurl with huF | hsUrl <;> simp_all
  simp [renderAttr, sanitizeKey_of_safe hkc, hnb]

theorem renderAttr_valid_flag (hs : Array msg) {k : String} (hv : (Attr.flag k true : Attr msg).valid = true) :
    renderAttr hs (.flag k true) = (" " ++ k ++ "=\"" ++ k ++ "\"", hs) := by
  simp only [Attr.valid, isSafeAttrName, Bool.and_eq_true] at hv; simp [renderAttr, sanitizeKey_of_safe hv.1, hv.2]

theorem renderAttr_valid_on (hs : Array msg) {ev : String} (m : msg) (hv : (Attr.on ev m).valid = true) (hne : ev ≠ "") :
    renderAttr hs (.on ev m) = (" data-qed-on-" ++ ev ++ "=\"" ++ toString hs.size ++ "\"", hs.push m) := by
  simp only [Attr.valid, isSafeAttrName, Bool.and_eq_true] at hv
  simp [renderAttr, sanitizeKey_of_safe hv.1, Bool.eq_false_iff.2 fun h => hne (String.isEmpty_iff.1 h)]

private abbrev NoAngle (c : Char) : Prop := c ≠ '<' ∧ c ≠ '>'

private theorem isKeyChar_no_angle {c : Char} (h : isKeyChar c = true) : NoAngle c := by
  unfold isKeyChar at h; simp only [Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨?_, ?_⟩ <;> intro heq <;> subst heq <;> simp [Char.isAlphanum, Char.isAlpha, Char.isDigit] at h

private theorem toDigitsCore_no_angle : ∀ (k m : Nat) (acc : List Char), (∀ c ∈ acc, NoAngle c) → ∀ c ∈ Nat.toDigitsCore 10 k m acc, NoAngle c
  | 0, _, _, hacc, c, hc => by rw [Nat.toDigitsCore.eq_1] at hc; exact hacc c hc
  | k + 1, m, acc, hacc, c, hc => by
      have hcons : ∀ x ∈ Nat.digitChar (m % 10) :: acc, NoAngle x := fun x hx =>
        (List.mem_cons.1 hx).elim (· ▸ (by decide : ∀ d : Fin 10, NoAngle (Nat.digitChar d.val)) ⟨m % 10, Nat.mod_lt _ (by decide)⟩) (hacc x)
      rw [Nat.toDigitsCore.eq_2] at hc; split at hc; exact hcons c hc; exact toDigitsCore_no_angle k (m / 10) _ hcons c hc

private theorem nat_repr_no_angle (n : Nat) : ∀ c ∈ (toString n).toList, NoAngle c := fun c hc => by
  change c ∈ (Nat.repr n).toList at hc; unfold Nat.repr Nat.toDigits at hc; rw [String.toList_ofList] at hc
  exact toDigitsCore_no_angle (n + 1) n [] (fun _ h => nomatch h) c hc

private theorem escapeHtml_no_angle (s : String) : ∀ c ∈ (escapeHtml s).toList, NoAngle c := fun c hc => by
  have hnm := escapeHtml_no_markup_or_quote s c hc; simp only [isMarkupOrQuote, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnm; exact ⟨hnm.1.1.1, hnm.1.1.2⟩

private theorem lit_no_angle (s : String) (h : s.toList.all (fun c => c != '<' && c != '>') = true) : ∀ c ∈ s.toList, NoAngle c :=
  fun c hc => by simpa only [Bool.and_eq_true, bne_iff_ne] using List.all_eq_true.1 h c hc

def Html.EveryElementSafe : Html msg → Prop
  | .text _ => True
  | .element tag attrs children =>
      isSafeTagName tag = true ∧ isForbiddenTag tag = false ∧ Attr.validList attrs = true ∧ (!isVoidTag tag || children.isEmpty) = true ∧
      (tag == "style" → containsCloseSeq (escapeRawText (String.join (children.map fun | .text s => s | _ => ""))).toList = false) ∧ ∀ c ∈ children, Html.EveryElementSafe c

mutual
  theorem Html.validIn_everyElementSafe (ctx : HtmlCtx) : (h : Html msg) → Html.validIn ctx h = true → Html.EveryElementSafe h
    | .text _, _ => by simp only [Html.EveryElementSafe]
    | .element tag attrs children, hv => by
        simp only [Html.validIn, Bool.and_eq_true] at hv; rcases hv with ⟨⟨⟨hattrs, hvoid⟩, _⟩, hrest⟩
        cases hctx : stepHtmlCtx ctx tag with
        | none => simp [hctx] at hrest
        | some childCtx =>
            simp only [hctx] at hrest; unfold stepHtmlCtx at hctx
            by_cases hbad : (!isSafeTagName tag || isForbiddenTag tag) = true
            · simp [hbad] at hctx
            · have hok : isSafeTagName tag = true ∧ isForbiddenTag tag = false := by simpa only [Bool.or_eq_false_iff, Bool.not_eq_false'] using Bool.eq_false_iff.2 hbad
              simp only [Html.EveryElementSafe]
              exact ⟨hok.1, hok.2, hattrs, hvoid, fun _ => containsCloseSeq_escapeRawText _, Html.validListIn_everyElementSafe childCtx children hrest⟩
  theorem Html.validListIn_everyElementSafe (ctx : HtmlCtx) : (cs : List (Html msg)) → Html.validListIn ctx cs = true → ∀ c ∈ cs, Html.EveryElementSafe c
    | [], _, _, h => nomatch h
    | y :: ys, hy, x, hx => by
        simp only [Html.validListIn, Bool.and_eq_true] at hy
        exact (List.mem_cons.1 hx).elim (· ▸ Html.validIn_everyElementSafe ctx y hy.1) (Html.validListIn_everyElementSafe ctx ys hy.2 x)
end

theorem Html.valid_everyElementSafe {h : Html msg} (hv : Html.valid h = true) : Html.EveryElementSafe h := Html.validIn_everyElementSafe {} h hv

theorem renderAttr_no_angle_brackets (hs : Array msg) (a : Attr msg) : ∀ c ∈ (renderAttr hs a).1.toList, c ≠ '<' ∧ c ≠ '>' := by
  cases a <;> simp only [renderAttr] <;> (try split) <;> (try simp only [toString_string])
  all_goals
    intro c; try simp only [String.toList_append, List.mem_append, or_imp]
    repeat refine And.intro ?_ ?_
    all_goals (revert c; first
      | with_reducible exact escapeHtml_no_angle _ | with_reducible exact nat_repr_no_angle _
      | with_reducible exact fun _ hc => isKeyChar_no_angle (sanitizeKey_safe _ _ hc) | (apply lit_no_angle; decide))

theorem renderAttrs_no_angle_brackets (hs : Array msg) : ∀ (attrs : List (Attr msg)), ∀ c ∈ (renderAttrs hs attrs).1.toList, c ≠ '<' ∧ c ≠ '>'
  | [] => lit_no_angle "" rfl
  | a :: as => fun c hc => by rw [renderAttrs, String.toList_append, List.mem_append] at hc; exact hc.elim (renderAttr_no_angle_brackets hs a c) (renderAttrs_no_angle_brackets (renderAttr hs a).2 as c)

end Qed
