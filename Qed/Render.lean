import Qed.Html

namespace Qed

def localKey (component key : String) : String := component ++ "@" ++ key

@[inline] def isMarkupOrQuote (c : Char) : Bool :=
  c == '<' || c == '>' || c == '"' || c == '\''

@[inline] def isHtmlSpecial (c : Char) : Bool :=
  c == '&' || isMarkupOrQuote c

def escapeHtmlStep (acc : String) (c : Char) : String :=
  if c == '&' then acc ++ "&amp;"
  else if c == '<' then acc ++ "&lt;"
  else if c == '>' then acc ++ "&gt;"
  else if c == '"' then acc ++ "&quot;"
  else if c == '\'' then acc ++ "&#39;"
  else acc.push c

def escapeHtml (s : String) : String :=
  let cs := s.toList
  if !cs.any isHtmlSpecial then s
  else cs.foldl escapeHtmlStep ""

@[inline] private def isHtmlSpecialByte (b : UInt8) : Bool :=
  b <= 62 && (b == 38 || b == 60 || b == 62 || b == 34 || b == 39)

def escapeHtmlAcc (acc s : String) : String :=
  if !hasAsciiByte s isHtmlSpecialByte then acc ++ s
  else s.foldl escapeHtmlStep acc

def escapeHtmlFast (s : String) : String := escapeHtmlAcc "" s

private theorem isHtmlSpecialByte_eq (c : Char) (hc : c.toNat ≤ 127) :
    isHtmlSpecialByte (UInt8.ofNat c.toNat) = isHtmlSpecial c := by
  unfold isHtmlSpecialByte isHtmlSpecial isMarkupOrQuote
  have hlt : (UInt8.ofNat c.toNat).toNat = c.toNat := by change c.toNat % 256 = c.toNat; omega
  change (decide (UInt8.ofNat c.toNat ≤ 62) &&
    ((UInt8.ofNat c.toNat == UInt8.ofNat '&'.toNat) ||
     (UInt8.ofNat c.toNat == UInt8.ofNat '<'.toNat) ||
     (UInt8.ofNat c.toNat == UInt8.ofNat '>'.toNat) ||
     (UInt8.ofNat c.toNat == UInt8.ofNat '"'.toNat) ||
     (UInt8.ofNat c.toNat == UInt8.ofNat '\''.toNat))) = _
  rw [asciiByte_beq_char c hc '&' (by decide), asciiByte_beq_char c hc '<' (by decide),
      asciiByte_beq_char c hc '>' (by decide), asciiByte_beq_char c hc '"' (by decide),
      asciiByte_beq_char c hc '\'' (by decide)]
  by_cases hle : c.toNat ≤ 62
  · have hle' : decide (UInt8.ofNat c.toNat ≤ 62) = true := by
      rw [decide_eq_true_iff]; change (UInt8.ofNat c.toNat).toNat ≤ 62; omega
    simp [hle', Bool.or_assoc]
  · have hle' : decide (UInt8.ofNat c.toNat ≤ 62) = false := by
      rw [decide_eq_false_iff_not]; change ¬((UInt8.ofNat c.toNat).toNat ≤ 62); omega
    have hne : ∀ t : Char, t.toNat ≤ 62 → (c == t) = false := by
      intro t ht; rw [beq_eq_false_iff_ne]; intro heq; subst heq; omega
    simp [hle', hne '&' (by decide), hne '<' (by decide), hne '>' (by decide),
      hne '"' (by decide), hne '\'' (by decide)]

private theorem foldl_escapeHtmlStep_append (cs : List Char) (acc : String) :
    cs.foldl escapeHtmlStep acc = acc ++ cs.foldl escapeHtmlStep "" := by
  have hstep : ∀ (a b : String) (c : Char), escapeHtmlStep (a ++ b) c = a ++ escapeHtmlStep b c := by
    intro a b c; unfold escapeHtmlStep
    repeat' split
    all_goals (ext; simp [String.append_assoc])
  have hgen : ∀ (cs : List Char) (a b : String), cs.foldl escapeHtmlStep (a ++ b) = a ++ cs.foldl escapeHtmlStep b := by
    intro cs; induction cs with
    | nil => intro _ _; rfl
    | cons c cs ih => intro a b; simp only [List.foldl_cons, hstep, ih]
  simpa using hgen cs acc ""

private theorem escapeHtmlAcc_eq (acc s : String) : escapeHtmlAcc acc s = acc ++ escapeHtml s := by
  unfold escapeHtmlAcc escapeHtml; dsimp only
  have h1 : hasAsciiByte s isHtmlSpecialByte = s.toList.any isHtmlSpecial := by
    apply hasAsciiByte_eq_any
    · intro b hb
      unfold isHtmlSpecialByte
      have : decide (b ≤ 62) = false := by rw [decide_eq_false_iff_not]; change ¬(b.toNat ≤ 62); omega
      simp [this]
    · exact isHtmlSpecialByte_eq
    · intro c hgt
      unfold isHtmlSpecial isMarkupOrQuote
      have hne : ∀ t : Char, t.toNat ≤ 127 → (c == t) = false := by
        intro t ht; rw [beq_eq_false_iff_ne]; intro heq; subst heq; omega
      simp [hne '&' (by decide), hne '<' (by decide), hne '>' (by decide),
        hne '"' (by decide), hne '\'' (by decide)]
  have h2 : s.foldl escapeHtmlStep acc = s.toList.foldl escapeHtmlStep acc := by simp
  rw [h1, h2]
  cases ha : s.toList.any isHtmlSpecial with
  | false => simp
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact foldl_escapeHtmlStep_append s.toList acc

@[csimp] theorem escapeHtml_eq_escapeHtmlFast : @escapeHtml = @escapeHtmlFast := by
  funext s; simpa [escapeHtmlFast] using (escapeHtmlAcc_eq "" s).symm

private theorem isMarkupOrQuote_false_of_not_special {c : Char} (h : isHtmlSpecial c = false) :
    isMarkupOrQuote c = false :=
  (Bool.or_eq_false_iff.1 h).2

private theorem escapeHtmlStep_safe (acc : String) (c : Char)
    (hacc : acc.toList.all (!isMarkupOrQuote ·) = true) :
    (escapeHtmlStep acc c).toList.all (!isMarkupOrQuote ·) = true := by
  unfold escapeHtmlStep
  by_cases h1 : c == '&'
  · rw [if_pos h1, String.toList_append, List.all_append, hacc]; decide
  · rw [if_neg h1]
    by_cases h2 : c == '<'
    · rw [if_pos h2, String.toList_append, List.all_append, hacc]; decide
    · rw [if_neg h2]
      by_cases h3 : c == '>'
      · rw [if_pos h3, String.toList_append, List.all_append, hacc]; decide
      · rw [if_neg h3]
        by_cases h4 : c == '"'
        · rw [if_pos h4, String.toList_append, List.all_append, hacc]; decide
        · rw [if_neg h4]
          by_cases h5 : c == '\''
          · rw [if_pos h5, String.toList_append, List.all_append, hacc]; decide
          · rw [if_neg h5, String.toList_push, List.all_append, hacc]
            unfold isMarkupOrQuote
            simp [Bool.eq_false_iff.2 h2, Bool.eq_false_iff.2 h3,
                  Bool.eq_false_iff.2 h4, Bool.eq_false_iff.2 h5]

private theorem foldl_escapeHtmlStep_safe :
    ∀ (cs : List Char) (acc : String),
      acc.toList.all (!isMarkupOrQuote ·) = true →
      (cs.foldl escapeHtmlStep acc).toList.all (!isMarkupOrQuote ·) = true
  | [], _, hacc => hacc
  | c :: cs, acc, hacc =>
      foldl_escapeHtmlStep_safe cs (escapeHtmlStep acc c) (escapeHtmlStep_safe acc c hacc)

/-- Every character emitted by `escapeHtml` is free of `<`, `>`, `"`, and `'`,
    making both HTML tag injection in text nodes and quote breakout in attributes impossible. -/
theorem escapeHtml_no_markup_or_quote (s : String) :
    ∀ c ∈ (escapeHtml s).toList, isMarkupOrQuote c = false := by
  unfold escapeHtml
  dsimp only
  by_cases h : s.toList.any isHtmlSpecial = true
  · simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hall := foldl_escapeHtmlStep_safe s.toList "" (by decide)
    rw [List.all_eq_true] at hall
    intro c hc
    simpa using hall c hc
  · have hf : s.toList.any isHtmlSpecial = false := Bool.eq_false_iff.2 h
    simp only [hf, Bool.not_false, ↓reduceIte]
    rw [List.any_eq_false] at hf
    intro c hc
    have hns : isHtmlSpecial c = false := Bool.eq_false_iff.2 (hf c hc)
    exact isMarkupOrQuote_false_of_not_special hns

def Attr.key? : Attr msg → Option String
  | .attr k _ => some k
  | .flag k _ => some k
  | _         => none

def dedupAttrs : List (Attr msg) → List (Attr msg)
  | []        => []
  | a :: rest =>
      match a.key? with
      | none   => a :: dedupAttrs rest
      | some k => if rest.any (·.key? == some k) then dedupAttrs rest else a :: dedupAttrs rest

def normalizeAttrs (attrs : List (Attr msg)) : List (Attr msg) :=
  let classes := (attrs.filterMap (fun | .cls c => some c | _ => none)).filter (· != "")
  let merged  := if classes.isEmpty then [] else [Attr.cls (String.intercalate " " classes)]
  merged ++ dedupAttrs (attrs.filter (fun | .cls _ => false | _ => true))

def sanitizeKey (k : String) : String :=
  let cs := k.toList
  if cs.all isKeyChar then k
  else String.ofList (cs.filter isKeyChar)

def sanitizeKeyFast (k : String) : String :=
  if k.foldl (fun b c => b && isKeyChar c) true then k
  else k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) ""

private theorem foldl_and_eq_all_r (p : Char → Bool) (cs : List Char) (init : Bool) :
    cs.foldl (fun b c => b && p c) init = (init && cs.all p) := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih => simp [ih, Bool.and_assoc]

private theorem foldl_filterPush_eq (p : Char → Bool) (cs : List Char) (acc : String) :
    cs.foldl (fun a c => if p c then a.push c else a) acc = acc ++ String.ofList (cs.filter p) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.filter_cons]
      cases hp : p c with
      | false => simpa using ih acc
      | true =>
          simp only [↓reduceIte, ih]
          ext; simp

@[csimp] theorem sanitizeKey_eq_sanitizeKeyFast : @sanitizeKey = @sanitizeKeyFast := by
  funext k
  unfold sanitizeKey sanitizeKeyFast
  have h1 : k.foldl (fun b c => b && isKeyChar c) true = k.toList.all isKeyChar := by
    have hf : k.foldl (fun b c => b && isKeyChar c) true =
        k.toList.foldl (fun b c => b && isKeyChar c) true := by simp
    rw [hf, foldl_and_eq_all_r, Bool.true_and]
  have h2 : k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" =
      String.ofList (k.toList.filter isKeyChar) := by
    have hf : k.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" =
        k.toList.foldl (fun acc c => if isKeyChar c then acc.push c else acc) "" := by simp
    rw [hf, foldl_filterPush_eq]; simp
  rw [h1, h2]

/-- Every character in `sanitizeKey k` is strictly alphanumeric or in `{- _ : .}`,
    preventing whitespace, `=`, quotes, `<`, `>`, or `/` from ever appearing in an attribute name. -/
theorem sanitizeKey_safe (k : String) :
    ∀ c ∈ (sanitizeKey k).toList, isKeyChar c = true := by
  unfold sanitizeKey
  dsimp only
  by_cases h : k.toList.all isKeyChar = true
  · simp only [h, ↓reduceIte]
    rw [List.all_eq_true] at h
    exact h
  · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
    intro c hc
    exact (List.mem_filter.1 hc).2

def renderAttr (hs : Array msg) : Attr msg → String × Array msg
  | .cls c     => (s!" class=\"{escapeHtml c}\"", hs)
  | .attr k v  =>
      let sk := sanitizeKey k
      if !isSafeRenderedKey sk || (isUrlAttrName sk && !isSafeUrl v) then ("", hs)
      else (s!" {sk}=\"{escapeHtml v}\"", hs)
  | .flag k present =>
      let sk := sanitizeKey k
      if !present || !isSafeRenderedKey sk then ("", hs)
      else (s!" {sk}=\"{sk}\"", hs)
  | .key _     => ("", hs)
  | .on event m | .signalOn _ event m =>
      let ev := sanitizeKey event
      if ev.isEmpty then ("", hs)
      else (s!" data-qed-on-{ev}=\"{hs.size}\"", hs.push m)
  | .onValue _ _ => ("", hs)
  | .localCell key comp _ _ _ => (s!" data-qed-local=\"{escapeHtml (localKey comp key)}\"", hs)
  | .signalBind name        => (s!" data-qed-signal=\"{escapeHtml name}\"", hs)
  | .signalAttr _ attr value =>
      let sk := sanitizeKey attr
      if !isSafeRenderedKey sk || (isUrlAttrName sk && !isSafeUrl value) then ("", hs)
      else (s!" {sk}=\"{escapeHtml value}\"", hs)

/-- Defense-in-depth: inline event handler attributes (`on*`) are unconditionally stripped
    by `renderAttr`, even if constructed programmatically outside JSX. -/
theorem renderAttr_blocks_inline_handler (hs : Array msg) (k v : String)
    (hon : hasOnPrefix ((sanitizeKey k).toList.map asciiLowerChar) = true) :
    (renderAttr hs (.attr k v)).1 = "" := by
  simp [renderAttr, isSafeRenderedKey, hon]

/-- Defense-in-depth: `srcdoc` attributes (case-insensitive) are unconditionally stripped. -/
theorem renderAttr_blocks_srcdoc (hs : Array msg) (k v : String)
    (hsd : asciiLower (sanitizeKey k) = "srcdoc") :
    (renderAttr hs (.attr k v)).1 = "" := by
  simp [renderAttr, isSafeRenderedKey, hsd]

/-- Defense-in-depth: URL-bearing attributes (`href`, `src`, `action`, `formaction`, `xlink:href`,
    `poster`, `data`, `cite`, `srcset`) with unsafe schemes (`javascript:`, `data:`, `vbscript:`,
    `//`, `/\`, whitespace/control chars) are unconditionally stripped. -/
theorem renderAttr_blocks_unsafe_url (hs : Array msg) (k v : String)
    (hurl : isUrlAttrName (sanitizeKey k) = true) (hbad : isSafeUrl v = false) :
    (renderAttr hs (.attr k v)).1 = "" := by
  simp [renderAttr, hurl, hbad]

def renderAttrs (hs : Array msg) : List (Attr msg) → String × Array msg
  | []      => ("", hs)
  | a :: as =>
      let (s1, hs1) := renderAttr hs a
      let (s2, hs2) := renderAttrs hs1 as
      (s1 ++ s2, hs2)

def renderElement (renderKids : Array msg → String × Array msg) (hs : Array msg)
    (tag : String) (attrs : List (Attr msg)) (children : List (Html msg)) : String × Array msg :=
  let (attrStr, hs1) := renderAttrs hs (normalizeAttrs attrs)
  if tag == "style" || tag == "script" then
    -- Escape `</` → `<\/` so text inside raw-text elements cannot close `<style>`/`<script>` early.
    let raw := escapeRawText (String.join (children.map fun | .text s => s | _ => ""))
    (s!"<{tag}{attrStr}>{raw}</{tag}>", hs1)
  else if isVoidTag tag then
    (s!"<{tag}{attrStr}>", hs1)
  else
    let (childStr, hs2) := renderKids hs1
    let body := if tag == "textarea" && childStr.front? == some '\n' then "\n" ++ childStr else childStr
    (s!"<{tag}{attrStr}>{body}</{tag}>", hs2)

mutual
  def renderNode (hs : Array msg) : Html msg → String × Array msg
    | .text s => (escapeHtml s, hs)
    | .element tag attrs children => renderElement (fun hs => renderChildren hs children) hs tag attrs children
  def renderChildren (hs : Array msg) : List (Html msg) → String × Array msg
    | [] => ("", hs)
    | c :: cs =>
        let (s1, hs1) := renderNode hs c
        let (s2, hs2) := renderChildren hs1 cs
        (s1 ++ s2, hs2)
end

private def renderSafeAttrAcc (acc k v : String) : String :=
  let sk := sanitizeKey k
  if !isSafeRenderedKey sk || (isUrlAttrName sk && !isSafeUrl v) then acc
  else (escapeHtmlAcc (((acc.push ' ') ++ sk) ++ "=\"") v).push '"'

def renderAttrAcc (hs : Array msg) (acc : String) : Attr msg → String × Array msg
  | .cls c => ((escapeHtmlAcc (acc ++ " class=\"") c).push '"', hs)
  | .attr k v | .signalAttr _ k v => (renderSafeAttrAcc acc k v, hs)
  | .flag k present =>
      let sk := sanitizeKey k
      if !present || !isSafeRenderedKey sk then (acc, hs)
      else (((((acc.push ' ') ++ sk) ++ "=\"") ++ sk).push '"', hs)
  | .key _ | .onValue _ _ => (acc, hs)
  | .on event m | .signalOn _ event m =>
      let ev := sanitizeKey event
      if ev.isEmpty then (acc, hs)
      else (((((acc ++ " data-qed-on-") ++ ev) ++ "=\"") ++ toString hs.size).push '"', hs.push m)
  | .localCell key comp _ _ _ => ((escapeHtmlAcc (acc ++ " data-qed-local=\"") (localKey comp key)).push '"', hs)
  | .signalBind name => ((escapeHtmlAcc (acc ++ " data-qed-signal=\"") name).push '"', hs)

private theorem push_eq_append_r (a : String) (c : Char) : a.push c = a ++ String.singleton c := by
  ext; simp

private theorem renderAttrAcc_eq (hs : Array msg) (acc : String) (a : Attr msg) :
    renderAttrAcc hs acc a = (acc ++ (renderAttr hs a).1, (renderAttr hs a).2) := by
  cases a <;> unfold renderAttrAcc renderAttr <;> dsimp only [renderSafeAttrAcc]
  all_goals first
    | (simp; done)
    | (simp only [escapeHtmlAcc_eq, push_eq_append_r, String.append_assoc]; rfl)
    | (split <;> first | (simp; done) | (simp only [escapeHtmlAcc_eq, push_eq_append_r, String.append_assoc]; rfl))

def renderAttrsAcc (hs : Array msg) (acc : String) : List (Attr msg) → String × Array msg
  | []      => (acc, hs)
  | a :: as =>
      let (acc1, hs1) := renderAttrAcc hs acc a
      renderAttrsAcc hs1 acc1 as

private theorem renderAttrsAcc_eq (hs : Array msg) (acc : String) (as : List (Attr msg)) :
    renderAttrsAcc hs acc as = (acc ++ (renderAttrs hs as).1, (renderAttrs hs as).2) := by
  induction as generalizing hs acc with
  | nil => simp [renderAttrsAcc, renderAttrs]
  | cons a as ih =>
      simp only [renderAttrsAcc, renderAttrAcc_eq, renderAttrs]
      rw [ih, String.append_assoc]

@[inline] private def renderElemAttrsAcc (hs : Array msg) (acc : String) : List (Attr msg) → String × Array msg
  | []        => (acc, hs)
  | [.key _]  => (acc, hs)
  | attrs     => renderAttrsAcc hs acc (normalizeAttrs attrs)

private theorem renderElemAttrsAcc_eq (hs : Array msg) (acc : String) (attrs : List (Attr msg)) :
    renderElemAttrsAcc hs acc attrs =
      (acc ++ (renderAttrs hs (normalizeAttrs attrs)).1, (renderAttrs hs (normalizeAttrs attrs)).2) := by
  cases attrs with
  | nil => simp [renderElemAttrsAcc, normalizeAttrs, dedupAttrs, renderAttrs]
  | cons a rest =>
      cases a with
      | key k =>
          cases rest with
          | nil => simp [renderElemAttrsAcc, normalizeAttrs, dedupAttrs, Attr.key?, renderAttrs, renderAttr]
          | cons b rest' => exact renderAttrsAcc_eq hs acc (normalizeAttrs (.key k :: b :: rest'))
      | _ => exact renderAttrsAcc_eq hs acc (normalizeAttrs (_ :: rest))

mutual
  def renderNodeAcc (hs : Array msg) (acc : String) : Html msg → String × Array msg
    | .text s => (escapeHtmlAcc acc s, hs)
    | .element tag attrs children =>
        let (acc1, hs1) := renderElemAttrsAcc hs ((acc.push '<') ++ tag) attrs
        if tag == "style" || tag == "script" then
          let raw := escapeRawText (String.join (children.map fun | .text s => s | _ => ""))
          (((((acc1.push '>') ++ raw) ++ "</") ++ tag).push '>', hs1)
        else if isVoidTag tag then
          (acc1.push '>', hs1)
        else if tag == "textarea" then
          let (childStr, hs2) := renderChildrenAcc hs1 "" children
          let acc2 := if childStr.front? == some '\n' then (acc1.push '>').push '\n' else acc1.push '>'
          ((((acc2 ++ childStr) ++ "</") ++ tag).push '>', hs2)
        else
          let (acc2, hs2) := renderChildrenAcc hs1 (acc1.push '>') children
          (((acc2 ++ "</") ++ tag).push '>', hs2)
  def renderChildrenAcc (hs : Array msg) (acc : String) : List (Html msg) → String × Array msg
    | [] => (acc, hs)
    | c :: cs =>
        let (acc', hs') := renderNodeAcc hs acc c
        renderChildrenAcc hs' acc' cs
end

mutual
  theorem renderNodeAcc_eq (hs : Array msg) (acc : String) (h : Html msg) :
      renderNodeAcc hs acc h = (acc ++ (renderNode hs h).1, (renderNode hs h).2) := by
    cases h with
    | text s => simp [renderNodeAcc, renderNode, escapeHtmlAcc_eq]
    | element tag attrs children =>
        unfold renderNodeAcc renderNode renderElement
        rw [renderElemAttrsAcc_eq]
        by_cases hraw : (tag == "style" || tag == "script") = true
        · simp only [hraw, ↓reduceIte, push_eq_append_r, String.append_assoc]; rfl
        · have hrawF : (tag == "style" || tag == "script") = false := Bool.eq_false_iff.2 hraw
          simp only [hrawF, Bool.false_eq_true, ↓reduceIte]
          by_cases hvoid : isVoidTag tag = true
          · simp only [hvoid, ↓reduceIte, push_eq_append_r, String.append_assoc]; rfl
          · have hvoidF : isVoidTag tag = false := Bool.eq_false_iff.2 hvoid
            simp only [hvoidF, Bool.false_eq_true, ↓reduceIte]
            by_cases hta : (tag == "textarea") = true
            · simp only [hta, ↓reduceIte, renderChildrenAcc_eq, String.empty_append, Bool.true_and]
              split <;> (simp only [push_eq_append_r, String.append_assoc]; rfl)
            · have htaF : (tag == "textarea") = false := Bool.eq_false_iff.2 hta
              simp only [htaF, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
                renderChildrenAcc_eq, push_eq_append_r, String.append_assoc]; rfl
  theorem renderChildrenAcc_eq (hs : Array msg) (acc : String) (cs : List (Html msg)) :
      renderChildrenAcc hs acc cs =
        (acc ++ (renderChildren hs cs).1, (renderChildren hs cs).2) := by
    cases cs with
    | nil => simp [renderChildrenAcc, renderChildren]
    | cons c cs =>
        simp only [renderChildrenAcc, renderNodeAcc_eq, renderChildren]
        rw [renderChildrenAcc_eq, String.append_assoc]
end

def renderNodeFast (hs : Array msg) (h : Html msg) : String × Array msg :=
  renderNodeAcc hs "" h

@[csimp] theorem renderNode_eq_renderNodeFast : @renderNode = @renderNodeFast := by
  funext msg hs h
  simpa [renderNodeFast] using (renderNodeAcc_eq hs "" h).symm

def renderChildrenFast (hs : Array msg) (cs : List (Html msg)) : String × Array msg :=
  renderChildrenAcc hs "" cs

@[csimp] theorem renderChildren_eq_renderChildrenFast : @renderChildren = @renderChildrenFast := by
  funext msg hs cs
  simpa [renderChildrenFast] using (renderChildrenAcc_eq hs "" cs).symm

def Html.render (h : Html msg) : String := (renderNode #[] h).1

def Html.textOf? : Html msg → Option String
  | .text s => some s
  | _       => none

def restOfTextRun : List (Html msg) → String
  | []      => ""
  | c :: cs =>
      match c.textOf? with
      | some s => s ++ restOfTextRun cs
      | none   => ""

def hasMoreText : List (Html msg) → Bool
  | []      => false
  | c :: cs =>
      match c.textOf? with
      | some "" => hasMoreText cs
      | some _  => true
      | none    => false

mutual
  def coalesceTextRun : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs =>
        match c.textOf? with
        | some s =>
            if s == "" then coalesceTextRun cs
            else .text (s ++ restOfTextRun cs) :: dropCurrentTextRun cs
        | none => c :: coalesceTextRun cs

  def dropCurrentTextRun : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs =>
        match c.textOf? with
        | some _ => dropCurrentTextRun cs
        | none   => c :: coalesceTextRun cs
end

def hydrateChildrenSpec (inTextRun : Bool) : List (Html msg) → List (Html msg) → List (Html msg)
  | [],      _   => []
  | c :: cs, dom =>
      match c.textOf? with
      | some s =>
          if s == "" then
            c :: hydrateChildrenSpec inTextRun cs dom
          else if inTextRun then
            c :: hydrateChildrenSpec true cs dom
          else
            match dom with
            | _ :: domRest => c :: hydrateChildrenSpec true cs domRest
            | []           => []
      | none =>
          match dom with
          | _ :: domRest => c :: hydrateChildrenSpec false cs domRest
          | []           => []

theorem hydrateChildrenSpec_roundtrip (cs : List (Html msg)) :
    hydrateChildrenSpec false cs (coalesceTextRun cs) = cs ∧
    hydrateChildrenSpec true cs (dropCurrentTextRun cs) = cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c rest ih =>
      rcases ih with ⟨ihFalse, ihTrue⟩
      cases h : c.textOf? with
      | none =>
          refine ⟨?_, ?_⟩ <;> simpa [hydrateChildrenSpec, coalesceTextRun, dropCurrentTextRun, h] using ihFalse
      | some s =>
          cases hs : (s == "") with
          | true =>
              refine ⟨?_, ?_⟩
              · simpa [hydrateChildrenSpec, coalesceTextRun, h, hs] using ihFalse
              · simpa [hydrateChildrenSpec, dropCurrentTextRun, h, hs] using ihTrue
          | false =>
              refine ⟨?_, ?_⟩
              · simpa [hydrateChildrenSpec, coalesceTextRun, h, hs] using ihTrue
              · simpa [hydrateChildrenSpec, dropCurrentTextRun, h, hs] using ihTrue

theorem hydrate_coalesce (cs : List (Html msg)) :
    hydrateChildrenSpec false cs (coalesceTextRun cs) = cs :=
  (hydrateChildrenSpec_roundtrip cs).1

/-! ## End-to-End Serialization & Valid-Attribute Preservation Closure -/

theorem sanitizeKey_of_safe {k : String} (hk : k.toList.all isKeyChar = true) :
    sanitizeKey k = k := by
  simp [sanitizeKey, hk]

theorem renderAttr_valid_attr (hs : Array msg) {k v : String}
    (hv : (Attr.attr k v : Attr msg).valid = true) :
    renderAttr hs (.attr k v) = (" " ++ k ++ "=\"" ++ escapeHtml v ++ "\"", hs) := by
  simp only [Attr.valid, Attr.validKeyValue, isSafeAttrName, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hv
  rcases hv with ⟨⟨hkc, hsafe⟩, hurl⟩
  have hsk : sanitizeKey k = k := sanitizeKey_of_safe hkc
  have hnotBad : (!isSafeRenderedKey k || isUrlAttrName k && !isSafeUrl v) = false := by
    cases hu : isUrlAttrName k with
    | false => simp [hsafe]
    | true =>
        rcases hurl with huF | hsUrl
        · simp [hu] at huF
        · simp [hsafe, hsUrl]
  simp [renderAttr, hsk, hnotBad]

theorem renderAttr_valid_flag (hs : Array msg) {k : String}
    (hv : (Attr.flag k true : Attr msg).valid = true) :
    renderAttr hs (.flag k true) = (" " ++ k ++ "=\"" ++ k ++ "\"", hs) := by
  simp only [Attr.valid, isSafeAttrName, Bool.and_eq_true] at hv
  have hsk : sanitizeKey k = k := sanitizeKey_of_safe hv.1
  simp [renderAttr, hsk, hv.2]

theorem renderAttr_valid_on (hs : Array msg) {ev : String} (m : msg)
    (hv : (Attr.on ev m).valid = true) (hne : ev ≠ "") :
    renderAttr hs (.on ev m) = (" data-qed-on-" ++ ev ++ "=\"" ++ toString hs.size ++ "\"", hs.push m) := by
  simp only [Attr.valid, isSafeAttrName, Bool.and_eq_true] at hv
  have hsk : sanitizeKey ev = ev := sanitizeKey_of_safe hv.1
  have hneB : ev.isEmpty = false := by
    cases he : ev.isEmpty with
    | false => rfl
    | true => exact absurd (String.isEmpty_iff.1 he) hne
  simp [renderAttr, hsk, hneB]

private theorem isKeyChar_no_angle {c : Char} (h : isKeyChar c = true) : c ≠ '<' ∧ c ≠ '>' := by
  unfold isKeyChar at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨?_, ?_⟩ <;> intro heq <;> subst heq <;> simp [Char.isAlphanum, Char.isAlpha, Char.isDigit] at h

private theorem digitChar_no_angle (d : Nat) (hd : d < 10) :
    Nat.digitChar d ≠ '<' ∧ Nat.digitChar d ≠ '>' := by
  match d, hd with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
  | _ + 10, h => omega

private theorem toDigitsCore_no_angle :
    ∀ (k m : Nat) (acc : List Char),
      (∀ c ∈ acc, c ≠ '<' ∧ c ≠ '>') →
      ∀ c ∈ Nat.toDigitsCore 10 k m acc, c ≠ '<' ∧ c ≠ '>'
  | 0, m, acc, hacc, c, hc => by
      rw [Nat.toDigitsCore.eq_1] at hc
      exact hacc c hc
  | k + 1, m, acc, hacc, c, hc => by
      rw [Nat.toDigitsCore.eq_2] at hc
      split at hc
      · rcases List.mem_cons.1 hc with rfl | hmem
        · exact digitChar_no_angle (m % 10) (Nat.mod_lt _ (by decide))
        · exact hacc c hmem
      · exact toDigitsCore_no_angle k (m / 10) (Nat.digitChar (m % 10) :: acc)
          (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hmem
            · exact digitChar_no_angle (m % 10) (Nat.mod_lt _ (by decide))
            · exact hacc x hmem)
          c hc

private theorem nat_repr_no_angle (n : Nat) :
    ∀ c ∈ (toString n).toList, c ≠ '<' ∧ c ≠ '>' := by
  intro c hc
  change c ∈ (Nat.repr n).toList at hc
  unfold Nat.repr Nat.toDigits at hc
  rw [String.toList_ofList] at hc
  exact toDigitsCore_no_angle (n + 1) n [] (fun _ h => nomatch h) c hc

private theorem escapeHtml_no_angle (s : String) :
    ∀ c ∈ (escapeHtml s).toList, c ≠ '<' ∧ c ≠ '>' := by
  intro c hc
  have hnm := escapeHtml_no_markup_or_quote s c hc
  simp only [isMarkupOrQuote, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnm
  exact ⟨hnm.1.1.1, hnm.1.1.2⟩

private theorem str_append_no_angle {a b : String}
    (ha : ∀ c ∈ a.toList, c ≠ '<' ∧ c ≠ '>')
    (hb : ∀ c ∈ b.toList, c ≠ '<' ∧ c ≠ '>') :
    ∀ c ∈ (a ++ b).toList, c ≠ '<' ∧ c ≠ '>' := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with h1 | h2
  · exact ha c h1
  · exact hb c h2

private theorem lit_no_angle (s : String) (h : s.toList.all (fun c => c != '<' && c != '>') = true) :
    ∀ c ∈ s.toList, c ≠ '<' ∧ c ≠ '>' := by
  rw [List.all_eq_true] at h
  intro c hc
  have hb := h c hc
  simp only [Bool.and_eq_true, bne_iff_ne] at hb
  exact hb

/-- Defense-in-depth: no rendered attribute string ever contains `<` or `>`, preventing HTML
    tag breakout from attribute context regardless of attribute values or keys. -/
theorem renderAttr_no_angle_brackets (hs : Array msg) (a : Attr msg) :
    ∀ c ∈ (renderAttr hs a).1.toList, c ≠ '<' ∧ c ≠ '>' := by
  cases a with
  | cls name =>
      simp only [renderAttr, toString_string]
      repeat apply str_append_no_angle
      · exact lit_no_angle " class=\"" rfl
      · exact escapeHtml_no_angle name
      · exact lit_no_angle "\"" rfl
  | attr k v =>
      simp only [renderAttr]
      split
      · exact lit_no_angle "" rfl
      · simp only [toString_string]
        repeat apply str_append_no_angle
        · exact lit_no_angle " " rfl
        · exact fun c hc => isKeyChar_no_angle (sanitizeKey_safe k c hc)
        · exact lit_no_angle "=\"" rfl
        · exact escapeHtml_no_angle v
        · exact lit_no_angle "\"" rfl
  | flag k present =>
      simp only [renderAttr]
      split
      · exact lit_no_angle "" rfl
      · simp only [toString_string]
        repeat apply str_append_no_angle
        · exact lit_no_angle " " rfl
        · exact fun c hc => isKeyChar_no_angle (sanitizeKey_safe k c hc)
        · exact lit_no_angle "=\"" rfl
        · exact fun c hc => isKeyChar_no_angle (sanitizeKey_safe k c hc)
        · exact lit_no_angle "\"" rfl
  | key _ => exact lit_no_angle "" rfl
  | on event m | signalOn _ event m =>
      simp only [renderAttr]
      split
      · exact lit_no_angle "" rfl
      · simp only [toString_string]
        repeat apply str_append_no_angle
        · exact lit_no_angle " data-qed-on-" rfl
        · exact fun c hc => isKeyChar_no_angle (sanitizeKey_safe event c hc)
        · exact lit_no_angle "=\"" rfl
        · exact nat_repr_no_angle hs.size
        · exact lit_no_angle "\"" rfl
  | onValue _ _ => exact lit_no_angle "" rfl
  | localCell key comp _ _ _ =>
      simp only [renderAttr, toString_string]
      repeat apply str_append_no_angle
      · exact lit_no_angle " data-qed-local=\"" rfl
      · exact escapeHtml_no_angle (localKey comp key)
      · exact lit_no_angle "\"" rfl
  | signalBind name =>
      simp only [renderAttr, toString_string]
      repeat apply str_append_no_angle
      · exact lit_no_angle " data-qed-signal=\"" rfl
      · exact escapeHtml_no_angle name
      · exact lit_no_angle "\"" rfl
  | signalAttr _ attr value =>
      simp only [renderAttr]
      split
      · exact lit_no_angle "" rfl
      · simp only [toString_string]
        repeat apply str_append_no_angle
        · exact lit_no_angle " " rfl
        · exact fun c hc => isKeyChar_no_angle (sanitizeKey_safe attr c hc)
        · exact lit_no_angle "=\"" rfl
        · exact escapeHtml_no_angle value
        · exact lit_no_angle "\"" rfl

theorem renderAttrs_no_angle_brackets (hs : Array msg) :
    ∀ (attrs : List (Attr msg)), ∀ c ∈ (renderAttrs hs attrs).1.toList, c ≠ '<' ∧ c ≠ '>'
  | [] => lit_no_angle "" rfl
  | a :: as => by
      simp only [renderAttrs]
      exact str_append_no_angle (renderAttr_no_angle_brackets hs a)
        (renderAttrs_no_angle_brackets (renderAttr hs a).2 as)

/-- End-to-end HTML safety closure: whenever `Html.validIn ctx h = true`, every element in `h`
    has a safe, non-forbidden tag (`<script>`/`<base>`/`<object>`/`<embed>`/`<applet>` forbidden),
    every attribute is `Attr.valid` (no `on*`, `srcdoc`, or unsafe URL schemes), void tags are
    childless, and rendered `<style>` bodies contain zero `</` close sequences. -/
def Html.EveryElementSafe : Html msg → Prop
  | .text _ => True
  | .element tag attrs children =>
      isSafeTagName tag = true ∧
      isForbiddenTag tag = false ∧
      Attr.validList attrs = true ∧
      (!isVoidTag tag || children.isEmpty) = true ∧
      (tag == "style" →
        containsCloseSeq (escapeRawText (String.join (children.map fun | .text s => s | _ => ""))).toList = false) ∧
      ∀ c ∈ children, Html.EveryElementSafe c

mutual
  theorem Html.validIn_everyElementSafe :
      ∀ (ctx : HtmlCtx) (h : Html msg),
        Html.validIn ctx h = true → Html.EveryElementSafe h
    | _, .text _, _ => by simp [Html.EveryElementSafe]
    | ctx, .element tag attrs children, hv => by
        simp only [Html.validIn, Bool.and_eq_true] at hv
        rcases hv with ⟨⟨⟨hattrs, hvoid⟩, _⟩, hrest⟩
        cases hctx : stepHtmlCtx ctx tag with
        | none => simp [hctx] at hrest
        | some childCtx =>
            simp only [hctx] at hrest
            unfold stepHtmlCtx at hctx
            by_cases hbad : (!isSafeTagName tag || isForbiddenTag tag) = true
            · simp [hbad] at hctx
            · have hok : isSafeTagName tag = true ∧ isForbiddenTag tag = false := by
                have hbf := Bool.eq_false_iff.2 hbad
                simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hbf
                exact hbf
              simp only [Html.EveryElementSafe]
              refine ⟨hok.1, hok.2, hattrs, hvoid, fun _ => containsCloseSeq_escapeRawText _, ?_⟩
              exact Html.validListIn_everyElementSafe childCtx children hrest

  theorem Html.validListIn_everyElementSafe :
      ∀ (ctx : HtmlCtx) (cs : List (Html msg)),
        Html.validListIn ctx cs = true → ∀ c ∈ cs, Html.EveryElementSafe c
    | _, [], _, _, h => nomatch h
    | ctx, y :: ys, hy, x, hx => by
        simp only [Html.validListIn, Bool.and_eq_true] at hy
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact Html.validIn_everyElementSafe ctx x hy.1
        · exact Html.validListIn_everyElementSafe ctx ys hy.2 x hx'
end

theorem Html.valid_everyElementSafe {h : Html msg} (hv : Html.valid h = true) :
    Html.EveryElementSafe h :=
  Html.validIn_everyElementSafe {} h hv

end Qed
