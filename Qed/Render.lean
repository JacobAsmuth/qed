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
  | .on event m  =>
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
    let body := if tag == "textarea" && childStr.toList.head? == some '\n' then "\n" ++ childStr else childStr
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

mutual
  def renderNodeTR (hs : Array msg) : Html msg → String × Array msg
    | .text s => (escapeHtml s, hs)
    | .element tag attrs children =>
        renderElement (fun hs => renderChildrenTR hs "" children) hs tag attrs children
  def renderChildrenTR (hs : Array msg) (acc : String) : List (Html msg) → String × Array msg
    | [] => (acc, hs)
    | c :: cs =>
        let (str, hs') := renderNodeTR hs c
        renderChildrenTR hs' (acc ++ str) cs
end

mutual
  theorem renderNodeTR_eq (hs : Array msg) (h : Html msg) : renderNodeTR hs h = renderNode hs h := by
    cases h with
    | text s => rfl
    | element tag attrs children =>
        unfold renderNodeTR renderNode
        congr 1
        funext table
        simpa using renderChildrenTR_eq table "" children
  theorem renderChildrenTR_eq (hs : Array msg) (acc : String) (cs : List (Html msg)) :
      renderChildrenTR hs acc cs =
        (acc ++ (renderChildren hs cs).1, (renderChildren hs cs).2) := by
    cases cs with
    | nil => simp [renderChildrenTR, renderChildren]
    | cons c cs =>
        simp only [renderChildrenTR, renderNodeTR_eq, renderChildren]
        rw [renderChildrenTR_eq]
        simp [String.append_assoc]
end

@[csimp] theorem renderNode_eq_renderNodeTR : @renderNode = @renderNodeTR := by
  funext msg hs h
  exact (renderNodeTR_eq hs h).symm

def renderChildrenFast (hs : Array msg) (cs : List (Html msg)) : String × Array msg :=
  renderChildrenTR hs "" cs

@[csimp] theorem renderChildren_eq_renderChildrenFast : @renderChildren = @renderChildrenFast := by
  funext msg hs cs
  simpa [renderChildrenFast] using (renderChildrenTR_eq hs "" cs).symm

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

end Qed
