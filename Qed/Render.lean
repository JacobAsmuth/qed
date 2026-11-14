import Qed.Html

namespace Qed

def localKey (component key : String) : String := component ++ "@" ++ key

@[inline] def isHtmlSpecial (c : Char) : Bool :=
  c == '&' || c == '<' || c == '>' || c == '"' || c == '\''

def escapeHtml (s : String) : String :=
  if !s.any isHtmlSpecial then s
  else s.foldl (init := "") fun acc c =>
    match c with
    | '&'  => acc ++ "&amp;"
    | '<'  => acc ++ "&lt;"
    | '>'  => acc ++ "&gt;"
    | '"'  => acc ++ "&quot;"
    | '\'' => "&#39;" |> (acc ++ ·)
    | c    => acc.push c

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

@[inline] def isKeyChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'

def sanitizeKey (k : String) : String :=
  if k.all isKeyChar then k
  else String.ofList (k.toList.filter isKeyChar)

def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]

def renderAttr (hs : Array msg) : Attr msg → String × Array msg
  | .cls c     => (s!" class=\"{escapeHtml c}\"", hs)
  | .attr k v  => (s!" {sanitizeKey k}=\"{escapeHtml v}\"", hs)
  | .flag k present => (if present then s!" {sanitizeKey k}=\"{sanitizeKey k}\"" else "", hs)
  | .key _     => ("", hs)
  | .on event m  => (s!" data-qed-on-{event}=\"{hs.size}\"", hs.push m)
  | .onValue _ _ => ("", hs)
  | .localCell key comp _ _ _ => (s!" data-qed-local=\"{escapeHtml (localKey comp key)}\"", hs)
  | .signalBind name        => (s!" data-qed-signal=\"{escapeHtml name}\"", hs)
  | .signalAttr _ attr value => (s!" {sanitizeKey attr}=\"{escapeHtml value}\"", hs)
  | .rawHtml _ => ("", hs)

def renderAttrs (hs : Array msg) : List (Attr msg) → String × Array msg
  | []      => ("", hs)
  | a :: as =>
      let (s1, hs1) := renderAttr hs a
      let (s2, hs2) := renderAttrs hs1 as
      (s1 ++ s2, hs2)

def rawHtml? : List (Attr msg) → Option String
  | []                   => none
  | .rawHtml markup :: _ => some markup
  | _ :: rest            => rawHtml? rest

def renderElement (renderKids : Array msg → String × Array msg) (hs : Array msg)
    (tag : String) (attrs : List (Attr msg)) (children : List (Html msg)) : String × Array msg :=
  let (attrStr, hs1) := renderAttrs hs (normalizeAttrs attrs)
  if let some markup := rawHtml? attrs then
    (s!"<{tag}{attrStr}>{markup}</{tag}>", hs1)
  else if tag == "style" || tag == "script" then
    -- Escape `</` → `<\/` so text inside raw-text elements cannot close `<style>`/`<script>` early.
    let raw := "<\\/".intercalate ((String.join (children.map fun | .text s => s | _ => "")).splitOn "</")
    (s!"<{tag}{attrStr}>{raw}</{tag}>", hs1)
  else if voidTags.contains tag then
    (s!"<{tag}{attrStr}>", hs1)
  else
    let (childStr, hs2) := renderKids hs1
    (s!"<{tag}{attrStr}>{childStr}</{tag}>", hs2)

mutual
  def renderNode (hs : Array msg) : Html msg → String × Array msg
    | .text s => (escapeHtml s, hs)
    | .element tag attrs children => renderElement (fun hs => renderChildren hs children) hs tag attrs children
    | .lazy _ sub => renderNode hs sub
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
    | .lazy _ sub => renderNodeTR hs sub
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
    | lazy k sub => exact renderNodeTR_eq hs sub
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
  | .text s     => some s
  | .lazy _ sub => Html.textOf? sub
  | _           => none

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
