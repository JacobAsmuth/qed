-- Avoids `String.Slice` from Lean ≥ 4.30 `trimAscii` so JS bundles stay free of `Slice` primitives.
def String.trimmed (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

namespace Qed

@[inline] def isSafeUrlChar (c : Char) : Bool :=
  c.toNat > 0x20 && c.toNat != 0x7F

def hasSafeUrlPrefix : List Char → Bool
  | ['/']                                                           => true
  | '/' :: c :: _                                                   => c != '/' && c != '\\'
  | '#' :: _                                                        => true
  | '?' :: _                                                        => true
  | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: c :: _ => c != '/' && c != '\\'
  | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: c :: _        => c != '/' && c != '\\'
  | 'm' :: 'a' :: 'i' :: 'l' :: 't' :: 'o' :: ':' :: c :: _        => c != '/' && c != '\\'
  | 't' :: 'e' :: 'l' :: ':' :: c :: _                             => c != '/' && c != '\\'
  | _                                                               => false

def isSafeUrl (s : String) : Bool :=
  let cs := s.toList
  hasSafeUrlPrefix cs && cs.all isSafeUrlChar

structure Url where
  raw  : String
  safe : isSafeUrl raw = true
deriving DecidableEq, Repr

namespace Url

def root : Url := ⟨"/", rfl⟩

instance : Inhabited Url := ⟨root⟩
instance : ToString Url := ⟨Url.raw⟩

@[simp] theorem isSafe (u : Url) : isSafeUrl u.raw = true := u.safe

def parse? (s : String) : Option Url :=
  if h : isSafeUrl s = true then some ⟨s, h⟩ else none

@[simp] theorem parse?_isSome (s : String) : (parse? s).isSome = isSafeUrl s := by
  unfold parse?
  by_cases h : isSafeUrl s = true <;> simp [h]

end Url

syntax (name := urlLitTerm) "url% " str : term

macro_rules
  | `(url% $s:str) => do
      let raw := s.getString
      if !isSafeUrl raw then
        Lean.Macro.throwErrorAt s
          s!"unsafe URL literal `{raw}`: URLs must be root-relative (`/path`, not `//`), `#fragment`, `?query`, or explicit `https://`, `http://`, `mailto:`, `tel:` with no whitespace or control characters"
      `(Qed.Url.mk $s (by decide))

def containsCloseSeqLoop (afterLt : Bool) : List Char → Bool
  | []      => false
  | c :: cs => (afterLt && c == '/') || containsCloseSeqLoop (c == '<') cs

def containsCloseSeq (cs : List Char) : Bool := containsCloseSeqLoop false cs

def escapeCloseSeqLoop (afterLt : Bool) : List Char → List Char
  | []      => []
  | c :: cs =>
      if afterLt && c == '/' then
        '\\' :: '/' :: escapeCloseSeqLoop false cs
      else
        c :: escapeCloseSeqLoop (c == '<') cs

def escapeRawText (s : String) : String :=
  if !containsCloseSeq s.toList then s
  else String.ofList (escapeCloseSeqLoop false s.toList)

theorem containsCloseSeqLoop_escapeCloseSeqLoop (cs : List Char) :
    ∀ (b : Bool), containsCloseSeqLoop b (escapeCloseSeqLoop b cs) = false := by
  induction cs with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro b
      simp only [escapeCloseSeqLoop]
      cases h : (b && c == '/')
      · simpa [containsCloseSeqLoop, h] using ih (c == '<')
      · simpa [containsCloseSeqLoop] using ih false

@[simp] theorem containsCloseSeq_escapeRawText (s : String) :
    containsCloseSeq (escapeRawText s).toList = false := by
  unfold escapeRawText containsCloseSeq
  by_cases h : containsCloseSeqLoop false s.toList
  · simp [h, containsCloseSeqLoop_escapeCloseSeqLoop]
  · simp [h]

inductive Attr (msg : Type) where
  | cls (name : String)
  | attr (key value : String)
  | flag (key : String) (present : Bool)
  | key (k : String)
  | on (event : String) (m : msg)
  | onValue (event : String) (decode : String → msg)
  | localCell (key component : String) (init? : Option String) (props : String) (bubble : String → Option msg)
  | signalBind (name : String)
  | signalAttr (name attr value : String)

inductive Html (msg : Type) where
  | text (content : String)
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))

def Attr.empty : Attr msg := .cls ""

def Html.ofOption : Option (Html msg) → Html msg
  | some h => h
  | none   => .text ""

@[simp] theorem toString_string (s : String) : toString s = s := rfl

instance : Inhabited (Attr msg) := ⟨.cls ""⟩
instance : Inhabited (Html msg) := ⟨.text ""⟩

instance : Coe String (Html msg) := ⟨.text⟩
instance : Coe String (List (Html msg)) := ⟨([·])⟩
instance : Coe Nat (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe Int (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe Float (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe (Option (Html msg)) (Html msg) := ⟨Html.ofOption⟩
instance : Coe (Array (Html msg)) (List (Html msg)) := ⟨Array.toList⟩

def Attr.map (f : α → β) : Attr α → Attr β
  | .cls n               => .cls n
  | .attr k v            => .attr k v
  | .flag k present      => .flag k present
  | .key k               => .key k
  | .on e m              => .on e (f m)
  | .onValue e h         => .onValue e (fun s => f (h s))
  | .localCell k c i p b => .localCell k c i p (fun s => (b s).map f)
  | .signalBind name     => .signalBind name
  | .signalAttr n a v    => .signalAttr n a v

mutual
  def Html.map (f : α → β) : Html α → Html β
    | .text s => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.map f)) (Html.mapChildren f children)
  def Html.mapChildren (f : α → β) : List (Html α) → List (Html β)
    | []      => []
    | c :: cs => Html.map f c :: Html.mapChildren f cs
end

def Attr.prefixSignal (pfx : String) : Attr msg → Attr msg
  | .signalBind n     => .signalBind (pfx ++ n)
  | .signalAttr n a v => .signalAttr (pfx ++ n) a v
  | other             => other

mutual
  def Html.prefixSignals (pfx : String) : Html msg → Html msg
    | .text s => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.prefixSignal pfx)) (Html.prefixSignalsList pfx children)
  def Html.prefixSignalsList (pfx : String) : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs => Html.prefixSignals pfx c :: Html.prefixSignalsList pfx cs
end

@[inline] def isKeyChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'

def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def asciiLower (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

def hasOnPrefix : List Char → Bool
  | 'o' :: 'n' :: _ => true
  | _               => false

def isSafeRenderedKey (k : String) : Bool :=
  !k.isEmpty && !hasOnPrefix (k.toList.map asciiLowerChar) && asciiLower k != "srcdoc"

def isSafeAttrName (k : String) : Bool :=
  k.toList.all isKeyChar && isSafeRenderedKey k

def isUrlAttrName (k : String) : Bool :=
  let kl := asciiLower k
  kl == "href" || kl == "src" || kl == "action" || kl == "formaction" ||
  kl == "xlink:href" || kl == "poster" || kl == "data" || kl == "cite" || kl == "srcset"

def Attr.validKeyValue (k v : String) : Bool :=
  isSafeAttrName k && (!isUrlAttrName k || isSafeUrl v)

def Attr.valid : Attr msg → Bool
  | .cls _            => true
  | .attr k v         => Attr.validKeyValue k v
  | .flag k _         => isSafeAttrName k
  | .key _            => true
  | .on event _       => isSafeAttrName event
  | .onValue event _  => isSafeAttrName event
  | .localCell ..     => true
  | .signalBind _     => true
  | .signalAttr _ a v => Attr.validKeyValue a v

@[simp] theorem Attr.valid_cls (n : String) : (Attr.cls n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_attr (k v : String) : (Attr.attr k v : Attr msg).valid = Attr.validKeyValue k v := rfl
@[simp] theorem Attr.valid_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).valid = isSafeAttrName k := rfl
@[simp] theorem Attr.valid_key (n : String) : (Attr.key n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_on (e : String) (m : msg) : (Attr.on e m).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.valid_onValue (e : String) (f : String → msg) : (Attr.onValue e f).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.valid_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) :
    (Attr.localCell k c i p b).valid = true := rfl
@[simp] theorem Attr.valid_signalBind (n : String) : (Attr.signalBind n : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_signalAttr (n a v : String) :
    (Attr.signalAttr n a v : Attr msg).valid = Attr.validKeyValue a v := rfl

def Attr.validList : List (Attr msg) → Bool
  | []      => true
  | a :: as => a.valid && Attr.validList as

def Attr.isLocalCell : Attr msg → Bool
  | .localCell .. => true
  | _             => false

@[simp] theorem Attr.isLocalCell_cls (n : String) : (Attr.cls n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_attr (k v : String) : (Attr.attr k v : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_key (n : String) : (Attr.key n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_on (e : String) (m : msg) : (Attr.on e m).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_onValue (e : String) (f : String → msg) : (Attr.onValue e f).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) :
    (Attr.localCell k c i p b).isLocalCell = true := rfl
@[simp] theorem Attr.isLocalCell_signalBind (n : String) : (Attr.signalBind n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_signalAttr (n a v : String) :
    (Attr.signalAttr n a v : Attr msg).isLocalCell = false := rfl

def Attr.hasLocalCell : List (Attr msg) → Bool
  | []        => false
  | a :: rest => a.isLocalCell || Attr.hasLocalCell rest

def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]

def isVoidTag (tag : String) : Bool := voidTags.contains tag

def isSafeTagName (tag : String) : Bool :=
  let cs := tag.toList
  !cs.isEmpty && cs.all (fun c => c.isAlphanum || c == '-')

def isForbiddenTag (tag : String) : Bool :=
  tag == "script" || tag == "base" || tag == "applet" || tag == "object" || tag == "embed"

def isHeadingTag (tag : String) : Bool :=
  tag == "h1" || tag == "h2" || tag == "h3" || tag == "h4" || tag == "h5" || tag == "h6"

def closesPTag (tag : String) : Bool :=
  tag == "address" || tag == "article" || tag == "aside" || tag == "blockquote" ||
  tag == "details" || tag == "div" || tag == "dl" || tag == "fieldset" ||
  tag == "figcaption" || tag == "figure" || tag == "footer" || tag == "form" ||
  isHeadingTag tag || tag == "header" || tag == "hgroup" || tag == "hr" ||
  tag == "main" || tag == "menu" || tag == "nav" || tag == "ol" || tag == "p" ||
  tag == "pre" || tag == "search" || tag == "section" || tag == "table" || tag == "ul"

def isInteractiveTag (tag : String) : Bool :=
  tag == "a" || tag == "button" || tag == "input" || tag == "select" ||
  tag == "textarea" || tag == "details" || tag == "summary"

def isContextOnlyTag (tag : String) : Bool :=
  tag == "li" || tag == "dt" || tag == "dd" ||
  tag == "caption" || tag == "colgroup" || tag == "col" ||
  tag == "thead" || tag == "tbody" || tag == "tfoot" ||
  tag == "tr" || tag == "td" || tag == "th" ||
  tag == "option" || tag == "optgroup"

inductive TagMode where
  | normal
  | ulOl
  | dl
  | table
  | colgroup
  | tableSection
  | tableRow
  | select
  | optgroup
  | option
  | rawStyle
  | textarea
  | svg
deriving DecidableEq, Repr

structure HtmlCtx where
  mode        : TagMode := .normal
  inP         : Bool := false
  interactive : Bool := false
  inForm      : Bool := false
deriving DecidableEq, Repr

def stepHtmlCtx (ctx : HtmlCtx) (tag : String) : Option HtmlCtx :=
  if !isSafeTagName tag || isForbiddenTag tag then none
  else
    match ctx.mode with
    | .svg =>
        if tag == "foreignObject" then some {}
        else some { ctx with mode := .svg }
    | .option | .textarea | .rawStyle => none
    | .ulOl =>
        if tag == "li" then some { ctx with mode := .normal, inP := false } else none
    | .dl =>
        if tag == "dt" || tag == "dd" then some { ctx with mode := .normal, inP := false } else none
    | .table =>
        if tag == "caption" then some { ctx with mode := .normal, inP := false }
        else if tag == "colgroup" then some { ctx with mode := .colgroup, inP := false }
        else if tag == "thead" || tag == "tbody" || tag == "tfoot" then
          some { ctx with mode := .tableSection, inP := false }
        else none
    | .colgroup =>
        if tag == "col" then some { ctx with mode := .normal } else none
    | .tableSection =>
        if tag == "tr" then some { ctx with mode := .tableRow, inP := false } else none
    | .tableRow =>
        if tag == "td" || tag == "th" then some { ctx with mode := .normal, inP := false } else none
    | .select =>
        if tag == "option" then some { ctx with mode := .option }
        else if tag == "optgroup" then some { ctx with mode := .optgroup }
        else none
    | .optgroup =>
        if tag == "option" then some { ctx with mode := .option } else none
    | .normal =>
        if isContextOnlyTag tag then none
        else if ctx.inP && closesPTag tag then none
        else if ctx.interactive && (isInteractiveTag tag || tag == "label" || tag == "form") then none
        else if ctx.inForm && tag == "form" then none
        else if tag == "svg" then some { ctx with mode := .svg }
        else if tag == "style" then some { ctx with mode := .rawStyle }
        else if tag == "textarea" then some { ctx with mode := .textarea, interactive := true }
        else if tag == "select" then some { ctx with mode := .select, interactive := true }
        else if tag == "ul" || tag == "ol" then some { ctx with mode := .ulOl }
        else if tag == "dl" then some { ctx with mode := .dl }
        else if tag == "table" then some { ctx with mode := .table }
        else
          some { mode        := .normal
                 inP         := ctx.inP || tag == "p" || isHeadingTag tag
                 interactive := ctx.interactive || tag == "a" || tag == "button" || tag == "details" || tag == "summary"
                 inForm      := ctx.inForm || tag == "form" }

def validTextIn (ctx : HtmlCtx) (s : String) : Bool :=
  match ctx.mode with
  | .normal | .option | .textarea | .svg => true
  | .rawStyle => !containsCloseSeq s.toList
  | .ulOl | .dl | .table | .colgroup | .tableSection | .tableRow | .select | .optgroup => s == ""

mutual
  def Html.validIn (ctx : HtmlCtx) : Html msg → Bool
    | .text s => validTextIn ctx s
    | .element tag attrs children =>
        Attr.validList attrs &&
        (!isVoidTag tag || children.isEmpty) &&
        (!Attr.hasLocalCell attrs || children.isEmpty) &&
        match stepHtmlCtx ctx tag with
        | some childCtx => Html.validListIn childCtx children
        | none          => false

  def Html.validListIn (ctx : HtmlCtx) : List (Html msg) → Bool
    | []      => true
    | c :: cs => Html.validIn ctx c && Html.validListIn ctx cs
end

def Html.valid (h : Html msg) : Bool := Html.validIn {} h

@[simp] theorem Attr.valid_empty : (Attr.empty : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.valid (if c then a else b) = (if c then a.valid else b.valid) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Attr.validList_nil : Attr.validList ([] : List (Attr msg)) = true := rfl
@[simp] theorem Attr.validList_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.validList (a :: as) = (a.valid && Attr.validList as) := rfl

@[simp] theorem Attr.validList_append (xs ys : List (Attr msg)) :
    Attr.validList (xs ++ ys) = (Attr.validList xs && Attr.validList ys) := by
  induction xs with
  | nil => simp [Attr.validList]
  | cons a rest ih => simp [Attr.validList, ih, Bool.and_assoc]

@[simp] theorem Attr.validList_filter_nonkey (xs : List (Attr msg)) :
    Attr.validList (xs.filter (fun | .key _ => false | _ => true)) = Attr.validList xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      cases a <;> simp [Attr.validList, Attr.valid, ih]

@[simp] theorem Attr.hasLocalCell_nil : Attr.hasLocalCell ([] : List (Attr msg)) = false := rfl
@[simp] theorem Attr.hasLocalCell_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.hasLocalCell (a :: as) = (a.isLocalCell || Attr.hasLocalCell as) := rfl

@[simp] theorem Attr.isLocalCell_empty : (Attr.empty : Attr msg).isLocalCell = false := rfl

@[simp] theorem Attr.isLocalCell_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.isLocalCell (if c then a else b) = (if c then a.isLocalCell else b.isLocalCell) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Attr.hasLocalCell_append (xs ys : List (Attr msg)) :
    Attr.hasLocalCell (xs ++ ys) = (Attr.hasLocalCell xs || Attr.hasLocalCell ys) := by
  induction xs with
  | nil => simp [Attr.hasLocalCell]
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, ih]

@[simp] theorem Attr.hasLocalCell_filter_nonkey (xs : List (Attr msg)) :
    Attr.hasLocalCell (xs.filter (fun | .key _ => false | _ => true)) = Attr.hasLocalCell xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, ih]

@[simp] theorem Attr.valid_map {α β : Type} (f : α → β) (a : Attr α) :
    (a.map f).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.validList_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.validList (as.map (Attr.map f)) = Attr.validList as := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp [Attr.validList, ih]

@[simp] theorem Attr.hasLocalCell_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.hasLocalCell (as.map (Attr.map f)) = Attr.hasLocalCell as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, Attr.map, ih]

@[simp] theorem Attr.valid_prefixSignal (pfx : String) (a : Attr msg) :
    (a.prefixSignal pfx).valid = a.valid := by
  cases a <;> rfl

@[simp] theorem Attr.validList_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.validList (as.map (Attr.prefixSignal pfx)) = Attr.validList as := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp [Attr.validList, ih]

@[simp] theorem Attr.hasLocalCell_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.hasLocalCell (as.map (Attr.prefixSignal pfx)) = Attr.hasLocalCell as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.hasLocalCell, Attr.prefixSignal, ih]

@[simp] theorem Html.mapChildren_isEmpty {α β : Type} (f : α → β) (cs : List (Html α)) :
    (Html.mapChildren f cs).isEmpty = cs.isEmpty := by
  cases cs <;> rfl

@[simp] theorem Html.prefixSignalsList_isEmpty (pfx : String) (cs : List (Html msg)) :
    (Html.prefixSignalsList pfx cs).isEmpty = cs.isEmpty := by
  cases cs <;> rfl

mutual
  @[simp] theorem Html.validIn_map {α β : Type} (ctx : HtmlCtx) (f : α → β) :
      (h : Html α) → Html.validIn ctx (h.map f) = Html.validIn ctx h
    | .text _ => rfl
    | .element tag attrs children => by
        simp only [Html.map, Html.validIn, Attr.validList_map_attrMap,
                   Attr.hasLocalCell_map_attrMap, Html.mapChildren_isEmpty]
        cases stepHtmlCtx ctx tag with
        | none => rfl
        | some childCtx => simp [Html.validListIn_mapChildren childCtx f children]

  @[simp] theorem Html.validListIn_mapChildren {α β : Type} (ctx : HtmlCtx) (f : α → β) :
      (cs : List (Html α)) → Html.validListIn ctx (Html.mapChildren f cs) = Html.validListIn ctx cs
    | [] => rfl
    | c :: cs => by
        simp [Html.mapChildren, Html.validListIn, Html.validIn_map ctx f c,
              Html.validListIn_mapChildren ctx f cs]
end

mutual
  @[simp] theorem Html.validIn_prefixSignals (ctx : HtmlCtx) (pfx : String) :
      (h : Html msg) → Html.validIn ctx (h.prefixSignals pfx) = Html.validIn ctx h
    | .text _ => rfl
    | .element tag attrs children => by
        simp only [Html.prefixSignals, Html.validIn, Attr.validList_prefixSignal,
                   Attr.hasLocalCell_prefixSignal, Html.prefixSignalsList_isEmpty]
        cases stepHtmlCtx ctx tag with
        | none => rfl
        | some childCtx => simp [Html.validListIn_prefixSignalsList childCtx pfx children]

  @[simp] theorem Html.validListIn_prefixSignalsList (ctx : HtmlCtx) (pfx : String) :
      (cs : List (Html msg)) → Html.validListIn ctx (Html.prefixSignalsList pfx cs) = Html.validListIn ctx cs
    | [] => rfl
    | c :: cs => by
        simp [Html.prefixSignalsList, Html.validListIn, Html.validIn_prefixSignals ctx pfx c,
              Html.validListIn_prefixSignalsList ctx pfx cs]
end

@[simp] theorem Html.validListIn_nil (ctx : HtmlCtx) :
    Html.validListIn ctx ([] : List (Html msg)) = true := rfl

@[simp] theorem Html.validListIn_cons (ctx : HtmlCtx) (c : Html msg) (cs : List (Html msg)) :
    Html.validListIn ctx (c :: cs) = (Html.validIn ctx c && Html.validListIn ctx cs) := rfl

@[simp] theorem Html.validListIn_append (ctx : HtmlCtx) (xs ys : List (Html msg)) :
    Html.validListIn ctx (xs ++ ys) = (Html.validListIn ctx xs && Html.validListIn ctx ys) := by
  induction xs with
  | nil => simp [Html.validListIn]
  | cons c rest ih => simp [Html.validListIn, ih, Bool.and_assoc]

@[simp] theorem Html.validIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg) :
    Html.validIn ctx (if c then a else b) = (if c then Html.validIn ctx a else Html.validIn ctx b) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Html.validListIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : List (Html msg)) :
    Html.validListIn ctx (if c then a else b) = (if c then Html.validListIn ctx a else Html.validListIn ctx b) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem Html.validIn_ofOption (ctx : HtmlCtx) (o : Option (Html msg)) :
    Html.validIn ctx (Html.ofOption o) =
      match o with | some h => Html.validIn ctx h | none => validTextIn ctx "" := by
  cases o <;> rfl

@[simp] theorem Html.validListIn_map {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f) = xs.all (fun a => Html.validIn ctx (f a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [ih]

@[simp] theorem Html.validListIn_toList_map {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f).toList = xs.toList.all (fun a => Html.validIn ctx (f a)) := by
  simp [Array.toList_map]

@[simp] theorem List.all_const_true {α : Type} (xs : List α) :
    xs.all (fun _ => true) = true := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp [ih]

@[simp] theorem validTextIn_normal (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.normal, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_option (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.option, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_textarea (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.textarea, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_svg (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.svg, inP, inter, inForm⟩ s = true := rfl

@[simp] theorem validTextIn_rawStyle (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.rawStyle, inP, inter, inForm⟩ s = !containsCloseSeq s.toList := rfl

@[simp] theorem validTextIn_empty (ctx : HtmlCtx) :
    validTextIn ctx "" = true := by
  cases ctx with
  | mk mode _ _ _ => cases mode <;> simp [validTextIn, containsCloseSeq, containsCloseSeqLoop]

end Qed
