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

@[specialize 2] def hasAsciiByteLoop (s : String) (p : UInt8 → Bool) (sz : Nat) (hsz : sz = s.utf8ByteSize) (i : Nat) : Bool :=
  if h : i < sz then
    if p (s.getUTF8Byte ⟨i⟩ (show i < s.utf8ByteSize from hsz ▸ h)) then true else hasAsciiByteLoop s p sz hsz (i + 1)
  else false
termination_by sz - i
decreasing_by exact Nat.sub_succ_lt_self sz i h

@[inline] def hasAsciiByte (s : String) (p : UInt8 → Bool) : Bool :=
  hasAsciiByteLoop s p s.utf8ByteSize rfl 0

private def escapeCloseSeqBytesSpec (afterLt : Bool) : List UInt8 → List UInt8
  | []      => []
  | b :: bs =>
      if afterLt && b == 47 then 92 :: 47 :: escapeCloseSeqBytesSpec false bs
      else b :: escapeCloseSeqBytesSpec (b == 60) bs

@[inline] private def copySliceAppend (src : ByteArray) (segStart stop : Nat) (acc : ByteArray) : ByteArray :=
  src.copySlice segStart acc acc.size (stop - segStart) false

private def hasCloseSeqStrLoop (s : String) (i : Nat) (afterLt : Bool) : Bool :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if afterLt && b == 47 then true
    else hasCloseSeqStrLoop s (i + 1) (b == 60)
  else false
termination_by s.utf8ByteSize - i
decreasing_by exact Nat.sub_succ_lt_self s.utf8ByteSize i h

private def escapeRawBytesLoop (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray) : ByteArray :=
  if h : i < ba.size then
    let b := ba[i]
    if afterLt && b == 47 then
      let acc' := (copySliceAppend ba segStart i acc).push 92
      escapeRawBytesLoop ba i (i + 1) false acc'
    else
      escapeRawBytesLoop ba segStart (i + 1) (b == 60) acc
  else
    copySliceAppend ba segStart ba.size acc
termination_by ba.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self ba.size i h

private def escapeRawBytesLoopU (ba : ByteArray) (sz : USize) (hsz : sz.toNat ≤ ba.size)
    (segStart i : USize) (afterLt : Bool) (acc : ByteArray) : ByteArray :=
  if h : i < sz then
    let b := ba.uget i (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.1 h) hsz)
    if afterLt && b == 47 then
      let acc' := (copySliceAppend ba segStart.toNat i.toNat acc).push 92
      escapeRawBytesLoopU ba sz hsz i (i + 1) false acc'
    else
      escapeRawBytesLoopU ba sz hsz segStart (i + 1) (b == 60) acc
  else
    copySliceAppend ba segStart.toNat sz.toNat acc
termination_by sz.toNat - i.toNat
decreasing_by
  all_goals
    have hlt : i.toNat < sz.toNat := USize.lt_iff_toNat_lt.1 h
    have hlt2 : i.toNat + 1 < 2 ^ System.Platform.numBits := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt) sz.toBitVec.isLt
    have hadd : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt hlt2
    rw [hadd]
    exact Nat.sub_succ_lt_self sz.toNat i.toNat hlt

/-- Appends the UTF-8 bytes of `escapeRawText s` directly into `acc` in a single unboxed `USize`
    pass without intermediate `String` allocations or UTF-8 re-validation. -/
def escapeRawTextBytesInto (acc : ByteArray) (s : String) : ByteArray :=
  let ba := s.toUTF8
  let sz := ba.usize
  if h : sz.toNat = ba.size then
    escapeRawBytesLoopU ba sz (Nat.le_of_eq h) 0 0 false acc
  else
    escapeRawBytesLoop ba 0 0 false acc

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
  | signalOn (name event : String) (m : msg)

inductive Html (msg : Type) where
  | text (content : String)
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))

def Attr.empty : Attr msg := .cls ""

abbrev Html.empty : Html msg := .text ""

def Html.ofOption : Option (Html msg) → Html msg
  | some h => h
  | none   => .text ""

@[simp] theorem toString_string (s : String) : toString s = s := rfl

def Attr.isSignalBind : Attr msg → Bool
  | .signalBind _ => true
  | _             => false

def Attr.canonical : Attr msg → Option (Attr msg)
  | .key _            => none
  | .signalBind _     => none
  | .signalAttr _ k v => some (.attr k v)
  | .signalOn _ e m   => some (.on e m)
  | .cls name         => some (.attr "class" name)
  | a                 => some a

private theorem fn_ite {α β : Type _} (f : α → β) (c : Prop) [Decidable c] (a b : α) :
    f (if c then a else b) = if c then f a else f b := by split <;> rfl

private theorem bool_ite_intro {α : Type _} (f : α → Bool) (v : Bool) (c : Prop) [Decidable c] (a b : α)
    (ht : c → f a = v) (hf : ¬c → f b = v) : f (if c then a else b) = v := by
  by_cases hc : c <;> simp [hc, ht, hf]

private theorem bool_dite_intro {α : Type _} (f : α → Bool) (v : Bool) (c : Prop) [Decidable c]
    (a : c → α) (b : ¬c → α) (ht : ∀ h, f (a h) = v) (hf : ∀ h, f (b h) = v) :
    f (dite c a b) = v := by
  by_cases hc : c <;> simp [hc, ht, hf]

@[simp] theorem Attr.isSignalBind_ite (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.isSignalBind (if c then a else b) = if c then Attr.isSignalBind a else Attr.isSignalBind b :=
  fn_ite Attr.isSignalBind c a b

@[simp] theorem Attr.canonical_ite (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.canonical (if c then a else b) = if c then Attr.canonical a else Attr.canonical b :=
  fn_ite Attr.canonical c a b

@[simp] theorem Option.ite_some {α : Type _} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) :=
  (fn_ite some c a b).symm

@[simp] theorem List.filterMap_ite {α β : Type _} (f : α → Option β) (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else b).filterMap f = if c then a.filterMap f else b.filterMap f :=
  fn_ite (List.filterMap f) c a b

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
  | .signalOn n e m      => .signalOn n e (f m)

mutual
  def Html.map (f : α → β) : Html α → Html β
    | .text s => .text s
    | .element tag attrs children => .element tag (attrs.map (Attr.map f)) (Html.mapChildren f children)
  def Html.mapChildren (f : α → β) : List (Html α) → List (Html β)
    | []      => []
    | c :: cs => Html.map f c :: Html.mapChildren f cs
end

def Attr.prefixSignal (pfx : String) : Attr msg → Attr msg
  | .signalBind n     => .signalBind (pfx ++ n)
  | .signalAttr n a v => .signalAttr (pfx ++ n) a v
  | .signalOn n e m   => .signalOn (pfx ++ n) e m
  | other             => other

mutual
  def Html.prefixSignals (pfx : String) : Html msg → Html msg
    | .text s => .text s
    | .element tag attrs children => .element tag (attrs.map (Attr.prefixSignal pfx)) (Html.prefixSignalsList pfx children)
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
  | .signalOn _ e _   => isSafeAttrName e

def Attr.validList : List (Attr msg) → Bool
  | []      => true
  | a :: as => a.valid && Attr.validList as

def Attr.isLocalCell : Attr msg → Bool
  | .localCell .. => true
  | _             => false

def Attr.hasLocalCell : List (Attr msg) → Bool
  | []        => false
  | a :: rest => a.isLocalCell || Attr.hasLocalCell rest

local macro "attr_ctor_simp " vThm:ident lThm:ident bs:bracketedBinder* " => " ctor:term " | " vRhs:term " , " lRhs:term : command =>
  `(@[simp] theorem $vThm $bs* : ($ctor : Attr _).valid = $vRhs := rfl
    @[simp] theorem $lThm $bs* : ($ctor : Attr _).isLocalCell = $lRhs := rfl)

attr_ctor_simp Attr.valid_cls        Attr.isLocalCell_cls        {msg : Type} (n : String)                                                   => (Attr.cls n : Attr msg)               | true,                  false
attr_ctor_simp Attr.valid_attr       Attr.isLocalCell_attr       {msg : Type} (k v : String)                                                 => (Attr.attr k v : Attr msg)            | Attr.validKeyValue k v, false
attr_ctor_simp Attr.valid_flag       Attr.isLocalCell_flag       {msg : Type} (k : String) (p : Bool)                                        => (Attr.flag k p : Attr msg)            | isSafeAttrName k,      false
attr_ctor_simp Attr.valid_key        Attr.isLocalCell_key        {msg : Type} (n : String)                                                   => (Attr.key n : Attr msg)               | true,                  false
attr_ctor_simp Attr.valid_on         Attr.isLocalCell_on         {msg : Type} (e : String) (m : msg)                                         => Attr.on e m                           | isSafeAttrName e,      false
attr_ctor_simp Attr.valid_onValue    Attr.isLocalCell_onValue    {msg : Type} (e : String) (f : String → msg)                                => Attr.onValue e f                      | isSafeAttrName e,      false
attr_ctor_simp Attr.valid_localCell  Attr.isLocalCell_localCell  {msg : Type} (k c : String) (i : Option String) (p : String) (b : String → Option msg) => Attr.localCell k c i p b | true, true
attr_ctor_simp Attr.valid_signalBind Attr.isLocalCell_signalBind {msg : Type} (n : String)                                                   => (Attr.signalBind n : Attr msg)        | true,                  false
attr_ctor_simp Attr.valid_signalAttr Attr.isLocalCell_signalAttr {msg : Type} (n a v : String)                                               => (Attr.signalAttr n a v : Attr msg)    | Attr.validKeyValue a v, false
attr_ctor_simp Attr.valid_signalOn   Attr.isLocalCell_signalOn   {msg : Type} (n e : String) (m : msg)                                       => Attr.signalOn n e m                   | isSafeAttrName e,      false

def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]

def isVoidTag (tag : String) : Bool := voidTags.contains tag

def isVoidTagFast (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 2 => tag == "br" || tag == "hr"
  | 3 => tag == "col" || tag == "img" || tag == "wbr"
  | 4 => tag == "area" || tag == "base" || tag == "link" || tag == "meta"
  | 5 => tag == "embed" || tag == "input" || tag == "track"
  | 6 => tag == "source"
  | _ => false

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

@[csimp] theorem isVoidTag_eq_fast : @isVoidTag = @isVoidTagFast := by
  funext tag
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    have hm : tag ∈ voidTags := List.contains_iff_mem.1 h
    unfold voidTags at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro h
    unfold isVoidTagFast at h; unfold isVoidTag; rw [List.contains_iff_mem]
    split at h <;> try exact absurd h (by decide)
    all_goals
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      repeat (cases h with | inl h => _ | inr h => _)
      all_goals (subst h; simp [voidTags])

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

private theorem Attr.validList_eq_all (as : List (Attr msg)) : Attr.validList as = as.all Attr.valid := by
  induction as <;> simp [Attr.validList, *]

private theorem Attr.hasLocalCell_eq_any (as : List (Attr msg)) : Attr.hasLocalCell as = as.any Attr.isLocalCell := by
  induction as <;> simp [Attr.hasLocalCell, *]

@[simp] theorem Attr.valid_empty : (Attr.empty : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_empty : (Attr.empty : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.valid (if c then a else b) = (if c then a.valid else b.valid) := fn_ite Attr.valid c a b
@[simp] theorem Attr.isLocalCell_ite {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg) :
    Attr.isLocalCell (if c then a else b) = (if c then a.isLocalCell else b.isLocalCell) := fn_ite Attr.isLocalCell c a b
@[simp] theorem Attr.validList_nil : Attr.validList ([] : List (Attr msg)) = true := rfl
@[simp] theorem Attr.validList_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.validList (a :: as) = (a.valid && Attr.validList as) := rfl
@[simp] theorem Attr.hasLocalCell_nil : Attr.hasLocalCell ([] : List (Attr msg)) = false := rfl
@[simp] theorem Attr.hasLocalCell_cons (a : Attr msg) (as : List (Attr msg)) :
    Attr.hasLocalCell (a :: as) = (a.isLocalCell || Attr.hasLocalCell as) := rfl
@[simp] theorem Attr.validList_append (xs ys : List (Attr msg)) :
    Attr.validList (xs ++ ys) = (Attr.validList xs && Attr.validList ys) := by simp [Attr.validList_eq_all]
@[simp] theorem Attr.hasLocalCell_append (xs ys : List (Attr msg)) :
    Attr.hasLocalCell (xs ++ ys) = (Attr.hasLocalCell xs || Attr.hasLocalCell ys) := by simp [Attr.hasLocalCell_eq_any]

@[simp] theorem Attr.validList_filter_nonkey (xs : List (Attr msg)) :
    Attr.validList (xs.filter (fun | .key _ => false | _ => true)) = Attr.validList xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp only [List.filter_cons, ↓reduceIte, Bool.false_eq_true, Attr.validList, Attr.valid, ih, Bool.true_and]

@[simp] theorem Attr.hasLocalCell_filter_nonkey (xs : List (Attr msg)) :
    Attr.hasLocalCell (xs.filter (fun | .key _ => false | _ => true)) = Attr.hasLocalCell xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp only [List.filter_cons, ↓reduceIte, Bool.false_eq_true, Attr.hasLocalCell, Attr.isLocalCell, ih, Bool.false_or]

@[simp] theorem Attr.valid_map {α β : Type} (f : α → β) (a : Attr α) : (a.map f).valid = a.valid := by cases a <;> rfl
@[simp] theorem Attr.isLocalCell_map {α β : Type} (f : α → β) (a : Attr α) : (a.map f).isLocalCell = a.isLocalCell := by cases a <;> rfl
@[simp] theorem Attr.valid_prefixSignal (pfx : String) (a : Attr msg) : (a.prefixSignal pfx).valid = a.valid := by cases a <;> rfl
@[simp] theorem Attr.isLocalCell_prefixSignal (pfx : String) (a : Attr msg) : (a.prefixSignal pfx).isLocalCell = a.isLocalCell := by cases a <;> rfl

@[simp] theorem Attr.validList_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.validList (as.map (Attr.map f)) = Attr.validList as := by simp [Attr.validList_eq_all, Function.comp_def]
@[simp] theorem Attr.hasLocalCell_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) :
    Attr.hasLocalCell (as.map (Attr.map f)) = Attr.hasLocalCell as := by simp [Attr.hasLocalCell_eq_any, Function.comp_def]
@[simp] theorem Attr.validList_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.validList (as.map (Attr.prefixSignal pfx)) = Attr.validList as := by simp [Attr.validList_eq_all, Function.comp_def]
@[simp] theorem Attr.hasLocalCell_prefixSignal (pfx : String) (as : List (Attr msg)) :
    Attr.hasLocalCell (as.map (Attr.prefixSignal pfx)) = Attr.hasLocalCell as := by simp [Attr.hasLocalCell_eq_any, Function.comp_def]

@[simp] theorem Html.mapChildren_isEmpty {α β : Type} (f : α → β) (cs : List (Html α)) :
    (Html.mapChildren f cs).isEmpty = cs.isEmpty := by cases cs <;> rfl

@[simp] theorem Html.prefixSignalsList_isEmpty (pfx : String) (cs : List (Html msg)) :
    (Html.prefixSignalsList pfx cs).isEmpty = cs.isEmpty := by cases cs <;> rfl

mutual
  private theorem htmlValidIn_map_of {α β : Type} (ctx : HtmlCtx) (f : Attr α → Attr β)
      (M : Html α → Html β) (ML : List (Html α) → List (Html β))
      (hT : ∀ s, M (.text s) = .text s) (hE : ∀ t a cs, M (.element t a cs) = .element t (a.map f) (ML cs))
      (hN : ML [] = []) (hC : ∀ c cs, ML (c :: cs) = M c :: ML cs)
      (hEmp : ∀ cs, (ML cs).isEmpty = cs.isEmpty)
      (hv : ∀ a, (f a).valid = a.valid) (hl : ∀ a, (f a).isLocalCell = a.isLocalCell) :
      (h : Html α) → Html.validIn ctx (M h) = Html.validIn ctx h
    | .text s => by rw [hT]; rfl
    | .element tag attrs children => by
        have hvl : Attr.validList (attrs.map f) = Attr.validList attrs := by simp [Attr.validList_eq_all, Function.comp_def, hv]
        have hlc : Attr.hasLocalCell (attrs.map f) = Attr.hasLocalCell attrs := by simp [Attr.hasLocalCell_eq_any, Function.comp_def, hl]
        simp only [hE, Html.validIn, hvl, hlc, hEmp]
        cases stepHtmlCtx ctx tag with
        | none => rfl
        | some childCtx => exact congrArg (_ && ·) (htmlValidListIn_map_of childCtx f M ML hT hE hN hC hEmp hv hl children)

  private theorem htmlValidListIn_map_of {α β : Type} (ctx : HtmlCtx) (f : Attr α → Attr β)
      (M : Html α → Html β) (ML : List (Html α) → List (Html β))
      (hT : ∀ s, M (.text s) = .text s) (hE : ∀ t a cs, M (.element t a cs) = .element t (a.map f) (ML cs))
      (hN : ML [] = []) (hC : ∀ c cs, ML (c :: cs) = M c :: ML cs)
      (hEmp : ∀ cs, (ML cs).isEmpty = cs.isEmpty)
      (hv : ∀ a, (f a).valid = a.valid) (hl : ∀ a, (f a).isLocalCell = a.isLocalCell) :
      (cs : List (Html α)) → Html.validListIn ctx (ML cs) = Html.validListIn ctx cs
    | [] => by rw [hN]; rfl
    | c :: cs => by
        simp only [hC, Html.validListIn,
          htmlValidIn_map_of ctx f M ML hT hE hN hC hEmp hv hl c,
          htmlValidListIn_map_of ctx f M ML hT hE hN hC hEmp hv hl cs]
end

@[simp] theorem Html.validIn_map {α β : Type} (ctx : HtmlCtx) (f : α → β) (h : Html α) :
    Html.validIn ctx (h.map f) = Html.validIn ctx h :=
  htmlValidIn_map_of ctx (Attr.map f) (Html.map f) (Html.mapChildren f)
    (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (Html.mapChildren_isEmpty f)
    (Attr.valid_map f) (Attr.isLocalCell_map f) h

@[simp] theorem Html.validListIn_mapChildren {α β : Type} (ctx : HtmlCtx) (f : α → β) (cs : List (Html α)) :
    Html.validListIn ctx (Html.mapChildren f cs) = Html.validListIn ctx cs :=
  htmlValidListIn_map_of ctx (Attr.map f) (Html.map f) (Html.mapChildren f)
    (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (Html.mapChildren_isEmpty f)
    (Attr.valid_map f) (Attr.isLocalCell_map f) cs

@[simp] theorem Html.validIn_prefixSignals (ctx : HtmlCtx) (pfx : String) (h : Html msg) :
    Html.validIn ctx (h.prefixSignals pfx) = Html.validIn ctx h :=
  htmlValidIn_map_of ctx (Attr.prefixSignal pfx) (Html.prefixSignals pfx) (Html.prefixSignalsList pfx)
    (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (Html.prefixSignalsList_isEmpty pfx)
    (Attr.valid_prefixSignal pfx) (Attr.isLocalCell_prefixSignal pfx) h

@[simp] theorem Html.validListIn_prefixSignalsList (ctx : HtmlCtx) (pfx : String) (cs : List (Html msg)) :
    Html.validListIn ctx (Html.prefixSignalsList pfx cs) = Html.validListIn ctx cs :=
  htmlValidListIn_map_of ctx (Attr.prefixSignal pfx) (Html.prefixSignals pfx) (Html.prefixSignalsList pfx)
    (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (Html.prefixSignalsList_isEmpty pfx)
    (Attr.valid_prefixSignal pfx) (Attr.isLocalCell_prefixSignal pfx) cs

@[simp] theorem Html.validListIn_nil (ctx : HtmlCtx) : Html.validListIn ctx ([] : List (Html msg)) = true := rfl
@[simp] theorem Html.validListIn_cons (ctx : HtmlCtx) (c : Html msg) (cs : List (Html msg)) :
    Html.validListIn ctx (c :: cs) = (Html.validIn ctx c && Html.validListIn ctx cs) := rfl

@[simp] theorem Html.validListIn_append (ctx : HtmlCtx) (xs ys : List (Html msg)) :
    Html.validListIn ctx (xs ++ ys) = (Html.validListIn ctx xs && Html.validListIn ctx ys) := by
  induction xs with | nil => simp [Html.validListIn] | cons _ _ ih => simp [Html.validListIn, ih, Bool.and_assoc]

@[simp] theorem Html.validIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg) :
    Html.validIn ctx (if c then a else b) = (if c then Html.validIn ctx a else Html.validIn ctx b) :=
  fn_ite (Html.validIn ctx) c a b

@[simp] theorem Html.validListIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : List (Html msg)) :
    Html.validListIn ctx (if c then a else b) = (if c then Html.validListIn ctx a else Html.validListIn ctx b) :=
  fn_ite (Html.validListIn ctx) c a b

@[simp] theorem Html.validIn_ofOption (ctx : HtmlCtx) (o : Option (Html msg)) :
    Html.validIn ctx (Html.ofOption o) =
      match o with | some h => Html.validIn ctx h | none => validTextIn ctx "" := by cases o <;> rfl

@[simp] theorem Html.validListIn_map {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f) = xs.all (fun a => Html.validIn ctx (f a)) := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

@[simp] theorem Html.validListIn_toList_map {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) :
    Html.validListIn ctx (xs.map f).toList = xs.toList.all (fun a => Html.validIn ctx (f a)) := by
  simp [Array.toList_map]

@[simp] theorem List.all_const_true {α : Type} (xs : List α) : xs.all (fun _ => true) = true := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

local macro "valid_text_in_simp " nm:ident mode:term : command =>
  `(@[simp] theorem $nm (inP inter inForm : Bool) (s : String) :
      validTextIn ⟨$mode, inP, inter, inForm⟩ s = true := rfl)

valid_text_in_simp validTextIn_normal   .normal
valid_text_in_simp validTextIn_option   .option
valid_text_in_simp validTextIn_textarea .textarea
valid_text_in_simp validTextIn_svg      .svg
@[simp] theorem validTextIn_rawStyle (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.rawStyle, inP, inter, inForm⟩ s = !containsCloseSeq s.toList := rfl

@[simp] theorem validTextIn_empty (ctx : HtmlCtx) : validTextIn ctx "" = true := by
  cases ctx with | mk mode _ _ _ => cases mode <;> simp [validTextIn, containsCloseSeq, containsCloseSeqLoop]

theorem Attr.validList_cons_intro {msg : Type} (a : Attr msg) (as : List (Attr msg))
    (ha : a.valid = true) (has : Attr.validList as = true) : Attr.validList (a :: as) = true := by
  simp [ha, has]

theorem Attr.validList_append_intro {msg : Type} (xs ys : List (Attr msg))
    (hx : Attr.validList xs = true) (hy : Attr.validList ys = true) : Attr.validList (xs ++ ys) = true := by
  simp [hx, hy]

theorem Attr.valid_ite_intro {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg)
    (ht : c → a.valid = true) (hf : ¬ c → b.valid = true) : Attr.valid (if c then a else b) = true :=
  bool_ite_intro Attr.valid true c a b ht hf

theorem Attr.hasLocalCell_cons_eq_false {msg : Type} (a : Attr msg) (as : List (Attr msg))
    (ha : a.isLocalCell = false) (has : Attr.hasLocalCell as = false) : Attr.hasLocalCell (a :: as) = false := by
  simp [ha, has]

theorem Attr.hasLocalCell_append_eq_false {msg : Type} (xs ys : List (Attr msg))
    (hx : Attr.hasLocalCell xs = false) (hy : Attr.hasLocalCell ys = false) : Attr.hasLocalCell (xs ++ ys) = false := by
  simp [hx, hy]

theorem Attr.isLocalCell_ite_eq_false {msg : Type} (c : Prop) [Decidable c] (a b : Attr msg)
    (ht : c → a.isLocalCell = false) (hf : ¬ c → b.isLocalCell = false) : Attr.isLocalCell (if c then a else b) = false :=
  bool_ite_intro Attr.isLocalCell false c a b ht hf

theorem Bool.not_false_or (a b : Bool) (ha : a = false) : (!a || b) = true := by simp [ha]

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
  by_cases h : containsCloseSeqLoop false s.toList <;> simp [h, containsCloseSeqLoop_escapeCloseSeqLoop]

theorem validTextIn_rawStyle_escape (inP inter inForm : Bool) (s : String) :
    validTextIn ⟨.rawStyle, inP, inter, inForm⟩ (escapeRawText s) = true := by
  simp [validTextIn, containsCloseSeq_escapeRawText]

theorem Html.validIn_element_intro {msg : Type} (ctx childCtx : HtmlCtx)
    (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))
    (hstep : stepHtmlCtx ctx tag = some childCtx) (hattrs : Attr.validList attrs = true)
    (hvoid : (!isVoidTag tag || children.isEmpty) = true)
    (hcell : (!Attr.hasLocalCell attrs || children.isEmpty) = true)
    (hkids : Html.validListIn childCtx children = true) :
    Html.validIn ctx (.element tag attrs children) = true := by
  simp [Html.validIn, hstep, hattrs, hvoid, hcell, hkids]

theorem Html.validListIn_cons_intro {msg : Type} (ctx : HtmlCtx) (c : Html msg) (cs : List (Html msg))
    (hc : Html.validIn ctx c = true) (hcs : Html.validListIn ctx cs = true) : Html.validListIn ctx (c :: cs) = true := by
  simp [hc, hcs]

theorem Html.validListIn_append_intro {msg : Type} (ctx : HtmlCtx) (xs ys : List (Html msg))
    (hx : Html.validListIn ctx xs = true) (hy : Html.validListIn ctx ys = true) : Html.validListIn ctx (xs ++ ys) = true := by
  simp [hx, hy]

theorem Html.validIn_ite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg)
    (ht : c → Html.validIn ctx a = true) (hf : ¬ c → Html.validIn ctx b = true) : Html.validIn ctx (if c then a else b) = true :=
  bool_ite_intro (Html.validIn ctx) true c a b ht hf

theorem Html.validIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a : c → Html msg) (b : ¬ c → Html msg)
    (ht : ∀ h : c, Html.validIn ctx (a h) = true) (hf : ∀ h : ¬ c, Html.validIn ctx (b h) = true) :
    Html.validIn ctx (if h : c then a h else b h) = true :=
  bool_dite_intro (Html.validIn ctx) true c a b ht hf

theorem Html.validListIn_ite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a b : List (Html msg))
    (ht : c → Html.validListIn ctx a = true) (hf : ¬ c → Html.validListIn ctx b = true) :
    Html.validListIn ctx (if c then a else b) = true :=
  bool_ite_intro (Html.validListIn ctx) true c a b ht hf

theorem Html.validListIn_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg)
    (hf : ∀ a, Html.validIn ctx (f a) = true) : Html.validListIn ctx (xs.map f) = true := by
  simp only [Html.validListIn_map, List.all_eq_true]; exact fun a _ => hf a

theorem Html.validListIn_toList_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg)
    (hf : ∀ a, Html.validIn ctx (f a) = true) : Html.validListIn ctx (xs.map f).toList = true := by
  simp only [Html.validListIn_toList_map, List.all_eq_true]; exact fun a _ => hf a

def onlySignalBind : List (Attr msg) → Bool
  | [.signalBind _] => true
  | .key _ :: rest  => onlySignalBind rest
  | _               => false

def mkCanonicalElem (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) : Html msg :=
  if tag == "span" && onlySignalBind attrs then
    match cs with
    | [c] => c
    | _   => .element tag (attrs.filterMap Attr.canonical) cs
  else
    .element tag (attrs.filterMap Attr.canonical) cs

mutual
  def Html.canonical : Html msg → Html msg
    | .text s               => .text s
    | .element tag attrs cs => mkCanonicalElem tag attrs (Html.canonicalList cs)

  def Html.canonicalList : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs => Html.canonical c :: Html.canonicalList cs
end

@[simp] theorem onlySignalBind_signalBind (sig : String) :
    onlySignalBind ([.signalBind sig] : List (Attr msg)) = true := rfl

@[simp] theorem onlySignalBind_key (k : String) (rest : List (Attr msg)) :
    onlySignalBind (.key k :: rest) = onlySignalBind rest := rfl

@[simp] theorem mkCanonicalElem_signalBind (sig : String) (c : Html msg) :
    mkCanonicalElem "span" [.signalBind sig] [c] = c := rfl

@[simp] theorem mkCanonicalElem_not_signal (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg))
    (h : (tag == "span" && onlySignalBind attrs) = false) :
    mkCanonicalElem tag attrs cs = .element tag (attrs.filterMap Attr.canonical) cs := by
  simp [mkCanonicalElem, h]

@[simp] theorem Html.canonical_text (s : String) :
    Html.canonical (.text s : Html msg) = .text s := rfl

@[simp] theorem Html.canonical_element (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) :
    Html.canonical (.element tag attrs cs) = mkCanonicalElem tag attrs (Html.canonicalList cs) := rfl

@[simp] theorem Html.canonical_ite (c : Prop) [Decidable c] (a b : Html msg) :
    Html.canonical (if c then a else b) = if c then Html.canonical a else Html.canonical b :=
  fn_ite Html.canonical c a b

@[simp] theorem Html.canonical_ofOption (o : Option (Html msg)) :
    Html.canonical (Html.ofOption o) = match o with | some h => Html.canonical h | none => .text "" := by
  cases o <;> rfl

@[simp] theorem Html.canonicalList_nil : Html.canonicalList ([] : List (Html msg)) = [] := rfl

@[simp] theorem Html.canonicalList_cons (c : Html msg) (cs : List (Html msg)) :
    Html.canonicalList (c :: cs) = Html.canonical c :: Html.canonicalList cs := rfl

@[simp] theorem Html.canonicalList_append (xs ys : List (Html msg)) :
    Html.canonicalList (xs ++ ys) = Html.canonicalList xs ++ Html.canonicalList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem Html.canonicalList_map {α : Type _} (xs : List α) (f : α → Html msg) :
    Html.canonicalList (xs.map f) = xs.map (fun x => Html.canonical (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem Html.canonicalList_eq_map (cs : List (Html msg)) :
    Html.canonicalList cs = cs.map Html.canonical := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-! ## Fast-Path `@[csimp]` Equivalences & ASCII Byte Helpers -/

private theorem list_toByteArray_loop_data (bs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bs acc).data.toList = acc.data.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons b bs ih => simp only [List.toByteArray.loop, ih]; simp [ByteArray.push, List.append_assoc]

private theorem list_toByteArray_data (bs : List UInt8) : bs.toByteArray.data.toList = bs := by
  have h := list_toByteArray_loop_data bs ByteArray.empty
  have hem : ByteArray.empty.data.toList = [] := rfl
  rw [hem, List.nil_append] at h; exact h

private theorem string_toByteArray_data (s : String) :
    s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  have h1 : s.toByteArray = s.toList.utf8Encode := by
    rw [← String.toByteArray_ofList, String.ofList_toList]
  rw [h1, List.utf8Encode, list_toByteArray_data]

private theorem utf8EncodeChar_le_127 (c : Char) (hc : c.toNat ≤ 127) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  have hc' : c.val.toNat ≤ 127 := hc
  simp only [hc', ↓reduceIte]; rfl

private theorem uint8_ofNat_mod_add_ge_128 {x m base : Nat} (hm : 0 < m) (hb : 128 ≤ base) (hlt : m + base ≤ 256) :
    (UInt8.ofNat (x % m + base)).toNat ≥ 128 := by
  change (x % m + base) % 256 ≥ 128
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.mod_lt x hm) base) hlt)]
  exact Nat.le_trans hb (Nat.le_add_left base (x % m))

private theorem utf8EncodeChar_gt_127 (c : Char) (h : c.toNat > 127) :
    ∀ b ∈ String.utf8EncodeChar c, b.toNat ≥ 128 := by
  unfold String.utf8EncodeChar
  have h1 : ¬(c.val.toNat ≤ 127) := Nat.not_le_of_gt h
  simp only [h1, ↓reduceIte]
  split <;> try split
  all_goals
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    repeat (rcases hb with rfl | hb; · apply uint8_ofNat_mod_add_ge_128 <;> decide)
    try (subst hb; apply uint8_ofNat_mod_add_ge_128 <;> decide)

private theorem utf8EncodeChar_ne_nil (c : Char) : String.utf8EncodeChar c ≠ [] := by
  unfold String.utf8EncodeChar; dsimp only; repeat (split <;> try simp)

private theorem hasAsciiByteLoop_eq (s : String) (p : UInt8 → Bool) (i : Nat) :
    hasAsciiByteLoop s p s.utf8ByteSize rfl i = (s.toByteArray.data.toList.drop i).any p := by
  fun_induction hasAsciiByteLoop s p s.utf8ByteSize rfl i with
  | case1 i h hp =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact h
      rw [List.drop_eq_getElem_cons hlt, List.any_cons]
      have hget : s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h := rfl
      rw [hget, hp]; rfl
  | case2 i h hp ih =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact h
      rw [List.drop_eq_getElem_cons hlt, List.any_cons]
      have hget : s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h := rfl
      have hpf : p (s.getUTF8Byte ⟨i⟩ h) = false := Bool.eq_false_iff.2 hp
      rw [hget, hpf, Bool.false_or, ih]
  | case3 i h =>
      have hge : s.toByteArray.data.toList.length ≤ i := by
        rw [Array.length_toList]
        have h' : ¬(i < s.toByteArray.size) := by rw [String.size_toByteArray]; exact h
        exact Nat.le_of_not_lt h'
      rw [List.drop_eq_nil_of_le hge]; rfl

theorem hasAsciiByte_eq_any (s : String) (p : UInt8 → Bool) (q : Char → Bool)
    (hhi : ∀ b : UInt8, b.toNat ≥ 128 → p b = false)
    (hlo : ∀ c : Char, c.toNat ≤ 127 → p (UInt8.ofNat c.toNat) = q c)
    (hqhi : ∀ c : Char, c.toNat > 127 → q c = false) :
    hasAsciiByte s p = s.toList.any q := by
  have hgo : hasAsciiByte s p = s.toByteArray.data.toList.any p := by
    simpa [hasAsciiByte] using hasAsciiByteLoop_eq s p 0
  rw [hgo, string_toByteArray_data, List.any_flatMap]
  congr 1
  funext c
  by_cases hc : c.toNat ≤ 127
  · rw [utf8EncodeChar_le_127 c hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    exact hlo c hc
  · have hgt : c.toNat > 127 := by omega
    rw [hqhi c hgt]
    rw [List.any_eq_false]
    intro b hb
    simp [hhi b (utf8EncodeChar_gt_127 c hgt b hb)]

theorem asciiByte_beq_char (c : Char) (hc : c.toNat ≤ 127) (target : Char) (ht : target.toNat ≤ 127) :
    (UInt8.ofNat c.toNat == UInt8.ofNat target.toNat) = (c == target) := by
  cases heq : (c == target)
  · rw [beq_eq_false_iff_ne] at heq ⊢
    intro h; apply heq
    have hnat : c.toNat = target.toNat := by
      have h1 : (UInt8.ofNat c.toNat).toNat = (UInt8.ofNat target.toNat).toNat := congrArg UInt8.toNat h
      change c.toNat % 256 = target.toNat % 256 at h1
      omega
    exact Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat))
  · rw [beq_iff_eq] at heq; subst heq; simp

private theorem escapeCloseSeqBytes_hi (xs ys : List UInt8) (hhi : ∀ b ∈ xs, b.toNat ≥ 128) (hne : xs ≠ []) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (xs ++ ys) = xs ++ escapeCloseSeqBytesSpec false ys := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
      intro afterLt
      have hb : b.toNat ≥ 128 := hhi b (by simp)
      have hb47 : (b == 47) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; subst heq; exact absurd hb (by decide)
      have hb60 : (b == 60) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; subst heq; exact absurd hb (by decide)
      simp only [List.cons_append, escapeCloseSeqBytesSpec, hb47, hb60, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      cases bs with
      | nil => rfl
      | cons b' bs' => rw [ih (fun x hx => hhi x (by simp [hx])) (by simp) false]

private theorem escapeCloseSeqBytes_flatMap (cs : List Char) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (cs.flatMap String.utf8EncodeChar) =
      (escapeCloseSeqLoop afterLt cs).flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro afterLt
      simp only [List.flatMap_cons, escapeCloseSeqLoop]
      by_cases hc : c.toNat ≤ 127
      · have h1 := utf8EncodeChar_le_127 c hc
        have h47 : (UInt8.ofNat c.toNat == 47) = (c == '/') := asciiByte_beq_char c hc '/' (by decide)
        have h60 : (UInt8.ofNat c.toNat == 60) = (c == '<') := asciiByte_beq_char c hc '<' (by decide)
        rw [h1, List.singleton_append, escapeCloseSeqBytesSpec, h47, h60]
        split
        · simp [List.flatMap_cons, ih]; rfl
        · simp [List.flatMap_cons, h1, ih]
      · have hgt : c.toNat > 127 := by omega
        have hc47 : (c == '/') = false := by
          rw [beq_eq_false_iff_ne]; intro h; subst h; exact absurd hgt (by decide)
        have hc60 : (c == '<') = false := by
          rw [beq_eq_false_iff_ne]; intro h; subst h; exact absurd hgt (by decide)
        rw [escapeCloseSeqBytes_hi _ _ (utf8EncodeChar_gt_127 c hgt) (utf8EncodeChar_ne_nil c) afterLt]
        simp [hc47, hc60, List.flatMap_cons, ih]

private theorem escapeCloseSeqLoop_noop (cs : List Char) (afterLt : Bool)
    (h : containsCloseSeqLoop afterLt cs = false) :
    escapeCloseSeqLoop afterLt cs = cs := by
  induction cs generalizing afterLt with
  | nil => rfl
  | cons c cs ih =>
      simp only [containsCloseSeqLoop, Bool.or_eq_false_iff] at h
      simp only [escapeCloseSeqLoop, h.1, Bool.false_eq_true, ↓reduceIte]
      rw [ih (c == '<') h.2]

private theorem escapeRawText_eq_always (s : String) :
    escapeRawText s = String.ofList (escapeCloseSeqLoop false s.toList) := by
  unfold escapeRawText containsCloseSeq
  cases h : containsCloseSeqLoop false s.toList
  · simp [escapeCloseSeqLoop_noop s.toList false h]
  · simp

private theorem copySliceAppend_data (src : ByteArray) (segStart stop : Nat) (acc : ByteArray)
    (hle : segStart ≤ stop) :
    (copySliceAppend src segStart stop acc).data.toList =
      acc.data.toList ++ (src.data.toList.drop segStart).take (stop - segStart) := by
  unfold copySliceAppend ByteArray.copySlice
  simp only [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  have hlen : acc.size = acc.data.toList.length := Array.length_toList.symm
  have h1 : (acc.data.toList.drop 0).take (acc.size - 0) = acc.data.toList := by
    rw [List.drop_zero, Nat.sub_zero, hlen, List.take_length]
  have h2 : acc.data.toList.drop (acc.size + min (stop - segStart) (src.data.size - segStart)) = [] :=
    List.drop_eq_nil_of_le (by rw [← hlen]; omega)
  have h3 : segStart + (stop - segStart) - segStart = stop - segStart := by omega
  rw [h1, h2, h3, List.take_nil, List.append_nil]

private theorem hasCloseSeqStrLoop_false_eq (s : String) (i : Nat) (afterLt : Bool)
    (hfalse : hasCloseSeqStrLoop s i afterLt = false) :
    escapeCloseSeqBytesSpec afterLt (s.toByteArray.data.toList.drop i) = s.toByteArray.data.toList.drop i := by
  fun_induction hasCloseSeqStrLoop s i afterLt with
  | case1 i afterLt hi b hhit => cases hfalse
  | case2 i afterLt hi b hmiss ih =>
      have hlt : i < s.toByteArray.data.toList.length := by
        rw [Array.length_toList]; change i < s.toByteArray.size; rw [String.size_toByteArray]; exact hi
      rw [List.drop_eq_getElem_cons hlt, escapeCloseSeqBytesSpec]
      have hget : s.toByteArray.data.toList[i] = b := rfl
      rw [hget, if_neg hmiss, ih hfalse]
  | case3 i afterLt hge =>
      have : s.toByteArray.data.toList.length ≤ i := by
        rw [Array.length_toList]
        have h' : ¬(i < s.toByteArray.size) := by rw [String.size_toByteArray]; exact hge
        exact Nat.le_of_not_lt h'
      rw [List.drop_eq_nil_of_le this]; rfl

private theorem escapeRawBytesLoop_data (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray)
    (hle : segStart ≤ i) (hi : i ≤ ba.size) :
    (escapeRawBytesLoop ba segStart i afterLt acc).data.toList =
      acc.data.toList ++ (ba.data.toList.drop segStart).take (i - segStart) ++
      escapeCloseSeqBytesSpec afterLt (ba.data.toList.drop i) := by
  fun_induction escapeRawBytesLoop ba segStart i afterLt acc with
  | case1 segStart i afterLt acc hlt b hhit acc' ih =>
      have hi_lt : i < ba.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hget : ba.data.toList[i] = b := rfl
      have h47 : b = 47 := beq_iff_eq.1 ((Bool.and_eq_true _ _).mp hhit).2
      rw [ih (by omega) (by omega)]
      simp only [acc', ByteArray.push, Array.toList_push]
      rw [copySliceAppend_data ba segStart i acc hle]
      rw [List.drop_eq_getElem_cons hi_lt, hget]
      rw [escapeCloseSeqBytesSpec, if_pos hhit]
      have htake1 : (b :: ba.data.toList.drop (i + 1)).take (i + 1 - i) = [47] := by
        rw [show i + 1 - i = 1 by omega, h47]; rfl
      rw [htake1]
      simp [List.append_assoc]
  | case2 segStart i afterLt acc hlt b hmiss ih =>
      have hi_lt : i < ba.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hget : ba.data.toList[i] = b := rfl
      rw [ih (by omega) (by omega)]
      rw [List.drop_eq_getElem_cons hi_lt, hget, escapeCloseSeqBytesSpec, if_neg hmiss]
      have hlen : i - segStart < (ba.data.toList.drop segStart).length := by
        rw [List.length_drop, Array.length_toList]; change i - segStart < ba.size - segStart; omega
      have htake : (ba.data.toList.drop segStart).take (i + 1 - segStart) =
          (ba.data.toList.drop segStart).take (i - segStart) ++ [b] := by
        rw [show i + 1 - segStart = (i - segStart) + 1 by omega, List.take_succ_eq_append_getElem hlen]
        simp [List.getElem_drop, show segStart + (i - segStart) = i by omega]; rfl
      rw [htake]
      simp [List.append_assoc]
  | case3 segStart i afterLt acc hge =>
      have heq : i = ba.size := by omega
      subst heq
      rw [copySliceAppend_data ba segStart ba.size acc hle]
      have hnil : ba.data.toList.drop ba.size = [] := by
        apply List.drop_eq_nil_of_le; rw [Array.length_toList]; exact Nat.le_refl _
      rw [hnil]; simp [escapeCloseSeqBytesSpec]

private theorem escapeRawBytes_eq_spec (s : String) :
    escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)) =
      (String.ofList (escapeCloseSeqLoop false s.toList)).toByteArray := by
  apply ByteArray.ext; apply Array.ext'
  unfold String.toUTF8
  rw [escapeRawBytesLoop_data s.toByteArray 0 0 false _ (Nat.le_refl _) (Nat.zero_le _)]
  have hem : (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)).data.toList = [] := rfl
  rw [hem, String.toByteArray_ofList, List.utf8Encode, list_toByteArray_data,
      ← escapeCloseSeqBytes_flatMap, ← string_toByteArray_data]
  simp

private def escapeRawTextFast (s : String) : String :=
  if !hasCloseSeqStrLoop s 0 false then s
  else
    String.fromUTF8
      (escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)))
      (by rw [escapeRawBytes_eq_spec]; exact (String.ofList (escapeCloseSeqLoop false s.toList)).isValidUTF8)

@[csimp] theorem escapeRawText_eq_fast : @escapeRawText = @escapeRawTextFast := by
  funext s
  rw [escapeRawText_eq_always]
  unfold escapeRawTextFast
  cases h : hasCloseSeqStrLoop s 0 false
  · simp only [Bool.not_false, ↓reduceIte]
    have h1 := hasCloseSeqStrLoop_false_eq s 0 false h
    simp only [List.drop_zero] at h1
    apply (String.toByteArray_inj).1
    apply ByteArray.ext; apply Array.ext'
    rw [String.toByteArray_ofList, List.utf8Encode, list_toByteArray_data,
        ← escapeCloseSeqBytes_flatMap, ← string_toByteArray_data, h1]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply (String.toByteArray_inj).1
    exact (escapeRawBytes_eq_spec s).symm

/-! ## Compile-Time Accessibility (A11y) Predicates & `Html.map` / `Html.canonical` Invariance -/

def attrValue (key : String) : List (Attr msg) → Option String
  | []                     => none
  | .attr k v :: r         => if k == key then some v else attrValue key r
  | .signalAttr _ k v :: r => if k == key then some v else attrValue key r
  | _ :: r                 => attrValue key r

def hasAttr (key : String) (as : List (Attr msg)) : Bool :=
  (attrValue key as).isSome

def isNonBlank (s : String) : Bool :=
  s.toList.any (fun c => !c.isWhitespace)

def hasNonBlankAttr (key : String) (as : List (Attr msg)) : Bool :=
  match attrValue key as with
  | some v => isNonBlank v
  | none   => false

@[simp] theorem attrValue_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) :
    attrValue key (as.map (Attr.map f)) = attrValue key as := by
  induction as with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | attr k v | signalAttr _ k v =>
          by_cases hk : (k == key) <;> simp [Attr.map, attrValue, hk, ih]
      | _ => simp [Attr.map, attrValue, ih]

@[simp] theorem hasAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) :
    hasAttr key (as.map (Attr.map f)) = hasAttr key as := by
  simp [hasAttr]

@[simp] theorem hasNonBlankAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) :
    hasNonBlankAttr key (as.map (Attr.map f)) = hasNonBlankAttr key as := by
  simp [hasNonBlankAttr]

theorem attrValue_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) :
    attrValue key (as.filterMap Attr.canonical) = attrValue key as := by
  have hcls : ("class" == key) = false := beq_false_of_ne (Ne.symm hk)
  induction as with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | cls _ => simp [Attr.canonical, attrValue, hcls, ih]
      | attr k v | signalAttr _ k v =>
          by_cases heq : (k == key) <;> simp [Attr.canonical, attrValue, heq, ih]
      | _ => simp [Attr.canonical, attrValue, ih]

theorem hasAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) :
    hasAttr key (as.filterMap Attr.canonical) = hasAttr key as := by
  simp [hasAttr, attrValue_canonical key hk]

theorem hasNonBlankAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) :
    hasNonBlankAttr key (as.filterMap Attr.canonical) = hasNonBlankAttr key as := by
  simp [hasNonBlankAttr, attrValue_canonical key hk]

theorem attrValue_of_onlySignalBind {msg : Type} (key : String) :
    ∀ as : List (Attr msg), onlySignalBind as = true → attrValue key as = none
  | [.signalBind _], _ => rfl
  | .key _ :: rest, h => attrValue_of_onlySignalBind key rest h

private theorem html_canonicalList_eq_singleton {msg : Type} {cs : List (Html msg)} {c : Html msg}
    (h : Html.canonicalList cs = [c]) : ∃ c₀, cs = [c₀] ∧ c = Html.canonical c₀ := by
  cases cs with
  | nil => simp [Html.canonicalList] at h
  | cons c₀ rest =>
      cases rest with
      | nil => simp [Html.canonicalList] at h; exact ⟨c₀, rfl, h.symm⟩
      | cons _ _ => simp [Html.canonicalList] at h

/-- Official WAI-ARIA 1.2 concrete role names (first-character indexed for fast kernel reduction). -/
def isValidAriaRole (r : String) : Bool :=
  match r.toList with
  | 'a' :: _ => r == "alert" || r == "alertdialog" || r == "application" || r == "article"
  | 'b' :: _ => r == "banner" || r == "blockquote" || r == "button"
  | 'c' :: _ => r == "caption" || r == "cell" || r == "checkbox" || r == "code" || r == "columnheader" || r == "combobox" || r == "complementary" || r == "contentinfo"
  | 'd' :: _ => r == "definition" || r == "deletion" || r == "dialog" || r == "directory" || r == "document"
  | 'e' :: _ => r == "emphasis"
  | 'f' :: _ => r == "feed" || r == "figure" || r == "form"
  | 'g' :: _ => r == "generic" || r == "grid" || r == "gridcell" || r == "group"
  | 'h' :: _ => r == "heading"
  | 'i' :: _ => r == "img" || r == "insertion"
  | 'l' :: _ => r == "link" || r == "list" || r == "listbox" || r == "listitem" || r == "log"
  | 'm' :: _ => r == "main" || r == "marquee" || r == "math" || r == "menu" || r == "menubar" || r == "menuitem" || r == "menuitemcheckbox" || r == "menuitemradio" || r == "meter"
  | 'n' :: _ => r == "navigation" || r == "none" || r == "note"
  | 'o' :: _ => r == "option"
  | 'p' :: _ => r == "paragraph" || r == "presentation" || r == "progressbar"
  | 'r' :: _ => r == "radio" || r == "radiogroup" || r == "region" || r == "row" || r == "rowgroup" || r == "rowheader"
  | 's' :: _ => r == "scrollbar" || r == "search" || r == "searchbox" || r == "separator" || r == "slider" || r == "spinbutton" || r == "status" || r == "strong" || r == "subscript" || r == "superscript" || r == "switch"
  | 't' :: _ => r == "tab" || r == "table" || r == "tablist" || r == "tabpanel" || r == "term" || r == "textbox" || r == "time" || r == "timer" || r == "toolbar" || r == "tooltip" || r == "tree" || r == "treegrid" || r == "treeitem"
  | _ => false

def attrsValidAriaRoles : List (Attr msg) → Bool
  | []                     => true
  | .attr k v :: r         => (k != "role" || isValidAriaRole v) && attrsValidAriaRoles r
  | .signalAttr _ k v :: r => (k != "role" || isValidAriaRole v) && attrsValidAriaRoles r
  | _ :: r                 => attrsValidAriaRoles r

@[simp] theorem attrsValidAriaRoles_map {α β : Type} (f : α → β) (as : List (Attr α)) :
    attrsValidAriaRoles (as.map (Attr.map f)) = attrsValidAriaRoles as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.map, attrsValidAriaRoles, ih]

@[simp] theorem attrsValidAriaRoles_canonical {msg : Type} (as : List (Attr msg)) :
    attrsValidAriaRoles (as.filterMap Attr.canonical) = attrsValidAriaRoles as := by
  induction as with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [Attr.canonical, attrsValidAriaRoles, ih]

private theorem attrsValidAriaRoles_of_onlySignalBind {msg : Type} :
    ∀ as : List (Attr msg), onlySignalBind as = true → attrsValidAriaRoles as = true
  | [.signalBind _], _ => rfl
  | .key _ :: rest, h => attrsValidAriaRoles_of_onlySignalBind rest h

def isFormControlTag (tag : String) : Bool :=
  tag == "input" || tag == "select" || tag == "textarea"

def headingLevel? : String → Option Nat
  | "h1" => some 1
  | "h2" => some 2
  | "h3" => some 3
  | "h4" => some 4
  | "h5" => some 5
  | "h6" => some 6
  | _    => none

def listNoDups : List String → Bool
  | []      => true
  | x :: xs => !xs.contains x && listNoDups xs

def headingLevelsOrderedFrom (prev : Nat) : List Nat → Bool
  | []          => true
  | lvl :: rest => (prev == 0 || lvl ≤ prev + 1) && headingLevelsOrderedFrom lvl rest

/-! ### Unified `Html.fold` Paramorphism & Accessibility Predicates -/

mutual
  def Html.fold {msg γ : Type} (onText : String → γ)
      (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ) : Html msg → γ
    | .text s => onText s
    | .element tag attrs kids => onElem tag attrs kids (Html.foldList onText onElem nil cons kids)
  def Html.foldList {msg γ : Type} (onText : String → γ)
      (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ) : List (Html msg) → γ
    | []      => nil
    | c :: cs => cons (Html.fold onText onElem nil cons c) (Html.foldList onText onElem nil cons cs)
end

private theorem mkCanonicalElem_cases {msg : Type} (t : String) (a : List (Attr msg)) (cs : List (Html msg)) :
    (t = "span" ∧ onlySignalBind a = true ∧ ∃ c₀, cs = [c₀] ∧ mkCanonicalElem t a (Html.canonicalList cs) = c₀.canonical) ∨
    mkCanonicalElem t a (Html.canonicalList cs) = .element t (a.filterMap Attr.canonical) (Html.canonicalList cs) := by
  unfold mkCanonicalElem
  split
  · next h =>
    have ⟨ht, ha⟩ := Bool.and_eq_true_iff.1 h
    cases hcl : Html.canonicalList cs with
    | cons c rest =>
      cases rest with
      | nil => rcases html_canonicalList_eq_singleton hcl with ⟨c₀, rfl, rfl⟩; exact .inl ⟨beq_iff_eq.1 ht, ha, c₀, rfl, rfl⟩
      | cons _ _ => exact .inr rfl
    | nil => exact .inr rfl
  · exact .inr rfl

mutual
  theorem Html.fold_map {α β γ : Type} (f : α → β) (onText : String → γ)
      (onElemα : String → List (Attr α) → List (Html α) → γ → γ)
      (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) :
      (h : Html α) → Html.fold onText onElemβ nil cons (h.map f) = Html.fold onText onElemα nil cons h
    | .text _ => rfl
    | .element t a cs => by
        change onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs)
            (Html.foldList onText onElemβ nil cons (Html.mapChildren f cs)) =
          onElemα t a cs (Html.foldList onText onElemα nil cons cs)
        rw [Html.foldList_map f onText onElemα onElemβ nil cons hElem cs, hElem]
  theorem Html.foldList_map {α β γ : Type} (f : α → β) (onText : String → γ)
      (onElemα : String → List (Attr α) → List (Html α) → γ → γ)
      (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) :
      (cs : List (Html α)) → Html.foldList onText onElemβ nil cons (Html.mapChildren f cs) = Html.foldList onText onElemα nil cons cs
    | [] => rfl
    | c :: cs => by
        change cons (Html.fold onText onElemβ nil cons (c.map f))
            (Html.foldList onText onElemβ nil cons (Html.mapChildren f cs)) =
          cons (Html.fold onText onElemα nil cons c) (Html.foldList onText onElemα nil cons cs)
        rw [Html.fold_map f onText onElemα onElemβ nil cons hElem c, Html.foldList_map f onText onElemα onElemβ nil cons hElem cs]
end

mutual
  theorem Html.fold_canonical {msg γ : Type} (onText : String → γ)
      (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
      (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) :
      (h : Html msg) → Html.fold onText onElem nil cons h.canonical = Html.fold onText onElem nil cons h
    | .text _ => rfl
    | .element t a cs => by
        change Html.fold onText onElem nil cons (mkCanonicalElem t a (Html.canonicalList cs)) = _
        rcases mkCanonicalElem_cases t a cs with ⟨rfl, ha, c₀, rfl, heq⟩ | heq
        · rw [heq, Html.fold, Html.foldList, Html.foldList, hUnwrap a c₀ _ ha]
          exact Html.fold_canonical onText onElem nil cons hUnwrap hElem c₀
        · rw [heq, Html.fold, Html.fold, Html.foldList_canonical onText onElem nil cons hUnwrap hElem cs, hElem]
  theorem Html.foldList_canonical {msg γ : Type} (onText : String → γ)
      (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
      (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) :
      (cs : List (Html msg)) → Html.foldList onText onElem nil cons (Html.canonicalList cs) = Html.foldList onText onElem nil cons cs
    | [] => rfl
    | c :: cs => by
        simp only [Html.canonicalList, Html.foldList,
          Html.fold_canonical onText onElem nil cons hUnwrap hElem c,
          Html.foldList_canonical onText onElem nil cons hUnwrap hElem cs]
end

mutual
  theorem Html.fold_eq_node {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ)
      (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks))
      (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) :
      (h : Html msg) → F h = Html.fold onText onElem nil cons h
    | .text s => hT s
    | .element t a ks => by rw [hE, Html.fold, Html.fold_eq_list F FL onText onElem nil cons hT hE hN hC ks]
  theorem Html.fold_eq_list {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ)
      (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks))
      (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) :
      (cs : List (Html msg)) → FL cs = Html.foldList onText onElem nil cons cs
    | [] => hN
    | c :: cs => by rw [hC, Html.foldList, Html.fold_eq_node F FL onText onElem nil cons hT hE hN hC c,
                         Html.fold_eq_list F FL onText onElem nil cons hT hE hN hC cs]
end

theorem Html.foldList_all_mapList {α : Type _} {msg : Type} (onText : String → Bool)
    (onElem : String → List (Attr msg) → List (Html msg) → Bool → Bool) (g : α → Html msg) (l : List α) :
    Html.foldList onText onElem true (· && ·) (l.map g) = true ↔
      ∀ x ∈ l, Html.fold onText onElem true (· && ·) (g x) = true := by
  induction l with | nil => simp [Html.foldList] | cons _ _ ih => simp [Html.foldList, ih, Bool.and_eq_true]

local macro "html_fold_spec" fn:ident fl:ident fnMap:ident flMap:ident fnCan:ident flCan:ident
    "type:" ty:term "text:" tFn:term "elem:" eFn:term "nil:" nVal:term "cons:" cFn:term
    "map:" mapPf:term "unwrap:" unwPf:term "can:" canPf:term : command =>
  `(mutual
      def $fn {msg : Type} : Html msg → $ty
        | .text s => $tFn s | .element tag attrs kids => $eFn tag attrs kids ($fl kids)
      def $fl {msg : Type} : List (Html msg) → $ty
        | [] => $nVal | c :: cs => $cFn ($fn c) ($fl cs)
    end
    private theorem eqNode {msg : Type} (h : Html msg) : $fn h = Html.fold $tFn $eFn $nVal $cFn h :=
      Html.fold_eq_node $fn $fl $tFn $eFn $nVal $cFn (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) h
    private theorem eqList {msg : Type} (cs : List (Html msg)) : $fl cs = Html.foldList $tFn $eFn $nVal $cFn cs :=
      Html.fold_eq_list $fn $fl $tFn $eFn $nVal $cFn (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) cs
    @[simp] theorem $fnMap {α β : Type} (f : α → β) (h : Html α) : $fn (h.map f) = $fn h := by
      rw [eqNode, eqNode]; exact Html.fold_map f $tFn $eFn $eFn $nVal $cFn $mapPf h
    @[simp] theorem $flMap {α β : Type} (f : α → β) (cs : List (Html α)) : $fl (Html.mapChildren f cs) = $fl cs := by
      rw [eqList, eqList]; exact Html.foldList_map f $tFn $eFn $eFn $nVal $cFn $mapPf cs
    @[simp] theorem $fnCan {msg : Type} (h : Html msg) : $fn (Html.canonical h) = $fn h := by
      rw [eqNode, eqNode]; exact Html.fold_canonical $tFn $eFn $nVal $cFn $unwPf $canPf h
    @[simp] theorem $flCan {msg : Type} (cs : List (Html msg)) : $fl (Html.canonicalList cs) = $fl cs := by
      rw [eqList, eqList]; exact Html.foldList_canonical $tFn $eFn $nVal $cFn $unwPf $canPf cs)

local macro "html_a11y_all" fn:ident fl:ident fnMap:ident flMap:ident fnCan:ident flCan:ident mlThm:ident
    "elem:" eFn:term "map:" mapPf:term "unwrap:" unwPf:term "can:" canPf:term : command =>
  `(html_fold_spec $fn $fl $fnMap $flMap $fnCan $flCan
      type: Bool text: (fun _ => true) elem: $eFn nil: true cons: (· && ·) map: $mapPf unwrap: $unwPf can: $canPf
    theorem $mlThm {α msg : Type} (g : α → Html msg) (l : List α) :
        $fl (l.map g) = true ↔ ∀ x ∈ l, $fn (g x) = true := by
      induction l with | nil => simp [$fl:ident] | cons _ _ ih => simp [$fl:ident, ih, Bool.and_eq_true])

html_a11y_all Html.imgsHaveAlt Html.imgsHaveAltList Html.imgsHaveAlt_map Html.imgsHaveAltList_map
    Html.imgsHaveAlt_canonical Html.imgsHaveAltList_canonical Html.imgsHaveAltList_mapList
  elem: (fun tag attrs _ r => (tag != "img" || hasAttr "alt" attrs) && r)
  map: (fun _ _ _ _ => by simp [hasAttr_map]) unwrap: (fun _ _ _ _ => by simp)
  can: (fun _ _ _ _ => by simp [hasAttr_canonical "alt" (by decide)])

html_fold_spec Html.hasAccessibleNameChild Html.hasAccessibleNameChildren
    Html.hasAccessibleNameChild_map Html.hasAccessibleNameChildren_map
    Html.hasAccessibleNameChild_canonical Html.hasAccessibleNameChildren_canonical
  type: Bool text: isNonBlank
  elem: (fun tag attrs _ r => (tag == "img" && hasNonBlankAttr "alt" attrs) || hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || r)
  nil: false cons: (· || ·) map: (fun _ _ _ _ => by simp [hasNonBlankAttr_map])
  unwrap: (fun a _ _ ha => by simp [hasNonBlankAttr, attrValue_of_onlySignalBind "aria-label" a ha, attrValue_of_onlySignalBind "aria-labelledby" a ha])
  can: (fun _ _ _ _ => by simp [hasNonBlankAttr_canonical "alt" (by decide), hasNonBlankAttr_canonical "aria-label" (by decide), hasNonBlankAttr_canonical "aria-labelledby" (by decide)])

def Html.elemHasAccessibleName (attrs : List (Attr msg)) (kids : List (Html msg)) : Bool :=
  hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs ||
  hasNonBlankAttr "title" attrs || Html.hasAccessibleNameChildren kids

html_a11y_all Html.buttonsAccessible Html.buttonsAccessibleList Html.buttonsAccessible_map Html.buttonsAccessibleList_map
    Html.buttonsAccessible_canonical Html.buttonsAccessibleList_canonical Html.buttonsAccessibleList_mapList
  elem: (fun tag attrs kids r => (!(tag == "button" || tag == "a") || Html.elemHasAccessibleName attrs kids) && r)
  map: (fun _ _ _ _ => by simp [Html.elemHasAccessibleName, hasNonBlankAttr_map, Html.hasAccessibleNameChildren_map])
  unwrap: (fun _ _ _ _ => by simp)
  can: (fun _ _ cs _ => by simp [Html.elemHasAccessibleName, hasNonBlankAttr_canonical "aria-label" (by decide),
    hasNonBlankAttr_canonical "aria-labelledby" (by decide), hasNonBlankAttr_canonical "title" (by decide), Html.hasAccessibleNameChildren_canonical cs])

html_a11y_all Html.validAriaRoles Html.validAriaRolesList Html.validAriaRoles_map Html.validAriaRolesList_map
    Html.validAriaRoles_canonical Html.validAriaRolesList_canonical Html.validAriaRolesList_mapList
  elem: (fun _ attrs _ r => attrsValidAriaRoles attrs && r)
  map: (fun _ _ _ _ => by simp [attrsValidAriaRoles_map])
  unwrap: (fun a _ _ ha => by simp [attrsValidAriaRoles_of_onlySignalBind a ha])
  can: (fun _ _ _ _ => by simp)

html_fold_spec Html.containsFormControl Html.containsFormControlList Html.containsFormControl_map
    Html.containsFormControlList_map Html.containsFormControl_canonical Html.containsFormControlList_canonical
  type: Bool text: (fun _ => false) elem: (fun tag _ _ r => isFormControlTag tag || r)
  nil: false cons: (· || ·) map: (fun _ _ _ _ => rfl) unwrap: (fun _ _ _ _ => by simp [isFormControlTag]) can: (fun _ _ _ _ => rfl)

html_a11y_all Html.labelsAssociated Html.labelsAssociatedList Html.labelsAssociated_map Html.labelsAssociatedList_map
    Html.labelsAssociated_canonical Html.labelsAssociatedList_canonical Html.labelsAssociatedList_mapList
  elem: (fun tag attrs kids r => (tag != "label" || hasNonBlankAttr "for" attrs || Html.containsFormControlList kids) && r)
  map: (fun _ _ _ _ => by simp [hasNonBlankAttr_map, Html.containsFormControlList_map]) unwrap: (fun _ _ _ _ => by simp)
  can: (fun _ _ cs _ => by simp [hasNonBlankAttr_canonical "for" (by decide), Html.containsFormControlList_canonical cs])

html_fold_spec Html.collectIds Html.collectIdsList Html.collectIds_map Html.collectIdsList_map
    Html.collectIds_canonical Html.collectIdsList_canonical
  type: (List String) text: (fun _ => [])
  elem: (fun _ attrs _ r => match attrValue "id" attrs with | some v => if v.isEmpty then r else v :: r | none => r)
  nil: [] cons: (· ++ ·) map: (fun _ _ _ _ => by simp [attrValue_map])
  unwrap: (fun a _ _ ha => by simp [attrValue_of_onlySignalBind "id" a ha])
  can: (fun _ _ _ _ => by simp [attrValue_canonical "id" (by decide)])

/-- No two elements in the HTML tree share the same non-empty `id` attribute. -/
def Html.noDuplicateIds (h : Html msg) : Bool := listNoDups (Html.collectIds h)
@[simp] theorem Html.noDuplicateIds_map {α β : Type} (f : α → β) (h : Html α) : Html.noDuplicateIds (h.map f) = Html.noDuplicateIds h := by simp [Html.noDuplicateIds]
@[simp] theorem Html.noDuplicateIds_canonical {msg : Type} (h : Html msg) : Html.noDuplicateIds (Html.canonical h) = Html.noDuplicateIds h := by simp [Html.noDuplicateIds]

html_fold_spec Html.collectHeadings Html.collectHeadingsList Html.collectHeadings_map Html.collectHeadingsList_map
    Html.collectHeadings_canonical Html.collectHeadingsList_canonical
  type: (List Nat) text: (fun _ => [])
  elem: (fun tag _ _ r => match headingLevel? tag with | some lvl => lvl :: r | none => r)
  nil: [] cons: (· ++ ·) map: (fun _ _ _ _ => rfl) unwrap: (fun _ _ _ _ => by simp [headingLevel?]) can: (fun _ _ _ _ => rfl)

/-- Heading elements never skip a level (e.g. `<h1>` directly followed by `<h3>` is rejected). -/
def Html.headingsOrdered (h : Html msg) : Bool := headingLevelsOrderedFrom 0 (Html.collectHeadings h)
@[simp] theorem Html.headingsOrdered_map {α β : Type} (f : α → β) (h : Html α) : Html.headingsOrdered (h.map f) = Html.headingsOrdered h := by simp [Html.headingsOrdered]
@[simp] theorem Html.headingsOrdered_canonical {msg : Type} (h : Html msg) : Html.headingsOrdered (Html.canonical h) = Html.headingsOrdered h := by simp [Html.headingsOrdered]

html_a11y_all Html.htmlHasLang Html.htmlHasLangList Html.htmlHasLang_map Html.htmlHasLangList_map
    Html.htmlHasLang_canonical Html.htmlHasLangList_canonical Html.htmlHasLangList_mapList
  elem: (fun tag attrs _ r => (tag != "html" || hasNonBlankAttr "lang" attrs) && r)
  map: (fun _ _ _ _ => by simp [hasNonBlankAttr_map]) unwrap: (fun _ _ _ _ => by simp)
  can: (fun _ _ _ _ => by simp [hasNonBlankAttr_canonical "lang" (by decide)])

/-- Composite compile-time accessibility predicate combining image alt text, interactive
    element accessible names, WAI-ARIA role validity, label-control association, unique IDs,
    heading hierarchy order, and `<html lang=...>` presence. -/
def Html.a11yValid (h : Html msg) : Bool :=
  Html.imgsHaveAlt h && Html.buttonsAccessible h && Html.validAriaRoles h &&
  Html.labelsAssociated h && Html.noDuplicateIds h && Html.headingsOrdered h && Html.htmlHasLang h

@[simp] theorem Html.a11yValid_map {α β : Type} (f : α → β) (h : Html α) : Html.a11yValid (h.map f) = Html.a11yValid h := by simp [Html.a11yValid]
@[simp] theorem Html.a11yValid_canonical {msg : Type} (h : Html msg) : Html.a11yValid (Html.canonical h) = Html.a11yValid h := by simp [Html.a11yValid]

abbrev imgsHaveAlt {msg : Type} : Html msg → Bool := Html.imgsHaveAlt
abbrev buttonsAccessible {msg : Type} : Html msg → Bool := Html.buttonsAccessible
abbrev validAriaRoles {msg : Type} : Html msg → Bool := Html.validAriaRoles
abbrev labelsAssociated {msg : Type} : Html msg → Bool := Html.labelsAssociated
abbrev noDuplicateIds {msg : Type} : Html msg → Bool := Html.noDuplicateIds
abbrev headingsOrdered {msg : Type} : Html msg → Bool := Html.headingsOrdered
abbrev htmlHasLang {msg : Type} : Html msg → Bool := Html.htmlHasLang
abbrev a11yValid {msg : Type} : Html msg → Bool := Html.a11yValid

end Qed
