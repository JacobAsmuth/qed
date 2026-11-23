-- Avoids `String.Slice` from Lean ≥ 4.30 `trimAscii` so JS bundles stay free of `Slice` primitives.
def String.trimmed (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

namespace Qed

@[inline] def isSafeUrlChar (c : Char) : Bool := c.toNat > 0x20 && c.toNat != 0x7F

def hasSafeUrlPrefix : List Char → Bool
  | ['/'] | '#' :: _ | '?' :: _ => true
  | '/' :: c :: _ | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: c :: _
  | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: c :: _
  | 'm' :: 'a' :: 'i' :: 'l' :: 't' :: 'o' :: ':' :: c :: _ | 't' :: 'e' :: 'l' :: ':' :: c :: _ => c != '/' && c != '\\'
  | _ => false

def isSafeUrl (s : String) : Bool := let cs := s.toList; hasSafeUrlPrefix cs && cs.all isSafeUrlChar

structure Url where
  raw  : String
  safe : isSafeUrl raw = true
deriving DecidableEq, Repr

namespace Url
def root : Url := ⟨"/", rfl⟩
instance : Inhabited Url := ⟨root⟩
instance : ToString Url := ⟨Url.raw⟩
@[simp] theorem isSafe (u : Url) : isSafeUrl u.raw = true := u.safe
def parse? (s : String) : Option Url := if h : isSafeUrl s = true then some ⟨s, h⟩ else none
@[simp] theorem parse?_isSome (s : String) : (parse? s).isSome = isSafeUrl s := by unfold parse?; split <;> simp [*]
end Url

/-! ## Hex Digit Helpers -/

@[inline] def hexDigitLower (n : Nat) : Char := let d := n % 16; Char.ofNat (if d < 10 then 48 + d else 87 + d)
@[inline] def hexDigitUpper (n : Nat) : Char := let d := n % 16; Char.ofNat (if d < 10 then 48 + d else 55 + d)
@[inline] def unhexNat? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48) else if 97 ≤ n && n ≤ 102 then some (n - 87) else if 65 ≤ n && n ≤ 70 then some (n - 55) else none

theorem unhexNat?_hexDigitLower {d : Nat} (hd : d < 16) : unhexNat? (hexDigitLower d) = some d :=
  (by decide : ∀ x : Fin 16, unhexNat? (hexDigitLower x.val) = some x.val) ⟨d, hd⟩
theorem unhexNat?_hexDigitUpper {d : Nat} (hd : d < 16) : unhexNat? (hexDigitUpper d) = some d :=
  (by decide : ∀ x : Fin 16, unhexNat? (hexDigitUpper x.val) = some x.val) ⟨d, hd⟩

theorem list_takeWhile_eq_self {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = true) → xs.takeWhile p = xs
  | [], _ => rfl
  | x :: xs, h => by simp [h x List.mem_cons_self, list_takeWhile_eq_self p fun y hy => h y (List.mem_cons_of_mem _ hy)]

def containsCloseSeqLoop (afterLt : Bool) : List Char → Bool
  | [] => false | c :: cs => (afterLt && c == '/') || containsCloseSeqLoop (c == '<') cs

def containsCloseSeq (cs : List Char) : Bool := containsCloseSeqLoop false cs

def escapeCloseSeqLoop (afterLt : Bool) : List Char → List Char
  | [] => []
  | c :: cs => if afterLt && c == '/' then '\\' :: '/' :: escapeCloseSeqLoop false cs else c :: escapeCloseSeqLoop (c == '<') cs

def escapeRawText (s : String) : String :=
  if !containsCloseSeq s.toList then s else String.ofList (escapeCloseSeqLoop false s.toList)

@[specialize 2] def hasAsciiByteLoop (s : String) (p : UInt8 → Bool) (sz : Nat) (hsz : sz = s.utf8ByteSize) (i : Nat) : Bool :=
  if h : i < sz then
    if p (s.getUTF8Byte ⟨i⟩ (show i < s.utf8ByteSize from hsz ▸ h)) then true else hasAsciiByteLoop s p sz hsz (i + 1)
  else false
termination_by sz - i
decreasing_by exact Nat.sub_succ_lt_self sz i h

@[inline] def hasAsciiByte (s : String) (p : UInt8 → Bool) : Bool := hasAsciiByteLoop s p s.utf8ByteSize rfl 0

private def escapeCloseSeqBytesSpec (afterLt : Bool) : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if afterLt && b == 47 then 92 :: 47 :: escapeCloseSeqBytesSpec false bs else b :: escapeCloseSeqBytesSpec (b == 60) bs

@[inline] private def copySliceAppend (src : ByteArray) (segStart stop : Nat) (acc : ByteArray) : ByteArray :=
  src.copySlice segStart acc acc.size (stop - segStart) false

private def hasCloseSeqStrLoop (s : String) (i : Nat) (afterLt : Bool) : Bool :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if afterLt && b == 47 then true else hasCloseSeqStrLoop s (i + 1) (b == 60)
  else false
termination_by s.utf8ByteSize - i
decreasing_by exact Nat.sub_succ_lt_self s.utf8ByteSize i h

private def escapeRawBytesLoop (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray) : ByteArray :=
  if h : i < ba.size then
    let b := ba[i]
    if afterLt && b == 47 then escapeRawBytesLoop ba i (i + 1) false ((copySliceAppend ba segStart i acc).push 92)
    else escapeRawBytesLoop ba segStart (i + 1) (b == 60) acc
  else copySliceAppend ba segStart ba.size acc
termination_by ba.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self ba.size i h

/-- Appends the UTF-8 bytes of `escapeRawText s` directly into `acc` in a single pass. -/
def escapeRawTextBytesInto (acc : ByteArray) (s : String) : ByteArray := escapeRawBytesLoop s.toUTF8 0 0 false acc

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
def Html.ofOption : Option (Html msg) → Html msg | some h => h | none => .text ""
@[simp] theorem toString_string (s : String) : toString s = s := rfl

def Attr.isSignalBind : Attr msg → Bool | .signalBind _ => true | _ => false

def Attr.canonical : Attr msg → Option (Attr msg)
  | .key _ | .signalBind _ => none
  | .signalAttr _ k v      => some (.attr k v)
  | .signalOn _ e m        => some (.on e m)
  | .cls name              => some (.attr "class" name)
  | a                      => some a

private theorem fn_ite {α β : Type _} (f : α → β) (c : Prop) [Decidable c] (a b : α) :
    f (if c then a else b) = if c then f a else f b := by split <;> rfl
private theorem bool_ite_intro {α : Type _} (f : α → Bool) (v : Bool) (c : Prop) [Decidable c] (a b : α)
    (ht : c → f a = v) (hf : ¬c → f b = v) : f (if c then a else b) = v := by by_cases hc : c <;> simp [hc, ht, hf]
private theorem bool_dite_intro {α : Type _} (f : α → Bool) (v : Bool) (c : Prop) [Decidable c]
    (a : c → α) (b : ¬c → α) (ht : ∀ h, f (a h) = v) (hf : ∀ h, f (b h) = v) :
    f (dite c a b) = v := by by_cases hc : c <;> simp [hc, ht, hf]

local macro "ite_simp " nm:ident bs:bracketedBinder* " | " fn:term " : " ty:term : command =>
  `(@[simp] theorem $nm $bs* (c : Prop) [Decidable c] (a b : $ty) :
      $fn (if c then a else b) = if c then $fn a else $fn b := fn_ite $fn c a b)

ite_simp Attr.isSignalBind_ite | Attr.isSignalBind : Attr msg
ite_simp Attr.canonical_ite    | Attr.canonical    : Attr msg
@[simp] theorem Option.ite_some {α : Type _} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := (fn_ite some c a b).symm
@[simp] theorem List.filterMap_ite {α β : Type _} (f : α → Option β) (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else b).filterMap f = if c then a.filterMap f else b.filterMap f := fn_ite (List.filterMap f) c a b

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
  | .cls n => .cls n | .attr k v => .attr k v | .flag k p => .flag k p | .key k => .key k
  | .on e m => .on e (f m) | .onValue e h => .onValue e (f ∘ h)
  | .localCell k c i p b => .localCell k c i p (fun s => (b s).map f)
  | .signalBind n => .signalBind n | .signalAttr n a v => .signalAttr n a v | .signalOn n e m => .signalOn n e (f m)

mutual
  def Html.mapAttrs (f : Attr α → Attr β) : Html α → Html β
    | .text s => .text s | .element tag attrs children => .element tag (attrs.map f) (Html.mapAttrsList f children)
  def Html.mapAttrsList (f : Attr α → Attr β) : List (Html α) → List (Html β)
    | [] => [] | c :: cs => Html.mapAttrs f c :: Html.mapAttrsList f cs
end

def Html.map (f : α → β) : Html α → Html β := Html.mapAttrs (Attr.map f)
def Html.mapChildren (f : α → β) : List (Html α) → List (Html β) := Html.mapAttrsList (Attr.map f)

def Attr.prefixSignal (pfx : String) : Attr msg → Attr msg
  | .signalBind n => .signalBind (pfx ++ n) | .signalAttr n a v => .signalAttr (pfx ++ n) a v
  | .signalOn n e m => .signalOn (pfx ++ n) e m | other => other

def Html.prefixSignals (pfx : String) : Html msg → Html msg := Html.mapAttrs (Attr.prefixSignal pfx)
def Html.prefixSignalsList (pfx : String) : List (Html msg) → List (Html msg) := Html.mapAttrsList (Attr.prefixSignal pfx)

@[inline] def isKeyChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'
def asciiLowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
def asciiLower (s : String) : String := String.ofList (s.toList.map asciiLowerChar)
def hasOnPrefix : List Char → Bool | 'o' :: 'n' :: _ => true | _ => false
def isSafeRenderedKey (k : String) : Bool := !k.isEmpty && !hasOnPrefix (k.toList.map asciiLowerChar) && asciiLower k != "srcdoc"
def isSafeAttrName (k : String) : Bool := k.toList.all isKeyChar && isSafeRenderedKey k

def isUrlAttrName (k : String) : Bool :=
  let kl := asciiLower k
  kl == "href" || kl == "src" || kl == "action" || kl == "formaction" || kl == "xlink:href" ||
  kl == "poster" || kl == "data" || kl == "cite" || kl == "srcset"

def Attr.validKeyValue (k v : String) : Bool := isSafeAttrName k && (!isUrlAttrName k || isSafeUrl v)

def Attr.valid : Attr msg → Bool
  | .cls _ | .key _ | .localCell .. | .signalBind _ => true
  | .attr k v | .signalAttr _ k v                   => Attr.validKeyValue k v
  | .flag k _ | .on k _ | .onValue k _ | .signalOn _ k _ => isSafeAttrName k

def Attr.validList : List (Attr msg) → Bool | [] => true | a :: as => a.valid && Attr.validList as
def Attr.isLocalCell : Attr msg → Bool | .localCell .. => true | _ => false
def Attr.hasLocalCell : List (Attr msg) → Bool | [] => false | a :: rest => a.isLocalCell || Attr.hasLocalCell rest

local macro "attr_ctor_simp " vThm:ident lThm:ident bs:bracketedBinder* " => " ctor:term " | " vRhs:term " , " lRhs:term : command =>
  `(@[simp] theorem $vThm $bs* : ($ctor : Attr _).valid = $vRhs := rfl
    @[simp] theorem $lThm $bs* : ($ctor : Attr _).isLocalCell = $lRhs := rfl)

attr_ctor_simp Attr.valid_cls        Attr.isLocalCell_cls        {msg : Type} (n : String) => (Attr.cls n : Attr msg) | true, false
attr_ctor_simp Attr.valid_attr       Attr.isLocalCell_attr       {msg : Type} (k v : String) => (Attr.attr k v : Attr msg) | Attr.validKeyValue k v, false
attr_ctor_simp Attr.valid_flag       Attr.isLocalCell_flag       {msg : Type} (k : String) (p : Bool) => (Attr.flag k p : Attr msg) | isSafeAttrName k, false
attr_ctor_simp Attr.valid_key        Attr.isLocalCell_key        {msg : Type} (n : String) => (Attr.key n : Attr msg) | true, false
attr_ctor_simp Attr.valid_on         Attr.isLocalCell_on         {msg : Type} (e : String) (m : msg) => Attr.on e m | isSafeAttrName e, false
attr_ctor_simp Attr.valid_onValue    Attr.isLocalCell_onValue    {msg : Type} (e : String) (f : String → msg) => Attr.onValue e f | isSafeAttrName e, false
attr_ctor_simp Attr.valid_localCell  Attr.isLocalCell_localCell  {msg : Type} (k c : String) (i : Option String) (p : String) (b : String → Option msg) => Attr.localCell k c i p b | true, true
attr_ctor_simp Attr.valid_signalBind Attr.isLocalCell_signalBind {msg : Type} (n : String) => (Attr.signalBind n : Attr msg) | true, false
attr_ctor_simp Attr.valid_signalAttr Attr.isLocalCell_signalAttr {msg : Type} (n a v : String) => (Attr.signalAttr n a v : Attr msg) | Attr.validKeyValue a v, false
attr_ctor_simp Attr.valid_signalOn   Attr.isLocalCell_signalOn   {msg : Type} (n e : String) (m : msg) => Attr.signalOn n e m | isSafeAttrName e, false

def voidTags : List String := ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]
def isVoidTag (tag : String) : Bool := voidTags.contains tag

def isVoidTagFast (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 2 => tag == "br" || tag == "hr" | 3 => tag == "col" || tag == "img" || tag == "wbr"
  | 4 => tag == "area" || tag == "base" || tag == "link" || tag == "meta"
  | 5 => tag == "embed" || tag == "input" || tag == "track" | 6 => tag == "source" | _ => false

def isSafeTagName (tag : String) : Bool := let cs := tag.toList; !cs.isEmpty && cs.all (fun c => c.isAlphanum || c == '-')
def isForbiddenTag (tag : String) : Bool := tag == "script" || tag == "base" || tag == "applet" || tag == "object" || tag == "embed"
def isHeadingTag (tag : String) : Bool := tag == "h1" || tag == "h2" || tag == "h3" || tag == "h4" || tag == "h5" || tag == "h6"
def closesPTag (tag : String) : Bool :=
  tag == "address" || tag == "article" || tag == "aside" || tag == "blockquote" || tag == "details" || tag == "div" ||
  tag == "dl" || tag == "fieldset" || tag == "figcaption" || tag == "figure" || tag == "footer" || tag == "form" ||
  isHeadingTag tag || tag == "header" || tag == "hgroup" || tag == "hr" || tag == "main" || tag == "menu" ||
  tag == "nav" || tag == "ol" || tag == "p" || tag == "pre" || tag == "search" || tag == "section" || tag == "table" || tag == "ul"
def isInteractiveTag (tag : String) : Bool :=
  tag == "a" || tag == "button" || tag == "input" || tag == "select" || tag == "textarea" || tag == "details" || tag == "summary"
def isContextOnlyTag (tag : String) : Bool :=
  tag == "li" || tag == "dt" || tag == "dd" || tag == "caption" || tag == "colgroup" || tag == "col" ||
  tag == "thead" || tag == "tbody" || tag == "tfoot" || tag == "tr" || tag == "td" || tag == "th" || tag == "option" || tag == "optgroup"

inductive TagMode where
  | normal | ulOl | dl | table | colgroup | tableSection | tableRow
  | select | optgroup | option | rawStyle | textarea | svg
deriving DecidableEq, Repr

structure HtmlCtx where
  mode        : TagMode := .normal
  inP         : Bool := false
  interactive : Bool := false
  inForm      : Bool := false
deriving DecidableEq, Repr

def stepHtmlCtx (ctx : HtmlCtx) (tag : String) : Option HtmlCtx :=
  if !isSafeTagName tag || isForbiddenTag tag then none
  else match ctx.mode with
    | .svg => some (if tag == "foreignObject" then {} else { ctx with mode := .svg })
    | .option | .textarea | .rawStyle => none
    | .ulOl => if tag == "li" then some { ctx with mode := .normal, inP := false } else none
    | .dl => if tag == "dt" || tag == "dd" then some { ctx with mode := .normal, inP := false } else none
    | .table =>
        if tag == "caption" then some { ctx with mode := .normal, inP := false }
        else if tag == "colgroup" then some { ctx with mode := .colgroup, inP := false }
        else if tag == "thead" || tag == "tbody" || tag == "tfoot" then some { ctx with mode := .tableSection, inP := false } else none
    | .colgroup => if tag == "col" then some { ctx with mode := .normal } else none
    | .tableSection => if tag == "tr" then some { ctx with mode := .tableRow, inP := false } else none
    | .tableRow => if tag == "td" || tag == "th" then some { ctx with mode := .normal, inP := false } else none
    | .select => if tag == "option" then some { ctx with mode := .option } else if tag == "optgroup" then some { ctx with mode := .optgroup } else none
    | .optgroup => if tag == "option" then some { ctx with mode := .option } else none
    | .normal =>
        if isContextOnlyTag tag || (ctx.inP && closesPTag tag) ||
           (ctx.interactive && (isInteractiveTag tag || tag == "label" || tag == "form")) || (ctx.inForm && tag == "form") then none
        else if tag == "svg" then some { ctx with mode := .svg }
        else if tag == "style" then some { ctx with mode := .rawStyle }
        else if tag == "textarea" then some { ctx with mode := .textarea, interactive := true }
        else if tag == "select" then some { ctx with mode := .select, interactive := true }
        else if tag == "ul" || tag == "ol" then some { ctx with mode := .ulOl }
        else if tag == "dl" then some { ctx with mode := .dl }
        else if tag == "table" then some { ctx with mode := .table }
        else some { mode := .normal, inP := ctx.inP || tag == "p" || isHeadingTag tag,
                    interactive := ctx.interactive || tag == "a" || tag == "button" || tag == "details" || tag == "summary",
                    inForm := ctx.inForm || tag == "form" }

def validTextIn (ctx : HtmlCtx) (s : String) : Bool :=
  match ctx.mode with
  | .normal | .option | .textarea | .svg => true
  | .rawStyle => !containsCloseSeq s.toList
  | _ => s == ""

@[csimp] theorem isVoidTag_eq_fast : @isVoidTag = @isVoidTagFast := by
  funext tag; apply Bool.eq_iff_iff.2; constructor
  · intro h; have hm := List.contains_iff_mem.1 h
    simp only [voidTags, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro h; unfold isVoidTagFast at h
    split at h <;> try exact absurd h (by decide)
    all_goals
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      repeat (cases h with | inl h => _ | inr h => _)
      all_goals (subst h; decide)

mutual
  def Html.validIn (ctx : HtmlCtx) : Html msg → Bool
    | .text s => validTextIn ctx s
    | .element tag attrs children =>
        Attr.validList attrs && (!isVoidTag tag || children.isEmpty) && (!Attr.hasLocalCell attrs || children.isEmpty) &&
        match stepHtmlCtx ctx tag with | some childCtx => Html.validListIn childCtx children | none => false
  def Html.validListIn (ctx : HtmlCtx) : List (Html msg) → Bool
    | [] => true | c :: cs => Html.validIn ctx c && Html.validListIn ctx cs
end

def Html.valid (h : Html msg) : Bool := Html.validIn {} h

private theorem Attr.validList_eq_all (as : List (Attr msg)) : Attr.validList as = as.all Attr.valid := by induction as <;> simp [Attr.validList, *]
private theorem Attr.hasLocalCell_eq_any (as : List (Attr msg)) : Attr.hasLocalCell as = as.any Attr.isLocalCell := by induction as <;> simp [Attr.hasLocalCell, *]
private theorem Html.validListIn_eq_all (ctx : HtmlCtx) (cs : List (Html msg)) : Html.validListIn ctx cs = cs.all (Html.validIn ctx) := by induction cs <;> simp [Html.validListIn, *]

@[simp] theorem Attr.valid_empty : (Attr.empty : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_empty : (Attr.empty : Attr msg).isLocalCell = false := rfl

local macro "bool_list_bundle "
    nilNm:ident consNm:ident appNm:ident iteNm:ident consI:ident appI:ident iteI:ident
    bs:bracketedBinder* " | " pElem:term " , " pList:term " , " op:term " , " eqL:ident " : " ty:term " => " v:term : command =>
  `(@[simp] theorem $nilNm $bs* : $pList ([] : List $ty) = $v := rfl
    @[simp] theorem $consNm $bs* (a : $ty) (as : List $ty) : $pList (a :: as) = $op ($pElem a) ($pList as) := rfl
    @[simp] theorem $appNm $bs* (xs ys : List $ty) : $pList (xs ++ ys) = $op ($pList xs) ($pList ys) := by simp [$eqL:ident]
    ite_simp $iteNm $bs* | $pElem : $ty
    theorem $consI $bs* (a : $ty) (as : List $ty) (ha : $pElem a = $v) (has : $pList as = $v) : $pList (a :: as) = $v := by simp [ha, has]
    theorem $appI $bs* (xs ys : List $ty) (hx : $pList xs = $v) (hy : $pList ys = $v) : $pList (xs ++ ys) = $v := by simp [hx, hy]
    theorem $iteI $bs* (c : Prop) [Decidable c] (a b : $ty) (ht : c → $pElem a = $v) (hf : ¬ c → $pElem b = $v) : $pElem (if c then a else b) = $v :=
      bool_ite_intro $pElem $v c a b ht hf)

bool_list_bundle Attr.validList_nil Attr.validList_cons Attr.validList_append Attr.valid_ite Attr.validList_cons_intro Attr.validList_append_intro Attr.valid_ite_intro
  {msg : Type} | Attr.valid , Attr.validList , (· && ·) , Attr.validList_eq_all : Attr msg => true
bool_list_bundle Attr.hasLocalCell_nil Attr.hasLocalCell_cons Attr.hasLocalCell_append Attr.isLocalCell_ite Attr.hasLocalCell_cons_eq_false Attr.hasLocalCell_append_eq_false Attr.isLocalCell_ite_eq_false
  {msg : Type} | Attr.isLocalCell , Attr.hasLocalCell , (· || ·) , Attr.hasLocalCell_eq_any : Attr msg => false
bool_list_bundle Html.validListIn_nil Html.validListIn_cons Html.validListIn_append Html.validIn_ite Html.validListIn_cons_intro Html.validListIn_append_intro Html.validIn_ite_intro
  {msg : Type} (ctx : HtmlCtx) | (Html.validIn ctx) , (Html.validListIn ctx) , (· && ·) , Html.validListIn_eq_all : Html msg => true

@[simp] theorem Attr.validList_filter_nonkey (xs : List (Attr msg)) : Attr.validList (xs.filter (fun | .key _ => false | _ => true)) = Attr.validList xs := by
  induction xs with | nil => rfl | cons a _ ih => cases a <;> simp only [List.filter_cons, ↓reduceIte, Bool.false_eq_true, Attr.validList, Attr.valid, ih, Bool.true_and]
@[simp] theorem Attr.hasLocalCell_filter_nonkey (xs : List (Attr msg)) : Attr.hasLocalCell (xs.filter (fun | .key _ => false | _ => true)) = Attr.hasLocalCell xs := by
  induction xs with | nil => rfl | cons a _ ih => cases a <;> simp only [List.filter_cons, ↓reduceIte, Bool.false_eq_true, Attr.hasLocalCell, Attr.isLocalCell, ih, Bool.false_or]
@[simp] theorem Html.mapAttrsList_isEmpty {α β : Type} (f : Attr α → Attr β) (cs : List (Html α)) : (Html.mapAttrsList f cs).isEmpty = cs.isEmpty := by cases cs <;> rfl

mutual
  private theorem htmlValidIn_mapAttrs {α β : Type} (ctx : HtmlCtx) (f : Attr α → Attr β)
      (hv : ∀ a, (f a).valid = a.valid) (hl : ∀ a, (f a).isLocalCell = a.isLocalCell) :
      (h : Html α) → Html.validIn ctx (Html.mapAttrs f h) = Html.validIn ctx h
    | .text _ => rfl
    | .element tag attrs children => by
        simp only [Html.mapAttrs, Html.validIn, Attr.validList_eq_all, Attr.hasLocalCell_eq_any,
          List.all_map, List.any_map, Function.comp_def, hv, hl, Html.mapAttrsList_isEmpty]
        cases stepHtmlCtx ctx tag with
        | none => rfl | some childCtx => exact congrArg (_ && ·) (htmlValidListIn_mapAttrs childCtx f hv hl children)
  private theorem htmlValidListIn_mapAttrs {α β : Type} (ctx : HtmlCtx) (f : Attr α → Attr β)
      (hv : ∀ a, (f a).valid = a.valid) (hl : ∀ a, (f a).isLocalCell = a.isLocalCell) :
      (cs : List (Html α)) → Html.validListIn ctx (Html.mapAttrsList f cs) = Html.validListIn ctx cs
    | [] => rfl
    | c :: cs => by simp only [Html.mapAttrsList, Html.validListIn, htmlValidIn_mapAttrs ctx f hv hl c, htmlValidListIn_mapAttrs ctx f hv hl cs]
end

local macro "attr_map_simps "
    vNm:ident lNm:ident vlNm:ident hlNm:ident hVN:ident hVLN:ident
    "[" tvs:ident* "]" " (" arg:ident " : " argTy:term ") "
    " | " af:term " , " hf:term " , " hfl:term " : " srcTy:term : command =>
  `(@[simp] theorem $vNm {$tvs:ident* : Type} ($arg : $argTy) (a : Attr $srcTy) : ($af a).valid = a.valid := by cases a <;> rfl
    @[simp] theorem $lNm {$tvs:ident* : Type} ($arg : $argTy) (a : Attr $srcTy) : ($af a).isLocalCell = a.isLocalCell := by cases a <;> rfl
    @[simp] theorem $vlNm {$tvs:ident* : Type} ($arg : $argTy) (as : List (Attr $srcTy)) : Attr.validList (as.map $af) = Attr.validList as := by simp [Attr.validList_eq_all, Function.comp_def]
    @[simp] theorem $hlNm {$tvs:ident* : Type} ($arg : $argTy) (as : List (Attr $srcTy)) : Attr.hasLocalCell (as.map $af) = Attr.hasLocalCell as := by simp [Attr.hasLocalCell_eq_any, Function.comp_def]
    @[simp] theorem $hVN {$tvs:ident* : Type} (ctx : HtmlCtx) ($arg : $argTy) (h : Html $srcTy) : Html.validIn ctx ($hf h) = Html.validIn ctx h := htmlValidIn_mapAttrs ctx $af ($vNm $arg) ($lNm $arg) h
    @[simp] theorem $hVLN {$tvs:ident* : Type} (ctx : HtmlCtx) ($arg : $argTy) (cs : List (Html $srcTy)) : Html.validListIn ctx ($hfl cs) = Html.validListIn ctx cs := htmlValidListIn_mapAttrs ctx $af ($vNm $arg) ($lNm $arg) cs)

attr_map_simps Attr.valid_map Attr.isLocalCell_map Attr.validList_map_attrMap Attr.hasLocalCell_map_attrMap Html.validIn_map Html.validListIn_mapChildren
  [α β] (f : α → β) | Attr.map f , Html.map f , Html.mapChildren f : α
attr_map_simps Attr.valid_prefixSignal Attr.isLocalCell_prefixSignal Attr.validList_prefixSignal Attr.hasLocalCell_prefixSignal Html.validIn_prefixSignals Html.validListIn_prefixSignalsList
  [msg] (pfx : String) | Attr.prefixSignal pfx , Html.prefixSignals pfx , Html.prefixSignalsList pfx : msg

ite_simp Html.validListIn_ite (ctx : HtmlCtx) | Html.validListIn ctx : List (Html msg)
@[simp] theorem Html.validIn_ofOption (ctx : HtmlCtx) (o : Option (Html msg)) : Html.validIn ctx (Html.ofOption o) = match o with | some h => Html.validIn ctx h | none => validTextIn ctx "" := by cases o <;> rfl
@[simp] theorem Html.validListIn_map {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) : Html.validListIn ctx (xs.map f) = xs.all (fun a => Html.validIn ctx (f a)) := by simp [Html.validListIn_eq_all, Function.comp_def]
@[simp] theorem Html.validListIn_toList_map {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) : Html.validListIn ctx (xs.map f).toList = xs.toList.all (fun a => Html.validIn ctx (f a)) := by simp [Array.toList_map]
@[simp] theorem List.all_const_true {α : Type} (xs : List α) : xs.all (fun _ => true) = true := by induction xs <;> simp [*]

@[simp] theorem validTextIn_normal   (inP inter inForm : Bool) (s : String) : validTextIn ⟨.normal, inP, inter, inForm⟩ s = true := rfl
@[simp] theorem validTextIn_option   (inP inter inForm : Bool) (s : String) : validTextIn ⟨.option, inP, inter, inForm⟩ s = true := rfl
@[simp] theorem validTextIn_textarea (inP inter inForm : Bool) (s : String) : validTextIn ⟨.textarea, inP, inter, inForm⟩ s = true := rfl
@[simp] theorem validTextIn_svg      (inP inter inForm : Bool) (s : String) : validTextIn ⟨.svg, inP, inter, inForm⟩ s = true := rfl
@[simp] theorem validTextIn_rawStyle (inP inter inForm : Bool) (s : String) : validTextIn ⟨.rawStyle, inP, inter, inForm⟩ s = !containsCloseSeq s.toList := rfl
@[simp] theorem validTextIn_empty (ctx : HtmlCtx) : validTextIn ctx "" = true := by rcases ctx with ⟨m, _, _, _⟩; cases m <;> rfl
theorem Bool.not_false_or (a b : Bool) (ha : a = false) : (!a || b) = true := by simp [ha]

theorem containsCloseSeqLoop_escapeCloseSeqLoop (cs : List Char) : ∀ (b : Bool), containsCloseSeqLoop b (escapeCloseSeqLoop b cs) = false := by
  induction cs with | nil => intro _; rfl | cons c _ ih => intro b; simp only [escapeCloseSeqLoop]; cases h : (b && c == '/') <;> simpa [containsCloseSeqLoop, h] using ih _
@[simp] theorem containsCloseSeq_escapeRawText (s : String) : containsCloseSeq (escapeRawText s).toList = false := by
  unfold escapeRawText containsCloseSeq; by_cases h : containsCloseSeqLoop false s.toList <;> simp [h, containsCloseSeqLoop_escapeCloseSeqLoop]
theorem validTextIn_rawStyle_escape (inP inter inForm : Bool) (s : String) : validTextIn ⟨.rawStyle, inP, inter, inForm⟩ (escapeRawText s) = true := by simp [validTextIn, containsCloseSeq_escapeRawText]

theorem Html.validIn_element_intro {msg : Type} (ctx childCtx : HtmlCtx) (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))
    (hstep : stepHtmlCtx ctx tag = some childCtx) (hattrs : Attr.validList attrs = true)
    (hvoid : (!isVoidTag tag || children.isEmpty) = true) (hcell : (!Attr.hasLocalCell attrs || children.isEmpty) = true)
    (hkids : Html.validListIn childCtx children = true) : Html.validIn ctx (.element tag attrs children) = true := by simp [Html.validIn, hstep, hattrs, hvoid, hcell, hkids]
theorem Html.validIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a : c → Html msg) (b : ¬ c → Html msg)
    (ht : ∀ h : c, Html.validIn ctx (a h) = true) (hf : ∀ h : ¬ c, Html.validIn ctx (b h) = true) :
    Html.validIn ctx (if h : c then a h else b h) = true := bool_dite_intro (Html.validIn ctx) true c a b ht hf
theorem Html.validListIn_ite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : List (Html msg))
    (ht : c → Html.validListIn ctx a = true) (hf : ¬ c → Html.validListIn ctx b = true) : Html.validListIn ctx (if c then a else b) = true := bool_ite_intro (Html.validListIn ctx) true c a b ht hf
theorem Html.validListIn_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) (hf : ∀ a, Html.validIn ctx (f a) = true) : Html.validListIn ctx (xs.map f) = true := by simp [hf]
theorem Html.validListIn_toList_map_intro {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) (hf : ∀ a, Html.validIn ctx (f a) = true) : Html.validListIn ctx (xs.map f).toList = true := by simp [hf]

def onlySignalBind : List (Attr msg) → Bool | [.signalBind _] => true | .key _ :: rest => onlySignalBind rest | _ => false

def mkCanonicalElem (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) : Html msg :=
  if tag == "span" && onlySignalBind attrs then match cs with | [c] => c | _ => .element tag (attrs.filterMap Attr.canonical) cs
  else .element tag (attrs.filterMap Attr.canonical) cs

mutual
  def Html.canonical : Html msg → Html msg | .text s => .text s | .element tag attrs cs => mkCanonicalElem tag attrs (Html.canonicalList cs)
  def Html.canonicalList : List (Html msg) → List (Html msg) | [] => [] | c :: cs => Html.canonical c :: Html.canonicalList cs
end

@[simp] theorem onlySignalBind_signalBind (sig : String) : onlySignalBind ([.signalBind sig] : List (Attr msg)) = true := rfl
@[simp] theorem onlySignalBind_key (k : String) (rest : List (Attr msg)) : onlySignalBind (.key k :: rest) = onlySignalBind rest := rfl
@[simp] theorem mkCanonicalElem_signalBind (sig : String) (c : Html msg) : mkCanonicalElem "span" [.signalBind sig] [c] = c := rfl
@[simp] theorem mkCanonicalElem_not_signal (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg))
    (h : (tag == "span" && onlySignalBind attrs) = false) : mkCanonicalElem tag attrs cs = .element tag (attrs.filterMap Attr.canonical) cs := by simp [mkCanonicalElem, h]
@[simp] theorem Html.canonical_text (s : String) : Html.canonical (.text s : Html msg) = .text s := rfl
@[simp] theorem Html.canonical_element (tag : String) (attrs : List (Attr msg)) (cs : List (Html msg)) :
    Html.canonical (.element tag attrs cs) = mkCanonicalElem tag attrs (Html.canonicalList cs) := rfl
ite_simp Html.canonical_ite | Html.canonical : Html msg
@[simp] theorem Html.canonical_ofOption (o : Option (Html msg)) :
    Html.canonical (Html.ofOption o) = match o with | some h => Html.canonical h | none => .text "" := by cases o <;> rfl
@[simp] theorem Html.canonicalList_nil : Html.canonicalList ([] : List (Html msg)) = [] := rfl
@[simp] theorem Html.canonicalList_cons (c : Html msg) (cs : List (Html msg)) : Html.canonicalList (c :: cs) = Html.canonical c :: Html.canonicalList cs := rfl
theorem Html.canonicalList_eq_map (cs : List (Html msg)) : Html.canonicalList cs = cs.map Html.canonical := by induction cs <;> simp [*]
@[simp] theorem Html.canonicalList_append (xs ys : List (Html msg)) : Html.canonicalList (xs ++ ys) = Html.canonicalList xs ++ Html.canonicalList ys := by simp [Html.canonicalList_eq_map]
@[simp] theorem Html.canonicalList_map {α : Type _} (xs : List α) (f : α → Html msg) :
    Html.canonicalList (xs.map f) = xs.map (fun x => Html.canonical (f x)) := by simp [Html.canonicalList_eq_map, Function.comp_def]

/-! ## Fast-Path `@[csimp]` Equivalences & ASCII Byte Helpers -/

private theorem string_toByteArray_data (s : String) : s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [show s.toByteArray = s.toList.utf8Encode by rw [← String.toByteArray_ofList, String.ofList_toList], List.utf8Encode, List.data_toByteArray, List.toList_toArray]
private theorem string_bytes_len (s : String) : s.toByteArray.data.toList.length = s.utf8ByteSize := Array.length_toList.trans String.size_toByteArray

private theorem utf8EncodeChar_le_127 (c : Char) (hc : c.toNat ≤ 127) : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar; simp only [show c.val.toNat ≤ 127 from hc, ↓reduceIte]; rfl

private theorem uint8_ofNat_mod_add_ge_128 {x m base : Nat} (hm : 0 < m) (hb : 128 ≤ base) (hlt : m + base ≤ 256) :
    (UInt8.ofNat (x % m + base)).toNat ≥ 128 := by
  change (x % m + base) % 256 ≥ 128; have := Nat.mod_lt x hm; rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem utf8EncodeChar_gt_127 (c : Char) (h : c.toNat > 127) : ∀ b ∈ String.utf8EncodeChar c, b.toNat ≥ 128 := by
  unfold String.utf8EncodeChar; simp only [show ¬(c.val.toNat ≤ 127) from Nat.not_le_of_gt h, ↓reduceIte]
  split <;> try split
  all_goals (intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; repeat (rcases hb with rfl | hb; · apply uint8_ofNat_mod_add_ge_128 <;> decide); try (subst hb; apply uint8_ofNat_mod_add_ge_128 <;> decide))

private theorem utf8EncodeChar_ne_nil (c : Char) : String.utf8EncodeChar c ≠ [] := by unfold String.utf8EncodeChar; dsimp only; repeat (split <;> try simp)

private theorem hasAsciiByteLoop_eq (s : String) (p : UInt8 → Bool) (i : Nat) :
    hasAsciiByteLoop s p s.utf8ByteSize rfl i = (s.toByteArray.data.toList.drop i).any p := by
  fun_induction hasAsciiByteLoop s p s.utf8ByteSize rfl i with
  | case1 i h hp => rw [List.drop_eq_getElem_cons (string_bytes_len s ▸ h), List.any_cons, show s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h from rfl, hp]; rfl
  | case2 i h hp ih => rw [List.drop_eq_getElem_cons (string_bytes_len s ▸ h), List.any_cons, show s.toByteArray.data.toList[i] = s.getUTF8Byte ⟨i⟩ h from rfl, Bool.eq_false_iff.2 hp, Bool.false_or, ih]
  | case3 i h => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt (string_bytes_len s ▸ h))]; rfl

theorem hasAsciiByte_eq_any (s : String) (p : UInt8 → Bool) (q : Char → Bool)
    (hhi : ∀ b : UInt8, b.toNat ≥ 128 → p b = false) (hlo : ∀ c : Char, c.toNat ≤ 127 → p (UInt8.ofNat c.toNat) = q c)
    (hqhi : ∀ c : Char, c.toNat > 127 → q c = false) : hasAsciiByte s p = s.toList.any q := by
  rw [show hasAsciiByte s p = s.toByteArray.data.toList.any p by simpa [hasAsciiByte] using hasAsciiByteLoop_eq s p 0, string_toByteArray_data, List.any_flatMap]
  congr 1; funext c
  by_cases hc : c.toNat ≤ 127
  · rw [utf8EncodeChar_le_127 c hc, List.any_cons, List.any_nil, Bool.or_false]; exact hlo c hc
  · have hgt : c.toNat > 127 := by omega
    rw [hqhi c hgt, List.any_eq_false]; exact fun b hb => by simp [hhi b (utf8EncodeChar_gt_127 c hgt b hb)]

theorem asciiByte_beq_char (c : Char) (hc : c.toNat ≤ 127) (target : Char) (ht : target.toNat ≤ 127) :
    (UInt8.ofNat c.toNat == UInt8.ofNat target.toNat) = (c == target) := by
  by_cases h : c = target
  · subst h; simp
  · rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne]; intro heq; apply h
    have : c.toNat % 256 = target.toNat % 256 := congrArg UInt8.toNat heq
    have hnat : c.toNat = target.toNat := by omega
    exact Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat))

private theorem escapeCloseSeqBytes_hi (xs ys : List UInt8) (hhi : ∀ b ∈ xs, b.toNat ≥ 128) (hne : xs ≠ []) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (xs ++ ys) = xs ++ escapeCloseSeqBytesSpec false ys := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
      intro afterLt; have hb := hhi b List.mem_cons_self
      have hneB (t : UInt8) (ht : t.toNat < 128) : (b == t) = false := beq_eq_false_iff_ne.2 fun h => by subst h; omega
      simp only [List.cons_append, escapeCloseSeqBytesSpec, hneB 47 (by decide), hneB 60 (by decide), Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      cases bs with | nil => rfl | cons _ _ => rw [ih (fun x hx => hhi x (List.mem_cons_of_mem _ hx)) (List.cons_ne_nil _ _) false]

private theorem escapeCloseSeqBytes_flatMap (cs : List Char) :
    ∀ afterLt, escapeCloseSeqBytesSpec afterLt (cs.flatMap String.utf8EncodeChar) = (escapeCloseSeqLoop afterLt cs).flatMap String.utf8EncodeChar := by
  induction cs with
  | nil => intro _; rfl
  | cons c _ ih =>
      intro afterLt; simp only [List.flatMap_cons, escapeCloseSeqLoop]
      by_cases hc : c.toNat ≤ 127
      · have h1 := utf8EncodeChar_le_127 c hc
        have h47 : (UInt8.ofNat c.toNat == 47) = (c == '/') := asciiByte_beq_char c hc '/' (by decide)
        have h60 : (UInt8.ofNat c.toNat == 60) = (c == '<') := asciiByte_beq_char c hc '<' (by decide)
        rw [h1, List.singleton_append, escapeCloseSeqBytesSpec, h47, h60]; split <;> simp [List.flatMap_cons, h1, ih] <;> rfl
      · have hgt : c.toNat > 127 := by omega
        have hneC (t : Char) (ht : t.toNat ≤ 127) : (c == t) = false := beq_eq_false_iff_ne.2 fun h => by subst h; omega
        rw [escapeCloseSeqBytes_hi _ _ (utf8EncodeChar_gt_127 c hgt) (utf8EncodeChar_ne_nil c) afterLt]
        simp [hneC '/' (by decide), hneC '<' (by decide), List.flatMap_cons, ih]

private theorem escapeCloseSeqLoop_noop : ∀ (cs : List Char) (afterLt : Bool), containsCloseSeqLoop afterLt cs = false → escapeCloseSeqLoop afterLt cs = cs
  | [], _, _ => rfl
  | c :: cs, afterLt, h => by simp only [containsCloseSeqLoop, Bool.or_eq_false_iff] at h; simp only [escapeCloseSeqLoop, h.1, Bool.false_eq_true, ↓reduceIte, escapeCloseSeqLoop_noop cs (c == '<') h.2]

private theorem escapeCloseSeq_utf8 (s : String) :
    (String.ofList (escapeCloseSeqLoop false s.toList)).toByteArray.data.toList = escapeCloseSeqBytesSpec false s.toByteArray.data.toList := by
  rw [String.toByteArray_ofList, List.utf8Encode, List.data_toByteArray, List.toList_toArray, ← escapeCloseSeqBytes_flatMap, ← string_toByteArray_data]

private theorem copySliceAppend_data (src : ByteArray) (segStart stop : Nat) (acc : ByteArray) (hle : segStart ≤ stop) :
    (copySliceAppend src segStart stop acc).data.toList = acc.data.toList ++ (src.data.toList.drop segStart).take (stop - segStart) := by
  unfold copySliceAppend ByteArray.copySlice; simp only [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  have hlen : acc.size = acc.data.toList.length := Array.length_toList.symm
  have h2 : acc.data.toList.drop (acc.size + min (stop - segStart) (src.data.size - segStart)) = [] := List.drop_eq_nil_of_le (by rw [← hlen]; omega)
  rw [List.drop_zero, Nat.sub_zero, hlen, List.take_length, show segStart + (stop - segStart) - segStart = stop - segStart by omega, ← hlen, h2, List.take_nil, List.append_nil]

private theorem hasCloseSeqStrLoop_false_eq (s : String) (i : Nat) (afterLt : Bool) (hfalse : hasCloseSeqStrLoop s i afterLt = false) :
    escapeCloseSeqBytesSpec afterLt (s.toByteArray.data.toList.drop i) = s.toByteArray.data.toList.drop i := by
  fun_induction hasCloseSeqStrLoop s i afterLt with
  | case1 => cases hfalse
  | case2 i afterLt hi b hmiss ih => rw [List.drop_eq_getElem_cons (string_bytes_len s ▸ hi), escapeCloseSeqBytesSpec, show s.toByteArray.data.toList[i] = b from rfl, if_neg hmiss, ih hfalse]
  | case3 i afterLt hge => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt (string_bytes_len s ▸ hge))]; rfl

private theorem escapeRawBytesLoop_data (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray) (hle : segStart ≤ i) (hi : i ≤ ba.size) :
    (escapeRawBytesLoop ba segStart i afterLt acc).data.toList =
      acc.data.toList ++ (ba.data.toList.drop segStart).take (i - segStart) ++ escapeCloseSeqBytesSpec afterLt (ba.data.toList.drop i) := by
  fun_induction escapeRawBytesLoop ba segStart i afterLt acc with
  | case1 segStart i afterLt acc hlt b hhit ih =>
      have h47 : b = 47 := beq_iff_eq.1 ((Bool.and_eq_true _ _).mp hhit).2
      rw [ih (by omega) (by omega), ByteArray.push, Array.toList_push, copySliceAppend_data ba segStart i acc hle,
          List.drop_eq_getElem_cons (i := i) (Array.length_toList.symm ▸ hlt), show ba.data.toList[i] = b from rfl,
          escapeCloseSeqBytesSpec, if_pos hhit, show (b :: ba.data.toList.drop (i + 1)).take (i + 1 - i) = [47] by rw [show i + 1 - i = 1 by omega, h47]; rfl]; simp [List.append_assoc]
  | case2 segStart i afterLt acc hlt b hmiss ih =>
      rw [ih (by omega) (by omega), List.drop_eq_getElem_cons (i := i) (Array.length_toList.symm ▸ hlt), show ba.data.toList[i] = b from rfl, escapeCloseSeqBytesSpec, if_neg hmiss]
      have hlen : i - segStart < (ba.data.toList.drop segStart).length := by rw [List.length_drop, Array.length_toList]; exact Nat.sub_lt_sub_right hle hlt
      rw [show i + 1 - segStart = (i - segStart) + 1 by omega, List.take_succ_eq_append_getElem hlen]; simp [List.getElem_drop, show segStart + (i - segStart) = i by omega, List.append_assoc]; rfl
  | case3 segStart i afterLt acc hge =>
      obtain rfl : i = ba.size := by omega
      rw [copySliceAppend_data ba segStart ba.size acc hle, List.drop_eq_nil_of_le (i := ba.size) (Array.length_toList.symm ▸ Nat.le_refl _)]; simp [escapeCloseSeqBytesSpec]

private theorem escapeRawBytes_eq_spec (s : String) :
    escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)) = (String.ofList (escapeCloseSeqLoop false s.toList)).toByteArray := by
  apply ByteArray.ext; apply Array.ext'; unfold String.toUTF8
  rw [escapeRawBytesLoop_data s.toByteArray 0 0 false _ (Nat.le_refl _) (Nat.zero_le _), show (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)).data.toList = [] from rfl, escapeCloseSeq_utf8]; simp

private def escapeRawTextFast (s : String) : String :=
  if !hasCloseSeqStrLoop s 0 false then s
  else String.fromUTF8 (escapeRawBytesLoop s.toUTF8 0 0 false (ByteArray.emptyWithCapacity (s.utf8ByteSize + 8)))
    (by rw [escapeRawBytes_eq_spec]; exact (String.ofList (escapeCloseSeqLoop false s.toList)).isValidUTF8)

@[csimp] theorem escapeRawText_eq_fast : @escapeRawText = @escapeRawTextFast := by
  funext s
  have halways : escapeRawText s = String.ofList (escapeCloseSeqLoop false s.toList) := by
    unfold escapeRawText containsCloseSeq; cases h : containsCloseSeqLoop false s.toList <;> simp [escapeCloseSeqLoop_noop s.toList false, *]
  rw [halways]; unfold escapeRawTextFast
  cases h : hasCloseSeqStrLoop s 0 false
  · simp only [Bool.not_false, ↓reduceIte]; apply String.toByteArray_inj.1; apply ByteArray.ext; apply Array.ext'
    rw [escapeCloseSeq_utf8]; simpa only [List.drop_zero] using hasCloseSeqStrLoop_false_eq s 0 false h
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact String.toByteArray_inj.1 (escapeRawBytes_eq_spec s).symm

/-! ## Compile-Time Accessibility (A11y) Predicates & `Html.map` / `Html.canonical` Invariance -/

def attrValue (key : String) : List (Attr msg) → Option String
  | [] => none | .attr k v :: r | .signalAttr _ k v :: r => if k == key then some v else attrValue key r | _ :: r => attrValue key r

def hasAttr (key : String) (as : List (Attr msg)) : Bool := (attrValue key as).isSome
def isNonBlank (s : String) : Bool := s.toList.any (!·.isWhitespace)
def hasNonBlankAttr (key : String) (as : List (Attr msg)) : Bool := match attrValue key as with | some v => isNonBlank v | none => false

@[simp] theorem attrValue_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) :
    attrValue key (as.map (Attr.map f)) = attrValue key as := by
  induction as with | nil => rfl | cons a _ ih => cases a with | attr k _ | signalAttr _ k _ => by_cases hk : (k == key) <;> simp [Attr.map, attrValue, hk, ih] | _ => simp [Attr.map, attrValue, ih]
@[simp] theorem hasAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) : hasAttr key (as.map (Attr.map f)) = hasAttr key as := by simp [hasAttr]
@[simp] theorem hasNonBlankAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) : hasNonBlankAttr key (as.map (Attr.map f)) = hasNonBlankAttr key as := by simp [hasNonBlankAttr]

theorem attrValue_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) :
    attrValue key (as.filterMap Attr.canonical) = attrValue key as := by
  have hcls : ("class" == key) = false := beq_false_of_ne (Ne.symm hk)
  induction as with
  | nil => rfl
  | cons a _ ih => cases a with | cls _ => simp [Attr.canonical, attrValue, hcls, ih] | attr k _ | signalAttr _ k _ => by_cases heq : (k == key) <;> simp [Attr.canonical, attrValue, heq, ih] | _ => simp [Attr.canonical, attrValue, ih]
theorem hasAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) : hasAttr key (as.filterMap Attr.canonical) = hasAttr key as := by simp [hasAttr, attrValue_canonical key hk]
theorem hasNonBlankAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) : hasNonBlankAttr key (as.filterMap Attr.canonical) = hasNonBlankAttr key as := by simp [hasNonBlankAttr, attrValue_canonical key hk]

theorem attrValue_of_onlySignalBind {msg : Type} (key : String) : ∀ as : List (Attr msg), onlySignalBind as = true → attrValue key as = none
  | [.signalBind _], _ => rfl | .key _ :: rest, h => attrValue_of_onlySignalBind key rest h

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
  | [] => true | .attr k v :: r | .signalAttr _ k v :: r => (k != "role" || isValidAriaRole v) && attrsValidAriaRoles r | _ :: r => attrsValidAriaRoles r

@[simp] theorem attrsValidAriaRoles_map {α β : Type} (f : α → β) (as : List (Attr α)) : attrsValidAriaRoles (as.map (Attr.map f)) = attrsValidAriaRoles as := by
  induction as with | nil => rfl | cons a _ ih => cases a <;> simp [Attr.map, attrsValidAriaRoles, ih]
@[simp] theorem attrsValidAriaRoles_canonical {msg : Type} (as : List (Attr msg)) : attrsValidAriaRoles (as.filterMap Attr.canonical) = attrsValidAriaRoles as := by
  induction as with | nil => rfl | cons a _ ih => cases a <;> simp [Attr.canonical, attrsValidAriaRoles, ih]
private theorem attrsValidAriaRoles_of_onlySignalBind {msg : Type} : ∀ as : List (Attr msg), onlySignalBind as = true → attrsValidAriaRoles as = true
  | [.signalBind _], _ => rfl | .key _ :: rest, h => attrsValidAriaRoles_of_onlySignalBind rest h

def isFormControlTag (tag : String) : Bool := tag == "input" || tag == "select" || tag == "textarea"
def headingLevel? : String → Option Nat | "h1" => some 1 | "h2" => some 2 | "h3" => some 3 | "h4" => some 4 | "h5" => some 5 | "h6" => some 6 | _ => none
def listNoDups : List String → Bool | [] => true | x :: xs => !xs.contains x && listNoDups xs
def headingLevelsOrderedFrom (prev : Nat) : List Nat → Bool | [] => true | lvl :: rest => (prev == 0 || lvl ≤ prev + 1) && headingLevelsOrderedFrom lvl rest

/-! ### Unified `Html.fold` Paramorphism & Accessibility Predicates -/

section
variable {msg γ : Type} (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
mutual
  def Html.fold : Html msg → γ | .text s => onText s | .element tag attrs kids => onElem tag attrs kids (Html.foldList kids)
  def Html.foldList : List (Html msg) → γ | [] => nil | c :: cs => cons (Html.fold c) (Html.foldList cs)
end
end

private theorem mkCanonicalElem_cases {msg : Type} (t : String) (a : List (Attr msg)) (cs : List (Html msg)) :
    (t = "span" ∧ onlySignalBind a = true ∧ ∃ c₀, cs = [c₀] ∧ mkCanonicalElem t a (Html.canonicalList cs) = c₀.canonical) ∨
    mkCanonicalElem t a (Html.canonicalList cs) = .element t (a.filterMap Attr.canonical) (Html.canonicalList cs) := by
  unfold mkCanonicalElem; split
  · next h =>
    have ⟨ht, ha⟩ := Bool.and_eq_true_iff.1 h
    cases cs with
    | cons c₀ rest => cases rest with | nil => exact .inl ⟨beq_iff_eq.1 ht, ha, c₀, rfl, rfl⟩ | cons _ _ => exact .inr rfl
    | nil => exact .inr rfl
  · exact .inr rfl

mutual
  theorem Html.fold_map {α β γ : Type} (f : α → β) (onText : String → γ)
      (onElemα : String → List (Attr α) → List (Html α) → γ → γ) (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) :
      (h : Html α) → Html.fold onText onElemβ nil cons (h.map f) = Html.fold onText onElemα nil cons h
    | .text _ => rfl
    | .element t a cs => by change onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) (Html.foldList _ _ _ _ (Html.mapChildren f cs)) = _; rw [Html.foldList_map f onText onElemα onElemβ nil cons hElem cs, hElem]; rfl
  theorem Html.foldList_map {α β γ : Type} (f : α → β) (onText : String → γ)
      (onElemα : String → List (Attr α) → List (Html α) → γ → γ) (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) :
      (cs : List (Html α)) → Html.foldList onText onElemβ nil cons (Html.mapChildren f cs) = Html.foldList onText onElemα nil cons cs
    | [] => rfl
    | c :: cs => by change cons (Html.fold _ _ _ _ (c.map f)) (Html.foldList _ _ _ _ (Html.mapChildren f cs)) = _; rw [Html.fold_map f onText onElemα onElemβ nil cons hElem c, Html.foldList_map f onText onElemα onElemβ nil cons hElem cs]; rfl
end

mutual
  theorem Html.fold_canonical {msg γ : Type} (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
      (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) :
      (h : Html msg) → Html.fold onText onElem nil cons h.canonical = Html.fold onText onElem nil cons h
    | .text _ => rfl
    | .element t a cs => by
        change Html.fold onText onElem nil cons (mkCanonicalElem t a (Html.canonicalList cs)) = _
        rcases mkCanonicalElem_cases t a cs with ⟨rfl, ha, c₀, rfl, heq⟩ | heq
        · rw [heq, Html.fold, Html.foldList, Html.foldList, hUnwrap a c₀ _ ha]; exact Html.fold_canonical onText onElem nil cons hUnwrap hElem c₀
        · rw [heq, Html.fold, Html.fold, Html.foldList_canonical onText onElem nil cons hUnwrap hElem cs, hElem]
  theorem Html.foldList_canonical {msg γ : Type} (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
      (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) :
      (cs : List (Html msg)) → Html.foldList onText onElem nil cons (Html.canonicalList cs) = Html.foldList onText onElem nil cons cs
    | [] => rfl
    | c :: cs => by simp only [Html.canonicalList, Html.foldList, Html.fold_canonical onText onElem nil cons hUnwrap hElem c, Html.foldList_canonical onText onElem nil cons hUnwrap hElem cs]
end

mutual
  theorem Html.fold_eq_node {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ)
      (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks)) (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) :
      (h : Html msg) → F h = Html.fold onText onElem nil cons h
    | .text s => hT s | .element _ _ ks => by rw [hE, Html.fold, Html.fold_eq_list F FL onText onElem nil cons hT hE hN hC ks]
  theorem Html.fold_eq_list {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ)
      (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
      (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks)) (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) :
      (cs : List (Html msg)) → FL cs = Html.foldList onText onElem nil cons cs
    | [] => hN | c :: cs => by rw [hC, Html.foldList, Html.fold_eq_node F FL onText onElem nil cons hT hE hN hC c, Html.fold_eq_list F FL onText onElem nil cons hT hE hN hC cs]
end

theorem Html.foldList_all_mapList {α : Type _} {msg : Type} (onText : String → Bool)
    (onElem : String → List (Attr msg) → List (Html msg) → Bool → Bool) (g : α → Html msg) (l : List α) :
    Html.foldList onText onElem true (· && ·) (l.map g) = true ↔ ∀ x ∈ l, Html.fold onText onElem true (· && ·) (g x) = true := by
  induction l with | nil => simp only [List.map_nil, Html.foldList, List.not_mem_nil, false_implies, implies_true] | cons _ _ ih => simp only [List.map_cons, Html.foldList, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]

local macro "html_fold_spec" fn:ident fl:ident
    "type:" ty:term "text:" tFn:term "elem:" eFn:term "nil:" nVal:term "cons:" cFn:term
    "map:" mapPf:term "unwrap:" unwPf:term "can:" canPf:term : command => do
  let suf (id : Lean.Ident) (s : String) := Lean.mkIdentFrom id (id.getId.appendAfter s)
  let eqN := suf fn "_eq_fold"; let eqL := suf fl "_eq_fold"
  `(mutual
      def $fn {msg : Type} : Html msg → $ty | .text s => $tFn s | .element tag attrs kids => $eFn tag attrs kids ($fl kids)
      def $fl {msg : Type} : List (Html msg) → $ty | [] => $nVal | c :: cs => $cFn ($fn c) ($fl cs)
    end
    private theorem $eqN {msg : Type} (h : Html msg) : $fn h = Html.fold $tFn $eFn $nVal $cFn h :=
      Html.fold_eq_node $fn $fl $tFn $eFn $nVal $cFn (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) h
    private theorem $eqL {msg : Type} (cs : List (Html msg)) : $fl cs = Html.foldList $tFn $eFn $nVal $cFn cs :=
      Html.fold_eq_list $fn $fl $tFn $eFn $nVal $cFn (fun _ => rfl) (fun _ _ _ => rfl) rfl (fun _ _ => rfl) cs
    @[simp] theorem $(suf fn "_map") {α β : Type} (f : α → β) (h : Html α) : $fn (h.map f) = $fn h := by
      rw [$eqN:ident, $eqN:ident]; exact Html.fold_map f $tFn $eFn $eFn $nVal $cFn $mapPf h
    @[simp] theorem $(suf fl "_map") {α β : Type} (f : α → β) (cs : List (Html α)) : $fl (Html.mapChildren f cs) = $fl cs := by
      rw [$eqL:ident, $eqL:ident]; exact Html.foldList_map f $tFn $eFn $eFn $nVal $cFn $mapPf cs
    @[simp] theorem $(suf fn "_canonical") {msg : Type} (h : Html msg) : $fn (Html.canonical h) = $fn h := by
      rw [$eqN:ident, $eqN:ident]; exact Html.fold_canonical $tFn $eFn $nVal $cFn $unwPf $canPf h
    @[simp] theorem $(suf fl "_canonical") {msg : Type} (cs : List (Html msg)) : $fl (Html.canonicalList cs) = $fl cs := by
      rw [$eqL:ident, $eqL:ident]; exact Html.foldList_canonical $tFn $eFn $nVal $cFn $unwPf $canPf cs)

local syntax "html_a11y_all" ident ident "elem:" term "map:" term ("unwrap:" term)? "can:" term : command
local macro_rules
  | `(html_a11y_all $fn $fl elem: $eFn map: $mapPf $[unwrap: $unwPf?]? can: $canPf) => do
      let suf (id : Lean.Ident) (s : String) := Lean.mkIdentFrom id (id.getId.appendAfter s)
      let eqN := suf fn "_eq_fold"; let eqL := suf fl "_eq_fold"
      let unwPf ← match unwPf? with | some u => pure u | none => `(fun _ _ r _ => by cases r <;> rfl)
      `(html_fold_spec $fn $fl type: Bool text: (fun _ => true) elem: $eFn nil: true cons: (· && ·) map: $mapPf unwrap: $unwPf can: $canPf
        theorem $(suf fl "_mapList") {α msg : Type} (g : α → Html msg) (l : List α) : $fl (l.map g) = true ↔ ∀ x ∈ l, $fn (g x) = true := by
          rw [$eqL:ident]; simpa only [$eqN:ident] using Html.foldList_all_mapList (fun _ => true) $eFn g l)

html_a11y_all Html.imgsHaveAlt Html.imgsHaveAltList
  elem: (fun tag attrs _ r => (tag != "img" || hasAttr "alt" attrs) && r)
  map: (fun _ _ _ _ => by simp only [hasAttr_map]) can: (fun _ _ _ _ => by simp only [hasAttr_canonical "alt" (by decide)])

html_fold_spec Html.hasAccessibleNameChild Html.hasAccessibleNameChildren
  type: Bool text: isNonBlank
  elem: (fun tag attrs _ r => (tag == "img" && hasNonBlankAttr "alt" attrs) || hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || r)
  nil: false cons: (· || ·) map: (fun _ _ _ _ => by simp only [hasNonBlankAttr_map])
  unwrap: (fun a _ r ha => by simp only [hasNonBlankAttr, attrValue_of_onlySignalBind "aria-label" a ha, attrValue_of_onlySignalBind "aria-labelledby" a ha]; cases r <;> rfl)
  can: (fun _ _ _ _ => by simp only [hasNonBlankAttr_canonical "alt" (by decide), hasNonBlankAttr_canonical "aria-label" (by decide), hasNonBlankAttr_canonical "aria-labelledby" (by decide)])

def Html.elemHasAccessibleName (attrs : List (Attr msg)) (kids : List (Html msg)) : Bool :=
  hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || hasNonBlankAttr "title" attrs || Html.hasAccessibleNameChildren kids

html_a11y_all Html.buttonsAccessible Html.buttonsAccessibleList
  elem: (fun tag attrs kids r => (!(tag == "button" || tag == "a") || Html.elemHasAccessibleName attrs kids) && r)
  map: (fun _ _ _ _ => by simp only [Html.elemHasAccessibleName, hasNonBlankAttr_map, Html.hasAccessibleNameChildren_map])
  can: (fun _ _ cs _ => by simp only [Html.elemHasAccessibleName, hasNonBlankAttr_canonical "aria-label" (by decide),
    hasNonBlankAttr_canonical "aria-labelledby" (by decide), hasNonBlankAttr_canonical "title" (by decide), Html.hasAccessibleNameChildren_canonical cs])

html_a11y_all Html.validAriaRoles Html.validAriaRolesList
  elem: (fun _ attrs _ r => attrsValidAriaRoles attrs && r)
  map: (fun _ _ _ _ => by simp only [attrsValidAriaRoles_map])
  unwrap: (fun a _ _ ha => by simp only [attrsValidAriaRoles_of_onlySignalBind a ha, Bool.true_and, Bool.and_true])
  can: (fun _ _ _ _ => by simp only [attrsValidAriaRoles_canonical])

html_fold_spec Html.containsFormControl Html.containsFormControlList
  type: Bool text: (fun _ => false) elem: (fun tag _ _ r => isFormControlTag tag || r)
  nil: false cons: (· || ·) map: (fun _ _ _ _ => rfl) unwrap: (fun _ _ r _ => by cases r <;> rfl) can: (fun _ _ _ _ => rfl)

html_a11y_all Html.labelsAssociated Html.labelsAssociatedList
  elem: (fun tag attrs kids r => (tag != "label" || hasNonBlankAttr "for" attrs || Html.containsFormControlList kids) && r)
  map: (fun _ _ _ _ => by simp only [hasNonBlankAttr_map, Html.containsFormControlList_map])
  can: (fun _ _ cs _ => by simp only [hasNonBlankAttr_canonical "for" (by decide), Html.containsFormControlList_canonical cs])

html_fold_spec Html.collectIds Html.collectIdsList
  type: (List String) text: (fun _ => [])
  elem: (fun _ attrs _ r => match attrValue "id" attrs with | some v => if v.isEmpty then r else v :: r | none => r)
  nil: [] cons: (· ++ ·) map: (fun _ _ _ _ => by simp only [attrValue_map])
  unwrap: (fun a _ _ ha => by simp only [attrValue_of_onlySignalBind "id" a ha, List.append_nil])
  can: (fun _ _ _ _ => by simp only [attrValue_canonical "id" (by decide)])

html_fold_spec Html.collectHeadings Html.collectHeadingsList
  type: (List Nat) text: (fun _ => []) elem: (fun tag _ _ r => match headingLevel? tag with | some lvl => lvl :: r | none => r)
  nil: [] cons: (· ++ ·) map: (fun _ _ _ _ => rfl) unwrap: (fun _ _ _ _ => List.append_nil _) can: (fun _ _ _ _ => rfl)

html_a11y_all Html.htmlHasLang Html.htmlHasLangList
  elem: (fun tag attrs _ r => (tag != "html" || hasNonBlankAttr "lang" attrs) && r)
  map: (fun _ _ _ _ => by simp only [hasNonBlankAttr_map]) can: (fun _ _ _ _ => by simp only [hasNonBlankAttr_canonical "lang" (by decide)])

def Html.noDuplicateIds (h : Html msg) : Bool := listNoDups (Html.collectIds h)
def Html.headingsOrdered (h : Html msg) : Bool := headingLevelsOrderedFrom 0 (Html.collectHeadings h)
def Html.a11yValid (h : Html msg) : Bool :=
  Html.imgsHaveAlt h && Html.buttonsAccessible h && Html.validAriaRoles h &&
  Html.labelsAssociated h && Html.noDuplicateIds h && Html.headingsOrdered h && Html.htmlHasLang h

local macro "html_a11y_derived " nm:ident : command => do
  let suf (s : String) := Lean.mkIdentFrom nm (nm.getId.appendAfter s)
  `(@[simp] theorem $(suf "_map") {α β : Type} (f : α → β) (h : Html α) : $nm (h.map f) = $nm h := by simp [$nm:ident]
    @[simp] theorem $(suf "_canonical") {msg : Type} (h : Html msg) : $nm (Html.canonical h) = $nm h := by simp [$nm:ident])

html_a11y_derived Html.noDuplicateIds
html_a11y_derived Html.headingsOrdered
html_a11y_derived Html.a11yValid

local macro "html_abbrevs " nms:ident* : command => do
  let cmds ← nms.mapM fun nm => do
    let nmId : Lean.Ident := ⟨nm⟩
    `(abbrev $nmId:ident {msg : Type} : Html msg → Bool := $(Lean.mkIdentFrom nmId (`Html ++ nmId.getId)))
  return ⟨Lean.mkNullNode (cmds.map (·.raw))⟩

html_abbrevs imgsHaveAlt buttonsAccessible validAriaRoles labelsAssociated noDuplicateIds headingsOrdered htmlHasLang a11yValid

end Qed
