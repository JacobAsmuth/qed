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
@[simp] theorem parse?_isSome (s : String) : (parse? s).isSome = isSafeUrl s := by
  unfold parse?; split <;> rename_i h
  · rw [h]; rfl
  · rw [Bool.eq_false_iff.2 h]; rfl
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

@[simp] theorem Attr.isSignalBind_ite (c : Prop) [Decidable c] (a b : Attr msg) : (if c then a else b).isSignalBind = if c then a.isSignalBind else b.isSignalBind := fn_ite Attr.isSignalBind c a b
@[simp] theorem Attr.canonical_ite (c : Prop) [Decidable c] (a b : Attr msg) : (if c then a else b).canonical = if c then a.canonical else b.canonical := fn_ite Attr.canonical c a b
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
def isSrcdocChars (cs : List Char) : Bool := cs == ['s', 'r', 'c', 'd', 'o', 'c']
@[simp] theorem isSrcdocChars_of_asciiLower {k : String} (h : asciiLower k = "srcdoc") :
    isSrcdocChars (k.toList.map asciiLowerChar) = true := by
  have := congrArg String.toList h; rw [asciiLower, String.toList_ofList] at this; rw [this]; rfl
def isSafeRenderedKey (k : String) : Bool :=
  let low := k.toList.map asciiLowerChar
  !low.isEmpty && !hasOnPrefix low && !isSrcdocChars low
def isSafeAttrName (k : String) : Bool := k.toList.all isKeyChar && isSafeRenderedKey k

@[inline] private def asciiLowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b ||| 32 else b
def isUrlAttrName (k : String) : Bool :=
  match k.utf8ByteSize with
  | 3 => k.toByteArray.data.toList.map asciiLowerByte == [115, 114, 99]
  | 4 => let b := k.toByteArray.data.toList.map asciiLowerByte
         b == [104, 114, 101, 102] || b == [100, 97, 116, 97] || b == [99, 105, 116, 101]
  | 6 => let b := k.toByteArray.data.toList.map asciiLowerByte
         b == [97, 99, 116, 105, 111, 110] || b == [112, 111, 115, 116, 101, 114] || b == [115, 114, 99, 115, 101, 116]
  | 10 => let b := k.toByteArray.data.toList.map asciiLowerByte
          b == [102, 111, 114, 109, 97, 99, 116, 105, 111, 110] || b == [120, 108, 105, 110, 107, 58, 104, 114, 101, 102]
  | _ => false

def Attr.validKeyValue (k v : String) : Bool := isSafeAttrName k && (!isUrlAttrName k || isSafeUrl v)

def Attr.valid : Attr msg → Bool
  | .cls _ | .key _ | .localCell .. | .signalBind _ => true
  | .attr k v | .signalAttr _ k v                   => Attr.validKeyValue k v
  | .flag k _ | .on k _ | .onValue k _ | .signalOn _ k _ => isSafeAttrName k

def Attr.validList : List (Attr msg) → Bool | [] => true | a :: as => a.valid && Attr.validList as
def Attr.isLocalCell : Attr msg → Bool | .localCell .. => true | _ => false
def Attr.hasLocalCell : List (Attr msg) → Bool | [] => false | a :: rest => a.isLocalCell || Attr.hasLocalCell rest

section AttrCtorSimp
variable {msg : Type}
@[simp] theorem Attr.valid_cls (n : String) : (Attr.cls n : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_cls (n : String) : (Attr.cls n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_attr (k v : String) : (Attr.attr k v : Attr msg).valid = Attr.validKeyValue k v := rfl
@[simp] theorem Attr.isLocalCell_attr (k v : String) : (Attr.attr k v : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).valid = isSafeAttrName k := rfl
@[simp] theorem Attr.isLocalCell_flag (k : String) (p : Bool) : (Attr.flag k p : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_key (n : String) : (Attr.key n : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_key (n : String) : (Attr.key n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_on (e : String) (m : msg) : (Attr.on e m).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.isLocalCell_on (e : String) (m : msg) : (Attr.on e m).isLocalCell = false := rfl
@[simp] theorem Attr.valid_onValue (e : String) (f : String → msg) : (Attr.onValue e f).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.isLocalCell_onValue (e : String) (f : String → msg) : (Attr.onValue e f).isLocalCell = false := rfl
@[simp] theorem Attr.valid_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) : (Attr.localCell k c i p b).valid = true := rfl
@[simp] theorem Attr.isLocalCell_localCell (k c : String) (i : Option String) (p : String) (b : String → Option msg) : (Attr.localCell k c i p b).isLocalCell = true := rfl
@[simp] theorem Attr.valid_signalBind (n : String) : (Attr.signalBind n : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_signalBind (n : String) : (Attr.signalBind n : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_signalAttr (n a v : String) : (Attr.signalAttr n a v : Attr msg).valid = Attr.validKeyValue a v := rfl
@[simp] theorem Attr.isLocalCell_signalAttr (n a v : String) : (Attr.signalAttr n a v : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.valid_signalOn (n e : String) (m : msg) : (Attr.signalOn n e m).valid = isSafeAttrName e := rfl
@[simp] theorem Attr.isLocalCell_signalOn (n e : String) (m : msg) : (Attr.signalOn n e m).isLocalCell = false := rfl
end AttrCtorSimp

def voidTags : List String := ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]
def isVoidTag (tag : String) : Bool := voidTags.contains tag

def isVoidTagFast (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 2 => tag == "br" || tag == "hr" | 3 => tag == "col" || tag == "img" || tag == "wbr"
  | 4 => tag == "area" || tag == "base" || tag == "link" || tag == "meta"
  | 5 => tag == "embed" || tag == "input" || tag == "track" | 6 => tag == "source" | _ => false

def isSafeTagName (tag : String) : Bool := let cs := tag.toList; !cs.isEmpty && cs.all (fun c => c.isAlphanum || c == '-')
def isForbiddenTag (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 4 => tag == "base" | 5 => tag == "embed"
  | 6 => tag == "script" || tag == "applet" || tag == "object" | _ => false
def isHeadingTag (tag : String) : Bool :=
  tag.utf8ByteSize == 2 && match tag.toByteArray.data.toList with | [104, b] => 49 ≤ b && b ≤ 54 | _ => false
def closesPTag (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 1 => tag == "p" | 2 => tag == "dl" || tag == "hr" || tag == "ol" || tag == "ul" || isHeadingTag tag
  | 3 => tag == "div" || tag == "nav" || tag == "pre" | 4 => tag == "form" || tag == "main" || tag == "menu"
  | 5 => tag == "aside" || tag == "table" | 8 => tag == "fieldset" | 10 => tag == "blockquote" || tag == "figcaption"
  | 6 => tag == "figure" || tag == "footer" || tag == "header" || tag == "hgroup" || tag == "search"
  | 7 => tag == "address" || tag == "article" || tag == "details" || tag == "section" | _ => false
def isInteractiveTag (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 1 => tag == "a" | 5 => tag == "input"
  | 6 => tag == "button" || tag == "select" | 7 => tag == "details" || tag == "summary"
  | 8 => tag == "textarea" | _ => false
def isContextOnlyTag (tag : String) : Bool :=
  match tag.utf8ByteSize with
  | 2 => tag == "li" || tag == "dt" || tag == "dd" || tag == "tr" || tag == "td" || tag == "th"
  | 3 => tag == "col" | 5 => tag == "thead" || tag == "tbody" || tag == "tfoot"
  | 6 => tag == "option" | 7 => tag == "caption" | 8 => tag == "colgroup" || tag == "optgroup" | _ => false

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
  · intro h; unfold isVoidTagFast at h; split at h
    · simp only [Bool.or_eq_true, beq_iff_eq] at h; rcases h with rfl | rfl <;> rfl
    · simp only [Bool.or_eq_true, beq_iff_eq] at h; rcases h with (rfl | rfl) | rfl <;> rfl
    · simp only [Bool.or_eq_true, beq_iff_eq] at h; rcases h with ((rfl | rfl) | rfl) | rfl <;> rfl
    · simp only [Bool.or_eq_true, beq_iff_eq] at h; rcases h with (rfl | rfl) | rfl <;> rfl
    · simp only [beq_iff_eq] at h; subst h; rfl
    · cases h

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

private theorem Attr.validList_eq_all (as : List (Attr msg)) : Attr.validList as = as.all Attr.valid := by
  induction as with | nil => rfl | cons _ _ ih => simp only [Attr.validList, List.all_cons, ih]
private theorem Attr.hasLocalCell_eq_any (as : List (Attr msg)) : Attr.hasLocalCell as = as.any Attr.isLocalCell := by
  induction as with | nil => rfl | cons _ _ ih => simp only [Attr.hasLocalCell, List.any_cons, ih]
private theorem Html.validListIn_eq_all (ctx : HtmlCtx) (cs : List (Html msg)) : Html.validListIn ctx cs = cs.all (Html.validIn ctx) := by
  induction cs with | nil => rfl | cons _ _ ih => simp only [Html.validListIn, List.all_cons, ih]

@[simp] theorem Attr.valid_empty : (Attr.empty : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_empty : (Attr.empty : Attr msg).isLocalCell = false := rfl

private theorem and_true_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by rw [ha, hb]; rfl
private theorem or_false_intro {a b : Bool} (ha : a = false) (hb : b = false) : (a || b) = false := by rw [ha, hb]; rfl

section ValidListSimp
variable {msg : Type}
@[simp] theorem Attr.validList_nil : Attr.validList ([] : List (Attr msg)) = true := rfl
@[simp] theorem Attr.validList_cons (a : Attr msg) (as : List (Attr msg)) : Attr.validList (a :: as) = (a.valid && Attr.validList as) := rfl
@[simp] theorem Attr.validList_append (xs ys : List (Attr msg)) : Attr.validList (xs ++ ys) = (Attr.validList xs && Attr.validList ys) := by simp only [Attr.validList_eq_all, List.all_append]
@[simp] theorem Attr.valid_ite (c : Prop) [Decidable c] (a b : Attr msg) : (if c then a else b).valid = if c then a.valid else b.valid := fn_ite Attr.valid c a b
theorem Attr.validList_cons_intro (a : Attr msg) (as : List (Attr msg)) (ha : a.valid = true) (has : Attr.validList as = true) : Attr.validList (a :: as) = true := and_true_intro ha has
theorem Attr.validList_append_intro (xs ys : List (Attr msg)) (hx : Attr.validList xs = true) (hy : Attr.validList ys = true) : Attr.validList (xs ++ ys) = true := (Attr.validList_append xs ys).trans (and_true_intro hx hy)
theorem Attr.valid_ite_intro (c : Prop) [Decidable c] (a b : Attr msg) (ht : c → a.valid = true) (hf : ¬c → b.valid = true) : (if c then a else b).valid = true := bool_ite_intro Attr.valid true c a b ht hf

@[simp] theorem Attr.hasLocalCell_nil : Attr.hasLocalCell ([] : List (Attr msg)) = false := rfl
@[simp] theorem Attr.hasLocalCell_cons (a : Attr msg) (as : List (Attr msg)) : Attr.hasLocalCell (a :: as) = (a.isLocalCell || Attr.hasLocalCell as) := rfl
@[simp] theorem Attr.hasLocalCell_append (xs ys : List (Attr msg)) : Attr.hasLocalCell (xs ++ ys) = (Attr.hasLocalCell xs || Attr.hasLocalCell ys) := by simp only [Attr.hasLocalCell_eq_any, List.any_append]
@[simp] theorem Attr.isLocalCell_ite (c : Prop) [Decidable c] (a b : Attr msg) : (if c then a else b).isLocalCell = if c then a.isLocalCell else b.isLocalCell := fn_ite Attr.isLocalCell c a b
theorem Attr.hasLocalCell_cons_eq_false (a : Attr msg) (as : List (Attr msg)) (ha : a.isLocalCell = false) (has : Attr.hasLocalCell as = false) : Attr.hasLocalCell (a :: as) = false := or_false_intro ha has
theorem Attr.hasLocalCell_append_eq_false (xs ys : List (Attr msg)) (hx : Attr.hasLocalCell xs = false) (hy : Attr.hasLocalCell ys = false) : Attr.hasLocalCell (xs ++ ys) = false := (Attr.hasLocalCell_append xs ys).trans (or_false_intro hx hy)
theorem Attr.isLocalCell_ite_eq_false (c : Prop) [Decidable c] (a b : Attr msg) (ht : c → a.isLocalCell = false) (hf : ¬c → b.isLocalCell = false) : (if c then a else b).isLocalCell = false := bool_ite_intro Attr.isLocalCell false c a b ht hf

@[simp] theorem Html.validListIn_nil (ctx : HtmlCtx) : Html.validListIn ctx ([] : List (Html msg)) = true := rfl
@[simp] theorem Html.validListIn_cons (ctx : HtmlCtx) (a : Html msg) (as : List (Html msg)) : Html.validListIn ctx (a :: as) = (Html.validIn ctx a && Html.validListIn ctx as) := rfl
@[simp] theorem Html.validListIn_append (ctx : HtmlCtx) (xs ys : List (Html msg)) : Html.validListIn ctx (xs ++ ys) = (Html.validListIn ctx xs && Html.validListIn ctx ys) := by simp only [Html.validListIn_eq_all, List.all_append]
@[simp] theorem Html.validIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg) : Html.validIn ctx (if c then a else b) = if c then Html.validIn ctx a else Html.validIn ctx b := fn_ite (Html.validIn ctx) c a b
theorem Html.validListIn_cons_intro (ctx : HtmlCtx) (a : Html msg) (as : List (Html msg)) (ha : Html.validIn ctx a = true) (has : Html.validListIn ctx as = true) : Html.validListIn ctx (a :: as) = true := and_true_intro ha has
theorem Html.validListIn_append_intro (ctx : HtmlCtx) (xs ys : List (Html msg)) (hx : Html.validListIn ctx xs = true) (hy : Html.validListIn ctx ys = true) : Html.validListIn ctx (xs ++ ys) = true := (Html.validListIn_append ctx xs ys).trans (and_true_intro hx hy)
theorem Html.validIn_ite_intro (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : Html msg) (ht : c → Html.validIn ctx a = true) (hf : ¬c → Html.validIn ctx b = true) : Html.validIn ctx (if c then a else b) = true := bool_ite_intro (Html.validIn ctx) true c a b ht hf
end ValidListSimp

@[simp] theorem Attr.validList_filter_nonkey (xs : List (Attr msg)) : Attr.validList (xs.filter (fun | .key _ => false | _ => true)) = Attr.validList xs := by
  induction xs with | nil => rfl | cons a _ ih => cases a <;> first | exact ih | exact congrArg (_ && ·) ih
@[simp] theorem Attr.hasLocalCell_filter_nonkey (xs : List (Attr msg)) : Attr.hasLocalCell (xs.filter (fun | .key _ => false | _ => true)) = Attr.hasLocalCell xs := by
  induction xs with | nil => rfl | cons a _ ih => cases a <;> first | exact ih | exact congrArg (_ || ·) ih
@[simp] theorem Html.mapAttrsList_isEmpty {α β : Type} (f : Attr α → Attr β) (cs : List (Html α)) : (Html.mapAttrsList f cs).isEmpty = cs.isEmpty := by cases cs <;> rfl

theorem Html.ind {msg : Type} {P : Html msg → Prop} {PL : List (Html msg) → Prop}
    (hText : ∀ s, P (.text s)) (hElem : ∀ t a cs, PL cs → P (.element t a cs)) (hNil : PL []) (hCons : ∀ c cs, P c → PL cs → PL (c :: cs)) :
    (∀ h, P h) ∧ (∀ cs, PL cs) :=
  let hNode : ∀ h, P h := @Html.rec msg P PL hText hElem hNil hCons
  ⟨hNode, fun cs => cs.rec hNil fun c _ ih => hCons c _ (hNode c) ih⟩

private theorem htmlValidIn_mapAttrs {α β : Type} (f : Attr α → Attr β) (hv : ∀ a, (f a).valid = a.valid) (hl : ∀ a, (f a).isLocalCell = a.isLocalCell) :
    (∀ h : Html α, ∀ ctx, Html.validIn ctx (Html.mapAttrs f h) = Html.validIn ctx h) ∧ (∀ cs : List (Html α), ∀ ctx, Html.validListIn ctx (Html.mapAttrsList f cs) = Html.validListIn ctx cs) :=
  Html.ind (fun _ _ => rfl) (fun tag attrs children ih ctx => by
      simp only [Html.mapAttrs, Html.validIn, Attr.validList_eq_all, Attr.hasLocalCell_eq_any, List.all_map, List.any_map, Function.comp_def, hv, hl, Html.mapAttrsList_isEmpty]
      cases stepHtmlCtx ctx tag with | none => rfl | some childCtx => exact congrArg (_ && ·) (ih childCtx))
    (fun _ => rfl) (fun _ _ ihc ihcs ctx => by simp only [Html.mapAttrsList, Html.validListIn, ihc ctx, ihcs ctx])

@[simp] theorem Attr.valid_map {α β : Type} (f : α → β) (a : Attr α) : (Attr.map f a).valid = a.valid := by cases a <;> rfl
@[simp] theorem Attr.isLocalCell_map {α β : Type} (f : α → β) (a : Attr α) : (Attr.map f a).isLocalCell = a.isLocalCell := by cases a <;> rfl
@[simp] theorem Attr.validList_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) : Attr.validList (as.map (Attr.map f)) = Attr.validList as := by simp only [Attr.validList_eq_all, List.all_map, Function.comp_def, Attr.valid_map]
@[simp] theorem Attr.hasLocalCell_map_attrMap {α β : Type} (f : α → β) (as : List (Attr α)) : Attr.hasLocalCell (as.map (Attr.map f)) = Attr.hasLocalCell as := by simp only [Attr.hasLocalCell_eq_any, List.any_map, Function.comp_def, Attr.isLocalCell_map]
@[simp] theorem Html.validIn_map {α β : Type} (ctx : HtmlCtx) (f : α → β) (h : Html α) : Html.validIn ctx (Html.map f h) = Html.validIn ctx h := (htmlValidIn_mapAttrs (Attr.map f) (Attr.valid_map f) (Attr.isLocalCell_map f)).1 h ctx
@[simp] theorem Html.validListIn_mapChildren {α β : Type} (ctx : HtmlCtx) (f : α → β) (cs : List (Html α)) : Html.validListIn ctx (Html.mapChildren f cs) = Html.validListIn ctx cs := (htmlValidIn_mapAttrs (Attr.map f) (Attr.valid_map f) (Attr.isLocalCell_map f)).2 cs ctx

@[simp] theorem Attr.valid_prefixSignal {msg : Type} (pfx : String) (a : Attr msg) : (Attr.prefixSignal pfx a).valid = a.valid := by cases a <;> rfl
@[simp] theorem Attr.isLocalCell_prefixSignal {msg : Type} (pfx : String) (a : Attr msg) : (Attr.prefixSignal pfx a).isLocalCell = a.isLocalCell := by cases a <;> rfl
@[simp] theorem Attr.validList_prefixSignal {msg : Type} (pfx : String) (as : List (Attr msg)) : Attr.validList (as.map (Attr.prefixSignal pfx)) = Attr.validList as := by simp only [Attr.validList_eq_all, List.all_map, Function.comp_def, Attr.valid_prefixSignal]
@[simp] theorem Attr.hasLocalCell_prefixSignal {msg : Type} (pfx : String) (as : List (Attr msg)) : Attr.hasLocalCell (as.map (Attr.prefixSignal pfx)) = Attr.hasLocalCell as := by simp only [Attr.hasLocalCell_eq_any, List.any_map, Function.comp_def, Attr.isLocalCell_prefixSignal]
@[simp] theorem Html.validIn_prefixSignals {msg : Type} (ctx : HtmlCtx) (pfx : String) (h : Html msg) : Html.validIn ctx (Html.prefixSignals pfx h) = Html.validIn ctx h := (htmlValidIn_mapAttrs (Attr.prefixSignal pfx) (Attr.valid_prefixSignal pfx) (Attr.isLocalCell_prefixSignal pfx)).1 h ctx
@[simp] theorem Html.validListIn_prefixSignalsList {msg : Type} (ctx : HtmlCtx) (pfx : String) (cs : List (Html msg)) : Html.validListIn ctx (Html.prefixSignalsList pfx cs) = Html.validListIn ctx cs := (htmlValidIn_mapAttrs (Attr.prefixSignal pfx) (Attr.valid_prefixSignal pfx) (Attr.isLocalCell_prefixSignal pfx)).2 cs ctx

@[simp] theorem Html.validListIn_ite (ctx : HtmlCtx) (c : Prop) [Decidable c] (a b : List (Html msg)) : Html.validListIn ctx (if c then a else b) = if c then Html.validListIn ctx a else Html.validListIn ctx b := fn_ite (Html.validListIn ctx) c a b
@[simp] theorem Html.validIn_ofOption (ctx : HtmlCtx) (o : Option (Html msg)) : Html.validIn ctx (Html.ofOption o) = match o with | some h => Html.validIn ctx h | none => validTextIn ctx "" := by cases o <;> rfl
@[simp] theorem Html.validListIn_map {α msg : Type} (ctx : HtmlCtx) (xs : List α) (f : α → Html msg) : Html.validListIn ctx (xs.map f) = xs.all (fun a => Html.validIn ctx (f a)) := by simp [Html.validListIn_eq_all, Function.comp_def]
@[simp] theorem Html.validListIn_toList_map {α msg : Type} (ctx : HtmlCtx) (xs : Array α) (f : α → Html msg) : Html.validListIn ctx (xs.map f).toList = xs.toList.all (fun a => Html.validIn ctx (f a)) := by simp [Array.toList_map]
@[simp] theorem List.all_const_true {α : Type} (xs : List α) : xs.all (fun _ => true) = true := by
  induction xs with | nil => rfl | cons _ _ ih => simp only [List.all_cons, Bool.true_and, ih]

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
@[simp] theorem Html.canonical_ite (c : Prop) [Decidable c] (a b : Html msg) : Html.canonical (if c then a else b) = if c then Html.canonical a else Html.canonical b := fn_ite Html.canonical c a b
@[simp] theorem Html.canonical_ofOption (o : Option (Html msg)) :
    Html.canonical (Html.ofOption o) = match o with | some h => Html.canonical h | none => .text "" := by cases o <;> rfl
@[simp] theorem Html.canonicalList_nil : Html.canonicalList ([] : List (Html msg)) = [] := rfl
@[simp] theorem Html.canonicalList_cons (c : Html msg) (cs : List (Html msg)) : Html.canonicalList (c :: cs) = Html.canonical c :: Html.canonicalList cs := rfl
theorem Html.canonicalList_eq_map (cs : List (Html msg)) : Html.canonicalList cs = cs.map Html.canonical := by
  induction cs with | nil => rfl | cons _ _ ih => simp only [Html.canonicalList, List.map_cons, ih]
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

private theorem flatMap_utf8_ascii : ∀ cs : List Char, (∀ c ∈ cs, c.toNat ≤ 127) →
    cs.flatMap String.utf8EncodeChar = cs.map (fun c => UInt8.ofNat c.toNat)
  | [], _ => rfl
  | c :: rest, hc => by
      rw [List.flatMap_cons, utf8EncodeChar_le_127 c (hc c List.mem_cons_self), List.singleton_append,
          List.map_cons, flatMap_utf8_ascii rest fun x hx => hc x (List.mem_cons_of_mem _ hx)]

private theorem bytes_all_toList {s : String} {p : UInt8 → Bool}
    (hhi : ∀ b : UInt8, b.toNat ≥ 128 → p b = false) (h : s.toByteArray.data.toList.all p = true) :
    (∀ c ∈ s.toList, c.toNat ≤ 127 ∧ p (UInt8.ofNat c.toNat) = true) ∧
      s.toByteArray.data.toList = s.toList.map (fun c => UInt8.ofNat c.toNat) := by
  rw [string_toByteArray_data] at h ⊢
  have h1 : ∀ c ∈ s.toList, c.toNat ≤ 127 ∧ p (UInt8.ofNat c.toNat) = true := fun c hc => by
    have hce := List.all_eq_true.1 (List.all_flatMap.symm ▸ h) c hc
    by_cases hle : c.toNat ≤ 127
    · rw [utf8EncodeChar_le_127 c hle] at hce; exact ⟨hle, List.all_eq_true.1 hce _ List.mem_cons_self⟩
    · cases hne : String.utf8EncodeChar c with
      | nil => exact absurd hne (utf8EncodeChar_ne_nil c)
      | cons b _ =>
          exact absurd (List.all_eq_true.1 hce b (hne ▸ List.mem_cons_self))
            (by rw [hhi b (utf8EncodeChar_gt_127 c (by omega) b (hne ▸ List.mem_cons_self))]; decide)
  exact ⟨h1, flatMap_utf8_ascii s.toList fun c hc => (h1 c hc).1⟩

@[inline] def isAsciiLowerTagByte (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) || b == 45
@[inline] def isAsciiLowerAttrByte (b : UInt8) : Bool := isAsciiLowerTagByte b || b == 95 || b == 58 || b == 46
def isSafeTagBytes (tag : String) : Bool := let bs := tag.toByteArray.data.toList; !bs.isEmpty && bs.all isAsciiLowerTagByte
def isSafeLowerAttrBytes (k : String) : Bool :=
  let bs := k.toByteArray.data.toList
  !bs.isEmpty && bs.all isAsciiLowerAttrByte && (match bs with | 111 :: 110 :: _ => false | _ => true) && bs != [115, 114, 99, 100, 111, 99]

private theorem isAsciiLowerTagByte_hi (b : UInt8) (h : b.toNat ≥ 128) : isAsciiLowerTagByte b = false := by
  simp only [isAsciiLowerTagByte, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  exact ⟨⟨.inr (show ¬ b.toNat ≤ 122 by omega), .inr (show ¬ b.toNat ≤ 57 by omega)⟩, fun heq => by subst heq; exact absurd h (by decide)⟩
private theorem isAsciiLowerAttrByte_hi (b : UInt8) (h : b.toNat ≥ 128) : isAsciiLowerAttrByte b = false := by
  simp only [isAsciiLowerAttrByte, isAsciiLowerTagByte_hi b h, Bool.false_or, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨⟨fun heq => by subst heq; exact absurd h (by decide), fun heq => by subst heq; exact absurd h (by decide)⟩, fun heq => by subst heq; exact absurd h (by decide)⟩
private theorem char_of_asciiByte_eq {c : Char} {b : UInt8} (hle : c.toNat ≤ 127) (h : UInt8.ofNat c.toNat = b) : c = Char.ofNat b.toNat := by
  rw [← (Nat.mod_eq_of_lt (show c.toNat < 256 by omega)).symm.trans (congrArg UInt8.toNat h), Char.ofNat_toNat]
private theorem char_isAlphanum_ascii (c : Char) (h : (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) : c.isAlphanum = true := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hl : c.isLower = true := by simp only [Char.isLower, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩
    simp only [Char.isAlphanum, Char.isAlpha, hl, Bool.or_true, Bool.true_or]
  · have hd : c.isDigit = true := by simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩
    simp only [Char.isAlphanum, hd, Bool.or_true]
private theorem asciiLowerTagByte_ok (c : Char) (hle : c.toNat ≤ 127) (hp : isAsciiLowerTagByte (UInt8.ofNat c.toNat) = true) :
    (c.isAlphanum || c == '-') = true ∧ asciiLowerChar c = c := by
  have hmod : (UInt8.ofNat c.toNat).toNat = c.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [isAsciiLowerTagByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  have hlow (hlt : c.toNat < 65 ∨ 90 < c.toNat) : asciiLowerChar c = c := by
    unfold asciiLowerChar; split
    · next hup => simp only [Bool.and_eq_true, decide_eq_true_eq] at hup; have : 65 ≤ c.toNat := hup.1; have : c.toNat ≤ 90 := hup.2; omega
    · rfl
  rcases hp with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h45
  · have ha : 97 ≤ c.toNat ∧ c.toNat ≤ 122 := ⟨hmod ▸ h1, hmod ▸ h2⟩; exact ⟨by simp only [char_isAlphanum_ascii c (.inl ha), Bool.true_or], hlow (by omega)⟩
  · have hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := ⟨hmod ▸ h1, hmod ▸ h2⟩; exact ⟨by simp only [char_isAlphanum_ascii c (.inr hd), Bool.true_or], hlow (by omega)⟩
  · rw [char_of_asciiByte_eq hle h45]; exact ⟨rfl, rfl⟩
private theorem asciiLowerAttrByte_ok (c : Char) (hle : c.toNat ≤ 127) (hp : isAsciiLowerAttrByte (UInt8.ofNat c.toNat) = true) :
    isKeyChar c = true ∧ asciiLowerChar c = c := by
  simp only [isAsciiLowerAttrByte, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with ((ht | h95) | h58) | h46
  · have ⟨h1, h2⟩ := asciiLowerTagByte_ok c hle ht; exact ⟨by simp only [isKeyChar, h1, Bool.true_or], h2⟩
  · rw [char_of_asciiByte_eq hle h95]; exact ⟨rfl, rfl⟩
  · rw [char_of_asciiByte_eq hle h58]; exact ⟨rfl, rfl⟩
  · rw [char_of_asciiByte_eq hle h46]; exact ⟨rfl, rfl⟩
theorem isSafeTagName_of_bytes (tag : String) (h : isSafeTagBytes tag = true) : isSafeTagName tag = true := by
  simp only [isSafeTagBytes, Bool.and_eq_true, Bool.not_eq_true'] at h
  have ⟨hc, hmap⟩ := bytes_all_toList isAsciiLowerTagByte_hi h.2
  simp only [isSafeTagName, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨by cases htl : tag.toList with | nil => rw [htl] at hmap; rw [hmap] at h; cases h.1 | cons _ _ => rfl,
          List.all_eq_true.2 fun c hm => (asciiLowerTagByte_ok c (hc c hm).1 (hc c hm).2).1⟩
theorem isSafeAttrName_of_bytes (k : String) (h : isSafeLowerAttrBytes k = true) : isSafeAttrName k = true := by
  simp only [isSafeLowerAttrBytes, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨hne, hall⟩, hnoOn⟩, hnoSrc⟩
  have ⟨hc, hmap⟩ := bytes_all_toList isAsciiLowerAttrByte_hi hall
  have hchars : ∀ c ∈ k.toList, isKeyChar c = true ∧ asciiLowerChar c = c := fun c hm => asciiLowerAttrByte_ok c (hc c hm).1 (hc c hm).2
  have hlow : k.toList.map asciiLowerChar = k.toList := by rw [List.map_congr_left fun c hm => (hchars c hm).2, List.map_id']
  simp only [isSafeAttrName, isSafeRenderedKey, hlow, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨List.all_eq_true.2 fun c hm => (hchars c hm).1, ⟨by cases htl : k.toList with | nil => rw [htl] at hmap; rw [hmap] at hne; cases hne | cons _ _ => rfl, ?_⟩, ?_⟩
  · cases hon : hasOnPrefix k.toList with | false => rfl | true =>
      unfold hasOnPrefix at hon; split at hon
      · next _ _ heq => rw [heq, List.map_cons, List.map_cons] at hmap; rw [hmap] at hnoOn; cases hnoOn
      · cases hon
  · cases hsd : isSrcdocChars k.toList with | false => rfl | true =>
      rw [beq_iff_eq.1 hsd] at hmap; rw [hmap] at hnoSrc; cases hnoSrc

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
  | case2 i afterLt hi b hmiss ih => rw [List.drop_eq_getElem_cons (string_bytes_len s ▸ hi), escapeCloseSeqBytesSpec, show s.toByteArray.data.toList[i] = b from rfl, ite_eq_right hmiss, ih hfalse]
  | case3 i afterLt hge => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt (string_bytes_len s ▸ hge))]; rfl

private theorem escapeRawBytesLoop_data (ba : ByteArray) (segStart i : Nat) (afterLt : Bool) (acc : ByteArray) (hle : segStart ≤ i) (hi : i ≤ ba.size) :
    (escapeRawBytesLoop ba segStart i afterLt acc).data.toList =
      acc.data.toList ++ (ba.data.toList.drop segStart).take (i - segStart) ++ escapeCloseSeqBytesSpec afterLt (ba.data.toList.drop i) := by
  fun_induction escapeRawBytesLoop ba segStart i afterLt acc with
  | case1 segStart i afterLt acc hlt b hhit ih =>
      have h47 : b = 47 := beq_iff_eq.1 ((Bool.and_eq_true _ _).mp hhit).2
      rw [ih (by omega) (by omega), ByteArray.push, Array.toList_push, copySliceAppend_data ba segStart i acc hle,
          List.drop_eq_getElem_cons (i := i) (Array.length_toList.symm ▸ hlt), show ba.data.toList[i] = b from rfl,
          escapeCloseSeqBytesSpec, ite_eq_left hhit, show (b :: ba.data.toList.drop (i + 1)).take (i + 1 - i) = [47] by rw [show i + 1 - i = 1 by omega, h47]; rfl]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  | case2 segStart i afterLt acc hlt b hmiss ih =>
      rw [ih (by omega) (by omega), List.drop_eq_getElem_cons (i := i) (Array.length_toList.symm ▸ hlt), show ba.data.toList[i] = b from rfl, escapeCloseSeqBytesSpec, ite_eq_right hmiss]
      have hlen : i - segStart < (ba.data.toList.drop segStart).length := by rw [List.length_drop, Array.length_toList]; exact Nat.sub_lt_sub_right hle hlt
      rw [show i + 1 - segStart = (i - segStart) + 1 by omega, List.take_succ_eq_append_getElem hlen]
      simp only [List.getElem_drop, show segStart + (i - segStart) = i by omega, List.append_assoc, List.cons_append, List.nil_append]; rfl
  | case3 segStart i afterLt acc hge =>
      obtain rfl : i = ba.size := by omega
      rw [copySliceAppend_data ba segStart ba.size acc hle, List.drop_eq_nil_of_le (i := ba.size) (Array.length_toList.symm ▸ Nat.le_refl _)]
      simp only [escapeCloseSeqBytesSpec, List.append_nil]

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

private def Attr.keyVal? {msg : Type} : Attr msg → Option (String × String) | .attr k v | .signalAttr _ k v => some (k, v) | _ => none
private theorem Attr.keyVal?_map {α β : Type} (f : α → β) (a : Attr α) : (Attr.map f a).keyVal? = a.keyVal? := by cases a <;> rfl
private theorem Attr.canonical_case {msg : Type} : (a : Attr msg) →
    (a.canonical = none ∧ a.keyVal? = none) ∨ (∃ n, a = .cls n ∧ a.canonical = some (.attr "class" n)) ∨ (∃ a', a.canonical = some a' ∧ a'.keyVal? = a.keyVal?)
  | .cls _ => .inr (.inl ⟨_, rfl, rfl⟩) | .key _ | .signalBind _ => .inl ⟨rfl, rfl⟩ | .attr .. | .flag .. | .on .. | .onValue .. | .localCell .. | .signalAttr .. | .signalOn .. => .inr (.inr ⟨_, rfl, rfl⟩)
private theorem onlySignalBind_elim {msg : Type} {P : List (Attr msg) → Prop} (hSig : ∀ n, P [.signalBind n]) (hKey : ∀ k rest, onlySignalBind rest = true → P rest → P (.key k :: rest)) :
    ∀ as : List (Attr msg), onlySignalBind as = true → P as
  | [], h => nomatch h
  | a :: rest, h => by
      cases a with
      | key k => exact hKey k rest h (onlySignalBind_elim hSig hKey rest h)
      | signalBind n => cases rest with | nil => exact hSig n | cons _ _ => cases h
      | _ => cases h

def attrValue (key : String) : List (Attr msg) → Option String
  | [] => none | .attr k v :: r | .signalAttr _ k v :: r => if k == key then some v else attrValue key r | _ :: r => attrValue key r
private theorem attrValue_cons (key : String) (a : Attr msg) (r : List (Attr msg)) :
    attrValue key (a :: r) = match a.keyVal? with | some (k, v) => if k == key then some v else attrValue key r | none => attrValue key r := by cases a <;> rfl

def hasAttr (key : String) (as : List (Attr msg)) : Bool := (attrValue key as).isSome
def isNonBlank (s : String) : Bool := s.toList.any (!·.isWhitespace)
def hasNonBlankAttr (key : String) (as : List (Attr msg)) : Bool := match attrValue key as with | some v => isNonBlank v | none => false

@[simp] theorem attrValue_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) : attrValue key (as.map (Attr.map f)) = attrValue key as := by
  induction as with | nil => rfl | cons a _ ih => rw [List.map_cons, attrValue_cons, attrValue_cons, Attr.keyVal?_map, ih]
@[simp] theorem hasAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) : hasAttr key (as.map (Attr.map f)) = hasAttr key as := by simp only [hasAttr, attrValue_map]
@[simp] theorem hasNonBlankAttr_map {α β : Type} (key : String) (f : α → β) (as : List (Attr α)) : hasNonBlankAttr key (as.map (Attr.map f)) = hasNonBlankAttr key as := by simp only [hasNonBlankAttr, attrValue_map]

theorem attrValue_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) : attrValue key (as.filterMap Attr.canonical) = attrValue key as := by
  have hcls : ("class" == key) = false := beq_false_of_ne (Ne.symm hk)
  induction as with
  | nil => rfl
  | cons a _ ih =>
      rcases a.canonical_case with ⟨hc, hkv⟩ | ⟨n, rfl, hc⟩ | ⟨a', hc, hkv⟩
      · rw [List.filterMap_cons, hc, attrValue_cons, hkv]; exact ih
      · rw [List.filterMap_cons, hc, attrValue_cons]; change (if "class" == key then some n else _) = _; rw [hcls, ih]; rfl
      · rw [List.filterMap_cons, hc, attrValue_cons, attrValue_cons, hkv, ih]
theorem hasAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) : hasAttr key (as.filterMap Attr.canonical) = hasAttr key as := by simp only [hasAttr, attrValue_canonical key hk]
theorem hasNonBlankAttr_canonical {msg : Type} (key : String) (hk : key ≠ "class") (as : List (Attr msg)) : hasNonBlankAttr key (as.filterMap Attr.canonical) = hasNonBlankAttr key as := by simp only [hasNonBlankAttr, attrValue_canonical key hk]
theorem attrValue_of_onlySignalBind {msg : Type} (key : String) : ∀ as : List (Attr msg), onlySignalBind as = true → attrValue key as = none := onlySignalBind_elim (fun _ => rfl) (fun _ _ _ ih => ih)

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
private theorem attrsValidAriaRoles_cons (a : Attr msg) (r : List (Attr msg)) :
    attrsValidAriaRoles (a :: r) = match a.keyVal? with | some (k, v) => (k != "role" || isValidAriaRole v) && attrsValidAriaRoles r | none => attrsValidAriaRoles r := by cases a <;> rfl

@[simp] theorem attrsValidAriaRoles_map {α β : Type} (f : α → β) (as : List (Attr α)) : attrsValidAriaRoles (as.map (Attr.map f)) = attrsValidAriaRoles as := by
  induction as with | nil => rfl | cons a _ ih => rw [List.map_cons, attrsValidAriaRoles_cons, attrsValidAriaRoles_cons, Attr.keyVal?_map, ih]
@[simp] theorem attrsValidAriaRoles_canonical {msg : Type} (as : List (Attr msg)) : attrsValidAriaRoles (as.filterMap Attr.canonical) = attrsValidAriaRoles as := by
  induction as with
  | nil => rfl
  | cons a _ ih =>
      rcases a.canonical_case with ⟨hc, hkv⟩ | ⟨_, rfl, hc⟩ | ⟨a', hc, hkv⟩
      · rw [List.filterMap_cons, hc, attrsValidAriaRoles_cons, hkv]; exact ih
      · rw [List.filterMap_cons, hc]; change ((true || _) && _) = _; rw [Bool.true_or, Bool.true_and, ih]; rfl
      · rw [List.filterMap_cons, hc, attrsValidAriaRoles_cons, attrsValidAriaRoles_cons, hkv, ih]
private theorem attrsValidAriaRoles_of_onlySignalBind {msg : Type} : ∀ as : List (Attr msg), onlySignalBind as = true → attrsValidAriaRoles as = true := onlySignalBind_elim (fun _ => rfl) (fun _ _ _ ih => ih)

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

theorem Html.fold_map {α β γ : Type} (f : α → β) (onText : String → γ) (onElemα : String → List (Attr α) → List (Html α) → γ → γ) (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
    (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) (h : Html α) :
    Html.fold onText onElemβ nil cons (h.map f) = Html.fold onText onElemα nil cons h :=
  (Html.ind (P := fun x => Html.fold onText onElemβ nil cons (x.map f) = Html.fold onText onElemα nil cons x)
    (PL := fun xs => Html.foldList onText onElemβ nil cons (Html.mapChildren f xs) = Html.foldList onText onElemα nil cons xs)
    (fun _ => rfl) (fun t a cs ih => by change onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) (Html.foldList _ _ _ _ (Html.mapChildren f cs)) = _; rw [ih, hElem]; rfl)
    rfl (fun c cs ihc ihcs => by change cons (Html.fold _ _ _ _ (c.map f)) (Html.foldList _ _ _ _ (Html.mapChildren f cs)) = _; rw [ihc, ihcs]; rfl)).1 h
theorem Html.foldList_map {α β γ : Type} (f : α → β) (onText : String → γ) (onElemα : String → List (Attr α) → List (Html α) → γ → γ) (onElemβ : String → List (Attr β) → List (Html β) → γ → γ) (nil : γ) (cons : γ → γ → γ)
    (hElem : ∀ t a cs r, onElemβ t (a.map (Attr.map f)) (Html.mapChildren f cs) r = onElemα t a cs r) (cs : List (Html α)) :
    Html.foldList onText onElemβ nil cons (Html.mapChildren f cs) = Html.foldList onText onElemα nil cons cs := by
  induction cs with | nil => rfl | cons c cs ih => change cons (Html.fold _ _ _ _ (c.map f)) (Html.foldList _ _ _ _ (Html.mapChildren f cs)) = _; rw [Html.fold_map f onText onElemα onElemβ nil cons hElem c, ih]; rfl

section FoldCanon
variable {msg γ : Type} (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)

theorem Html.fold_canonical (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
    (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) (h : Html msg) :
    Html.fold onText onElem nil cons h.canonical = Html.fold onText onElem nil cons h :=
  (Html.ind (P := fun x => Html.fold onText onElem nil cons x.canonical = Html.fold onText onElem nil cons x)
    (PL := fun cs => (∀ c ∈ cs, Html.fold onText onElem nil cons c.canonical = Html.fold onText onElem nil cons c) ∧ Html.foldList onText onElem nil cons (Html.canonicalList cs) = Html.foldList onText onElem nil cons cs)
    (fun _ => rfl) (fun t a cs ih => by
      change Html.fold onText onElem nil cons (mkCanonicalElem t a (Html.canonicalList cs)) = _
      rcases mkCanonicalElem_cases t a cs with ⟨rfl, ha, c₀, rfl, heq⟩ | heq
      · rw [heq, Html.fold, Html.foldList, Html.foldList, hUnwrap a c₀ _ ha]; exact ih.1 c₀ List.mem_cons_self
      · rw [heq, Html.fold, Html.fold, ih.2, hElem])
    ⟨(fun _ h => nomatch h), rfl⟩ (fun _ _ ihc ihcs => ⟨fun _ hx => (List.mem_cons.1 hx).elim (· ▸ ihc) (ihcs.1 _), by simp only [Html.canonicalList, Html.foldList, ihc, ihcs.2]⟩)).1 h
theorem Html.foldList_canonical (hUnwrap : ∀ a c₀ r, onlySignalBind a = true → onElem "span" a [c₀] (cons r nil) = r)
    (hElem : ∀ t a cs r, onElem t (a.filterMap Attr.canonical) (Html.canonicalList cs) r = onElem t a cs r) (cs : List (Html msg)) :
    Html.foldList onText onElem nil cons (Html.canonicalList cs) = Html.foldList onText onElem nil cons cs := by
  induction cs with | nil => rfl | cons c _ ih => simp only [Html.canonicalList, Html.foldList, Html.fold_canonical onText onElem nil cons hUnwrap hElem c, ih]

@[simp] theorem Html.fold_text (s : String) : Html.fold onText onElem nil cons (.text s) = onText s := rfl
@[simp] theorem Html.fold_element (tag : String) (attrs : List (Attr msg)) (kids : List (Html msg)) : Html.fold onText onElem nil cons (.element tag attrs kids) = onElem tag attrs kids (Html.foldList onText onElem nil cons kids) := rfl
@[simp] theorem Html.foldList_nil : Html.foldList onText onElem nil cons [] = nil := rfl
@[simp] theorem Html.foldList_cons (c : Html msg) (cs : List (Html msg)) : Html.foldList onText onElem nil cons (c :: cs) = cons (Html.fold onText onElem nil cons c) (Html.foldList onText onElem nil cons cs) := rfl
end FoldCanon

theorem Html.fold_eq_node {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ) (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
    (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks)) (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) (h : Html msg) :
    F h = Html.fold onText onElem nil cons h :=
  (Html.ind (P := fun x => F x = Html.fold onText onElem nil cons x) (PL := fun xs => FL xs = Html.foldList onText onElem nil cons xs) hT (fun _ _ _ ih => by rw [hE, Html.fold, ih]) hN (fun _ _ ihc ihcs => by rw [hC, Html.foldList, ihc, ihcs])).1 h
theorem Html.fold_eq_list {msg γ : Type} (F : Html msg → γ) (FL : List (Html msg) → γ) (onText : String → γ) (onElem : String → List (Attr msg) → List (Html msg) → γ → γ) (nil : γ) (cons : γ → γ → γ)
    (hT : ∀ s, F (.text s) = onText s) (hE : ∀ t a ks, F (.element t a ks) = onElem t a ks (FL ks)) (hN : FL [] = nil) (hC : ∀ c cs, FL (c :: cs) = cons (F c) (FL cs)) (cs : List (Html msg)) :
    FL cs = Html.foldList onText onElem nil cons cs := by
  induction cs with | nil => exact hN | cons c _ ih => rw [hC, Html.foldList, Html.fold_eq_node F FL onText onElem nil cons hT hE hN hC c, ih]

theorem Html.foldList_all_mapList {α : Type _} {msg : Type} (onText : String → Bool)
    (onElem : String → List (Attr msg) → List (Html msg) → Bool → Bool) (g : α → Html msg) (l : List α) :
    Html.foldList onText onElem true (· && ·) (l.map g) = true ↔ ∀ x ∈ l, Html.fold onText onElem true (· && ·) (g x) = true := by
  induction l with | nil => simp only [List.map_nil, Html.foldList, List.not_mem_nil, false_implies, implies_true] | cons _ _ ih => simp only [List.map_cons, Html.foldList, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]

private theorem Html.allElem_map {α β : Type} (f : α → β) {pα : String → List (Attr α) → List (Html α) → Bool} {pβ : String → List (Attr β) → List (Html β) → Bool}
    (hp : ∀ t a cs, pβ t (a.map (Attr.map f)) (Html.mapChildren f cs) = pα t a cs) (h : Html α) :
    Html.fold (fun _ => true) (fun t a k r => pβ t a k && r) true (· && ·) (h.map f) =
    Html.fold (fun _ => true) (fun t a k r => pα t a k && r) true (· && ·) h :=
  Html.fold_map f _ _ _ _ _ (fun t a cs _ => by rw [hp t a cs]) h
private theorem Html.allElem_canonical {msg : Type} {p : String → List (Attr msg) → List (Html msg) → Bool}
    (hSpan : ∀ a c₀, onlySignalBind a = true → p "span" a [c₀] = true)
    (hp : ∀ t a cs, p t (a.filterMap Attr.canonical) (Html.canonicalList cs) = p t a cs) (h : Html msg) :
    Html.fold (fun _ => true) (fun t a k r => p t a k && r) true (· && ·) h.canonical =
    Html.fold (fun _ => true) (fun t a k r => p t a k && r) true (· && ·) h :=
  Html.fold_canonical _ _ _ _ (fun a c₀ _ ha => by rw [hSpan a c₀ ha, Bool.true_and, Bool.and_true]) (fun t a cs _ => by rw [hp t a cs]) h

def Html.hasAccessibleNameChild {msg : Type} : Html msg → Bool := Html.fold isNonBlank (fun tag attrs _ r => (tag == "img" && hasNonBlankAttr "alt" attrs) || hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || r) false (· || ·)
abbrev Html.hasAccessibleNameChildren {msg : Type} : List (Html msg) → Bool := Html.foldList isNonBlank (fun tag attrs _ r => (tag == "img" && hasNonBlankAttr "alt" attrs) || hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || r) false (· || ·)
@[simp] theorem Html.hasAccessibleNameChild_map {α β : Type} (f : α → β) (h : Html α) : Html.hasAccessibleNameChild (h.map f) = Html.hasAccessibleNameChild h := Html.fold_map f _ _ _ _ _ (fun _ _ _ _ => by simp only [hasNonBlankAttr_map]) h
@[simp] theorem Html.hasAccessibleNameChildren_map {α β : Type} (f : α → β) (cs : List (Html α)) : Html.hasAccessibleNameChildren (Html.mapChildren f cs) = Html.hasAccessibleNameChildren cs := Html.foldList_map f _ _ _ _ _ (fun _ _ _ _ => by simp only [hasNonBlankAttr_map]) cs
@[simp] theorem Html.hasAccessibleNameChild_canonical {msg : Type} (h : Html msg) : Html.hasAccessibleNameChild (Html.canonical h) = Html.hasAccessibleNameChild h :=
  Html.fold_canonical _ _ _ _ (fun a _ r ha => by simp only [hasNonBlankAttr, attrValue_of_onlySignalBind "aria-label" a ha, attrValue_of_onlySignalBind "aria-labelledby" a ha]; cases r <;> rfl)
    (fun _ _ _ _ => by simp only [hasNonBlankAttr_canonical "alt" (by decide), hasNonBlankAttr_canonical "aria-label" (by decide), hasNonBlankAttr_canonical "aria-labelledby" (by decide)]) h
@[simp] theorem Html.hasAccessibleNameChildren_canonical {msg : Type} (cs : List (Html msg)) : Html.hasAccessibleNameChildren (Html.canonicalList cs) = Html.hasAccessibleNameChildren cs := by
  induction cs with | nil => rfl | cons c cs ih => change (Html.hasAccessibleNameChild c.canonical || Html.hasAccessibleNameChildren (Html.canonicalList cs)) = _; rw [Html.hasAccessibleNameChild_canonical c, ih]; rfl

def Html.elemHasAccessibleName (attrs : List (Attr msg)) (kids : List (Html msg)) : Bool :=
  hasNonBlankAttr "aria-label" attrs || hasNonBlankAttr "aria-labelledby" attrs || hasNonBlankAttr "title" attrs || Html.hasAccessibleNameChildren kids

def Html.containsFormControl {msg : Type} : Html msg → Bool := Html.fold (fun _ => false) (fun tag _ _ r => isFormControlTag tag || r) false (· || ·)
abbrev Html.containsFormControlList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => false) (fun tag _ _ r => isFormControlTag tag || r) false (· || ·)
@[simp] theorem Html.containsFormControl_map {α β : Type} (f : α → β) (h : Html α) : Html.containsFormControl (h.map f) = Html.containsFormControl h := Html.fold_map f _ _ _ _ _ (fun _ _ _ _ => rfl) h
@[simp] theorem Html.containsFormControlList_map {α β : Type} (f : α → β) (cs : List (Html α)) : Html.containsFormControlList (Html.mapChildren f cs) = Html.containsFormControlList cs := Html.foldList_map f _ _ _ _ _ (fun _ _ _ _ => rfl) cs
@[simp] theorem Html.containsFormControl_canonical {msg : Type} (h : Html msg) : Html.containsFormControl (Html.canonical h) = Html.containsFormControl h := Html.fold_canonical _ _ _ _ (fun _ _ r _ => by cases r <;> rfl) (fun _ _ _ _ => rfl) h
@[simp] theorem Html.containsFormControlList_canonical {msg : Type} (cs : List (Html msg)) : Html.containsFormControlList (Html.canonicalList cs) = Html.containsFormControlList cs := Html.foldList_canonical _ _ _ _ (fun _ _ r _ => by cases r <;> rfl) (fun _ _ _ _ => rfl) cs

@[simp] private def imgsHaveAltStep {msg : Type} (tag : String) (attrs : List (Attr msg)) (_ : List (Html msg)) (r : Bool) : Bool := (tag != "img" || hasAttr "alt" attrs) && r
def Html.imgsHaveAlt {msg : Type} : Html msg → Bool := Html.fold (fun _ => true) imgsHaveAltStep true (· && ·)
abbrev Html.imgsHaveAltList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => true) imgsHaveAltStep true (· && ·)
@[simp] theorem Html.imgsHaveAlt_map {α β : Type} (f : α → β) (h : Html α) : Html.imgsHaveAlt (h.map f) = Html.imgsHaveAlt h := Html.allElem_map f (fun _ _ _ => by simp only [hasAttr_map]) h
@[simp] theorem Html.imgsHaveAlt_canonical {msg : Type} (h : Html msg) : Html.imgsHaveAlt (Html.canonical h) = Html.imgsHaveAlt h := Html.allElem_canonical (fun _ _ _ => rfl) (fun _ _ _ => by simp only [hasAttr_canonical "alt" (by decide)]) h
theorem Html.imgsHaveAltList_mapList {α msg : Type} (g : α → Html msg) (l : List α) : Html.imgsHaveAltList (l.map g) = true ↔ ∀ x ∈ l, Html.imgsHaveAlt (g x) = true := Html.foldList_all_mapList _ _ g l

@[simp] private def buttonsAccessibleStep {msg : Type} (tag : String) (attrs : List (Attr msg)) (kids : List (Html msg)) (r : Bool) : Bool := (!(tag == "button" || tag == "a") || Html.elemHasAccessibleName attrs kids) && r
def Html.buttonsAccessible {msg : Type} : Html msg → Bool := Html.fold (fun _ => true) buttonsAccessibleStep true (· && ·)
abbrev Html.buttonsAccessibleList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => true) buttonsAccessibleStep true (· && ·)
@[simp] theorem Html.buttonsAccessible_map {α β : Type} (f : α → β) (h : Html α) : Html.buttonsAccessible (h.map f) = Html.buttonsAccessible h :=
  Html.allElem_map f (fun _ _ _ => by simp only [Html.elemHasAccessibleName, hasNonBlankAttr_map, Html.hasAccessibleNameChildren_map]) h
@[simp] theorem Html.buttonsAccessible_canonical {msg : Type} (h : Html msg) : Html.buttonsAccessible (Html.canonical h) = Html.buttonsAccessible h :=
  Html.allElem_canonical (fun _ _ _ => rfl) (fun _ _ cs => by simp only [Html.elemHasAccessibleName, hasNonBlankAttr_canonical "aria-label" (by decide), hasNonBlankAttr_canonical "aria-labelledby" (by decide), hasNonBlankAttr_canonical "title" (by decide), Html.hasAccessibleNameChildren_canonical cs]) h
theorem Html.buttonsAccessibleList_mapList {α msg : Type} (g : α → Html msg) (l : List α) : Html.buttonsAccessibleList (l.map g) = true ↔ ∀ x ∈ l, Html.buttonsAccessible (g x) = true := Html.foldList_all_mapList _ _ g l

@[simp] private def validAriaRolesStep {msg : Type} (_ : String) (attrs : List (Attr msg)) (_ : List (Html msg)) (r : Bool) : Bool := attrsValidAriaRoles attrs && r
def Html.validAriaRoles {msg : Type} : Html msg → Bool := Html.fold (fun _ => true) validAriaRolesStep true (· && ·)
abbrev Html.validAriaRolesList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => true) validAriaRolesStep true (· && ·)
@[simp] theorem Html.validAriaRoles_map {α β : Type} (f : α → β) (h : Html α) : Html.validAriaRoles (h.map f) = Html.validAriaRoles h := Html.allElem_map f (fun _ _ _ => attrsValidAriaRoles_map f _) h
@[simp] theorem Html.validAriaRoles_canonical {msg : Type} (h : Html msg) : Html.validAriaRoles (Html.canonical h) = Html.validAriaRoles h := Html.allElem_canonical (fun a _ ha => attrsValidAriaRoles_of_onlySignalBind a ha) (fun _ a _ => attrsValidAriaRoles_canonical a) h
theorem Html.validAriaRolesList_mapList {α msg : Type} (g : α → Html msg) (l : List α) : Html.validAriaRolesList (l.map g) = true ↔ ∀ x ∈ l, Html.validAriaRoles (g x) = true := Html.foldList_all_mapList _ _ g l

@[simp] private def labelsAssociatedStep {msg : Type} (tag : String) (attrs : List (Attr msg)) (kids : List (Html msg)) (r : Bool) : Bool := (tag != "label" || hasNonBlankAttr "for" attrs || Html.containsFormControlList kids) && r
def Html.labelsAssociated {msg : Type} : Html msg → Bool := Html.fold (fun _ => true) labelsAssociatedStep true (· && ·)
abbrev Html.labelsAssociatedList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => true) labelsAssociatedStep true (· && ·)
@[simp] theorem Html.labelsAssociated_map {α β : Type} (f : α → β) (h : Html α) : Html.labelsAssociated (h.map f) = Html.labelsAssociated h := Html.allElem_map f (fun _ _ _ => by simp only [hasNonBlankAttr_map, Html.containsFormControlList_map]) h
@[simp] theorem Html.labelsAssociated_canonical {msg : Type} (h : Html msg) : Html.labelsAssociated (Html.canonical h) = Html.labelsAssociated h := Html.allElem_canonical (fun _ _ _ => rfl) (fun _ _ cs => by simp only [hasNonBlankAttr_canonical "for" (by decide), Html.containsFormControlList_canonical cs]) h
theorem Html.labelsAssociatedList_mapList {α msg : Type} (g : α → Html msg) (l : List α) : Html.labelsAssociatedList (l.map g) = true ↔ ∀ x ∈ l, Html.labelsAssociated (g x) = true := Html.foldList_all_mapList _ _ g l

@[simp] private def htmlHasLangStep {msg : Type} (tag : String) (attrs : List (Attr msg)) (_ : List (Html msg)) (r : Bool) : Bool := (tag != "html" || hasNonBlankAttr "lang" attrs) && r
def Html.htmlHasLang {msg : Type} : Html msg → Bool := Html.fold (fun _ => true) htmlHasLangStep true (· && ·)
abbrev Html.htmlHasLangList {msg : Type} : List (Html msg) → Bool := Html.foldList (fun _ => true) htmlHasLangStep true (· && ·)
@[simp] theorem Html.htmlHasLang_map {α β : Type} (f : α → β) (h : Html α) : Html.htmlHasLang (h.map f) = Html.htmlHasLang h := Html.allElem_map f (fun _ _ _ => by simp only [hasNonBlankAttr_map]) h
@[simp] theorem Html.htmlHasLang_canonical {msg : Type} (h : Html msg) : Html.htmlHasLang (Html.canonical h) = Html.htmlHasLang h := Html.allElem_canonical (fun _ _ _ => rfl) (fun _ _ _ => by simp only [hasNonBlankAttr_canonical "lang" (by decide)]) h
theorem Html.htmlHasLangList_mapList {α msg : Type} (g : α → Html msg) (l : List α) : Html.htmlHasLangList (l.map g) = true ↔ ∀ x ∈ l, Html.htmlHasLang (g x) = true := Html.foldList_all_mapList _ _ g l

def Html.collectIds {msg : Type} : Html msg → List String := Html.fold (fun _ => []) (fun _ attrs _ r => match attrValue "id" attrs with | some v => if v.isEmpty then r else v :: r | none => r) [] (· ++ ·)
abbrev Html.collectIdsList {msg : Type} : List (Html msg) → List String := Html.foldList (fun _ => []) (fun _ attrs _ r => match attrValue "id" attrs with | some v => if v.isEmpty then r else v :: r | none => r) [] (· ++ ·)
@[simp] theorem Html.collectIds_map {α β : Type} (f : α → β) (h : Html α) : Html.collectIds (h.map f) = Html.collectIds h := Html.fold_map f _ _ _ _ _ (fun _ _ _ _ => by simp only [attrValue_map]) h
@[simp] theorem Html.collectIds_canonical {msg : Type} (h : Html msg) : Html.collectIds (Html.canonical h) = Html.collectIds h :=
  Html.fold_canonical _ _ _ _ (fun a _ _ ha => by simp only [attrValue_of_onlySignalBind "id" a ha, List.append_nil]) (fun _ _ _ _ => by simp only [attrValue_canonical "id" (by decide)]) h

def Html.collectHeadings {msg : Type} : Html msg → List Nat := Html.fold (fun _ => []) (fun tag _ _ r => match headingLevel? tag with | some lvl => lvl :: r | none => r) [] (· ++ ·)
abbrev Html.collectHeadingsList {msg : Type} : List (Html msg) → List Nat := Html.foldList (fun _ => []) (fun tag _ _ r => match headingLevel? tag with | some lvl => lvl :: r | none => r) [] (· ++ ·)
@[simp] theorem Html.collectHeadings_map {α β : Type} (f : α → β) (h : Html α) : Html.collectHeadings (h.map f) = Html.collectHeadings h := Html.fold_map f _ _ _ _ _ (fun _ _ _ _ => rfl) h
@[simp] theorem Html.collectHeadings_canonical {msg : Type} (h : Html msg) : Html.collectHeadings (Html.canonical h) = Html.collectHeadings h := Html.fold_canonical _ _ _ _ (fun _ _ _ _ => List.append_nil _) (fun _ _ _ _ => rfl) h

def Html.noDuplicateIds (h : Html msg) : Bool := listNoDups (Html.collectIds h)
def Html.headingsOrdered (h : Html msg) : Bool := headingLevelsOrderedFrom 0 (Html.collectHeadings h)
def Html.a11yValid (h : Html msg) : Bool :=
  Html.imgsHaveAlt h && Html.buttonsAccessible h && Html.validAriaRoles h &&
  Html.labelsAssociated h && Html.noDuplicateIds h && Html.headingsOrdered h && Html.htmlHasLang h

@[simp] theorem Html.noDuplicateIds_map {α β : Type} (f : α → β) (h : Html α) : Html.noDuplicateIds (h.map f) = Html.noDuplicateIds h := congrArg listNoDups (Html.collectIds_map f h)
@[simp] theorem Html.noDuplicateIds_canonical {msg : Type} (h : Html msg) : Html.noDuplicateIds (Html.canonical h) = Html.noDuplicateIds h := congrArg listNoDups (Html.collectIds_canonical h)
@[simp] theorem Html.headingsOrdered_map {α β : Type} (f : α → β) (h : Html α) : Html.headingsOrdered (h.map f) = Html.headingsOrdered h := congrArg (headingLevelsOrderedFrom 0) (Html.collectHeadings_map f h)
@[simp] theorem Html.headingsOrdered_canonical {msg : Type} (h : Html msg) : Html.headingsOrdered (Html.canonical h) = Html.headingsOrdered h := congrArg (headingLevelsOrderedFrom 0) (Html.collectHeadings_canonical h)
@[simp] theorem Html.a11yValid_map {α β : Type} (f : α → β) (h : Html α) : Html.a11yValid (h.map f) = Html.a11yValid h := by simp only [Html.a11yValid, Html.imgsHaveAlt_map, Html.buttonsAccessible_map, Html.validAriaRoles_map, Html.labelsAssociated_map, Html.noDuplicateIds_map, Html.headingsOrdered_map, Html.htmlHasLang_map]
@[simp] theorem Html.a11yValid_canonical {msg : Type} (h : Html msg) : Html.a11yValid (Html.canonical h) = Html.a11yValid h := by simp only [Html.a11yValid, Html.imgsHaveAlt_canonical, Html.buttonsAccessible_canonical, Html.validAriaRoles_canonical, Html.labelsAssociated_canonical, Html.noDuplicateIds_canonical, Html.headingsOrdered_canonical, Html.htmlHasLang_canonical]

abbrev imgsHaveAlt {msg : Type} : Html msg → Bool := Html.imgsHaveAlt
abbrev buttonsAccessible {msg : Type} : Html msg → Bool := Html.buttonsAccessible
abbrev validAriaRoles {msg : Type} : Html msg → Bool := Html.validAriaRoles
abbrev labelsAssociated {msg : Type} : Html msg → Bool := Html.labelsAssociated
abbrev noDuplicateIds {msg : Type} : Html msg → Bool := Html.noDuplicateIds
abbrev headingsOrdered {msg : Type} : Html msg → Bool := Html.headingsOrdered
abbrev htmlHasLang {msg : Type} : Html msg → Bool := Html.htmlHasLang
abbrev a11yValid {msg : Type} : Html msg → Bool := Html.a11yValid

/-! ## Core JS-Safe & Kernel-Reducible String Primitives (`Qed.Str`) -/

namespace Str

def splitCharAux (sep : Char) (cur : List Char) (acc : List String) : List Char → List String
  | [] => (String.ofList cur.reverse :: acc).reverse
  | c :: cs => if c == sep then splitCharAux sep [] (String.ofList cur.reverse :: acc) cs else splitCharAux sep (c :: cur) acc cs
def splitChar (s : String) (sep : Char) : List String := splitCharAux sep [] [] s.toList

theorem splitCharAux_acc (sep : Char) : ∀ (xs cur : List Char) (acc : List String),
    splitCharAux sep cur acc xs = acc.reverse ++ splitCharAux sep cur [] xs
  | [], _, _ => by simp only [splitCharAux, List.reverse_cons, List.reverse_nil, List.nil_append]
  | c :: cs, cur, acc => by
      simp only [splitCharAux]; split
      · rw [splitCharAux_acc sep cs [] (_ :: acc), splitCharAux_acc sep cs [] [_], List.reverse_cons, List.reverse_singleton, List.append_assoc]
      · exact splitCharAux_acc sep cs (c :: cur) acc

theorem splitCharAux_append_not_mem (sep : Char) : ∀ (xs ys cur : List Char) (acc : List String), sep ∉ xs →
    splitCharAux sep cur acc (xs ++ sep :: ys) = splitCharAux sep [] (String.ofList (cur.reverse ++ xs) :: acc) ys
  | [], _, _, _, _ => by simp only [List.nil_append, splitCharAux, beq_self_eq_true, ↓reduceIte, List.append_nil]
  | c :: xs, ys, cur, acc, hnd => by
      have hc : (c == sep) = false := beq_false_of_ne fun h => hnd (h ▸ .head _)
      simp only [List.cons_append, splitCharAux, hc, Bool.false_eq_true, ↓reduceIte]
      rw [splitCharAux_append_not_mem sep xs ys (c :: cur) acc (fun hm => hnd (.tail _ hm)), List.reverse_cons, List.append_assoc, List.singleton_append]

theorem splitCharAux_not_mem (sep : Char) : ∀ (xs cur : List Char) (acc : List String), sep ∉ xs →
    splitCharAux sep cur acc xs = (String.ofList (cur.reverse ++ xs) :: acc).reverse
  | [], _, _, _ => by simp only [splitCharAux, List.append_nil]
  | c :: xs, cur, acc, hnd => by
      have hc : (c == sep) = false := beq_false_of_ne fun h => hnd (h ▸ .head _)
      simp only [splitCharAux, hc, Bool.false_eq_true, ↓reduceIte]
      rw [splitCharAux_not_mem sep xs (c :: cur) acc (fun hm => hnd (.tail _ hm))]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def parseNatAux (acc : Nat) : List Char → Option Nat
  | [] => some acc | c :: cs => if '0' ≤ c && c ≤ '9' then parseNatAux (acc * 10 + (c.toNat - 48)) cs else none
def parseNat? (s : String) : Option Nat := match s.toList with | [] => none | cs => parseNatAux 0 cs
def parseInt? (s : String) : Option Int := match s.toList with
  | [] | ['-'] => none | '-' :: cs => (parseNatAux 0 cs).map (fun n => -(Int.ofNat n)) | cs => (parseNatAux 0 cs).map Int.ofNat

theorem digitChar_ok (d : Fin 10) :
    ('0' ≤ Nat.digitChar d.val ∧ Nat.digitChar d.val ≤ '9') ∧ (Nat.digitChar d.val).toNat - 48 = d.val ∧ Nat.digitChar d.val ≠ '-' := by revert d; decide
theorem toDigitsCore_ne_nil : ∀ fuel n ds, Nat.toDigitsCore 10 (fuel + 1) n ds ≠ []
  | 0, n, ds => by rw [Nat.toDigitsCore]; by_cases hq : n / 10 = 0 <;> simp [hq, Nat.toDigitsCore]
  | fuel + 1, n, ds => by rw [Nat.toDigitsCore]; by_cases hq : n / 10 = 0 <;> simp [hq, toDigitsCore_ne_nil]

private theorem parseNatAux_digit (acc d : Nat) (hd : d < 10) (ds : List Char) :
    parseNatAux acc (Nat.digitChar d :: ds) = parseNatAux (acc * 10 + d) ds := by
  have ⟨⟨h1, h2⟩, hval, _⟩ := digitChar_ok ⟨d, hd⟩
  simp only [parseNatAux, decide_eq_true h1, decide_eq_true h2, Bool.and_self, ↓reduceIte, hval]

theorem parseNatAux_toDigitsCore : ∀ fuel n ds, n ≤ fuel →
    parseNatAux 0 (Nat.toDigitsCore 10 (fuel + 1) n ds) = parseNatAux n ds
  | 0, n, _, hn => by have hn0 : n = 0 := by omega
                      subst hn0; rfl
  | fuel + 1, n, ds, hn => by
      rw [Nat.toDigitsCore]; by_cases hq : n / 10 = 0
      · simp only [hq, ↓reduceIte]; rw [parseNatAux_digit 0 (n % 10) (Nat.mod_lt _ (by omega)) ds, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt (show n < 10 by omega)]
      · simp only [hq, ↓reduceIte]
        rw [parseNatAux_toDigitsCore fuel (n / 10) _ (by omega), parseNatAux_digit (n / 10) (n % 10) (Nat.mod_lt _ (by omega)) ds, Nat.mul_comm (n / 10) 10, Nat.div_add_mod]

theorem parseNat?_repr (n : Nat) : parseNat? (Nat.repr n) = some n := by
  unfold parseNat? Nat.repr Nat.toDigits; rw [String.toList_ofList]
  have h1 := parseNatAux_toDigitsCore n n [] (Nat.le_refl n)
  cases h : Nat.toDigitsCore 10 (n + 1) n [] with
  | nil => exact absurd h (toDigitsCore_ne_nil n n [])
  | cons _ _ => rw [h] at h1; exact h1

theorem parseInt?_repr (i : Int) : parseInt? (Int.repr i) = some i := by
  cases i with
  | ofNat n =>
      simp only [Int.repr, parseInt?]; unfold Nat.repr Nat.toDigits; rw [String.toList_ofList]
      have h1 := parseNatAux_toDigitsCore n n [] (Nat.le_refl n)
      cases h : Nat.toDigitsCore 10 (n + 1) n [] with
      | nil => exact absurd h (toDigitsCore_ne_nil n n [])
      | cons c cs =>
          have hnc : c ≠ '-' := fun heq => by have hp := h ▸ h1; subst heq; cases hp
          have hmatch : (match c :: cs with | [] | ['-'] => none | '-' :: cs' => (parseNatAux 0 cs').map (fun m => -(Int.ofNat m)) | cs' => (parseNatAux 0 cs').map Int.ofNat) = (parseNatAux 0 (c :: cs)).map Int.ofNat := by
            split
            · next he => cases he
            · next he => exact absurd (List.cons.inj he).1 hnc
            · next _ he => exact absurd (List.cons.inj he).1 hnc
            · rfl
          rw [hmatch, ← h, h1]; rfl
  | negSucc n =>
      simp only [Int.repr, parseInt?, String.toList_append, show "-".toList = ['-'] from rfl, List.cons_append, List.nil_append]
      unfold Nat.repr Nat.toDigits; rw [String.toList_ofList]
      cases h : Nat.toDigitsCore 10 (n + 2) (n + 1) [] with
      | nil => exact absurd h (toDigitsCore_ne_nil (n + 1) (n + 1) [])
      | cons _ _ => change (parseNatAux 0 _).map _ = _; rw [← h, parseNatAux_toDigitsCore (n + 1) (n + 1) [] (Nat.le_refl _)]; rfl

theorem nat_toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, '0' ≤ c ∧ c ≤ '9' := by
  have hmem : ∀ m (b : Nat) (acc : List Char), (∀ y ∈ acc, '0' ≤ y ∧ y ≤ '9') → ∀ y ∈ Nat.toDigitsCore 10 m b acc, '0' ≤ y ∧ y ≤ '9' := by
    intro m; induction m with
    | zero => exact fun _ _ hacc => hacc
    | succ _ ih =>
        intro b acc hacc y hy; unfold Nat.toDigitsCore at hy; dsimp only at hy
        have hd := (digitChar_ok ⟨b % 10, Nat.mod_lt b (by decide)⟩).1
        split at hy
        · exact (List.mem_cons.1 hy).elim (· ▸ hd) (hacc y)
        · exact ih (b / 10) _ (fun z hz => (List.mem_cons.1 hz).elim (· ▸ hd) (hacc z)) y hy
  intro c hc; rw [show (toString n).toList = Nat.toDigits 10 n from String.toList_ofList] at hc
  exact hmem (n + 1) n [] (fun _ h => nomatch h) c hc

theorem nat_toString_not_mem {d : Char} (hd : d < '0' ∨ '9' < d) (n : Nat) : d ∉ (toString n).toList := fun hm => by
  have ⟨h1, h2⟩ := nat_toString_digits n d hm
  have h1' : 48 ≤ d.toNat := h1; have h2' : d.toNat ≤ 57 := h2
  rcases hd with hlt | hgt <;> ((first | have : d.toNat < 48 := hlt | have : 57 < d.toNat := hgt); omega)

private theorem digits_toList : "0123456789".toList = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := rfl
private theorem negDigits_toList : "-0123456789".toList = '-' :: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := rfl
private theorem fin10_mem_digits : ∀ d : Fin 10, Char.ofNat (48 + d.val) ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by decide

private theorem digit_mem_digits {c : Char} (h1 : '0' ≤ c) (h2 : c ≤ '9') : c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
  have h1' : 48 ≤ c.toNat := h1; have h2' : c.toNat ≤ 57 := h2
  have hc : c = Char.ofNat (48 + (c.toNat - 48)) := by rw [Nat.add_sub_cancel' h1', Char.ofNat_toNat]
  rw [hc]; exact fin10_mem_digits ⟨c.toNat - 48, by omega⟩

theorem nat_toString_all {p : Char → Bool} (hp : "0123456789".toList.all p = true) (n : Nat) : (toString n).toList.all p = true := by
  rw [digits_toList] at hp; exact List.all_eq_true.2 fun c hc => let ⟨h1, h2⟩ := nat_toString_digits n c hc; List.all_eq_true.1 hp c (digit_mem_digits h1 h2)
theorem nat_toString_injective {a b : Nat} (h : toString a = toString b) : a = b :=
  Option.some.inj (by have h' : Nat.repr a = Nat.repr b := h; rw [← parseNat?_repr a, ← parseNat?_repr b, h'])

theorem int_toString_chars (i : Int) : ∀ c ∈ (toString i).toList, c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') := by
  cases i with
  | ofNat n => exact fun c hc => .inr (nat_toString_digits n c hc)
  | negSucc n =>
      intro c hc; rw [show (toString (Int.negSucc n)).toList = '-' :: (toString (n + 1)).toList from by change ("-" ++ Nat.repr (n + 1)).toList = _; rw [String.toList_append]; rfl] at hc
      exact (List.mem_cons.1 hc).elim .inl fun hm => .inr (nat_toString_digits (n + 1) c hm)

theorem int_toString_not_mem {d : Char} (hd : d ≠ '-' ∧ (d < '0' ∨ '9' < d)) (i : Int) : d ∉ (toString i).toList := fun hm => by
  rcases int_toString_chars i d hm with heq | ⟨h1, h2⟩
  · exact hd.1 heq
  · have h1' : 48 ≤ d.toNat := h1; have h2' : d.toNat ≤ 57 := h2
    rcases hd.2 with hlt | hgt <;> ((first | have : d.toNat < 48 := hlt | have : 57 < d.toNat := hgt); omega)

theorem int_toString_all {p : Char → Bool} (hp : "-0123456789".toList.all p = true) (i : Int) : (toString i).toList.all p = true := by
  rw [negDigits_toList] at hp
  exact List.all_eq_true.2 fun c hc => (int_toString_chars i c hc).elim
    (fun heq => List.all_eq_true.1 hp c (heq ▸ List.mem_cons_self)) (fun ⟨h1, h2⟩ => List.all_eq_true.1 hp c (List.mem_cons_of_mem '-' (digit_mem_digits h1 h2)))
theorem int_toString_injective {a b : Int} (h : toString a = toString b) : a = b :=
  Option.some.inj (by have h' : Int.repr a = Int.repr b := h; rw [← parseInt?_repr a, ← parseInt?_repr b, h'])

theorem list_append_sep_inj {α : Type} {d : α} {xs₁ xs₂ ys₁ ys₂ : List α}
    (h₁ : d ∉ xs₁) (h₂ : d ∉ xs₂) (heq : xs₁ ++ d :: ys₁ = xs₂ ++ d :: ys₂) : xs₁ = xs₂ ∧ ys₁ = ys₂ := by
  induction xs₁ generalizing xs₂ with
  | nil => cases xs₂ with | nil => exact ⟨rfl, (List.cons.inj heq).2⟩ | cons _ _ => exact absurd (List.cons.inj heq).1 (fun h => h₂ (h ▸ List.mem_cons_self))
  | cons _ _ ih => cases xs₂ with
      | nil => exact absurd (List.cons.inj heq).1.symm (fun h => h₁ (h ▸ List.mem_cons_self))
      | cons _ _ => have ⟨hab, htl⟩ := List.cons.inj heq; have ⟨has, hys⟩ := ih (fun hm => h₁ (.tail _ hm)) (fun hm => h₂ (.tail _ hm)) htl; exact ⟨hab ▸ has ▸ rfl, hys⟩

theorem str_toString (s : String) : toString s = s := rfl
theorem str_append_left_cancel {p x y : String} (h : p ++ x = p ++ y) : x = y :=
  String.ext (List.append_cancel_left (as := p.toList) (by rw [← String.toList_append, ← String.toList_append, h]))
theorem str_append_right_cancel {s x y : String} (h : x ++ s = y ++ s) : x = y :=
  String.ext (List.append_cancel_right (bs := s.toList) (by rw [← String.toList_append, ← String.toList_append, h]))

theorem str_split_sep_inj {sep a₁ a₂ r₁ r₂ : String} {d : Char}
    (hsep : sep.toList.head? = some d) (h₁ : d ∉ a₁.toList) (h₂ : d ∉ a₂.toList)
    (heq : a₁ ++ (sep ++ r₁) = a₂ ++ (sep ++ r₂)) : a₁ = a₂ ∧ r₁ = r₂ := by
  have htl := congrArg String.toList heq; simp only [String.toList_append] at htl
  cases hsp : sep.toList with
  | nil => rw [hsp] at hsep; cases hsep
  | cons _ _ => rw [hsp] at hsep htl; cases hsep; have ⟨ha, hrest⟩ := list_append_sep_inj h₁ h₂ htl; exact ⟨String.ext ha, String.ext (List.append_cancel_left hrest)⟩

private theorem list_append_ne_of_diff_prefix {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {p₁ p₂ x y : List α}, (p₁.zip p₂).any (fun ab => ab.1 != ab.2) = true → p₁ ++ x = p₂ ++ y → False
  | [], _, _, _, h, _ | _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _, _, h, heq => by
      have ⟨hab, htl⟩ := List.cons.inj heq; simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_true, bne_iff_ne] at h
      exact h.elim (· hab) (list_append_ne_of_diff_prefix · htl)

theorem str_append_ne_of_diff_prefix {p₁ p₂ x y : String} (hdiff : (p₁.toList.zip p₂.toList).any (fun ab => ab.1 != ab.2) = true) (heq : p₁ ++ x = p₂ ++ y) : False :=
  list_append_ne_of_diff_prefix hdiff (by simpa [String.toList_append] using congrArg String.toList heq)
theorem str_not_mem_append {a b : String} {d : Char} (ha : d ∉ a.toList) (hb : d ∉ b.toList) : d ∉ (a ++ b).toList := fun hm => (List.mem_append.1 (String.toList_append ▸ hm)).elim ha hb
theorem str_not_mem_of_toList_all {s : String} {p : Char → Bool} {d : Char} (hall : s.toList.all p = true) (hd : p d = false) : d ∉ s.toList := fun hm => Bool.false_ne_true (hd ▸ List.all_eq_true.1 hall d hm)
theorem str_not_mem_of_all {s : String} {p : Char → Bool} {d : Char} (hall : s.all p = true) (hd : p d = false) : d ∉ s.toList := str_not_mem_of_toList_all (String.all_bool_eq ▸ hall) hd
theorem str_not_mem_of_forall {s : String} {P : Char → Prop} {d : Char} (h : ∀ c ∈ s.toList, P c) (hd : ¬ P d) : d ∉ s.toList := fun hm => hd (h d hm)
theorem str_not_mem_of_contains_false {s : String} {d : Char} (h : s.contains d = false) : d ∉ s.toList := by rwa [String.contains_char_eq, decide_eq_false_iff_not] at h
theorem str_not_mem_of_not_contains {s : String} {d : Char} (h : ¬ s.contains d = true) : d ∉ s.toList := by rwa [String.contains_char_eq, decide_eq_true_eq] at h
theorem str_not_mem_of_mem_list {s : String} {xs : List String} {d : Char} (hmem : s ∈ xs) (hall : xs.all (fun x => !x.toList.contains d) = true) : d ∉ s.toList :=
  fun hm => Bool.false_ne_true (((Bool.not_eq_true' _).mp (List.all_eq_true.1 hall s hmem)) ▸ List.contains_iff_mem.2 hm)
theorem str_not_mem_of_mem_array {s : String} {xs : Array String} {d : Char} (hmem : s ∈ xs) (hall : xs.toList.all (fun x => !x.toList.contains d) = true) : d ∉ s.toList := str_not_mem_of_mem_list (Array.mem_def.1 hmem) hall
theorem str_all_of_mem_list {s : String} {xs : List String} {p : Char → Bool} (hmem : s ∈ xs) (hall : xs.all (fun x => x.toList.all p) = true) : s.toList.all p = true := List.all_eq_true.1 hall s hmem
theorem str_all_of_mem_array {s : String} {xs : Array String} {p : Char → Bool} (hmem : s ∈ xs) (hall : xs.toList.all (fun x => x.toList.all p) = true) : s.toList.all p = true := str_all_of_mem_list (Array.mem_def.1 hmem) hall
theorem list_all_mono {α : Type} {p₁ p₂ : α → Bool} {xs : List α} (h : xs.all p₁ = true) (himp : ∀ x, p₁ x = true → p₂ x = true) : xs.all p₂ = true := List.all_eq_true.2 fun x hx => himp x (List.all_eq_true.1 h x hx)
theorem str_length_bounds_of_mem_list {s : String} {xs : List String} {lo hi : Nat} (hmem : s ∈ xs) (hall : xs.all (fun x => decide (lo ≤ x.length ∧ x.length ≤ hi)) = true) : lo ≤ s.length ∧ s.length ≤ hi := of_decide_eq_true (List.all_eq_true.1 hall s hmem)
theorem str_length_bounds_of_mem_array {s : String} {xs : Array String} {lo hi : Nat} (hmem : s ∈ xs) (hall : xs.toList.all (fun x => decide (lo ≤ x.length ∧ x.length ≤ hi)) = true) : lo ≤ s.length ∧ s.length ≤ hi := str_length_bounds_of_mem_list (Array.mem_def.1 hmem) hall

theorem dite_eq_cases.{u} {α : Sort u} {c : Prop} [Decidable c] {t : c → α} {e : ¬c → α} {v : α} {P : Prop} (heq : (if h : c then t h else e h) = v) (ht : ∀ h : c, t h = v → P) (hf : ∀ h : ¬c, e h = v → P) : P :=
  if h : c then ht h (by rwa [dite_eq_left h] at heq) else hf h (by rwa [dite_eq_right h] at heq)
theorem eq_dite_cases.{u} {α : Sort u} {c : Prop} [Decidable c] {t : c → α} {e : ¬c → α} {v : α} {P : Prop} (heq : v = (if h : c then t h else e h)) (ht : ∀ h : c, v = t h → P) (hf : ∀ h : ¬c, v = e h → P) : P :=
  dite_eq_cases heq.symm (fun h htv => ht h htv.symm) (fun h hev => hf h hev.symm)
theorem ite_eq_cases.{u} {α : Sort u} {c : Prop} [Decidable c] {t e v : α} {P : Prop} (heq : (if c then t else e) = v) (ht : c → t = v → P) (hf : ¬c → e = v → P) : P :=
  if h : c then ht h (by rwa [ite_eq_left h] at heq) else hf h (by rwa [ite_eq_right h] at heq)
theorem eq_ite_cases.{u} {α : Sort u} {c : Prop} [Decidable c] {t e v : α} {P : Prop} (heq : v = (if c then t else e)) (ht : c → v = t → P) (hf : ¬c → v = e → P) : P :=
  ite_eq_cases heq.symm (fun h htv => ht h htv.symm) (fun h hev => hf h hev.symm)

attribute [irreducible] splitChar

def listStartsWith {α : Type} [BEq α] : List α → List α → Bool | _, [] => true | [], _ :: _ => false | a :: as, b :: bs => a == b && listStartsWith as bs
def listContains {α : Type} [BEq α] (needle : List α) : List α → Bool | [] => needle.isEmpty | xs@(_ :: tl) => listStartsWith xs needle || listContains needle tl
def containsBytes (haystack needle : String) : Bool := if needle.utf8ByteSize == 0 then true else listContains needle.toByteArray.data.toList haystack.toByteArray.data.toList
def containsAllBytes (haystack : String) (needles : List String) : Bool :=
  let hbs := haystack.toByteArray.data.toList; needles.all fun n => if n.utf8ByteSize == 0 then true else listContains n.toByteArray.data.toList hbs
def containsNoneBytes (haystack : String) (needles : List String) : Bool :=
  let hbs := haystack.toByteArray.data.toList; needles.all fun n => if n.utf8ByteSize == 0 then false else !listContains n.toByteArray.data.toList hbs

end Str

end Qed
