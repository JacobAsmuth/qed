import Std.Data.String.ToNat
import Std.Data.String.ToInt
import Qed.Html
import Qed.Json

namespace Qed

class RouteParam (α : Type) where
  toSeg      : α → String
  fromSeg    : String → Option α
  round_trip : ∀ a, fromSeg (toSeg a) = some a

attribute [simp] RouteParam.round_trip

instance : RouteParam String := ⟨id, some, fun _ => rfl⟩
instance : RouteParam Nat    := ⟨Nat.repr, String.toNat?, Nat.toNat?_repr⟩
instance : RouteParam Int    := ⟨Int.repr, String.toInt?, Int.toInt?_repr⟩

@[simp] theorem RouteParam.toSeg_string (s : String) : RouteParam.toSeg s = s := rfl

class Router (α : Type) where
  print      : α → List String
  parse      : List String → Option α
  round_trip : ∀ a, parse (print a) = some a

instance [Router R] : ToJson R := ⟨fun r => toJson (Router.print r)⟩
instance [Router R] : FromJson R := ⟨fun j => do
  let segs ← (fromJson j : Except String (List String))
  (Router.parse segs).elim (.error "invalid route") .ok⟩
instance [Router R] : LawfulJson R where
  depthBound := 1
  depth_toJson r := LawfulJson.depth_toJson (Router.print r)
  fromJson_toJson r := by
    change (fromJson (toJson (Router.print r)) : Except String (List String)).bind
      (fun segs => (Router.parse segs).elim (.error "invalid route") .ok) = .ok r
    rw [LawfulJson.fromJson_toJson (Router.print r)]
    change (Router.parse (Router.print r)).elim _ _ = _
    rw [Router.round_trip]; rfl

class LawfulKey (α : Type) where
  toKey     : α → String
  injective : ∀ a₁ a₂ : α, toKey a₁ = toKey a₂ → a₁ = a₂

instance : LawfulKey String where
  toKey := id
  injective _ _ h := h

instance : LawfulKey Nat where
  toKey := Nat.repr
  injective a₁ a₂ h := by
    have := congrArg String.toNat? h
    simpa [Nat.toNat?_repr] using this

instance : LawfulKey Int where
  toKey := Int.repr
  injective a₁ a₂ h := by
    have := congrArg String.toInt? h
    simpa [Int.toInt?_repr] using this

instance : LawfulKey Bool where
  toKey | true => "1" | false => "0"
  injective a₁ a₂ h := by cases a₁ <;> cases a₂ <;> simp_all

instance (priority := low) {α : Type} [LawfulJson α] : LawfulKey α where
  toKey a := Json.render (toJson a)
  injective a₁ a₂ h := by
    have h₁ := LawfulJson.parse_render_toJson a₁ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    have h₂ := LawfulJson.parse_render_toJson a₂ (maxDepth := LawfulJson.depthBound α) (Nat.le_refl _)
    rw [h] at h₁
    rw [h₁] at h₂
    exact Except.ok.inj h₂

private def hexDigit (n : UInt8) : Char :=
  match n.toNat % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E'
  | _ => 'F'

private def isUnreserved (b : UInt8) : Bool :=
  let c := b.toNat
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
    || c == 45 || c == 95 || c == 46 || c == 126

@[inline] private def isSafePathBodyChar (c : Char) : Bool :=
  isSafeUrlChar c && c.toNat != 92

private theorem isSafePathBodyChar_hexDigit (n : UInt8) :
    isSafePathBodyChar (hexDigit n) = true := by
  unfold hexDigit
  split <;> rfl

private theorem isSafePathBodyChar_unreserved {b : UInt8} (h : isUnreserved b = true) :
    isSafePathBodyChar (Char.ofNat b.toNat) = true := by
  unfold isUnreserved at h
  have hb : b.toNat ≤ 126 ∧ b.toNat ≥ 45 ∧ b.toNat ≠ 92 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    omega
  have hv : b.toNat.isValidChar := by
    simp [Nat.isValidChar]; omega
  have htn : (Char.ofNat b.toNat).toNat = b.toNat := by
    simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
  unfold isSafePathBodyChar isSafeUrlChar
  rw [htn]
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]
  omega

private def encodeUTF8Loop (bs : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < bs.size then
    let b := bs[i]
    let next := if isUnreserved b then acc.push (Char.ofNat b.toNat)
                else ((acc.push '%').push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0F))
    encodeUTF8Loop bs (i + 1) next
  else acc
termination_by bs.size - i

private theorem encodeUTF8Loop_safe (bs : ByteArray) :
    ∀ (i : Nat) (acc : String),
      acc.toList.all isSafePathBodyChar = true →
      (encodeUTF8Loop bs i acc).toList.all isSafePathBodyChar = true := by
  intro i
  induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc hacc
      unfold encodeUTF8Loop
      have hnot : ¬ i < bs.size := by omega
      simp [hnot, hacc]
  | succ k ih =>
      intro acc hacc
      unfold encodeUTF8Loop
      have hlt : i < bs.size := by omega
      simp only [hlt, ↓reduceDIte]
      apply ih (i + 1) (by omega)
      by_cases hu : isUnreserved bs[i]
      · simp [hu, String.toList_push, hacc, isSafePathBodyChar_unreserved hu]
      · have hpct : isSafePathBodyChar '%' = true := rfl
        simp [hu, String.toList_push, hacc, hpct, isSafePathBodyChar_hexDigit]

def encodeSeg (s : String) : String :=
  encodeUTF8Loop s.toUTF8 0 ""

theorem encodeSeg_safe (s : String) :
    (encodeSeg s).toList.all isSafePathBodyChar = true :=
  encodeUTF8Loop_safe s.toUTF8 0 "" rfl

private def unhex (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (UInt8.ofNat (n - 48))
  else if 65 ≤ n && n ≤ 70 then some (UInt8.ofNat (n - 55))
  else if 97 ≤ n && n ≤ 102 then some (UInt8.ofNat (n - 87))
  else none

private def decodeBytes : List Char → ByteArray → ByteArray
  | '%' :: h :: l :: rest, acc =>
      match unhex h, unhex l with
      | some hi, some lo => decodeBytes rest (acc.push ((hi <<< 4) ||| lo))
      | _,       _       => decodeBytes (h :: l :: rest) (acc.push 37)
  | c :: rest, acc => decodeBytes rest (acc ++ c.toString.toUTF8)
  | [], acc => acc

def decodeSeg (s : String) : String :=
  (String.fromUTF8? (decodeBytes s.toList .empty)).getD s

private def joinSlash : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ "/" ++ joinSlash ss

private theorem joinSlash_safe :
    ∀ (segs : List String),
      (∀ s ∈ segs, s.toList.all isSafePathBodyChar = true) →
      (joinSlash segs).toList.all isSafePathBodyChar = true
  | [], _ => rfl
  | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by
      have hslash : isSafePathBodyChar '/' = true := rfl
      have ih := joinSlash_safe (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      simp [joinSlash, String.toList_append, hs s₁ (by simp), hslash, ih]

private theorem dropWhile_slash_safe :
    ∀ (cs : List Char),
      cs.all isSafePathBodyChar = true →
      hasSafeUrlPrefix ('/' :: cs.dropWhile (· == '/')) = true ∧
      ('/' :: cs.dropWhile (· == '/')).all isSafeUrlChar = true
  | [], _ => ⟨rfl, rfl⟩
  | c :: rest, hcs => by
      simp only [List.all_cons, Bool.and_eq_true] at hcs
      rcases hcs with ⟨hc, hrest⟩
      by_cases hslash : (c == '/') = true
      · simpa [List.dropWhile, hslash] using dropWhile_slash_safe rest hrest
      · have hcf : (c == '/') = false := Bool.eq_false_iff.2 hslash
        simp only [List.dropWhile, hcf]
        unfold isSafePathBodyChar at hc
        rcases Bool.and_eq_true_iff.1 hc with ⟨hcUrl, hcNot92⟩
        have hnotBs : (c != '\\') = true := by
          rw [bne_iff_ne]
          intro heq; subst heq; simp at hcNot92
        have hnotSlash : (c != '/') = true := by
          rw [bne_iff_ne]
          intro heq; subst heq; simp at hcf
        have hrestUrl : rest.all isSafeUrlChar = true := by
          rw [List.all_eq_true] at hrest ⊢
          intro x hx
          exact (Bool.and_eq_true_iff.1 (hrest x hx)).1
        have hslashUrl : isSafeUrlChar '/' = true := rfl
        exact ⟨by simp [hasSafeUrlPrefix, hnotSlash, hnotBs],
               by simp [List.all_cons, hslashUrl, hcUrl, hrestUrl]⟩

def Router.toURL {α} [Router α] (a : α) : String :=
  String.ofList ('/' :: (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/'))

@[simp] theorem Router.isSafeUrl_toURL {α : Type} [Router α] (a : α) :
    isSafeUrl (Router.toURL a) = true := by
  unfold Router.toURL isSafeUrl
  rw [String.toList_ofList]
  have hbody : (joinSlash ((Router.print a).map encodeSeg)).toList.all isSafePathBodyChar = true := by
    apply joinSlash_safe
    intro s hs
    rcases List.mem_map.1 hs with ⟨raw, _, rfl⟩
    exact encodeSeg_safe raw
  have ⟨hpfx, hall⟩ := dropWhile_slash_safe _ hbody
  exact Bool.and_eq_true_iff.2 ⟨hpfx, hall⟩

def Router.toUrl {α : Type} [Router α] (a : α) : Url :=
  ⟨Router.toURL a, Router.isSafeUrl_toURL a⟩

def stripQueryAndHash (path : String) : String :=
  (((path.splitOn "#").headD path).splitOn "?").headD ""

def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse ((((stripQueryAndHash path).splitOn "/").filter (· ≠ "")).map decodeSeg)

class ToHref (α : Type) where
  toUrl : α → Url

def ToHref.toHref {α : Type} [ToHref α] (v : α) : String := (ToHref.toUrl v).raw

instance : ToHref Url := ⟨id⟩
instance [Router R] : ToHref R := ⟨Router.toUrl⟩

@[simp] theorem ToHref.toUrl_url (u : Url) : ToHref.toUrl u = u := rfl
@[simp] theorem ToHref.toHref_url (u : Url) : ToHref.toHref u = u.raw := rfl
@[simp] theorem ToHref.toHref_route {R : Type} [Router R] (r : R) :
    ToHref.toHref r = Router.toURL r := rfl
@[simp] theorem ToHref.isSafeUrl_toHref {α : Type} [ToHref α] (v : α) :
    isSafeUrl (ToHref.toHref v) = true := (ToHref.toUrl v).safe

syntax routeEnumAlt := ident (" => " str)?
syntax (name := routeEnumCmd) "route_enum " ident " where " sepBy1IndentSemicolon(routeEnumAlt) : command

open Lean in
macro_rules
  | `(route_enum $t:ident where $[$alts:routeEnumAlt]*) => do
      let toSegId   := mkIdent (t.getId ++ `toSeg)
      let fromSegId := mkIdent (t.getId ++ `fromSeg)
      let rtId      := mkIdent (t.getId ++ `round_trip)
      let mut ctors : Array (TSyntax `ident) := #[]
      let mut ctorPats : Array (TSyntax `term) := #[]
      let mut slugs : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      for alt in alts do
        let (c, seg) ← match alt with
          | `(routeEnumAlt| $c:ident $[=> $seg:str]?) => pure (c, seg)
          | _ => Macro.throwErrorAt alt "route_enum: expected constructor name with optional `=> \"slug\"`"
        let ctorId := mkIdent (t.getId ++ c.getId)
        let slugLit : TSyntax `term := match seg with
          | some s => ⟨s.raw⟩
          | none   => quote (toString c.getId)
        ctors     := ctors.push c
        ctorPats  := ctorPats.push ctorId
        slugs     := slugs.push slugLit
        parseRhss := parseRhss.push (← `(some $ctorId))
      let parsePatsAll := slugs.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      `(inductive $t:ident where
          $[| $ctors:ident]*
        deriving Repr, DecidableEq, Inhabited
        def $toSegId:ident (x : $t) : String :=
          match x with
          $[| $ctorPats:term => $slugs:term]*
        def $fromSegId:ident (s : String) : Option $t :=
          match s with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $fromSegId:ident ($toSegId:ident a) = some a := by
          intro a; cases a <;> rfl
        instance : RouteParam $t:ident := ⟨$toSegId, $fromSegId, $rtId⟩)

syntax routeBinder := "(" ident (" : " term)? ")"
syntax routeAlt := ("*")? ident (routeBinder)* (" => " str)?
syntax (name := routerCmd) "router " ident " where " sepBy1IndentSemicolon(routeAlt) : command

open Lean in
private def parseRouteBinder (b : TSyntax ``routeBinder) : MacroM (TSyntax `ident × TSyntax `term) := do
  match b with
  | `(routeBinder| ($id:ident : $ty:term)) => pure (id, ty)
  | `(routeBinder| ($id:ident))            => pure (id, ← `(String))
  | _ => Macro.throwErrorAt b "router: expected `(param)` or `(param : Type)`"

open Lean in
macro_rules
  | `(router $t:ident where $[$alts:routeAlt]*) => do
      let printId := mkIdent (t.getId ++ `print)
      let parseId := mkIdent (t.getId ++ `parse)
      let rtId    := mkIdent (t.getId ++ `round_trip)
      let mut ctorNames : Array (TSyntax `ident) := #[]
      let mut ctorBs    : Array (Array (TSyntax `ident)) := #[]
      let mut ctorBts   : Array (Array (TSyntax `term))  := #[]
      let mut printPats : Array (TSyntax `term) := #[]
      let mut printRhss : Array (TSyntax `term) := #[]
      let mut parsePats : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      let mut markedCtor : Option (TSyntax `ident) := none
      for alt in alts do
        let (marked, c, rawBinders, seg) ← (match alt with
          | `(routeAlt| * $c:ident $[$rbs:routeBinder]* $[=> $seg:str]?) =>
              pure (true,  c, rbs, seg)
          | `(routeAlt| $c:ident $[$rbs:routeBinder]* $[=> $seg:str]?) =>
              pure (false, c, rbs, seg)
          | _ => Macro.throwErrorAt alt "router: couldn't read this route. Each one is a constructor name, then zero or more params like (slug : String) or (slug), then an optional path like \"/books/:id\"; mark the not-found fallback with a leading *.")
        let explicitBinders ← rawBinders.mapM parseRouteBinder
        let rawSegs : Array String := match seg with
          | some s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray
          | none   => #[toString c.getId]
        let hasPlaceholders := rawSegs.any (·.startsWith ":")
        let mut bs     : Array (TSyntax `ident) := #[]
        let mut btsArr : Array (TSyntax `term)  := #[]
        if hasPlaceholders then
          let mut seenPlaceholders : Array String := #[]
          for rs in rawSegs do
            if rs.startsWith ":" then
              let pname := String.ofList (rs.toList.drop 1)
              if pname.isEmpty then
                Macro.throwErrorAt alt "router: empty `:` parameter in route path"
              if seenPlaceholders.contains pname then
                Macro.throwErrorAt alt s!"router: duplicate `:{pname}` parameter in route path"
              seenPlaceholders := seenPlaceholders.push pname
              match explicitBinders.find? (fun (b, _) => toString b.getId == pname) with
              | some (b, bt) =>
                  bs     := bs.push b
                  btsArr := btsArr.push bt
              | none =>
                  bs     := bs.push (mkIdent (Name.mkSimple pname))
                  btsArr := btsArr.push (← `(String))
          for (b, _) in explicitBinders do
            unless seenPlaceholders.contains (toString b.getId) do
              Macro.throwErrorAt b s!"router: parameter `{b.getId}` is not referenced as `:{b.getId}` in the route path"
        else
          bs     := explicitBinders.map (·.1)
          btsArr := explicitBinders.map (·.2)
        let ctorId := mkIdent (t.getId ++ c.getId)
        let (printSeg, parseSeg) ← if hasPlaceholders then do
          let mut pr : Array (TSyntax `term) := #[]
          let mut pa : Array (TSyntax `term) := #[]
          for rs in rawSegs do
            if rs.startsWith ":" then
              let pname := String.ofList (rs.toList.drop 1)
              let some bId := bs.find? (fun b => toString b.getId == pname)
                | Macro.throwErrorAt alt "router: internal missing param"
              let bTerm : TSyntax `term := ⟨bId.raw⟩
              pr := pr.push (← `(RouteParam.toSeg $bTerm))
              pa := pa.push bTerm
            else
              pr := pr.push (quote rs)
              pa := pa.push (quote rs)
          pure (pr, pa)
        else do
          let segs : Array (TSyntax `term) := rawSegs.map (quote ·)
          let printTerms ← bs.mapM fun b => do
            let bTerm : TSyntax `term := ⟨b.raw⟩
            `(RouteParam.toSeg $bTerm)
          pure (segs ++ printTerms, segs ++ bs.map (fun b => (⟨b.raw⟩ : TSyntax `term)))
        let mut parseBody : TSyntax `term ← `(some ($ctorId $bs*))
        for i in (List.range bs.size).reverse do
          let bTerm : TSyntax `term := ⟨bs[i]!.raw⟩
          let bt := btsArr[i]!
          parseBody ← `(match (RouteParam.fromSeg $bTerm : Option $bt) with | some $bTerm => $parseBody | none => none)
        if marked then
          if bs.size != 0 then
            Macro.throwErrorAt c "router: the not-found route (marked `*`) must take no arguments. It is the fallback for any unmatched URL, so there's nothing to parse into it."
          markedCtor := some c
        ctorNames := ctorNames.push c
        ctorBs    := ctorBs.push bs
        ctorBts   := ctorBts.push btsArr
        printPats := printPats.push (← `($ctorId $bs*))
        printRhss := printRhss.push (← `([$printSeg,*]))
        parsePats := parsePats.push (← `([$parseSeg,*]))
        parseRhss := parseRhss.push parseBody
      let parsePatsAll := parsePats.push (← `(_))
      let parseRhssAll := parseRhss.push (← `(none))
      let inhCmd : TSyntax `command ← match markedCtor with
        | some mc => `(instance : Inhabited $t := ⟨$(mkIdent (t.getId ++ mc.getId))⟩)
        | none    => `(deriving instance Inhabited for $t)
      `(inductive $t:ident where
          $[| $ctorNames:ident $[($ctorBs:ident : $ctorBts:term)]*]*
        deriving Repr, DecidableEq
        $inhCmd:command
        def $printId:ident (r : $t) : List String :=
          match r with
          $[| $printPats:term => $printRhss:term]*
        def $parseId:ident (p : List String) : Option $t :=
          match p with
          $[| $parsePatsAll:term => $parseRhssAll:term]*
        theorem $rtId:ident : ∀ a, $parseId:ident ($printId:ident a) = some a := by
          intro a; cases a <;> simp [$printId:ident, $parseId:ident, RouteParam.round_trip]
        instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩)

router Route where
  home => ""
  about
  post (slug : String) => "posts"
  user (name : String) => "users"

router TypedRoute where
  page (n : Nat) => "page"
  delta (i : Int) => "delta"
  item (slug : String) (n : Nat) => "items"

end Qed
