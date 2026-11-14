import Std.Data.String.ToNat
import Std.Data.String.ToInt
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

private def hexDigit (n : UInt8) : Char :=
  let d := n.toNat
  Char.ofNat (if d < 10 then 48 + d else 55 + d)

private def isUnreserved (b : UInt8) : Bool :=
  let c := b.toNat
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
    || c == 45 || c == 95 || c == 46 || c == 126

def encodeSeg (s : String) : String := Id.run do
  let bs := s.toUTF8
  let mut out := ""
  for i in [0:bs.size] do
    let b := bs.get! i
    if isUnreserved b then out := out.push (Char.ofNat b.toNat)
    else out := ((out.push '%').push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0F))
  return out

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

def Router.toURL {α} [Router α] (a : α) : String :=
  "/" ++ String.intercalate "/" ((Router.print a).map encodeSeg)

def stripQueryAndHash (path : String) : String :=
  (((path.splitOn "#").headD path).splitOn "?").headD ""

def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse ((((stripQueryAndHash path).splitOn "/").filter (· ≠ "")).map decodeSeg)

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

syntax routeBinder := "(" ident " : " term ")"
syntax routeAlt := ("*")? ident (routeBinder)* (" => " str)?
syntax (name := routerCmd) "router " ident " where " sepBy1IndentSemicolon(routeAlt) : command

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
        let (marked, c, bs, bts, seg) ← (match alt with
          | `(routeAlt| * $c:ident $[($bs:ident : $bts:term)]* $[=> $seg:str]?) =>
              pure (true,  c, bs, bts, seg)
          | `(routeAlt| $c:ident $[($bs:ident : $bts:term)]* $[=> $seg:str]?) =>
              pure (false, c, bs, bts, seg)
          | _ => Macro.throwErrorAt alt "router: couldn't read this route. Each one is a constructor name, then zero or more typed params like (slug : String), then an optional path override; mark the not-found fallback with a leading *.")
        let bs : Array (TSyntax `ident) := bs
        let btsArr : Array (TSyntax `term) := bts
        let ctorId := mkIdent (t.getId ++ c.getId)
        let segs : Array (TSyntax `term) :=
          match seg with
          | some s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray.map (quote ·)
          | none   => #[quote (toString c.getId)]
        let printTerms ← bs.mapM fun b => do
          let bTerm : TSyntax `term := ⟨b.raw⟩
          `(RouteParam.toSeg $bTerm)
        let printSeg := segs ++ printTerms
        let parseSeg := segs ++ bs.map (fun b => (⟨b.raw⟩ : TSyntax `term))
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
        ctorBts   := ctorBts.push bts
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
