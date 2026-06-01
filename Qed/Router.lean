/-
  Qed.Router — typed routes that round-trip with their URLs, by proof (dream-API #4).

  A `Router` instance must supply `print`, `parse`, **and** a proof that parsing a
  printed route recovers it exactly. The law is a *field of the class*, so an
  instance simply cannot exist without the round-trip guarantee — there is no way
  to ship a router whose URLs don't round-trip. No route is unreachable, and no
  printed URL fails to parse back to the route that produced it.

  A path is modelled as its list of segments (`/posts/hello` ↦ `["posts","hello"]`),
  which keeps the round-trip proof a clean case analysis.
-/
namespace Qed

/-- A bijective-on-its-image encoding of `α` to/from URL path segments. -/
class Router (α : Type) where
  /-- Render a value to URL path segments. -/
  print : α → List String
  /-- Parse path segments back to a value (or `none` if they match no route). -/
  parse : List String → Option α
  /-- The guarantee: printing then parsing is the identity. -/
  round_trip : ∀ a, parse (print a) = some a

/-! ### Percent-coding for the URL string boundary

`print`/`parse` work on segment *lists* and are proven to round-trip (`round_trip`). The
URL is a *string*, and joining segments with `/` is only reversible if a segment can't
itself contain `/` (or other URL-structural characters). So `toURL`/`fromURL` percent-code
each segment on the way in and out. This is the trusted string⟷segments shim — the same
kind of boundary as the driver (Html⟷DOM) or the renderer (Html⟷markup): the *semantics*
(which segments map to which route) is verified; the byte-level codec is a small total
function. With it, a param like `"C++ & Lean"` survives the round trip a browser puts it
through, instead of corrupting the path. -/

private def hexDigit (n : UInt8) : Char :=
  let d := n.toNat
  Char.ofNat (if d < 10 then 48 + d else 55 + d)   -- 0–9, then 'A'–'F'

private def isUnreserved (b : UInt8) : Bool :=
  let c := b.toNat
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
    || c == 45 || c == 95 || c == 46 || c == 126   -- - _ . ~

/-- Percent-encode a path segment (`encodeURIComponent`): unreserved bytes stay, every
    other UTF-8 byte becomes `%XX`. So an encoded segment never contains `/`, making the
    `/`-join in `toURL` reversible. -/
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
      | _,       _       => decodeBytes (h :: l :: rest) (acc.push 37)   -- stray '%', keep it
  | c :: rest, acc => decodeBytes rest (acc ++ c.toString.toUTF8)
  | [], acc => acc

/-- Invert `encodeSeg`: turn `%XX` back into its byte, pass others through. A malformed
    `%` is kept literally, so decoding is total. -/
def decodeSeg (s : String) : String :=
  (String.fromUTF8? (decodeBytes s.toList .empty)).getD s

/-- Render a value to a URL string, e.g. `Route.user "ada"` ↦ `"/users/ada"`; each segment
    is percent-encoded so a param with a `/` or a space can't break the path. -/
def Router.toURL {α} [Router α] (a : α) : String :=
  "/" ++ String.intercalate "/" ((Router.print a).map encodeSeg)

/-- Parse a URL path string (`"/users/ada"`) into a route: split on `/`, drop empty
    segments (so `"/"` is the index, `[]`), percent-decode each, then `parse`. `none` if no
    route matches. -/
def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse (((path.splitOn "/").filter (· ≠ "")).map decodeSeg)

/-! ### The `router` command

`router T where …` declares the page enum *and* its lawful `Router` instance from
one table; each line is a constructor:

    router Route where
      home => ""                       -- the index route `/`  (empty path)
      about                            -- `/about`   (segment = constructor name)
      post (slug : String) => "posts"  -- `/posts/<slug>`
      user (name : String) => "users"  -- `/users/<name>`
      * notFound => "404"              -- the fallback for an unknown URL (no args)

A route's path is its leading segment followed by its string arguments. The
leading segment defaults to the constructor name; `=> "seg"` overrides it (and a
`"/"` in the override is split into several segments, so `=> "books/new"` is two);
`=> ""` makes the path empty (the index). A leading `*` marks the *not-found*
route — a no-argument route that an unknown URL falls back to (it is the route's
`Inhabited` default, so `(fromURL p).getD default` lands on it); without one, the
default is the first constructor, as before. The command generates `T.print`,
`T.parse`, the `T.round_trip` proof (`parse (print r) = some r`, by case
analysis), the `Router T` instance — so an unlawful router is impossible and none
of it is written by hand — and `Repr`/`DecidableEq`/`Inhabited`. Fields use
one-per-line or `;`-separated layout. Core-syntax only (no `import Lean`). -/

syntax routeBinder := "(" ident " : " term ")"
syntax routeAlt := ("*")? ident (routeBinder)* (" => " str)?
syntax (name := routerCmd) "router " ident " where " sepBy1IndentSemicolon(routeAlt) : command

open Lean in
macro_rules
  | `(router $t:ident where $[$alts:routeAlt]*) => do
      let printId := mkIdent (t.getId ++ `print)
      let parseId := mkIdent (t.getId ++ `parse)
      let rtId    := mkIdent (t.getId ++ `round_trip)
      -- Parallel arrays, spliced into one core quotation below (no `Lean.Parser`
      -- categories, so this stays compilable without `import Lean`).
      let mut ctorNames : Array (TSyntax `ident) := #[]
      let mut ctorBs    : Array (Array (TSyntax `ident)) := #[]   -- binders per ctor
      let mut ctorBts   : Array (Array (TSyntax `term))  := #[]
      let mut printPats : Array (TSyntax `term) := #[]
      let mut printRhss : Array (TSyntax `term) := #[]
      let mut parsePats : Array (TSyntax `term) := #[]
      let mut parseRhss : Array (TSyntax `term) := #[]
      let mut markedCtor : Option (TSyntax `ident) := none
      for alt in alts do
        -- `* ctor …` marks the not-found route; normalize both forms to one body.
        let (marked, c, bs, bts, seg) ← (match alt with
          | `(routeAlt| * $c:ident $[($bs:ident : $bts:term)]* $[=> $seg:str]?) =>
              pure (true,  c, bs, bts, seg)
          | `(routeAlt| $c:ident $[($bs:ident : $bts:term)]* $[=> $seg:str]?) =>
              pure (false, c, bs, bts, seg)
          | _ => Macro.throwErrorAt alt "router: expected `[*] ctor (arg : T)* (=> \"segment\")?`")
        -- A parameter is a URL segment verbatim, so only `String` round-trips *by proof* (a
        -- `Nat`/`Int` would need `(toString n).toNat? = some n`, which has no library lemma, so
        -- the generated `round_trip` would not close). Reject other types with a
        -- clear message instead of a confusing error inside the generated code. (Iterate a plain
        -- `Array` copy so `bts` keeps the `TSyntaxArray` type the splices below need.)
        let btsArr : Array (TSyntax `term) := bts
        for bt in btsArr do
          match bt with
          | `(String) => pure ()
          | _ => Macro.throwErrorAt bt
                   "router: a route parameter must have type `String`; decode richer types from \
                    the String in your `update` (a verified non-String URL round-trip isn't supported)"
        let ctorId := mkIdent (t.getId ++ c.getId)
        -- leading segment(s): "" ⇒ index (no segment); a string ⇒ those segments
        -- (split on `/`, so `=> "books/archive"` is two segments and stays reachable);
        -- omitted ⇒ the constructor name.
        let segs : Array (TSyntax `term) :=
          match seg with
          | some s => ((s.getString.splitOn "/").filter (· ≠ "")).toArray.map (quote ·)
          | none   => #[quote (toString c.getId)]
        let bterms : Array (TSyntax `term) := bs.map (⟨·.raw⟩)
        let segments := segs ++ bterms          -- one list, used as term and pattern
        if marked then
          if bs.size != 0 then
            Macro.throwErrorAt c "router: the not-found route (marked `*`) must take no arguments"
          markedCtor := some c
        ctorNames := ctorNames.push c
        ctorBs    := ctorBs.push bs
        ctorBts   := ctorBts.push bts
        printPats := printPats.push (← `($ctorId $bs*))
        printRhss := printRhss.push (← `([$segments,*]))
        parsePats := parsePats.push (← `([$segments,*]))
        parseRhss := parseRhss.push (← `(some ($ctorId $bs*)))
      let parsePatsAll := parsePats.push (← `(_))           -- final wildcard ⇒ none
      let parseRhssAll := parseRhss.push (← `(none))
      -- The `*`-marked route is what a routed app falls back to on an unknown URL (it is the
      -- `Inhabited` default `fromURL … |>.getD default` lands on). Unmarked ⇒ derive it as before.
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
          intro a; cases a <;> simp [$printId:ident, $parseId:ident]
        instance : Router $t:ident := ⟨$printId, $parseId, $rtId⟩)

/-! ### An example route table

`Route` is the application's pages; `router` also generates its lawful `Router`
instance (`Route.print`/`Route.parse`/`Route.round_trip`). -/

router Route where
  home => ""
  about
  post (slug : String) => "posts"
  user (name : String) => "users"

end Qed
