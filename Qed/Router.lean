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

/-- Render a value to a URL string, e.g. `Route.user "ada"` ↦ `"/users/ada"`. -/
def Router.toURL {α} [Router α] (a : α) : String :=
  "/" ++ String.intercalate "/" (Router.print a)

/-- Parse a URL path string (`"/users/ada"`) into a route, splitting on `/` and
    dropping empty segments (so `"/"` is the index, `[]`). `none` if no route matches. -/
def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse ((path.splitOn "/").filter (· ≠ ""))

/-! ### The `router` command

`router T where …` declares the page enum *and* its lawful `Router` instance from
one table; each line is a constructor:

    router Route where
      home => ""                       -- the index route `/`  (empty path)
      about                            -- `/about`   (segment = constructor name)
      post (slug : String) => "posts"  -- `/posts/<slug>`
      user (name : String) => "users"  -- `/users/<name>`

A route's path is its leading segment followed by its string arguments. The
leading segment defaults to the constructor name; `=> "seg"` overrides it, and
`=> ""` makes the path empty (the index). The command generates `T.print`,
`T.parse`, the `T.round_trip` proof (`parse (print r) = some r`, by case
analysis), the `Router T` instance — so an unlawful router is impossible and
none of it is written by hand — and `Repr`/`DecidableEq`/`Inhabited` (the last so a
typed `ui (onRoute := …)` can `default` the route on an unknown URL; the table needs
at least one no-argument route, e.g. the index). Fields use one-per-line or
`;`-separated layout. Core-syntax only (no `import Lean`). -/

syntax routeBinder := "(" ident " : " term ")"
syntax routeAlt := ident (routeBinder)* (" => " str)?
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
      for alt in alts do
        match alt with
        | `(routeAlt| $c:ident $[($bs:ident : $bts:term)]* $[=> $seg:str]?) =>
            let ctorId := mkIdent (t.getId ++ c.getId)
            -- leading segment(s): "" ⇒ index (no segment); a string ⇒ that segment;
            -- omitted ⇒ the constructor name.
            let segs : Array (TSyntax `term) :=
              match seg with
              | some s => if s.getString == "" then #[] else #[quote s.getString]
              | none   => #[quote (toString c.getId)]
            let bterms : Array (TSyntax `term) := bs.map (⟨·.raw⟩)
            let segments := segs ++ bterms          -- one list, used as term and pattern
            ctorNames := ctorNames.push c
            ctorBs    := ctorBs.push bs
            ctorBts   := ctorBts.push bts
            printPats := printPats.push (← `($ctorId $bs*))
            printRhss := printRhss.push (← `([$segments,*]))
            parsePats := parsePats.push (← `([$segments,*]))
            parseRhss := parseRhss.push (← `(some ($ctorId $bs*)))
        | _ => Macro.throwErrorAt alt "router: expected `ctor (arg : T)* (=> \"segment\")?`"
      let parsePatsAll := parsePats.push (← `(_))           -- final wildcard ⇒ none
      let parseRhssAll := parseRhss.push (← `(none))
      `(inductive $t:ident where
          $[| $ctorNames:ident $[($ctorBs:ident : $ctorBts:term)]*]*
        deriving Repr, DecidableEq, Inhabited
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
