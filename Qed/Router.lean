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

/-! ### An example route table -/

/-- The application's pages. -/
inductive Route
  | home
  | about
  | post (slug : String)
  | user (name : String)
  deriving DecidableEq, Repr

namespace Route

def print : Route → List String
  | .home      => []
  | .about     => ["about"]
  | .post slug => ["posts", slug]
  | .user name => ["users", name]

def parse : List String → Option Route
  | []               => some .home
  | ["about"]        => some .about
  | ["posts", slug]  => some (.post slug)
  | ["users", name]  => some (.user name)
  | _                => none

/-- The round-trip law, discharged by case analysis — no manual reasoning. -/
theorem round_trip : ∀ r, parse (print r) = some r := by
  intro r; cases r <;> simp [print, parse]

end Route

/-- `Route` is a lawful `Router`; the instance carries the proof. -/
instance : Router Route where
  print      := Route.print
  parse      := Route.parse
  round_trip := Route.round_trip

end Qed
