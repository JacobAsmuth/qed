/-
  Tour 15 · Everything together

  Bookshelf: a small catalog that wires the whole stack into one app: routing, a
  typed remote `Resource` (a list and a single record, fetched and decoded), a
  validated `schema` whose form POSTs and navigates to the result, and scoped styles.

  Three pages, behind the verified router (`R.round_trip`):

    /              the catalog, fetches `/api/books` into `Resource (Array Book)`
    /books/<id>    one book, fetches `/api/books/<id>` into `Resource Book`
    /new           the `schema`-generated form (text/number/select/checkbox, each refined)
                   that, on a valid submit, POSTs the book and routes to its new detail page

  Navigation goes through `link` / `Cmd.pushUrl`, so it never reloads. The server
  renders any page from a model (`Examples/BookshelfSSR.lean`), and the browser
  adopts that markup on load. Pure Lean; the browser entry is `BookshelfWeb.lean`.
-/
import Qed
open Qed

namespace Bookshelf

-- The pages, with a lawful `Router` generated alongside.
router R where
  catalog => ""
  detail (id : String) => "books"
  newBook => "new"

-- Field refinements, shared by the form and the JSON decode. `abbrev` so the `Decidable`
-- instances are inferred.
abbrev NonEmpty (s : String) : Prop := s.length ≥ 1
abbrev Year (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 2026

-- One book, declared once. `schema` generates the editable draft + validated `Book` (each
-- refined field a proof-carrying `Field`), `parse`, the `canSubmit` gate + its proof, the
-- `formView` widgets, and the JSON codec, decode for the GET responses, encode for the POST
-- body. The refinements guard *both* directions, so an out-of-range API record is rejected at
-- decode exactly as the form rejects it at submit. `id` is server-assigned: it rides the JSON
-- but never appears in the form.
schema Book where
  id      : Codec.text.jsonOnly
  title   : Codec.text.refine NonEmpty
  author  : Codec.text.refine NonEmpty
  year    : Codec.nat.refine Year
  genre   : Codec.select [("fiction", "Fiction"), ("nonfiction", "Non-fiction"), ("poetry", "Poetry")]
  inPrint : Codec.checkbox

structure Model where
  route   : R
  catalog : Resource (Array Book)   -- the list page
  current : Resource Book           -- the detail page
  draft   : Book.Draft              -- the add form

def init : Model :=
  { route := .catalog, catalog := .idle, current := .idle, draft := Book.Draft.empty }

inductive Msg where
  | routed     (r : R)                    -- startup / link / back / push, parsed to a route
  | gotCatalog (r : Resource (Array Book))
  | gotBook    (r : Resource Book)
  | edit       (d : Book.Draft)           -- the form hands back the whole draft
  | submit
  | created    (r : Resource Book)        -- the POST resolved (ok with the new book, or failed)

-- One combined transition, written with `steps`: an arm is the next model, or
-- `(next model, effect)`. A page that needs data flips its `Resource` to `.loading` and
-- fires the fetch in the same arm that sets the route.
def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .routed route =>
      match route with
      | .catalog   => ({ m with route := .catalog, catalog := .loading },
                       Resource.fetch "/api/books" Msg.gotCatalog)
      | .detail id =>
          -- keep a book we already hold (e.g. one we just created), else fetch it
          match m.current with
          | .ok b => if b.id == id then { m with route := .detail id }
                     else ({ m with route := .detail id, current := .loading },
                           Resource.fetch s!"/api/books/{id}" Msg.gotBook)
          | _     => ({ m with route := .detail id, current := .loading },
                      Resource.fetch s!"/api/books/{id}" Msg.gotBook)
      | .newBook   => { m with route := .newBook }
  | .gotCatalog r => { m with catalog := r }
  | .gotBook r    => { m with current := r }
  | .edit d       => { m with draft := d }
  | .submit       =>
      -- `Book.parse` yields a valid book (empty id; the server assigns one) only when every
      -- refined field passes, so the POST body is `Book.encode` of that, no separate bridge.
      match Book.parse m.draft with
      | some book => (m, Cmd.postJson "/api/books" (Book.encode book)
                         (fun b => Msg.created (.ok b)) (fun e => Msg.created (.failed e)))
      | none    => m
  | .created r    =>
      match r with
      | .ok b     => ({ m with current := .ok b, draft := Book.Draft.empty },
                      Cmd.pushUrl (Router.toURL (R.detail b.id)))
      | .failed e => { m with current := .failed e }
      | _         => m

/-! Scoped styles, co-located with the view. Each class name is a content hash; the typed
    property helpers (`maxWidth`, `display`, `color`, …) make a misspelled property, not just a
    misspelled reference, a compile error. Raw strings coerce in for compound values, `screenMax`
    is a responsive block, and `brand` is a design token set once in `theme`. -/
def brand : Token := token "brand"
def shell : Style := css [
  maxWidth (rem 40), margin "2rem auto", fontFamily "system-ui, sans-serif", lineHeight "1.5",
  screenMax (px 600) [ margin "1rem", maxWidth (pct 100) ] ]
def topnav : Style := css [
  display .flex, gap (rem 1), prop "margin-bottom" "1.5rem" ]
def navlink : Style := css [
  textDecoration "none", color brand, fontWeight "600" ]
def card : Style := css [
  padding "1rem 1.25rem", border "1px solid #ddd", radius (px 8) ]

def bookList (books : Array Book) : Html Msg :=
  <ul class="books">{books.map fun b =>
    <li key={b.id}>
      {link (Router.toURL (R.detail b.id)) [navlink, cls "book-link"] [text b.title]}
      <span class="byline">{s!" by {b.author}"}</span>
    </li>}</ul>

def bookCard (b : Book) : Html Msg :=
  <div {card} class="book">
    <h1>{text b.title}</h1>
    <p class="author">{s!"by {b.author} ({b.year})"}</p>
    <p class="genre">{b.genre}</p>
    <p class={if b.inPrint then "in-print" else "out-of-print"}>
      {if b.inPrint then "In print" else "Out of print"}</p>
  </div>

/-- Serialize the route + fetched data into the page, so a deep-linked SSR load starts the
    client from the same model the server drew, no flash, no refetch. The route rides the URL
    codec; the catalog/current `Resource`s use their JSON instances; the form draft is left to
    `init` (it's empty on load). -/
def dehydrateModel (m : Model) : String :=
  Json.render (.obj [
    ("route",   .str (Router.toURL m.route)),
    ("catalog", ToJson.toJson m.catalog),
    ("current", ToJson.toJson m.current) ])

def rehydrateModel (s : String) : Option Model :=
  match Json.parse s with
  | .ok j =>
      let res {α} [FromJson α] (key : String) : Resource α :=
        ((j.get? key).bind (fun v => (FromJson.fromJson v : Except String (Resource α)).toOption)).getD .idle
      some { init with
             route   := (((j.get? "route").bind (·.str?)).bind Router.fromURL).getD .catalog
             catalog := res "catalog"
             current := res "current" }
  | _ => none

def appBase : App Model Msg :=
  ui init transition (onRoute := Msg.routed) fun m =>
    <div {shell} class="app">
      {theme [ brand.set "#06c" ]}
      {styleSheet [shell, topnav, navlink, card]}
      <nav {topnav}>
        {link "/" [navlink] ["Catalog"]}
        {link "/new" [navlink] ["Add a book"]}
      </nav>
      {match m.route with
       | .catalog =>
           <div class="catalog">
             <h1>Bookshelf</h1>
             {m.catalog.view (fun books => bookList books)
               (loading := <p class="loading">Loading catalog…</p>)
               (failed  := fun e => <p class="error">{"Error: "}{e}</p>)}
           </div>
       | .detail _ =>
           <div class="detail">
             {m.current.view (fun b => bookCard b)
               (loading := <p class="loading">Loading…</p>)
               (failed  := fun e => <p class="error">{"Error: "}{e}</p>)}
           </div>
       | .newBook =>
           <div class="new">
             <h1>Add a book</h1>
             {Book.formView m.draft Msg.edit Msg.submit}
           </div>}
    </div>

/-- The app, with dehydration wired in (so an SSR deep link hydrates without refetching). -/
def app : App Model Msg := { appBase with dehydrate := dehydrateModel, rehydrate := rehydrateModel }

end Bookshelf
