/-
  Bookshelf — a small catalog that wires the whole stack into one app: routing, a
  typed remote `Resource` (a list and a single record, fetched and decoded), a
  validated `form` that POSTs and navigates to the result, and scoped styles.

  Three pages, behind the verified router (`R.round_trip`):

    /              the catalog — fetches `/api/books` into `Resource (Array Book)`
    /books/<id>    one book — fetches `/api/books/<id>` into `Resource Book`
    /new           a form (text/number/select/checkbox, each refined) that, on a
                   valid submit, POSTs the book and routes to its new detail page

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

-- One book, with a JSON codec (decode for the GET responses, encode for the POST body).
jsonStruct Book where
  id      : String
  title   : String
  author  : String
  year    : Nat
  genre   : String
  inPrint : Bool

-- Field refinements for the add form. `abbrev` so the `Decidable` instances are inferred.
abbrev NonEmpty (s : String) : Prop := s.length ≥ 1
abbrev Year (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 2026

-- The add-book form: each control is a typed `Input`, so "submit ⇔ valid" holds by
-- construction. `form` generates the draft, the validated `NewBook`, `parse`, the
-- `canSubmit` gate + its proof, and `formView`.
form NewBook where
  title   : Input.text.refine NonEmpty
  author  : Input.text.refine NonEmpty
  year    : Input.nat.refine Year
  genre   : Input.select [("fiction", "Fiction"), ("nonfiction", "Non-fiction"), ("poetry", "Poetry")]
  inPrint : Input.checkbox

structure Model where
  route   : R
  catalog : Resource (Array Book)   -- the list page
  current : Resource Book           -- the detail page
  draft   : NewBook.Draft           -- the add form

def init : Model :=
  { route := .catalog, catalog := .idle, current := .idle, draft := NewBook.Draft.empty }

inductive Msg where
  | routed     (r : R)                    -- startup / link / back / push, parsed to a route
  | gotCatalog (r : Resource (Array Book))
  | gotBook    (r : Resource Book)
  | edit       (d : NewBook.Draft)        -- the form hands back the whole draft
  | submit
  | created    (r : Resource Book)        -- the POST resolved (ok with the new book, or failed)

/-- The POST body for a valid draft: a book with an empty id (the server assigns one). -/
def bodyOf (nb : NewBook) : String :=
  Book.encode { id := "", title := nb.title.val, author := nb.author.val,
                year := nb.year.val, genre := nb.genre.val, inPrint := nb.inPrint.val }

-- One combined transition. A page that needs data flips its `Resource` to `.loading` and
-- fires the fetch in the same arm that sets the route.
def transition (m : Model) : Msg → Model × Cmd Msg
  | .routed route =>
      match route with
      | .catalog   => also { m with route := .catalog, catalog := .loading }
                          (Resource.fetch "/api/books" Msg.gotCatalog)
      | .detail id =>
          -- keep a book we already hold (e.g. one we just created), else fetch it
          match m.current with
          | .ok b => if b.id == id then still { m with route := .detail id }
                     else also { m with route := .detail id, current := .loading }
                              (Resource.fetch s!"/api/books/{id}" Msg.gotBook)
          | _     => also { m with route := .detail id, current := .loading }
                         (Resource.fetch s!"/api/books/{id}" Msg.gotBook)
      | .newBook   => still { m with route := .newBook }
  | .gotCatalog r => still { m with catalog := r }
  | .gotBook r    => still { m with current := r }
  | .edit d       => still { m with draft := d }
  | .submit       =>
      match NewBook.parse m.draft with
      | some nb => also m (Cmd.postJson "/api/books" (bodyOf nb)
                            (fun b => Msg.created (.ok b)) (fun e => Msg.created (.failed e)))
      | none    => still m
  | .created r    =>
      match r with
      | .ok b     => also { m with current := .ok b, draft := NewBook.Draft.empty }
                         (Cmd.pushUrl (Router.toURL (R.detail b.id)))
      | .failed e => still { m with current := .failed e }
      | _         => still m

/-! Scoped styles, co-located with the view. Each class name is a content hash, and a
    typo in a reference is a compile error. -/
def shell : Style := css "max-width: 40rem; margin: 2rem auto; font-family: system-ui, sans-serif; line-height: 1.5"
def topnav : Style := css "display: flex; gap: 1rem; margin-bottom: 1.5rem"
def navlink : Style := css "text-decoration: none; color: #06c; font-weight: 600"
def card : Style := css "padding: 1rem 1.25rem; border: 1px solid #ddd; border-radius: 8px"

def bookList (books : Array Book) : Html Msg :=
  ul [cls "books"] (books.toList.map fun b =>
    li [key b.id] [
      link (Router.toURL (R.detail b.id)) [navlink, cls "book-link"] [text b.title],
      span [cls "byline"] [text s!" — {b.author}"]
    ])

def bookCard (b : Book) : Html Msg :=
  div [card, cls "book"] [
    h1 [] [text b.title],
    p [cls "author"] [text s!"by {b.author} ({b.year})"],
    p [cls "genre"] [text b.genre],
    p [cls (if b.inPrint then "in-print" else "out-of-print")]
      [text (if b.inPrint then "In print" else "Out of print")]
  ]

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) fun m =>
    div [shell, cls "app"] [
      styleSheet [shell, topnav, navlink, card],
      nav [topnav] [ link "/" [navlink] ["Catalog"], link "/new" [navlink] ["Add a book"] ],
      match m.route with
      | .catalog =>
          div [cls "catalog"] [
            h1 [] ["Bookshelf"],
            m.catalog.view (fun books => bookList books)
              (loading := p [cls "loading"] ["Loading catalog…"])
              (failed  := fun e => p [cls "error"] ["Error: ", text e])
          ]
      | .detail _ =>
          div [cls "detail"] [
            m.current.view (fun b => bookCard b)
              (loading := p [cls "loading"] ["Loading…"])
              (failed  := fun e => p [cls "error"] ["Error: ", text e])
          ]
      | .newBook =>
          div [cls "new"] [
            h1 [] ["Add a book"],
            NewBook.formView m.draft Msg.edit Msg.submit
          ]
    ]

end Bookshelf
