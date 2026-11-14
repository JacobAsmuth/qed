import Qed
open Qed

namespace Bookshelf

router R where
  catalog => ""
  detail (id : String) => "books"
  newBook => "new"

abbrev NonEmpty (s : String) : Prop := s.length ≥ 1
abbrev Year (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 2026

schema Book where
  id      : Codec.text.jsonOnly
  title   : Codec.text.refine NonEmpty
  author  : Codec.text.refine NonEmpty
  year    : Codec.nat.refine Year
  genre   : Codec.select [("fiction", "Fiction"), ("nonfiction", "Non-fiction"), ("poetry", "Poetry")]
  inPrint : Codec.checkbox

structure Model where
  route   : R
  catalog : Resource (Array Book)
  current : Resource Book
  draft   : Book.Draft

def init : Model :=
  { route := .catalog, catalog := .idle, current := .idle, draft := Book.Draft.empty }

inductive Msg where
  | routed     (r : R)
  | gotCatalog (r : Resource (Array Book))
  | gotBook    (r : Resource Book)
  | edit       (d : Book.Draft)
  | submit
  | created    (r : Resource Book)

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .routed route =>
      match route with
      | .catalog   => ({ m with route := .catalog, catalog := .loading },
                       Resource.fetch "/api/books" Msg.gotCatalog)
      | .detail id =>
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

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed)
    (dehydrate := Dehydrate.slice init
      (fun m => (m.route, m.catalog, m.current))
      (fun m (r, cat, cur) => { m with route := r, catalog := cat, current := cur }))
    fun m =>
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

end Bookshelf
