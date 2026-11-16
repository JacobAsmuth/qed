import Qed
open Qed

namespace Bookshelf

router R where
  catalog => "/"
  detail  => "/books/:id"
  newBook => "/new"

schema Book where
  id      : jsonOnly String
  title   : String where title.length ≥ 1
  author  : String where author.length ≥ 1
  year    : Nat    where 1 ≤ year, year ≤ 2026
  genre   : select [("fiction", "Fiction"), ("nonfiction", "Non-fiction"), ("poetry", "Poetry")]
  inPrint : Bool

def brand : Token := token "brand"
def shell : Style := css [
  maxWidth (rem 40), margin (rem 2) .auto, fontFamily "system-ui, sans-serif", lineHeight 1.5,
  screenMax (px 600) [ margin (rem 1), maxWidth (pct 100) ] ]
def topnav : Style := css [
  display .flex, gap (rem 1), marginBottom (rem 1.5) ]
def navlink : Style := css [
  textDecoration "none", color brand, fontWeight 600 ]
def card : Style := css [
  padding (rem 1) (rem 1.25), border "1px solid #ddd", radius (px 8) ]

component BookItem where
  prop book : Book
  view =>
    <li>
      <a href={R.detail book.id} {navlink} class="book-link">{book.title}</a>
      <span class="byline">{s!" by {book.author}"}</span>
    </li>

component BookCard where
  prop book : Book
  view =>
    <div {card} class="book">
      <h1>{book.title}</h1>
      <p class="author">{s!"by {book.author} ({book.year})"}</p>
      <p class="genre">{book.genre}</p>
      <p class={if book.inPrint then "in-print" else "out-of-print"}>
        {if book.inPrint then "In print" else "Out of print"}</p>
    </div>

app Storefront where
  route route : R := .catalog
    | .catalog => catalog := .loading, perform (Resource.fetch "/api/books" (catalog := ·))
    | .detail id =>
        match current with
        | .ok b =>
            if b.id == id then ()
            else current := .loading, perform (Resource.fetch s!"/api/books/{id}" (current := ·))
        | _ => current := .loading, perform (Resource.fetch s!"/api/books/{id}" (current := ·))
    | .newBook => ()
  state catalog : Resource (Array Book) := .idle
  state current : Resource Book := .idle
  state draft   := Book.Draft.empty

  action submit =>
    if let some book := Book.parse draft then
      perform (Resource.post "/api/books" book .created)

  action created (r : Resource Book) =>
    match r with
    | .ok b     => current := .ok b, draft := Book.Draft.empty, perform (Cmd.pushUrl (R.detail b.id))
    | .failed e => current := .failed e
    | _         => ()

  view =>
    <div {shell} class="app">
      {theme [ brand.set "#06c" ]}
      <nav {topnav}>
        <a href={R.catalog} {navlink}>Catalog</a>
        <a href={R.newBook} {navlink}>Add a book</a>
      </nav>
      {match route with
       | .catalog =>
           <div class="catalog">
             <h1>Bookshelf</h1>
             <Await of={catalog} as={books}
               loading={<p class="loading">Loading catalog…</p>}
               failed={fun e => <p class="error">{"Error: "}{e}</p>}>
               <ul class="books">{books.map fun b => <BookItem key={b.id} book={b}/>}</ul>
             </Await>
           </div>
       | .detail _ =>
           <div class="detail">
             <Await of={current} as={b}
               loading={<p class="loading">Loading…</p>}
               failed={fun e => <p class="error">{"Error: "}{e}</p>}>
               <BookCard book={b}/>
             </Await>
           </div>
       | .newBook =>
           <div class="new">
             <h1>Add a book</h1>
             {Book.formView draft (draft := ·) .submit}
           </div>}
    </div>

def app : App Storefront.State Storefront.Msg := Storefront.app

end Bookshelf
