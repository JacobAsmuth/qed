import Qed
open Qed

namespace Bookshelf

router R:
  catalog = "/"
  detail  = "/books/:id"
  newBook = "/new"

schema Book:
  id      : jsonOnly(String)
  title   : String where title.length >= 1
  author  : String where author.length >= 1
  year    : Nat    where 1 <= year <= 2026
  genre   : select([("fiction", "Fiction"), ("nonfiction", "Non-fiction"), ("poetry", "Poetry")])
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
  padding (rem 1) (rem 1.25), border (px 1) .solid (hex "ddd"), borderRadius (px 8) ]

component BookItem:
  prop book : Book
  view:
    <li>
      <a href={R.detail(book.id)} {navlink} class="book-link">{book.title}</a>
      <span class="byline"> by {book.author}</span>
    </li>

component BookCard:
  prop book : Book
  view:
    <div {card} class="book">
      <h1>{book.title}</h1>
      <p class="author">by {book.author} ({book.year})</p>
      <p class="genre">{book.genre}</p>
      <p class={"in-print" if book.inPrint else "out-of-print"}>
        {"In print" if book.inPrint else "Out of print"}</p>
    </div>

end Bookshelf

component Bookshelf:
  route : R = .catalog:
    case .catalog:
      catalog = .loading
      perform Resource.fetch("/api/books", (catalog = ·))
    case .detail(id):
      if let .ok(b) = current:
        if b.id == id: return
      current = .loading
      perform Resource.fetch(f"/api/books/{id}", (current = ·))
    case .newBook:
      pass
  state catalog : Resource Book[] = .idle
  state current : Resource Book = .idle
  state draft   = Book.Draft.empty

  action submit(book: Book):
    perform Resource.post("/api/books", book, .created)

  action created(r: Resource Book):
    match r:
      case .ok(b):
        current = .ok(b)
        draft = Book.Draft.empty
        perform Cmd.pushUrl(R.detail(b.id))
      case .failed(e):
        current = .failed(e)
      case _:
        pass

  view:
    <div {shell} class="app">
      {theme([brand.set("#06c")])}
      <nav {topnav}>
        <a href={R.catalog} {navlink}>Catalog</a>
        <a href={R.newBook} {navlink}>Add a book</a>
      </nav>
      {match route:
        case .catalog:
          <div class="catalog">
            <h1>Bookshelf</h1>
            <Await of={catalog} as={books} err={e}
              loading={<p class="loading">Loading catalog…</p>}
              failed={<p class="error">Error: {e}</p>}>
              <ul class="books">{for b in books: <BookItem key={b.id} book={b}/>}</ul>
            </Await>
          </div>
        case .detail(_):
          <div class="detail">
            <Await of={current} as={b} err={e}
              loading={<p class="loading">Loading…</p>}
              failed={<p class="error">Error: {e}</p>}>
              <BookCard book={b}/>
            </Await>
          </div>
        case .newBook:
          <div class="new">
            <h1>Add a book</h1>
            <Book.Form bind={draft} onSubmit={.submit}/>
          </div>}
    </div>
