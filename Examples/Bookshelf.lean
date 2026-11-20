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

theme BookshelfTheme:
  color brand = #06c

style shell:
  max-width: 40rem
  margin: 2rem auto
  font-family: system-ui, sans-serif
  line-height: 1.5
  @media (max-width: 600px):
    margin: 1rem
    max-width: 100%

style topnav:
  display: flex
  gap: 1rem
  margin-bottom: 1.5rem

style navlink:
  text-decoration: none
  color: BookshelfTheme.brand
  font-weight: 600

style card:
  padding: 1rem 1.25rem
  border: 1px solid #ddd
  border-radius: 8px

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
      Resource.fetch("/api/books", (catalog = _))
    case .detail(id):
      if let .ok(b) = current:
        if b.id == id: return
      current = .loading
      Resource.fetch(f"/api/books/{id}", (current = _))
    case .newBook:
      pass
  state catalog : Resource Book[] = .idle
  state current : Resource Book = .idle
  state draft   = Book.Draft.empty

  action submit(book: Book):
    Resource.post("/api/books", book, .created)

  action created(r: Resource Book):
    match r:
      case .ok(b):
        current = .ok(b)
        draft = Book.Draft.empty
        Cmd.pushUrl(R.detail(b.id))
      case .failed(e):
        current = .failed(e)
      case _:
        pass

  view:
    <div {shell} class="app">
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
