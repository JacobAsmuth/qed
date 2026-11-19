import Qed
open Qed

namespace CloudBooks

router R:
  catalog = "/"
  detail(idx: Nat) = "/books/:idx"

schema D1Result:
  success : Bool

schema D1Query:
  sql    : String where sql.length <= 512
  params : String[]

external CloudflareD1:
  base "https://api.cloudflare.com/client/v4"
  auth bearer(secret("CF_D1_TOKEN"))

  post "/accounts/:accountId/d1/database/:dbId/query"
    query(accountId: String, dbId: String, body: D1Query) -> D1Result

external GcpStorage:
  base "https://storage.googleapis.com"
  auth gcpServiceAccount(secret("GCP_SA_JSON"), "https://www.googleapis.com/auth/devstorage.read_write")

  post "/upload/storage/v1/b/:bucket/o?uploadType=media&name=:name"
    upload(bucket: String, name: String, data: Bytes) -> Json

  get "/storage/v1/b/:bucket/o/:key*?alt=media"
    download(bucket: String, key: String) -> Bytes

schema Book:
  slot  : Nat    where slot <= 1000
  id    : String where 1 <= id.length <= 64
  title : String where 1 <= title.length <= 200
  stock : Nat    where stock <= 10000

server Catalog:
  env cfAccount = "CF_ACCOUNT_ID" ?? "demo-account"
  env d1Db      = "CF_D1_DB_ID"   ?? "demo-db"
  env gcsBucket = "GCS_BUCKET"    ?? "qed-covers"

  state books: Book[] = [
    Book(slot=0, id="tpil4", title="Theorem Proving in Lean 4", stock=12),
    Book(slot=1, id="fpil",  title="Functional Programming in Lean", stock=8)
  ]
  state totalOrders: Nat = 0

  invariant all b in books: b.stock <= 10000
  invariant totalOrders >= old(totalOrders)
  invariant mutating books requires ctx.userId != none

  def list() -> Book[]:
    return books

  def findAt(idx: Nat) -> Book?:
    ensures result.slot == idx
    if idx < books.size and books[idx].slot == idx:
      return books[idx]
    return none

  def cover(key: String) -> Bytes!:
    return await GcpStorage.download(gcsBucket, f"covers/{key}")

  def order(idx: Nat, qty: Nat) -> Book!:
    requires ctx.userId != none
    requires 1 <= qty <= 50
    ensures result.slot == idx, result.stock < 10000
    let bookId = atomic:
      ensure idx < books.size and books[idx].slot == idx else fail(.notFound)
      ensure books[idx].stock >= qty else fail(.outOfStock)
      return books[idx].id
    let _ = await CloudflareD1.query(cfAccount, d1Db, D1Query(
      sql="INSERT INTO orders (book_id, qty) VALUES (?, ?)",
      params=[bookId, toString(qty)])) catch _:
      D1Result(success=false)
    return atomic:
      ensure idx < books.size and books[idx].slot == idx else fail(.notFound)
      ensure books[idx].stock >= qty else fail(.outOfStock)
      books[idx].stock -= qty
      totalOrders += 1
      return books[idx]

  def addBook(id: String, title: String, stock: Nat, coverPng: Bytes) -> Book!:
    requires ctx.userId != none
    requires 1 <= id.length <= 64, 1 <= title.length <= 200, stock <= 10000
    ensures result.id == id, result.stock == stock
    await GcpStorage.upload(gcsBucket, f"covers/{id}.png", coverPng)?
    return atomic:
      ensure books.size < 1000 else fail(.catalogFull)
      let nb = Book(slot=books.size, id=id, title=title, stock=stock)
      books.push(nb)
      return nb

style shell:
  max-width: 42rem
  margin: 2rem auto
  font-family: system-ui, sans-serif
  line-height: 1.5

style rowStyle:
  display: flex
  gap: 1rem
  padding: 0.75rem 1rem
  border: 1px solid #ddd
  border-radius: 8px
  margin-bottom: 0.75rem

style btnStyle:
  padding: 0.35rem 0.75rem
  border-radius: 6px
  border: 1px solid #06c

component BookRow:
  prop book : Book
  event onOrder
  view:
    <li {rowStyle} class="book-row">
      <a href={R.detail(book.slot)} class="book-title">{book.title}</a>
      <span class="book-stock">Stock: {book.stock}</span>
      <button {btnStyle} class="order-btn" onClick={onOrder}>Order copy</button>
    </li>

component BookDetail:
  prop book : Book
  view:
    <article class="book-detail">
      <h2>{book.title}</h2>
      <p class="detail-stock">In stock: {book.stock}</p>
    </article>

component Storefront:
  session user
  route : R = .catalog:
    case .catalog:
      books = await Catalog.list()
    case .detail(_):
      pass
  query current = Catalog.findAt(idx) if let .detail(idx) = route
  state books       : Resource Book[]
  state lastSlot    : Nat?
  state lastOrdered : Book?
  state statusMsg   = ""

  invariant orderedMatchesSlot:
    all b, idx: (lastOrdered == some(b) and lastSlot == some(idx)) -> b.slot == idx

  action orderOne(idx: Nat):
    if user.isSome:
      statusMsg = "Ordering…"
      let updated = await Catalog.order(idx, 1) catch:
        case .outOfStock:  statusMsg = "Order failed: out of stock"
        case .notFound:    statusMsg = "Order failed: book not found"
        case .failed(err): statusMsg = f"Order failed: {err}"
      books = books.map(arr => arr.set(idx, updated) if idx < arr.size else arr)
      lastSlot = some(idx)
      lastOrdered = some(updated)
      statusMsg = f"Ordered {updated.title}"

  view:
    <div {shell} class="cloudbooks">
      <nav class="topnav">
        <a href={R.catalog} class="home-link">CloudBooks</a>
        {match user:
          case some(u): <span class="session-user">{u}</span>
          case none:    <span class="session-guest">Guest</span>}
      </nav>
      <p class="status">{statusMsg}</p>
      {match route:
        case .catalog:
          <section class="catalog">
            <h1>Verified Cloud Bookstore</h1>
            <Await of={books} as={arr} err={e}
              loading={<p class="loading">Loading catalog…</p>}
              failed={<p class="error">{e}</p>}>
              <ul class="books">{for b in arr:
                <BookRow key={b.id} book={b} onOrder={.orderOne(b.slot)}/>}</ul>
            </Await>
          </section>
        case .detail(_):
          <section class="detail">
            <Await of={current} as={b} err={e}
              loading={<p class="loading">Loading book…</p>}
              failed={<p class="error">{e}</p>}>
              <BookDetail book={b}/>
            </Await>
          </section>}
    </div>

fullstack Main:
  server Catalog
  client Storefront
  title "CloudBooks"

end CloudBooks
