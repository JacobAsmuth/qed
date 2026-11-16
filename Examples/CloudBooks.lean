import Qed
open Qed

namespace CloudBooks

router R where
  catalog => "/"
  detail (idx : Nat) => "/books/:idx"

schema D1Result where
  success : Bool

schema D1Query where
  sql    : String where sql.length <= 512
  params : Array String

external CloudflareD1
  base "https://api.cloudflare.com/client/v4"
  auth bearer(secret("CF_D1_TOKEN"))

  post "/accounts/:accountId/d1/database/:dbId/query"
    query(accountId: String, dbId: String, body: D1Query) -> D1Result

external GcpStorage
  base "https://storage.googleapis.com"
  auth gcpServiceAccount(secret("GCP_SA_JSON"), "https://www.googleapis.com/auth/devstorage.read_write")

  post "/upload/storage/v1/b/:bucket/o?uploadType=media&name=:name"
    upload(bucket: String, name: String, data: Bytes) -> Json

  get "/storage/v1/b/:bucket/o/:key*?alt=media"
    download(bucket: String, key: String) -> Bytes

schema Book where
  slot  : Nat    where slot <= 1000
  id    : String where 1 <= id.length, id.length <= 64
  title : String where 1 <= title.length, title.length <= 200
  stock : Nat    where stock <= 10000

server Catalog
  env cfAccount = "CF_ACCOUNT_ID" ?? "demo-account"
  env d1Db      = "CF_D1_DB_ID"   ?? "demo-db"
  env gcsBucket = "GCS_BUCKET"    ?? "qed-covers"

  state books: Book[] = [
    Book(slot = 0, id = "tpil4", title = "Theorem Proving in Lean 4", stock = 12),
    Book(slot = 1, id = "fpil",  title = "Functional Programming in Lean", stock = 8)
  ]
  state totalOrders: Nat = 0

  invariant forall b in books, b.stock <= 10000
  invariant totalOrders >= old(totalOrders)
  invariant mutating books requires ctx.userId != none

  fn list() -> Book[]
    return books

  fn findAt(idx: Nat) -> Book?
    if idx < books.size
      return books[idx]
    return none

  fn cover(key: String) -> Bytes!
    return await GcpStorage.download(gcsBucket, "covers/" ++ key)

  fn order(idx: Nat, qty: Nat) -> Book!
    requires ctx.userId != none
    requires 1 <= qty && qty <= 50
    let bookId = atomic
      if idx >= books.size
        return fail("book not found")
      if books[idx].stock < qty
        return fail("out of stock")
      return books[idx].id
    let _ = await CloudflareD1.query(cfAccount, d1Db, D1Query(
      sql = "INSERT INTO orders (book_id, qty) VALUES (?, ?)",
      params = [bookId, toString(qty)])) catch _
      D1Result(success = false)
    let updated = atomic
      if idx >= books.size
        return fail("book not found")
      if books[idx].stock < qty
        return fail("out of stock")
      books[idx].stock -= qty
      totalOrders += 1
      return books[idx]
    return updated

  fn addBook(id: String, title: String, stock: Nat, coverPng: Bytes) -> Book!
    requires ctx.userId != none
    requires 1 <= id.length && id.length <= 64
    requires 1 <= title.length && title.length <= 200
    requires stock <= 10000
    let _ = await GcpStorage.upload(gcsBucket, "covers/" ++ id ++ ".png", coverPng)?
    let created = atomic
      if books.size >= 1000
        return fail("catalog full")
      let nb = Book(slot = books.size, id = id, title = title, stock = stock)
      books.push(nb)
      return nb
    return created

def shell : Style := css [
  maxWidth (rem 42), margin (rem 2) .auto, fontFamily "system-ui, sans-serif", lineHeight 1.5 ]
def rowStyle : Style := css [
  display .flex, gap (rem 1), padding (rem 0.75) (rem 1), border "1px solid #ddd",
  radius (px 8), marginBottom (rem 0.75) ]
def btnStyle : Style := css [
  padding (rem 0.35) (rem 0.75), radius (px 6), border "1px solid #06c" ]

component BookRow where
  prop book : Book
  event onOrder
  view =>
    <li {rowStyle} class="book-row">
      <a href={R.detail book.slot} class="book-title">{book.title}</a>
      <span class="book-stock">Stock: {book.stock}</span>
      <button {btnStyle} class="order-btn" onClick={onOrder}>Order copy</button>
    </li>

component BookDetail where
  prop book : Book
  view =>
    <article class="book-detail">
      <h2>{book.title}</h2>
      <p class="detail-stock">In stock: {book.stock}</p>
    </article>

component Storefront where
  route : R := .catalog
    | .catalog    => books := .loading, perform (Catalog.list (books := ·))
    | .detail idx => current := .loading, perform (Catalog.findAt idx (current := ·))
  state books     : Resource (Array Book) := .idle
  state current   : Resource Book := .idle
  state statusMsg := ""

  action orderOne (idx : Nat) =>
    statusMsg := "Ordering…"
    perform (Catalog.order idx 1 (.ordered idx))

  action ordered (idx : Nat) (r : Resource Book) =>
    match r with
    | .ok updated =>
        books := books.map fun arr => if h : idx < arr.size then arr.set idx updated else arr
        statusMsg := s!"Ordered {updated.title}"
    | .failed err => statusMsg := s!"Order failed: {err}"
    | _ => ()

  view =>
    <div {shell} class="cloudbooks">
      <nav class="topnav">
        <a href={R.catalog} class="home-link">CloudBooks</a>
      </nav>
      <p class="status">{statusMsg}</p>
      {match route with
       | .catalog =>
           <section class="catalog">
             <h1>Verified Cloud Bookstore</h1>
             <Await of={books} as={arr} err={e}
               loading={<p class="loading">Loading catalog…</p>}
               failed={<p class="error">{e}</p>}>
               <ul class="books">{for b in arr =>
                 <BookRow key={b.id} book={b} onOrder={.orderOne b.slot}/>}</ul>
             </Await>
           </section>
       | .detail _ =>
           <section class="detail">
             <Await of={current} as={b} err={e}
               loading={<p class="loading">Loading book…</p>}
               failed={<p class="error">{e}</p>}>
               <BookDetail book={b}/>
             </Await>
           </section>}
    </div>

fullstack Main
  server Catalog
  client Storefront
  title "CloudBooks"

end CloudBooks
