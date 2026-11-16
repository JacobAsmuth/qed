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
      return books[idx].id.val
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

structure Model where
  route     : R
  books     : Resource (Array Book)
  current   : Resource Book
  statusMsg : String

def init : Model :=
  { route := .catalog, books := .idle, current := .idle, statusMsg := "" }

inductive Msg where
  | routed     (r : R)
  | gotCatalog (r : Resource (Array Book))
  | gotBook    (r : Resource (Option Book))
  | orderOne   (idx : Nat)
  | ordered    (idx : Nat) (r : Resource Book)

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .routed route =>
      match route with
      | .catalog =>
          ({ m with route := .catalog, books := .loading },
           Catalog.list Msg.gotCatalog)
      | .detail idx =>
          ({ m with route := .detail idx, current := .loading },
           Catalog.findAt idx Msg.gotBook)
  | .gotCatalog r => { m with books := r }
  | .gotBook r =>
      let cur : Resource Book := match r with
        | .idle        => .idle
        | .loading     => .loading
        | .ok (some b) => .ok b
        | .ok none     => .failed "Book not found"
        | .failed e    => .failed e
      { m with current := cur }
  | .orderOne idx =>
      ({ m with statusMsg := "Ordering…" },
       Catalog.order idx 1 (Msg.ordered idx))
  | .ordered idx r =>
      match r with
      | .ok updated =>
          let nextBooks := m.books.map fun arr =>
            if h : idx < arr.size then arr.set idx updated else arr
          { m with books := nextBooks, statusMsg := s!"Ordered {updated.title}" }
      | .failed err =>
          { m with statusMsg := s!"Order failed: {err}" }
      | _ => m

def shell : Style := css [
  maxWidth (rem 42), margin "2rem auto", fontFamily "system-ui, sans-serif", lineHeight "1.5" ]
def rowStyle : Style := css [
  display .flex, gap (rem 1), padding "0.75rem 1rem", border "1px solid #ddd",
  radius (px 8), marginBottom "0.75rem" ]
def btnStyle : Style := css [
  padding "0.35rem 0.75rem", radius (px 6), border "1px solid #06c" ]

def bookList (books : Array Book) : Html Msg :=
  <ul class="books">{books.map fun b =>
    <li key={b.id.val} {rowStyle} class="book-row">
      <a href={R.detail b.slot.val} class="book-title">{b.title.val}</a>
      <span class="book-stock">{s!"Stock: {b.stock.val}"}</span>
      <button {btnStyle} class="order-btn" onClick={Msg.orderOne b.slot.val}>Order copy</button>
    </li>}</ul>

def bookDetail (b : Book) : Html Msg :=
  <article class="book-detail">
    <h2>{b.title.val}</h2>
    <p class="detail-stock">{s!"In stock: {b.stock.val}"}</p>
  </article>

def Storefront : App Model Msg :=
  ui init transition (onRoute := Msg.routed) (dehydrate := [route, books, current, statusMsg]) fun m =>
    <div {shell} class="cloudbooks">
      <nav class="topnav">
        <a href={R.catalog} class="home-link">CloudBooks</a>
      </nav>
      <p class="status">{m.statusMsg}</p>
      {match m.route with
       | .catalog =>
           <section class="catalog">
             <h1>Verified Cloud Bookstore</h1>
             {m.books.view (fun arr => bookList arr)
               (loading := <p class="loading">Loading catalog…</p>)
               (failed  := fun e => <p class="error">{e}</p>)}
           </section>
       | .detail _ =>
           <section class="detail">
             {m.current.view (fun b => bookDetail b)
               (loading := <p class="loading">Loading book…</p>)
               (failed  := fun e => <p class="error">{e}</p>)}
           </section>}
    </div>

fullstack Main
  server Catalog
  client Storefront
  title "CloudBooks"

end CloudBooks
