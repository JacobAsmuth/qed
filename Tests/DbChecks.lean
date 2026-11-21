import Qed
open Qed

namespace DbChecks

database VaultDb:
  url secret("QED_TEST_DB_URL")
  dev sqlite ".qed/vault_checks.db"

  table books:
    id    : String primary_key where 1 <= id.length <= 64
    title : String             where 1 <= title.length <= 200
    stock : Nat                where stock <= 10000

    policy write requires ctx.userId != none

  table notes:
    id      : Nat    primary_key
    ownerId : String immutable where 1 <= ownerId.length <= 64
    body    : String           where 1 <= body.length <= 2000
    version : Nat
    status  : String

    policy read, write requires some(row.ownerId) == ctx.userId
    invariant versionMonotonic: row.version >= old(row.version)
    invariant statusFlow: transition row.status: "draft" -> "published" -> "archived"
    index (ownerId, version)

-- Verify DDL & Postgres RLS generation
#guard (VaultDb.ddl .postgres).contains "CREATE TABLE IF NOT EXISTS \"notes\""
#guard (VaultDb.ddl .postgres).contains "CHECK (1 <= LENGTH(\"body\") AND LENGTH(\"body\") <= 2000)"
#guard (VaultDb.ddl .sqlite).contains "CREATE INDEX IF NOT EXISTS \"idx_notes_0\" ON \"notes\" (\"ownerId\", \"version\")"
#guard VaultDb.rlsDdl.contains "ENABLE ROW LEVEL SECURITY"
#guard VaultDb.rlsDdl.contains "current_setting('qed.user_id', true)"

def sameCompiledSql (q1 q2 : Qed.Server.Db.SqlQuery) : Bool :=
  (q1.compile .postgres).1 == (q2.compile .postgres).1 &&
  (q1.compile .sqlite).1 == (q2.compile .sqlite).1

-- Verify SQL injection closure on compiled parameterized queries
#guard
  let mk (v : String) := Qed.Server.Db.SqlQuery.select ⟨"notes", by decide⟩ [⟨"id", by decide⟩]
    (.binOp .eq (.col ⟨"ownerId", by decide⟩) (.param (.text v)))
  sameCompiledSql (mk "alice") (mk "' OR 1=1; DROP TABLE notes; --")

/-! ## Positive End-to-End Verification: Valid DB-Backed Server + Client -/

server VaultApi:
  use db : VaultDb

  def listBooks() -> VaultDb.books[]!:
    return await db.books.select(orderBy = "id")?

  def listMyNotes() -> VaultDb.notes[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.select(where = r => r.ownerId == uid, orderBy = "-version", limit = 50)?

  def getNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    ensures result.id == noteId
    if let some(uid) = ctx.userId:
      return await db.notes.findOne(where = r => r.id == noteId and r.ownerId == uid)?
    return none

  def countMyNotes() -> Nat!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.count(where = r => r.ownerId == uid)?

  def createNote(noteId: Nat, body: String) -> VaultDb.notes!:
    requires ctx.userId != none
    requires 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body, 1 <= result.body.length <= 2000
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.notes.insert(id = noteId, ownerId = uid, body = body, version = 0, status = "draft")?

  def editNote(noteId: Nat, body: String) -> VaultDb.notes?!:
    requires ctx.userId != none
    requires 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid,
      set   = r => { body = body, version = r.version + 1 }
    )?

  def publishNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    ensures result.id == noteId, result.status == "published"
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid and r.status == "draft",
      set   = r => { status = "published", version = r.version + 1 }
    )?

  def deleteNote(noteId: Nat) -> Nat!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.delete(where = r => r.id == noteId and r.ownerId == uid)?

  def seedBook(bookId: String, title: String, stock: Nat) -> VaultDb.books!:
    requires ctx.userId != none
    requires 1 <= bookId.length <= 64, 1 <= title.length <= 200, stock <= 10000
    return await db.books.insert(id = bookId, title = title, stock = stock)?

  def orderBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires ctx.userId != none
    requires 1 <= qty <= 50
    ensures result.id == bookId, result.stock <= 10000
    return await db.books.updateOne(
      where = r => r.id == bookId and r.stock >= qty,
      set   = r => { stock = r.stock - qty }
    )?

component VaultClient:
  session user
  query myNotes = VaultApi.listMyNotes() if user.isSome
  state lastNoteId : Nat = 0
  state lastBody   : String = "init"
  state statusMsg  : String = ""

  invariant bodyNonEmpty: 1 <= lastBody.length <= 2000

  action saveNew(noteId: Nat, text: String):
    if user.isSome and 1 <= text.length <= 2000:
      let created = await VaultApi.createNote(noteId, text) catch:
        case .invalidUser: statusMsg = "Invalid user"
        case .failed(e):   statusMsg = e
      lastNoteId = created.id
      lastBody = created.body
      statusMsg = "Saved"

  view:
    <div>
      <p>{statusMsg}</p>
      <p>{lastBody}</p>
    </div>

fullstack VaultApp:
  server VaultApi
  client VaultClient
  title "Vault"

/-! ## Negative Compile-Time Verification Tests (Every Bug Below MUST Be Rejected!) -/

-- 1. Rejects `findOne` missing `r.ownerId == uid` (IDOR / read policy violation)
/--
error: Database read policy `VaultDb.notes.read` failed in `leakNote → VaultDb.notes.findOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` (together with `requires` / `if` guards) implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadReadIdor:
  use db : VaultDb
  def leakNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    return await db.notes.findOne(where = r => r.id == noteId)?

-- 2. Rejects unfiltered `select()` on a read-protected table
/--
error: Database read policy `VaultDb.notes.read` failed in `dumpAll → VaultDb.notes.select`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` (together with `requires` / `if` guards) implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadSelectAll:
  use db : VaultDb
  def dumpAll() -> VaultDb.notes[]!:
    return await db.notes.select()?

-- 3. Rejects `delete` missing `r.ownerId == uid`
/--
error: Database delete policy `VaultDb.notes.delete` failed in `nukeNote → VaultDb.notes.delete`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadDeleteIdor:
  use db : VaultDb
  def nukeNote(noteId: Nat) -> Nat!:
    requires ctx.userId != none
    return await db.notes.delete(where = r => r.id == noteId)?

-- 4. Rejects `updateOne` missing `r.ownerId == uid`
/--
error: Database update policy `VaultDb.notes.update` failed in `hijackEdit → VaultDb.notes.updateOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` implies `some(row.ownerId) == ctx.userId`.
---
error: Database post-update policy `VaultDb.notes.update` (anti-hijack) failed in `hijackEdit → VaultDb.notes.updateOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadUpdateIdor:
  use db : VaultDb
  def hijackEdit(noteId: Nat, body: String) -> VaultDb.notes?!:
    requires ctx.userId != none
    requires 1 <= body.length <= 2000
    return await db.notes.updateOne(
      where = r => r.id == noteId,
      set   = r => { body = body, version = r.version + 1 }
    )?

-- 5. Rejects `insert` under another user's `ownerId` (insert policy violation)
/--
error: Database insert policy `VaultDb.notes.insert` failed in `spoofInsert → VaultDb.notes.insert`:
  • must prove: some "victim" = ctx.userId

Hint: Ensure inserted row satisfies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadInsertSpoof:
  use db : VaultDb
  def spoofInsert(noteId: Nat, body: String) -> VaultDb.notes!:
    requires ctx.userId != none
    requires 1 <= body.length <= 2000
    return await db.notes.insert(id = noteId, ownerId = "victim", body = body, version = 0, status = "draft")?

-- 6. Rejects `update` modifying an `immutable` column (`ownerId`)
/--
error: cannot update `immutable` column `VaultDb.notes.ownerId` in `stealOwner`
-/
#guard_msgs in
server BadImmutableUpdate:
  use db : VaultDb
  def stealOwner(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid,
      set   = r => { ownerId = "attacker" }
    )?

-- 7. Rejects `insert` violating column `where` constraint (empty body)
/--
error: Database table constraint `VaultDb.notes.RowInv` failed in `emptyNote → VaultDb.notes.insert`:
  • must prove: (1 <= (ctx.userId.getD "").length and (ctx.userId.getD "").length <= 64) and 1 <= 0 and 0 <= 2000

Hint: Guard input parameters with `requires` or `if` so every column `where` constraint and table `invariant` holds.
-/
#guard_msgs in
server BadInsertConstraint:
  use db : VaultDb
  def emptyNote(noteId: Nat) -> VaultDb.notes!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    return await db.notes.insert(id = noteId, ownerId = uid, body = "", version = 0, status = "draft")?

-- 8. Rejects `update` violating `old(row)` monotonicity (`version = r.version - 1`)
/--
error: Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `downgradeVersion → VaultDb.notes.updateOne`:
  • must prove: version - 1 >= version

Hint: Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants.
-/
#guard_msgs in
server BadMonotonicUpdate:
  use db : VaultDb
  def downgradeVersion(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid and r.version >= 1,
      set   = r => { version = r.version - 1 }
    )?

-- 9. Rejects `update` violating state-machine `transition` (`"draft" -> "archived"` skips `"published"`)
/--
error: Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `skipPublish → VaultDb.notes.updateOne`:
  • must prove: version >= version and (("archived" = "draft" or "archived" = "published") or "draft" = "published")

Hint: Ensure the `where` clause matches a valid predecessor state for all `old(...)` and `transition` invariants.
-/
#guard_msgs in
server BadTransitionSkip:
  use db : VaultDb
  def skipPublish(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid and r.status == "draft",
      set   = r => { status = "archived" }
    )?

-- 10. Rejects `update` violating upper column bound (`stock = r.stock + 5` without upper guard)
/--
error: Database table constraint `VaultDb.books.RowInv` failed in `restockOverflow → VaultDb.books.updateOne`:
  • must prove: stock + 5 <= 10000

Hint: Guard the update in `where = r => ...` (e.g. `r.stock >= qty`) or `requires` so all column `where` rules hold after `set`.
-/
#guard_msgs in
server BadUpdateOverflow:
  use db : VaultDb
  def restockOverflow(bookId: String) -> VaultDb.books?!:
    requires ctx.userId != none
    return await db.books.updateOne(
      where = r => r.id == bookId,
      set   = r => { stock = r.stock + 5 }
    )?

-- 11. Rejects client calling DB-backed RPC with a param violating DB write constraint (`""` violates `1 <= body.length <= 2000`)
/--
error: RPC `VaultApi.createNote` precondition `1 <= body.length <= 2000` could not be proved here:
  • must satisfy:  1 <= "".length and "".length <= 2000

Hint: Pass valid arguments, guard with `if ...:`, or add a component `invariant`.
-/
#guard_msgs in
component BadClientParam:
  session user
  state msg = ""
  action go:
    if user.isSome:
      let _ = await VaultApi.createNote(1, "") catch:
        case .invalidUser: msg = "bad"
        case .failed(e):   msg = e
  view:
    <p>{msg}</p>

-- 12. Rejects client `query` calling a DB-mutating endpoint
/--
error: reactive `query bad` cannot call mutating server RPC `VaultApi.deleteNote`; `query` only permits read-only server functions
-/
#guard_msgs in
component BadClientQueryMut:
  session user
  query bad = VaultApi.deleteNote(1) if user.isSome
  view:
    <p>hi</p>

/-! ## Extended Verified Database Layer: Richer SQL, FK Joins, Transactions & Migrations -/

database ShopDb:
  url secret("QED_TEST_SHOP_URL")
  dev sqlite ".qed/shop_checks.db"

  table authors:
    id   : String primary_key where 1 <= id.length <= 64
    name : String             where 1 <= name.length <= 120

  table items:
    id       : String primary_key where 1 <= id.length <= 64
    authorId : String references authors(id)
    ownerId  : String immutable   where 1 <= ownerId.length <= 64
    title    : String             where 1 <= title.length <= 200
    price    : Nat                where price <= 100000

    policy read, write requires some(row.ownerId) == ctx.userId
    index (ownerId, price)

  table privateProfiles:
    id      : String primary_key where 1 <= id.length <= 64
    ownerId : String immutable   where 1 <= ownerId.length <= 64
    bio     : String             where 1 <= bio.length <= 500

    policy read, write requires some(row.ownerId) == ctx.userId

  table secretLogs:
    id        : String primary_key where 1 <= id.length <= 64
    profileId : String references privateProfiles(id)
    ownerId   : String immutable   where 1 <= ownerId.length <= 64
    msg       : String             where 1 <= msg.length <= 200

    policy read, write requires some(row.ownerId) == ctx.userId

-- SQL injection closure for LIKE / startsWith / contains / IN / aggregate / joinSelect
#guard
  let mk (p1 p2 i1 i2 : String) := Qed.Server.Db.SqlQuery.select ⟨"items", by decide⟩ [⟨"id", by decide⟩]
    (.binOp .and (.startsWith (.col ⟨"title", by decide⟩) (.param (.text p1)))
      (.binOp .and (.contains (.col ⟨"title", by decide⟩) (.param (.text p2)))
        (.inList (.col ⟨"id", by decide⟩) [.text i1, .text i2])))
    (limit := some 10) (offset := some 5)
  sameCompiledSql (mk "Rust" "Lean" "a" "b") (mk "'; DROP TABLE items; --" "%' OR 1=1 --" "'; DELETE FROM items;" "x")

/-- Shared v1/v2/unsafe additive migration fixture reused by `Tests.Native.Database`. -/
def mkMigrationFixture (tblName : Qed.Server.Db.SqlIdent)
    (extraV1Cols : List Qed.Server.Db.ColumnSchema := [])
    (unsafeColName : Qed.Server.Db.SqlIdent := ⟨"code", by decide⟩) :
    Qed.Server.Db.TableSchema × Qed.Server.Db.TableSchema × Qed.Server.Db.ColumnSchema :=
  let baseCols : List Qed.Server.Db.ColumnSchema :=
    { name := ⟨"id", by decide⟩, colType := .text, isPrimaryKey := true } :: extraV1Cols
  let v1 : Qed.Server.Db.TableSchema := { name := tblName, columns := baseCols, indexes := [] }
  let v2 : Qed.Server.Db.TableSchema := {
    name := tblName
    columns := baseCols ++ [
      { name := ⟨"notes", by decide⟩, colType := .text, nullable := true },
      { name := ⟨"views", by decide⟩, colType := .int, nullable := false, checkSql? := some "\"views\" >= 0" }
    ]
    indexes := [[⟨"views", by decide⟩]]
  }
  let unsafeCol : Qed.Server.Db.ColumnSchema := {
    name := unsafeColName, colType := .text, nullable := false,
    checkSql? := some s!"LENGTH(\"{unsafeColName.raw}\") >= 4"
  }
  (v1, v2, unsafeCol)

-- Pure schema diffing & migration safety checks (safe additive v1->v2 & rejected unsafe CHECK)
#guard
  let (oldTbl, newTbl, unsafeCol) := mkMigrationFixture ⟨"items", by decide⟩
  let steps := Qed.Server.Db.diffTableSchemas [oldTbl] [newTbl]
  let pgDdl := Qed.Server.Db.renderMigrationDdl .postgres steps
  let sqDdl := Qed.Server.Db.renderMigrationDdl .sqlite steps
  steps.length == 3 &&
  (Qed.Server.Db.verifyMigrationSafe steps).isOk &&
  pgDdl.contains "ADD COLUMN IF NOT EXISTS \"notes\" TEXT" &&
  pgDdl.contains "ADD COLUMN IF NOT EXISTS \"views\" BIGINT NOT NULL DEFAULT 0" &&
  sqDdl.contains "ADD COLUMN \"views\" INTEGER NOT NULL DEFAULT 0" &&
  sqDdl.contains "CREATE INDEX IF NOT EXISTS \"idx_items_0\"" &&
  (Qed.Server.Db.diffTableSchemas [newTbl] [newTbl]).isEmpty &&
  !(Qed.Server.Db.verifyMigrationSafe [.addColumn ⟨"items", by decide⟩ unsafeCol none]).isOk

server ShopApi:
  use db : ShopDb
  state txOps : Nat = 0
  invariant txOpsNonNeg: txOps >= 0

  def searchItems(pfx: String, sub: String, pageOffset: Nat) -> ShopDb.items[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.select(
      where = r => r.ownerId == uid and r.title.startsWith(pfx) and r.title.contains(sub),
      orderBy = "-price",
      limit = 20,
      offset = pageOffset
    )?

  def filterByIds(ids: String[]) -> ShopDb.items[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.select(
      where = r => r.ownerId == uid and ids.contains(r.id),
      orderBy = "id",
      limit = 50,
      offset = 0
    )?

  def totalInventoryValue() -> Nat!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.sum(col = "price", where = r => r.ownerId == uid)?

  def cheapestPrice() -> Nat?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.min(col = "price", where = r => r.ownerId == uid)?

  def highestPrice() -> Nat?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.max(col = "price", where = r => r.ownerId == uid)?

  def itemsWithAuthors() -> (ShopDb.items, ShopDb.authors)[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.items.join(
      table = authors,
      where = r => r.ownerId == uid,
      orderBy = "-price",
      limit = 25,
      offset = 0
    )?

  def logsWithProfiles() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.secretLogs.join(
      table = privateProfiles,
      where = r => r.ownerId == uid,
      rightWhere = p => p.ownerId == uid
    )?

  def createAuthorAndItem(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires ctx.userId != none
    requires 1 <= aid.length <= 64, 1 <= aname.length <= 120
    requires 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid, result.price == price
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction:
      let _a = await db.authors.insert(id = aid, name = aname)?
      let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?
      atomic:
        txOps += 1
      return created

  def createPairDotSyntax(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires ctx.userId != none
    requires 1 <= aid.length <= 64, 1 <= aname.length <= 120
    requires 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction:
      let _a = await db.authors.insert(id = aid, name = aname)?
      if price == 99999:
        return fail(.aborted)
      let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?
      return created

-- 13. Negative: aggregate (`sum`) without ReadPolicy proof is rejected
/--
error: Database read policy `ShopDb.items.read` failed in `leakSum → ShopDb.items.sum`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` (together with `requires` / `if` guards) implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadAggNoPolicy:
  use db : ShopDb
  def leakSum() -> Nat!:
    return await db.items.sum(col = "price")?

-- 14. Negative: FK `join` where right-hand table ReadPolicy is NOT satisfied is rejected!
/--
error: Database read policy `ShopDb.privateProfiles.read` (joined table) failed in `leakProfileJoin → ShopDb.secretLogs.join`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `rightWhere = r => ...` (together with `requires` / `if` guards) implies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadJoinRightPolicy:
  use db : ShopDb
  def leakProfileJoin() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.secretLogs.join(
      table = privateProfiles,
      where = r => r.ownerId == uid
    )?

-- 15. Negative: policy violation inside a `db.transaction:` block is still rejected!
/--
error: Database insert policy `ShopDb.items.insert` failed in `badTxInsert → ShopDb.items.insert`:
  • must prove: some "victim" = ctx.userId

Hint: Ensure inserted row satisfies `some(row.ownerId) == ctx.userId`.
-/
#guard_msgs in
server BadTxPolicy:
  use db : ShopDb
  def badTxInsert(aid: String, iid: String) -> ShopDb.items!:
    requires ctx.userId != none
    requires 1 <= aid.length <= 64, 1 <= iid.length <= 64
    db.transaction:
      return await db.items.insert(id = iid, authorId = aid, ownerId = "victim", title = "oops", price = 10)?

end DbChecks
