import Qed
import QedTests.CheckHelper
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

def sameCompiledSql (q1 q2 : Qed.Server.Db.SqlQuery) : Bool := (q1.compile .postgres).1 == (q2.compile .postgres).1 && (q1.compile .sqlite).1 == (q2.compile .sqlite).1
example : (
  let pg := VaultDb.ddl .postgres; let mk (v : String) := Qed.Server.Db.SqlQuery.select ⟨"notes", by decide⟩ [⟨"id", by decide⟩] (.binOp .eq (.col ⟨"ownerId", by decide⟩) (.param (.text v)))
  ["CREATE TABLE IF NOT EXISTS \"notes\"", "CHECK (1 <= LENGTH(\"body\") AND LENGTH(\"body\") <= 2000)"].all (Qed.Str.contains pg ·) &&
  Qed.Str.contains (VaultDb.ddl .sqlite) "CREATE INDEX IF NOT EXISTS \"idx_notes_0\" ON \"notes\" (\"ownerId\", \"version\")" &&
  ["ENABLE ROW LEVEL SECURITY", "current_setting('qed.user_id', true)"].all (Qed.Str.contains VaultDb.rlsDdl ·) && sameCompiledSql (mk "alice") (mk "' OR 1=1; DROP TABLE notes; --")) = true := by decide +kernel
server VaultApi:
  use db : VaultDb
  rpc listBooks() -> VaultDb.books[]!: return await db.books.select(orderBy = "id")?
  rpc listMyNotes() -> VaultDb.notes[]!:
    requires ctx.userId != none
    return await db.notes.select(where = r => r.ownerId == ctx.userId.getD(""), orderBy = "-version", limit = 50)?
  rpc getNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    ensures result.id == noteId
    if let some(uid) = ctx.userId: return await db.notes.findOne(where = r => r.id == noteId and r.ownerId == uid)?
    return none
  rpc countMyNotes() -> Nat!:
    requires ctx.userId != none
    return await db.notes.count(where = r => r.ownerId == ctx.userId.getD(""))?
  rpc createNote(noteId: Nat, body: String) -> VaultDb.notes!:
    requires ctx.userId != none, 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body, 1 <= result.body.length <= 2000
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.notes.insert(id = noteId, ownerId = uid, body = body, version = 0, status = "draft")?
  rpc editNote(noteId: Nat, body: String) -> VaultDb.notes?!:
    requires ctx.userId != none, 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body
    return await db.notes.updateOne(where = r => r.id == noteId and r.ownerId == ctx.userId.getD(""), set = r => { body = body, version = r.version + 1 })?
  rpc publishNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    ensures result.id == noteId, result.status == "published"
    return await db.notes.updateOne(where = r => r.id == noteId and r.ownerId == ctx.userId.getD("") and r.status == "draft", set = r => { status = "published", version = r.version + 1 })?
  rpc deleteNote(noteId: Nat) -> Nat!:
    requires ctx.userId != none
    return await db.notes.delete(where = r => r.id == noteId and r.ownerId == ctx.userId.getD(""))?
  rpc seedBook(bookId: String, title: String, stock: Nat) -> VaultDb.books!:
    requires ctx.userId != none, 1 <= bookId.length <= 64, 1 <= title.length <= 200, stock <= 10000
    return await db.books.insert(id = bookId, title = title, stock = stock)?
  rpc orderBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires ctx.userId != none, 1 <= qty <= 50
    ensures result.id == bookId, result.stock <= 10000
    return await db.books.updateOne(where = r => r.id == bookId and r.stock >= qty, set = r => { stock = r.stock - qty })?
  rpc restockBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires ctx.userId != none, 1 <= qty <= 50
    return await db.books.updateOne(where = r => r.id == bookId and r.stock + qty <= 10000, set = { stock += qty })?
  rpc atomicOrderBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires ctx.userId != none, 1 <= qty <= 50
    return await db.books.updateOne(where = r => r.id == bookId and r.stock >= qty, set = { stock -= qty })?
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
  view: <div><p>{statusMsg}</p><p>{lastBody}</p></div>
fullstack VaultApp:
  server VaultApi
  client VaultClient
  title "Vault"

/-! ## Negative Compile-Time Verification Tests -/
bad_db1 "Database read policy `VaultDb.notes.read` failed in `leakNote → VaultDb.notes.findOne`:\n  • must prove: some ownerId = ctx.userId" VaultDb leakNote(noteId: Nat) -> VaultDb.notes?! : return await db.notes.findOne(where = r => r.id == noteId)?
bad_db "Database read policy `VaultDb.notes.read` failed in `dumpAll → VaultDb.notes.select`:\n  • must prove: some ownerId = ctx.userId" VaultDb : rpc dumpAll() -> VaultDb.notes[]!: return await db.notes.select()?
bad_db1 "Database delete policy `VaultDb.notes.delete` failed in `nukeNote → VaultDb.notes.delete`:\n  • must prove: some ownerId = ctx.userId" VaultDb nukeNote(noteId: Nat) -> Nat! : return await db.notes.delete(where = r => r.id == noteId)?
/-- error: Database update policy `VaultDb.notes.update` failed in `hijackEdit → VaultDb.notes.updateOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` implies `some(row.ownerId) == ctx.userId`.
---
error: Database post-update policy `VaultDb.notes.update` (anti-hijack) failed in `hijackEdit → VaultDb.notes.updateOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` implies `some(row.ownerId) == ctx.userId`. -/
#guard_msgs in rollback_env
server BadUpdateIdor:
  use db : VaultDb
  rpc hijackEdit(noteId: Nat, body: String) -> VaultDb.notes?!:
    requires ctx.userId != none, 1 <= body.length <= 2000
    return await db.notes.updateOne(where = r => r.id == noteId, set = r => { body = body, version = r.version + 1 })?
bad_db "Database insert policy `VaultDb.notes.insert` failed in `spoofInsert → VaultDb.notes.insert`:\n  • must prove: some \"victim\" = ctx.userId" VaultDb :
  rpc spoofInsert(noteId: Nat, body: String) -> VaultDb.notes!:
    requires ctx.userId != none, 1 <= body.length <= 2000
    return await db.notes.insert(id = noteId, ownerId = "victim", body = body, version = 0, status = "draft")?
bad_db1 "cannot update `immutable` column `VaultDb.notes.ownerId` in `stealOwner`" VaultDb stealOwner(noteId: Nat) -> VaultDb.notes?! : return await db.notes.updateOne(where = r => r.id == noteId and r.ownerId == ctx.userId.getD(""), set = r => { ownerId = "attacker" })?
bad_db "Database table constraint `VaultDb.notes.RowInv` failed in `emptyNote → VaultDb.notes.insert`" VaultDb :
  rpc emptyNote(noteId: Nat) -> VaultDb.notes!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    return await db.notes.insert(id = noteId, ownerId = uid, body = "", version = 0, status = "draft")?
bad_db1 "Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `downgradeVersion → VaultDb.notes.updateOne`:\n  • must prove: version - 1 >= version" VaultDb downgradeVersion(noteId: Nat) -> VaultDb.notes?! : return await db.notes.updateOne(where = r => r.id == noteId and r.ownerId == ctx.userId.getD("") and r.version >= 1, set = r => { version = r.version - 1 })?
bad_db1 "Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `skipPublish → VaultDb.notes.updateOne`:\n  • must prove: version >= version and ((\"archived\" = \"draft\" or \"archived\" = \"published\") or \"draft\" = \"published\")" VaultDb skipPublish(noteId: Nat) -> VaultDb.notes?! : return await db.notes.updateOne(where = r => r.id == noteId and r.ownerId == ctx.userId.getD("") and r.status == "draft", set = r => { status = "archived" })?
bad_db1 "Database table constraint `VaultDb.books.RowInv` failed in `restockOverflow → VaultDb.books.updateOne`:\n  • must prove: stock + 5 <= 10000" VaultDb restockOverflow(bookId: String) -> VaultDb.books?! : return await db.books.updateOne(where = r => r.id == bookId, set = r => { stock = r.stock + 5 })?
bad_comp_sess "RPC `VaultApi.createNote` precondition `1 <= body.length <= 2000` could not be proved here:\n  • must satisfy:  1 <= \"\".length and \"\".length <= 2000" BadClientParam :
  if user.isSome:
    let _ = await VaultApi.createNote(1, "") catch:
      case _: pass
expect_err "reactive `query bad` cannot call mutating server RPC `VaultApi.deleteNote`" in
component BadClientQueryMut:
  session user
  query bad = VaultApi.deleteNote(1) if user.isSome
  view: <p>hi</p>

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

def mkMigrationFixture (tblName : Qed.Server.Db.SqlIdent) (extraV1Cols : List Qed.Server.Db.ColumnSchema := []) (unsafeColName : Qed.Server.Db.SqlIdent := ⟨"code", by decide⟩) :
    Qed.Server.Db.TableSchema × Qed.Server.Db.TableSchema × Qed.Server.Db.ColumnSchema :=
  let baseCols := { name := ⟨"id", by decide⟩, colType := .text, isPrimaryKey := true : Qed.Server.Db.ColumnSchema } :: extraV1Cols
  ({ name := tblName, columns := baseCols, indexes := [] },
   { name := tblName, indexes := [[⟨"views", by decide⟩]], columns := baseCols ++ [{ name := ⟨"notes", by decide⟩, colType := .text, nullable := true }, { name := ⟨"views", by decide⟩, colType := .int, nullable := false, checkSql? := some "\"views\" >= 0" }] },
   { name := unsafeColName, colType := .text, nullable := false, checkSql? := some s!"LENGTH(\"{unsafeColName.raw}\") >= 4" })
example : (
  let mk (p1 p2 i1 i2 : String) := Qed.Server.Db.SqlQuery.select ⟨"items", by decide⟩ [⟨"id", by decide⟩]
    (.binOp .and (.startsWith (.col ⟨"title", by decide⟩) (.param (.text p1))) (.binOp .and (.contains (.col ⟨"title", by decide⟩) (.param (.text p2))) (.inList (.col ⟨"id", by decide⟩) [.text i1, .text i2])))
    (limit := some 10) (offset := some 5)
  let (oldTbl, newTbl, unsafeCol) := mkMigrationFixture ⟨"items", by decide⟩; let steps := Qed.Server.Db.diffTableSchemas [oldTbl] [newTbl]
  let (pgDdl, sqDdl) := (Qed.Server.Db.renderMigrationDdl .postgres steps, Qed.Server.Db.renderMigrationDdl .sqlite steps)
  sameCompiledSql (mk "Rust" "Lean" "a" "b") (mk "'; DROP TABLE items; --" "%' OR 1=1 --" "'; DELETE FROM items;" "x") &&
  steps.length == 3 && (Qed.Server.Db.verifyMigrationSafe steps).isOk &&
  ["ADD COLUMN IF NOT EXISTS \"notes\" TEXT", "ADD COLUMN IF NOT EXISTS \"views\" BIGINT NOT NULL DEFAULT 0"].all (Qed.Str.contains pgDdl ·) &&
  ["ADD COLUMN \"views\" INTEGER NOT NULL DEFAULT 0", "CREATE INDEX IF NOT EXISTS \"idx_items_0\""].all (Qed.Str.contains sqDdl ·) &&
  (Qed.Server.Db.diffTableSchemas [newTbl] [newTbl]).isEmpty && !(Qed.Server.Db.verifyMigrationSafe [.addColumn ⟨"items", by decide⟩ unsafeCol none]).isOk) = true := by decide +kernel
server ShopApi:
  use db : ShopDb
  state txOps : Nat = 0
  invariant txOpsNonNeg: txOps >= 0
  rpc searchItems(pfx: String, sub: String, pageOffset: Nat) -> ShopDb.items[]!:
    requires ctx.userId != none
    return await db.items.select(where = r => r.ownerId == ctx.userId.getD("") and r.title.startsWith(pfx) and r.title.contains(sub), orderBy = "-price", limit = 20, offset = pageOffset)?
  rpc filterByIds(ids: String[]) -> ShopDb.items[]!:
    requires ctx.userId != none
    return await db.items.select(where = r => r.ownerId == ctx.userId.getD("") and ids.contains(r.id), orderBy = "id", limit = 50, offset = 0)?
  rpc totalInventoryValue() -> Nat!:
    requires ctx.userId != none
    return await db.items.sum(col = "price", where = r => r.ownerId == ctx.userId.getD(""))?
  rpc cheapestPrice() -> Nat?!:
    requires ctx.userId != none
    return await db.items.min(col = "price", where = r => r.ownerId == ctx.userId.getD(""))?
  rpc highestPrice() -> Nat?!:
    requires ctx.userId != none
    return await db.items.max(col = "price", where = r => r.ownerId == ctx.userId.getD(""))?
  rpc itemsWithAuthors() -> (ShopDb.items, ShopDb.authors)[]!:
    requires ctx.userId != none
    return await db.items.join(table = authors, where = r => r.ownerId == ctx.userId.getD(""), orderBy = "-price", limit = 25, offset = 0)?
  rpc logsWithProfiles() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]!:
    requires ctx.userId != none
    return await db.secretLogs.join(table = privateProfiles, where = r => r.ownerId == ctx.userId.getD(""), rightWhere = p => p.ownerId == ctx.userId.getD(""))?
  rpc createAuthorAndItem(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires ctx.userId != none, 1 <= aid.length <= 64, 1 <= aname.length <= 120, 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid, result.price == price
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction: let _a = await db.authors.insert(id = aid, name = aname)?; let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?; atomic: txOps += 1; return created
  rpc createPairDotSyntax(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires ctx.userId != none, 1 <= aid.length <= 64, 1 <= aname.length <= 120, 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction:
      let _a = await db.authors.insert(id = aid, name = aname)?
      if price == 99999: return fail(.aborted)
      let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?
      return created
bad_db "Database read policy `ShopDb.items.read` failed in `leakSum → ShopDb.items.sum`:\n  • must prove: some ownerId = ctx.userId" ShopDb : rpc leakSum() -> Nat!: return await db.items.sum(col = "price")?
bad_db "Database read policy `ShopDb.privateProfiles.read` (joined table) failed in `leakProfileJoin → ShopDb.secretLogs.join`:\n  • must prove: some ownerId = ctx.userId" ShopDb :
  rpc leakProfileJoin() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]!:
    requires ctx.userId != none
    return await db.secretLogs.join(table = privateProfiles, where = r => r.ownerId == ctx.userId.getD(""))?
bad_db "Database insert policy `ShopDb.items.insert` failed in `badTxInsert → ShopDb.items.insert`:\n  • must prove: some \"victim\" = ctx.userId" ShopDb :
  rpc badTxInsert(aid: String, iid: String) -> ShopDb.items!:
    requires ctx.userId != none, 1 <= aid.length <= 64, 1 <= iid.length <= 64
    db.transaction: return await db.items.insert(id = iid, authorId = aid, ownerId = "victim", title = "oops", price = 10)?

/-! ## Verified Bidirectional Mappings & `Field`/`Ensured` DB Fact Harvesting -/
schema SecretNoteInput:
  body : String where 1 <= body.utf8ByteSize <= 200
schema PlainNoteInput:
  body : String where 1 <= body.length <= 2000
database CipherDb:
  url secret("QED_TEST_CIPHER_URL")
  dev sqlite ".qed/cipher_checks.db"
  table sealedNotes:
    id         : Nat    primary_key
    ownerId    : String immutable where 1 <= ownerId.length <= 64
    ciphertext : String           where 40 <= ciphertext.length <= 304
    policy read, write requires some(row.ownerId) == ctx.userId

mapping Base64BoundsMap:
  from bs : Bytes  where 29 <= bs.size <= 228
  to   s  : String where 40 <= s.length <= 304
  encode(bs): return Qed.Base64.encode(bs)
  decode(s):  return Qed.Base64.decode(s)?

def sealPrefixBytes : Mapping (fun _ : SecretNoteInput => True) (fun bs : ByteArray => 29 ≤ bs.size ∧ bs.size ≤ 228) where
  toTarget input := ByteArray.mk (Array.replicate 28 0 ++ input.body.val.toUTF8.data)
  toSource ct := do
    if ct.size < 28 then .error "short"
    let pt := ByteArray.mk (ct.data.extract 28 ct.data.size)
    let s ← match String.fromUTF8? pt with | some s => .ok s | none => .error "utf8"
    if h : 1 ≤ s.utf8ByteSize ∧ s.utf8ByteSize ≤ 200 then .ok { body := ⟨s, h⟩ } else .error "bounds"
  encode_ok input _ := by
    have hpt : 1 ≤ input.body.val.utf8ByteSize ∧ input.body.val.utf8ByteSize ≤ 200 := input.body.ok
    have hsz := Qed.toUTF8_size input.body.val
    show 29 ≤ (Array.replicate 28 (0 : UInt8) ++ input.body.val.toUTF8.data).size ∧ (Array.replicate 28 (0 : UInt8) ++ input.body.val.toUTF8.data).size ≤ 228
    rw [Array.size_append, Array.size_replicate]; simp only [ByteArray.size] at hsz; omega
  decode_ok _ _ _ := trivial
  roundtrip input _ := by
    have hlt : ¬ (Array.replicate 28 (0 : UInt8) ++ input.body.val.toUTF8.data).size < 28 := by rw [Array.size_append, Array.size_replicate]; omega
    have hpt : 1 ≤ input.body.val.utf8ByteSize ∧ input.body.val.utf8ByteSize ≤ 200 := input.body.ok
    have hExt : ByteArray.mk ((Array.replicate 28 (0 : UInt8) ++ input.body.val.toUTF8.data).extract 28 (Array.replicate 28 (0 : UInt8) ++ input.body.val.toUTF8.data).size) = input.body.val.toUTF8 := by
      cases input.body.val.toUTF8 with | mk data =>
      congr 1; apply Array.ext
      · simp [Array.size_append, Array.size_replicate]
      · intro i _ _; rw [Array.getElem_extract, Array.getElem_append_right]
        · simp [Array.size_replicate]
        · rw [Array.size_replicate]; omega
    simp only [ByteArray.size, hlt, ↓reduceIte, bind, Except.bind, hExt, Qed.fromUTF8?_toUTF8, dite_eq_left hpt]

def sealedNoteMap := Base64BoundsMap.mapping.comp sealPrefixBytes
example (input : SecretNoteInput) :
    sealedNoteMap.decode (sealedNoteMap.encode input).val = .ok ⟨input, trivial⟩ ∧
    (Base64BoundsMap.mapping.encodeField (sealPrefixBytes.encode input)).val = (sealedNoteMap.encode input).val :=
  ⟨sealedNoteMap.decode_encode input trivial, rfl⟩
def widerCipherMap : Mapping (fun _ : SecretNoteInput => True) (fun s : String => 40 ≤ s.length ∧ s.length ≤ 368) :=
  { toTarget := sealedNoteMap.toTarget, toSource := sealedNoteMap.toSource
    encode_ok := fun d hd => have h := sealedNoteMap.encode_ok d hd; by omega
    decode_ok := sealedNoteMap.decode_ok, roundtrip := sealedNoteMap.roundtrip }

example : (
  match SecretNoteInput.parse { body := "hello" } with
  | none => false
  | some sample =>
    let ct := sealedNoteMap.encode sample
    40 <= ct.val.length && ct.val.length <= 304 &&
    (match sealedNoteMap.toSource ct.val with | .ok d => d.body.val == "hello" | .error _ => false)) = true := by decide +kernel

server CipherApi:
  use db : CipherDb
  use vdb : VaultDb
  rpc saveSealed(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    let ct = sealedNoteMap.encode(input)
    return await db.sealedNotes.insert(id = noteId, ownerId = uid, ciphertext = ct)?
  rpc editSealed(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    let ct = sealedNoteMap.encode(input)
    return await db.sealedNotes.updateOne(where = r => r.id == noteId and r.ownerId == uid, set = r => { ciphertext = ct })?
  rpc savePlainFromSchema(noteId: Nat, input: PlainNoteInput) -> VaultDb.notes!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await vdb.notes.insert(id = noteId, ownerId = uid, body = input.body, version = 0, status = "draft")?

bad_db "Database table constraint `CipherDb.sealedNotes.RowInv` failed in `driftInsert → CipherDb.sealedNotes.insert`" CipherDb :
  rpc driftInsert(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    let ct = widerCipherMap.encode(input)
    return await db.sealedNotes.insert(id = noteId, ownerId = uid, ciphertext = ct)?

/-! ## Surface `mapping` DSL, Built-in `encrypted(...)` DB Columns & `{field}` View Rendering -/
mapping DollarsToCentsMap:
  from dollars : Nat where dollars <= 10000
  to   cents   : Nat where cents <= 1000000
  encode(d): return d * 100
  decode(c):
    if c % 100 == 0: return c / 100
    fail("must be whole dollars")

example : (
  let cents := DollarsToCentsMap.encode ⟨25, by decide⟩
  cents.val == 2500 &&
  (match DollarsToCentsMap.decode cents.val with | .ok d => d.val == 25 | .error _ => false) &&
  (match DollarsToCentsMap.decode 2550 with | .error msg => msg == "must be whole dollars" | .ok _ => false) &&
  (match DollarsToCentsMap.decode 1000100 with | .error _ => true | .ok _ => false)) = true := by decide +kernel

structure TestAeadSpec where
  sealBytes   : ByteArray → ByteArray
  unsealBytes : ByteArray → Except String ByteArray
  seal_size   : ∀ pt, (sealBytes pt).size = pt.size + 28
  roundtrip   : ∀ pt, unsealBytes (sealBytes pt) = .ok pt

mapping NoteCipherMap(cipher: TestAeadSpec):
  from SecretNoteInput
  to   ct : String where 40 <= ct.length <= 304
  using [cipher.seal_size, cipher.roundtrip]
  encode(input): return Qed.Base64.encode(cipher.sealBytes(input.body.toUTF8))
  decode(ct):
    let raw = Qed.Base64.decode(ct)?
    let pt  = cipher.unsealBytes(raw)?
    return SecretNoteInput.parse({ body = String.fromUTF8?(pt)? })?

expect_err "Mapping `DriftMap` failed target constraint `40 <= s.length <= 100`" in
mapping DriftMap:
  from bs : Bytes  where 29 <= bs.size <= 228
  to   s  : String where 40 <= s.length <= 100
  encode(bs): return Qed.Base64.encode(bs)
  decode(s):  return Qed.Base64.decode(s)?

database EncSecretDb:
  url secret("QED_TEST_ENC_DB_URL")
  dev sqlite ".qed/enc_secret_check.db"
  table items:
    id   : Nat primary_key
    body : encrypted(String, key = secret("QED_REQUIRED_ENC_KEY")) where 1 <= body.utf8ByteSize <= 200

database EncVaultDb:
  url secret("QED_TEST_ENC_VAULT_URL")
  dev sqlite ".qed/enc_vault_checks.db"
  table entries:
    id      : Nat    primary_key
    ownerId : String immutable where 1 <= ownerId.length <= 64
    body    : encrypted(String, key = secret("QED_TEST_ENC_KEY") ?? "qed-test-enc-key") where 1 <= body.utf8ByteSize <= 200
    note    : encrypted(String, key = secret("QED_TEST_ENC_KEY") ?? "qed-test-enc-key") where 1 <= note.length <= 200
    raw     : encrypted(Bytes,  key = secret("QED_TEST_ENC_KEY") ?? "qed-test-enc-key")?
    policy read, write requires some(row.ownerId) == ctx.userId

example : (
  let pg := EncVaultDb.ddl .postgres
  Qed.Str.contains pg "\"body\" TEXT NOT NULL CHECK (40 <= LENGTH(\"body\") AND LENGTH(\"body\") <= 304)" &&
  Qed.Str.contains pg "\"note\" TEXT NOT NULL CHECK (40 <= LENGTH(\"note\") AND LENGTH(\"note\") <= 1104)" &&
  Qed.Str.contains pg "\"raw\" TEXT CHECK (40 <= LENGTH(\"raw\"))" &&
  EncSecretDb.secrets.contains "QED_REQUIRED_ENC_KEY" &&
  !(EncVaultDb.secrets.contains "QED_TEST_ENC_KEY")) = true := by decide +kernel

server EncVaultApi:
  use db : EncVaultDb
  rpc save(noteId: Nat, input: SecretNoteInput, rawOpt: Bytes?) -> EncVaultDb.entries!:
    requires ctx.userId != none
    ensures result.id == noteId
    let uid = ctx.userId.getD("")
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.entries.insert(id = noteId, ownerId = uid, body = input.body, note = "ok", raw = rawOpt)?
  rpc edit(noteId: Nat, input: SecretNoteInput) -> EncVaultDb.entries?!:
    requires ctx.userId != none
    ensures result.id == noteId
    let uid = ctx.userId.getD("")
    return await db.entries.updateOne(where = r => r.id == noteId and r.ownerId == uid, set = r => { body = input.body })?
  rpc get(noteId: Nat) -> EncVaultDb.entries?!:
    requires ctx.userId != none
    ensures result.id == noteId
    let uid = ctx.userId.getD("")
    return await db.entries.findOne(where = r => r.id == noteId and r.ownerId == uid)?
  rpc list() -> EncVaultDb.entries[]!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.entries.select(where = r => r.ownerId == uid, orderBy = "id")?

component FieldRenderCheck:
  state items : SecretNoteInput[] = []
  view: <ul>{for item in items: <li key={item.body}><span>{item.body}</span></li>}</ul>

bad_db1 "cannot reference encrypted column `entries.body` inside SQL `where`" EncVaultDb badWhere(q: String) -> EncVaultDb.entries[]! : return await db.entries.select(where = r => r.ownerId == ctx.userId.getD("") and r.body == q)?
bad_db1 "cannot `orderBy` encrypted column `entries.body`" EncVaultDb badOrder(x: Nat) -> EncVaultDb.entries[]! : return await db.entries.select(where = r => r.ownerId == ctx.userId.getD(""), orderBy = "body")?
bad_db1 "cannot compute SQL aggregate on encrypted column `entries.body`" EncVaultDb badAgg(x: Nat) -> String?! : return await db.entries.min(col = "body", where = r => r.ownerId == ctx.userId.getD(""))?
bad_db1 "cannot update encrypted column `EncVaultDb.entries.body` using a row-dependent SQL expression" EncVaultDb badSet(x: Nat) -> EncVaultDb.entries?! : return await db.entries.updateOne(where = r => r.id == x and r.ownerId == ctx.userId.getD(""), set = r => { body = r.body })?
expect_err "cannot index encrypted column `bad.body`" in
database BadEncIndexDb:
  sqlite ".qed/bad_idx.db"
  table bad:
    id   : Nat primary_key
    body : encrypted(String, key = secret("K"))
    index (body)
expect_err "encrypted column `bad.body` cannot be `unique`" in
database BadEncUniqueDb:
  sqlite ".qed/bad_uniq.db"
  table bad:
    id   : Nat primary_key
    body : encrypted(String, key = secret("K")) unique

database TierCheckDb:
  sqlite ".qed/tier_checks.db"
  table scaling:
    id           : String primary_key where 1 <= id.length <= 64
    plan         : String
    minInstances : Nat
    maxInstances : Nat
    invariant freeScaling:
      minInstances <= maxInstances,
      (plan == "pro" or plan == "enterprise") or (minInstances == 0 and maxInstances <= 1)

example : (
  let pg := TierCheckDb.ddl .postgres
  let chk := Qed.Server.Db.renderDatabaseCheckDdl TierCheckDb.config.tables
  Qed.Str.contains pg "CONSTRAINT \"qed_chk_scaling_0\" CHECK (\"minInstances\" <= \"maxInstances\")" &&
  Qed.Str.contains pg "CONSTRAINT \"qed_chk_scaling_1\" CHECK ((((\"plan\" = 'pro' OR \"plan\" = 'enterprise')) OR ((\"minInstances\" = 0 AND \"maxInstances\" <= 1))))" &&
  Qed.Str.contains chk "ADD CONSTRAINT \"qed_chk_scaling_1\" CHECK" &&
  Qed.Str.contains chk "NOT VALID") = true := by decide +kernel

bad_db "Database table constraint `TierCheckDb.scaling.RowInv` failed in `badFreeWarm → TierCheckDb.scaling.insert`" TierCheckDb :
  rpc badFreeWarm(appId: String) -> TierCheckDb.scaling!:
    requires 1 <= appId.length <= 64
    return await db.scaling.insert(id = appId, plan = "free", minInstances = 1, maxInstances = 1)?

/-! ## Track 3 & 4: Unit `enum` columns, `on_delete`, `backfill`, `upsert`, and standalone `<Db>.client` -/

enum DeployStage:
  queued
  building   = "in-progress"
  live
  failed

field ServiceSlug : String where s => 1 <= s.length <= 32
field ServicePort : Nat where p => 1 <= p <= 65535

database RoadmapDb:
  sqlite ".qed/roadmap_checks.db"
  table orgs:
    id   : String primary_key where 1 <= id.length <= 64
    name : String where 1 <= name.length <= 120
  table projects:
    id      : String primary_key where 1 <= id.length <= 64
    orgId   : String references orgs(id) on_delete cascade
    ownerId : String where 1 <= ownerId.length <= 128
    stage   : DeployStage
    note    : String?
    policy read, write requires some(row.ownerId) == ctx.userId
    invariant stageOrder: transition row.stage: .queued -> .building -> .live, .building -> .failed
  table audits:
    id        : String primary_key where 1 <= id.length <= 64
    projectId : String? references projects(id) on_delete set_null
    orgId     : String references orgs(id) on_delete restrict
    day       : Date?
  table services:
    slug    : ServiceSlug primary_key
    port    : ServicePort
    altPort : ServicePort?
  backfill projects set { note = "migrated" } where r => r.note == none

example : (
  let pg := RoadmapDb.ddl .postgres
  let sq := RoadmapDb.ddl .sqlite
  let d? := Date.mk? 2026 11 25
  Qed.Str.contains pg "ON DELETE CASCADE" &&
  Qed.Str.contains pg "ON DELETE SET NULL" &&
  Qed.Str.contains pg "ON DELETE RESTRICT" &&
  Qed.Str.contains pg "CHECK (\"stage\" IN ('queued', 'in-progress', 'live', 'failed'))" &&
  Qed.Str.contains pg "\"slug\" TEXT NOT NULL PRIMARY KEY" &&
  Qed.Str.contains pg "\"port\" BIGINT NOT NULL CHECK (\"port\" >= 0)" &&
  Qed.Str.contains pg "\"altPort\" BIGINT" &&
  Qed.Str.contains sq "\"port\" INTEGER NOT NULL CHECK (\"port\" >= 0)" &&
  Qed.Str.contains sq "ON DELETE CASCADE" &&
  (match d?.map fun d => Qed.Server.Db.FromSql.fromSql (α := Date) (Qed.Server.Db.ToSql.toSql d) with
   | some (.ok d') => some d' == d? | _ => false) &&
  RoadmapDb.config.backfills.length == 1 &&
  (RoadmapDb.config.backfills[0]?.map fun q => Qed.Str.contains (q.compile .postgres).1 "UPDATE \"projects\" SET \"note\" = $1 WHERE (\"note\" IS NULL)") == some true) = true := by decide +kernel

server RoadmapApi:
  use db : RoadmapDb
  rpc createAndUpsert(orgId: String, projId: String, stg: DeployStage) -> RoadmapDb.projects!:
    requires auth, 1 <= orgId.length <= 64, 1 <= projId.length <= 64, stg == .queued
    let _o = await db.orgs.upsert(on = "id", id = orgId, name = "Acme")?
    return await db.projects.upsert(on = ["id"], where = r => r.ownerId == uid and r.stage == .queued, id = projId, orgId = orgId, ownerId = uid, stage = .queued, note = some("ok"))?
  rpc listLive() -> RoadmapDb.projects[]!:
    requires auth
    return await db.projects.select(where = r => r.ownerId == uid and r.stage == .live)?
  rpc advanceToBuilding(projId: String) -> RoadmapDb.projects?!:
    requires auth
    return await db.projects.updateOne(where = r => r.id == projId and r.ownerId == uid and r.stage == .queued, set = { stage = .building })?
  rpc registerService(rawSlug: String, rawPort: Nat) -> RoadmapDb.services!:
    let s = ServiceSlug.parse(rawSlug)?
    let p = ServicePort.parse(rawPort)?
    return await db.services.insert(slug = s, port = p, altPort = some(ServicePort.make(8443)))?
  rpc registerDefaultService() -> RoadmapDb.services!:
    return await db.services.insert(slug = "api", port = 8080)?
  rpc idempotentOrg(orgId: String, name: String) -> RoadmapDb.orgs?!:
    requires 1 <= orgId.length <= 64, 1 <= name.length <= 64
    return await db.orgs.insertOrIgnore(id = orgId, name = name)?
  rpc findByTrimmedOwner(rawOwner: String) -> RoadmapDb.projects[]!:
    let clean = Qed.Str.truncate(Qed.Str.toLower(Qed.Str.trim(rawOwner)), 64)
    if some(clean) != ctx.userId:
      return fail(.forbidden)
    return await db.projects.select(where = r => r.ownerId == clean)?

example : RoadmapDb.Client := RoadmapDb.client

-- Verify `sql!"..."` macro, fail-closed `SqlQuery.select` on empty columns, and explicit `.selectAll`.
example : (
  let tbl := sql!"projects"
  let col := sql!"owner_id"
  let emptySel := (Qed.Server.Db.SqlQuery.select tbl [] .litTrue).compile .postgres
  let explicitAll := (Qed.Server.Db.SqlQuery.selectAll tbl .litTrue).compile .postgres
  let insIgn := (Qed.Server.Db.SqlQuery.insertOrIgnore tbl [(col, .text "a")] [] [col]).compile .postgres
  !Qed.Str.contains emptySel.1 "*" && Qed.Str.contains emptySel.1 "0 = 1" &&
  explicitAll.1 == "SELECT * FROM \"projects\" WHERE TRUE" &&
  insIgn.1 == "INSERT INTO \"projects\" (\"owner_id\") VALUES ($1) ON CONFLICT DO NOTHING RETURNING \"owner_id\"") = true := by decide +kernel

bad_db "Nat non-underflow for `books.stock -= ...`" VaultDb :
  rpc badAtomicDec(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires ctx.userId != none, 1 <= qty <= 50
    return await db.books.updateOne(where = r => r.id == bookId, set = { stock -= qty })?

bad_db "Database upsert conflict update policy `RoadmapDb.projects.update` failed in `badUpsert → RoadmapDb.projects.upsert`" RoadmapDb :
  rpc badUpsert(orgId: String, projId: String) -> RoadmapDb.projects!:
    requires auth, 1 <= orgId.length <= 64, 1 <= projId.length <= 64
    return await db.projects.upsert(on = "id", id = projId, orgId = orgId, ownerId = uid, stage = .queued, note = none)?

expect_err "`on_delete set_null` on `bad.orgId` requires a nullable column (`T?`)" in
database BadSetNullDb:
  sqlite ".qed/bad_set_null.db"
  table orgs:
    id : String primary_key
  table bad:
    id    : String primary_key
    orgId : String references orgs(id) on_delete set_null

/-! ## Item 6: Encrypted Column Projections (`Meta`, `selectMeta`, `columns = [...]`) & `prevKeys` Rotation -/

database RotatingVaultDb:
  sqlite ".qed/rotating_vault_checks.db"
  table entries:
    id      : Nat primary_key immutable
    ownerId : String immutable where 1 <= ownerId.length <= 128
    label   : String where 1 <= label.length <= 120
    secret  : encrypted(String, key = secret("VAULT_PRIMARY_KEY"), prevKeys = [secret("VAULT_PREV_KEY"), secret("VAULT_LEGACY_KEY")]) where 1 <= secret.length <= 512
    policy read, write requires some(row.ownerId) == ctx.userId

example : (
  -- `prevKeys` are optional rotation fallbacks and MUST NOT be required at boot in `.secrets`.
  RotatingVaultDb.secrets == #["VAULT_PRIMARY_KEY"] &&
  RotatingVaultDb.entries.metaColNames == ["id", "ownerId", "label"] &&
  (let m : RotatingVaultDb.entries.Meta := { id := 7, ownerId := "u1", label := "api-key" }
   (match Qed.fromJson (α := RotatingVaultDb.entries.Meta) (Qed.toJson m) with | .ok m' => m' == m | _ => false) &&
   (match Qed.Proto.decode (α := RotatingVaultDb.entries.Meta) (Qed.Proto.encode m) with | .ok m' => m' == m | _ => false))) = true := by decide +kernel

server RotatingVaultApi:
  use db : RotatingVaultDb
  rpc save(id: Nat, label: String, secret: String) -> RotatingVaultDb.entries!:
    requires auth, 1 <= uid.length <= 128, 1 <= label.length <= 120, 1 <= secret.length <= 512
    return await db.entries.insert(id = id, ownerId = uid, label = label, secret = secret)?
  rpc get(id: Nat) -> RotatingVaultDb.entries?!:
    requires auth
    return await db.entries.findOne(where = r => r.id == id and r.ownerId == uid)?
  rpc rotateValue(id: Nat, secret: String) -> RotatingVaultDb.entries?!:
    requires auth, 1 <= secret.length <= 512
    return await db.entries.updateOne(where = r => r.id == id and r.ownerId == uid, set = { secret = secret })?
  rpc listMeta() -> RotatingVaultDb.entries.Meta[]!:
    requires auth
    return await db.entries.selectMeta(where = r => r.ownerId == uid, orderBy = "id")?
  rpc getMeta(id: Nat) -> RotatingVaultDb.entries.Meta?!:
    requires auth
    return await db.entries.findOneMeta(where = r => r.id == id and r.ownerId == uid)?
  rpc listLabels() -> (Nat, String)[]!:
    requires auth
    return await db.entries.select(columns = ["id", "label"], where = r => r.ownerId == uid, orderBy = "id")?
  rpc getLabel(id: Nat) -> String?!:
    requires auth
    return await db.entries.findOne(columns = ["label"], where = r => r.id == id and r.ownerId == uid)?

bad_db "read policy `RotatingVaultDb.entries.read`" RotatingVaultDb :
  rpc leakMeta() -> RotatingVaultDb.entries.Meta[]!:
    requires auth
    return await db.entries.selectMeta()?

bad_db "unknown column `nope` on table `entries`" RotatingVaultDb :
  rpc badProjCol() -> String[]!:
    requires auth
    return await db.entries.select(columns = ["nope"], where = r => r.ownerId == uid)?

/-! ## Item 4: Cross-Table `any m in tbl:` RLS Policies & Queries -/

database MultiTenantDb:
  sqlite ".qed/multi_tenant_checks.db"
  table apps:
    id      : String primary_key immutable where 1 <= id.length <= 64
    ownerId : String immutable where 1 <= ownerId.length <= 128
    orgId   : String?
    name    : String where 1 <= name.length <= 120
    policy read requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.id and some(m.userId) == ctx.userId and m.status == "accepted") or
      (any om in org_members: some(om.orgId) == row.orgId and some(om.userId) == ctx.userId)
    policy insert requires some(row.ownerId) == ctx.userId
    policy update requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])
    policy delete requires some(row.ownerId) == ctx.userId
  table app_members:
    id     : String primary_key immutable where 1 <= id.length <= 64
    appId  : String immutable references apps(id) on_delete cascade
    userId : String immutable where 1 <= userId.length <= 128
    role   : String where 1 <= role.length <= 32
    status : String where 1 <= status.length <= 32
    policy read, write requires ctx.userId != none
  table org_members:
    id     : String primary_key immutable where 1 <= id.length <= 64
    orgId  : String immutable where 1 <= orgId.length <= 64
    userId : String immutable where 1 <= userId.length <= 128
    policy read, write requires ctx.userId != none

example : strHasAll MultiTenantDb.rlsDdl [
  "EXISTS (SELECT 1 FROM \"app_members\" AS \"m\" WHERE",
  "\"apps\".\"id\"",
  "EXISTS (SELECT 1 FROM \"org_members\" AS \"om\" WHERE",
  "\"m\".\"role\" IN ('owner', 'admin')"] = true := by decide +kernel

server MultiTenantApi:
  use db : MultiTenantDb
  rpc createApp(id: String, name: String, orgId: String?) -> MultiTenantDb.apps!:
    requires auth, 1 <= id.length <= 64, 1 <= name.length <= 120, 1 <= uid.length <= 128
    return await db.apps.insert(id = id, ownerId = uid, orgId = orgId, name = name)?
  rpc addMember(id: String, appId: String, userId: String, role: String, status: String) -> MultiTenantDb.app_members!:
    requires auth, 1 <= id.length <= 64, 1 <= userId.length <= 128, 1 <= role.length <= 32, 1 <= status.length <= 32
    return await db.app_members.insert(id = id, appId = appId, userId = userId, role = role, status = status)?
  rpc addOrgMember(id: String, orgId: String, userId: String) -> MultiTenantDb.org_members!:
    requires auth, 1 <= id.length <= 64, 1 <= orgId.length <= 64, 1 <= userId.length <= 128
    return await db.org_members.insert(id = id, orgId = orgId, userId = userId)?
  rpc listOwnedApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.select(where = r => r.ownerId == uid, orderBy = "id")?
  rpc listAccessibleApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.select(where = r =>
      some(r.ownerId) == ctx.userId or
      (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted") or
      (any om in org_members: some(om.orgId) == r.orgId and some(om.userId) == ctx.userId), orderBy = "id")?
  rpc listSharedApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.select(where = r => any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted", orderBy = "id")?
  rpc renameAppAsAdmin(appId: String, newName: String) -> MultiTenantDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps.updateOne(
      where = r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"]),
      set = r => { name = newName })?
  rpc renameAppAsSpecificAdmin(appId: String, newName: String) -> MultiTenantDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps.updateOne(
      where = r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "admin"),
      set = r => { name = newName })?

bad_db "read policy `MultiTenantDb.apps.read`" MultiTenantDb :
  rpc leakAllApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.select()?

bad_db "read policy `MultiTenantDb.apps.read`" MultiTenantDb :
  rpc leakPendingApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.select(where = r => any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "pending")?

bad_db "update policy `MultiTenantDb.apps.update`" MultiTenantDb :
  rpc viewerCannotRename(appId: String, newName: String) -> MultiTenantDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps.updateOne(
      where = r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "viewer"),
      set = r => { name = newName })?

expect_err "unknown table `ghosts` in cross-table `any m in ghosts:`" in
database BadCrossTableRefDb:
  sqlite ".qed/bad_cross.db"
  table apps:
    id : String primary_key
    policy read requires any m in ghosts: m.appId == row.id

expect_err "cannot reference encrypted column `secrets.val` inside cross-table `any s in secrets:`" in
database BadCrossEncDb:
  sqlite ".qed/bad_cross_enc.db"
  table apps:
    id : String primary_key
    policy read requires any s in secrets: s.val == row.id
  table secrets:
    id  : String primary_key
    val : encrypted(String, key = secret("K"))

/-! ## Item 5: Database `example`, `rejects`, `transition_example`, `transition_rejects`, `policy_allows`, `policy_denies` -/

database VerifiedExamplesDb:
  sqlite ".qed/verified_examples_checks.db"
  table orders:
    id       : String primary_key immutable where 1 <= id.length <= 64
    ownerId  : String immutable where 1 <= ownerId.length <= 64
    status   : String where status in ["draft", "paid", "shipped", "cancelled"]
    amount   : Nat where amount <= 100000
    invariant paidPositive: status != "paid" or amount > 0
    invariant lifecycle: transition status: "draft" -> "paid" -> "shipped", "draft" -> "cancelled"
    policy read requires some(ownerId) == ctx.userId or ctx.claim("role") == some("admin") or (any s in shares: s.orderId == row.id and some(s.userId) == ctx.userId)
    policy write requires some(ownerId) == ctx.userId
    example draftOrder: id = "ord-1", ownerId = "u1", status = "draft", amount = 0
    example paidOrder from draftOrder: status = "paid", amount = 2500
    rejects zeroPaid from draftOrder: status = "paid", amount = 0
    rejects badStatus from draftOrder: status = "refunded"
    rejects overLimit from draftOrder: amount = 200000
    transition_example draftToPaid: draftOrder -> status = "paid", amount = 100
    transition_example draftToCancelled: draftOrder -> status = "cancelled"
    transition_rejects paidBackToDraft: paidOrder -> status = "draft"
    transition_rejects draftSkipToShipped: draftOrder -> status = "shipped"
    policy_allows read ownerCanRead:
      user = "u1"
      row = draftOrder
    policy_allows read adminCanRead:
      user = "u2"
      role = "admin"
      row = draftOrder
    policy_allows read sharedCanRead:
      user = "u3"
      row = draftOrder
      snap shares = [VerifiedExamplesDb.shares.mk("s1", "ord-1", "u3")]
    policy_denies read strangerDenied:
      user = "u9"
      row = draftOrder
    policy_denies write nonOwnerDenied:
      user = "u2"
      role = "admin"
      row = draftOrder
  table shares:
    id      : String primary_key immutable where 1 <= id.length <= 64
    orderId : String immutable references orders(id) on_delete cascade
    userId  : String immutable where 1 <= userId.length <= 64
    policy read, write requires ctx.userId != none

expect_err "Database `example badRow`" in
database BadDbExample:
  sqlite ".qed/bad_db_ex.db"
  table items:
    id : String primary_key where 1 <= id.length <= 16
    example badRow: id = ""

expect_err "Database `rejects badReject`" in
database BadDbRejects:
  sqlite ".qed/bad_db_rej.db"
  table items:
    id : String primary_key where 1 <= id.length <= 16
    rejects badReject: id = "ok"

expect_err "Database `transition_example badStep`" in
database BadDbTransEx:
  sqlite ".qed/bad_db_tex.db"
  table jobs:
    id : String primary_key where 1 <= id.length <= 16
    status : String where status in ["queued", "done"]
    invariant flow: transition status: "queued" -> "done"
    example doneJob: id = "j1", status = "done"
    transition_example badStep: doneJob -> status = "queued"

expect_err "Database `transition_rejects badRejStep`" in
database BadDbTransRej:
  sqlite ".qed/bad_db_trej.db"
  table jobs:
    id : String primary_key where 1 <= id.length <= 16
    status : String where status in ["queued", "done"]
    invariant flow: transition status: "queued" -> "done"
    example queuedJob: id = "j1", status = "queued"
    transition_rejects badRejStep: queuedJob -> status = "done"

expect_err "Database `policy_allows read badAllow`" in
database BadDbPolAllow:
  sqlite ".qed/bad_db_pallow.db"
  table docs:
    id : String primary_key where 1 <= id.length <= 16
    ownerId : String where 1 <= ownerId.length <= 16
    policy read requires some(ownerId) == ctx.userId
    example d1: id = "d1", ownerId = "alice"
    policy_allows read badAllow:
      user = "bob"
      row = d1

expect_err "Database `policy_denies read badDeny`" in
database BadDbPolDeny:
  sqlite ".qed/bad_db_pdeny.db"
  table docs:
    id : String primary_key where 1 <= id.length <= 16
    ownerId : String where 1 <= ownerId.length <= 16
    policy read requires some(ownerId) == ctx.userId
    example d1: id = "d1", ownerId = "alice"
    policy_denies read badDeny:
      user = "alice"
      row = d1

/-! ## Transactional, System-Scoped, and Conditional-Where DB Upgrades -/

database SysTxDb:
  sqlite ".qed/sys_tx_checks.db"
  table leases:
    id      : String primary_key where 1 <= id.length <= 32
    ownerId : String immutable   where 1 <= ownerId.length <= 32
    status  : String             where status in ["open", "claimed", "done"]
    retries : Nat                where retries <= 10
    policy read, write requires ctx.isSystem or some(row.ownerId) == ctx.userId
    invariant leaseFlow: transition row.status: "open" -> "claimed" -> "done"
    invariant retriesMono: row.retries >= old(row.retries)
    example openLease: id = "l1", ownerId = "alice", status = "open", retries = 0
    policy_allows read sysCanReadAny:
      system = true
      row = openLease
    policy_allows read ownerCanRead:
      user = "alice"
      row = openLease
    policy_denies read otherCannotRead:
      user = "bob"
      row = openLease
    policy_denies write anonCannotWrite:
      row = openLease

server stateless SysTxSrv:
  use db : SysTxDb

  fn claimInsideTx(tx: db.Tx, leaseId: String, uid: String) -> SysTxDb.leases?!:
    requires some(uid) == ctx.userId
    return await tx.leases.updateOne(
      where = r => r.id == leaseId and r.ownerId == uid and r.status == "open" and r.retries < 10,
      set = r => { status = "claimed", retries = r.retries + 1 })?

  rpc claimMyLease(leaseId: String) -> SysTxDb.leases?!:
    requires auth
    db.transaction as tx:
      return await claimInsideTx(tx, leaseId, uid)?

  system fn claimAnyOpen(leaseId: String) -> SysTxDb.leases?!:
    db.transaction as tx:
      return await tx.leases.updateOne(
        where = r => r.id == leaseId and r.status == "open" and r.retries < 10,
        set = r => { status = "claimed", retries = r.retries + 1 })?

  system fn bulkClaimOpen(onlyId: String?) -> SysTxDb.leases[]!:
    return await db.leases.update(
      where = r =>
        if let some(lid) = onlyId:
          r.id == lid and r.status == "open" and r.retries < 10
        else:
          r.status == "open" and r.retries < 10,
      set = r => { status = "claimed", retries = r.retries + 1 })?

  read_only rpc listMyLeases(onlyOpen: Bool, filterId: String?) -> SysTxDb.leases[]!:
    requires auth
    return await db.leases.select(
      where = r =>
        if onlyOpen:
          (r.id == filterId.getD("") if filterId != none else true) and r.ownerId == uid and r.status == "open"
        else:
          r.ownerId == uid)?

  read_only system fn countAllLeases(onlyOpen: Bool) -> Nat!:
    return await db.leases.count(
      where = r => (r.status == "open" if onlyOpen else true))?

  example systemCanCount:
    with db db.leases = [{ id = "l1", ownerId = "alice", status = "open", retries = 0 }, { id = "l2", ownerId = "bob", status = "done", retries = 1 }]
    call countAllLeases(true)
    expect ok(1)

  example ownerConditionalSelect:
    with user "alice"
    with db db.leases = [{ id = "l1", ownerId = "alice", status = "open", retries = 0 }, { id = "l2", ownerId = "alice", status = "done", retries = 1 }]
    call listMyLeases(true, none)
    expect ok([{ id = "l1", ownerId = "alice", status = "open", retries = 0 }])

expect_err "Database `policy_allows read badSysAllow`" in
database BadSysPolAllow:
  sqlite ".qed/bad_sys_pallow.db"
  table leases:
    id      : String primary_key where 1 <= id.length <= 32
    ownerId : String             where 1 <= ownerId.length <= 32
    policy read requires ctx.isSystem or some(ownerId) == ctx.userId
    example l1: id = "l1", ownerId = "alice"
    policy_allows read badSysAllow:
      user = "bob"
      row = l1

expect_err "Database read policy `SysTxDb.leases.read` failed in `sneakyReadAll → SysTxDb.leases.select`" in
server stateless BadNonSysRead:
  use db : SysTxDb
  rpc sneakyReadAll() -> SysTxDb.leases[]!:
    return await db.leases.select()?

expect_err "Database read policy `SysTxDb.leases.read` failed in `leakySelect → SysTxDb.leases.select`" in
server stateless BadCondWhereRls:
  use db : SysTxDb
  read_only rpc leakySelect(onlyOpen: Bool) -> SysTxDb.leases[]!:
    requires auth
    return await db.leases.select(
      where = r =>
        if onlyOpen:
          r.ownerId == uid and r.status == "open"
        else:
          r.status == "done")?

expect_err "Database update policy `SysTxDb.leases.update` failed in `badTxUpdate → SysTxDb.leases.updateOne`" in
service BadTxPolicyHelper:
  use db : SysTxDb
  fn badTxUpdate(tx: db.Tx, leaseId: String) -> SysTxDb.leases?!:
    return await tx.leases.updateOne(
      where = r => r.id == leaseId and r.status == "open" and r.retries < 10,
      set = r => { status = "claimed" })?

expect_err "Database transition/monotonicity invariant `SysTxDb.leases.TransInv` failed in `invalidReopen → SysTxDb.leases.updateOne`" in
service BadTxTransInv:
  use db : SysTxDb
  system fn invalidReopen(leaseId: String) -> SysTxDb.leases?!:
    return await db.leases.updateOne(
      where = r => r.id == leaseId and r.status == "done",
      set = r => { status = "open" })?

end DbChecks
