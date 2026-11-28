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
    policy read requires true
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
server VaultApi:
  use db : VaultDb
  rpc listBooks() -> VaultDb.books[]!: return await db.books.orderBy("id").select()?
  rpc listMyNotes() -> VaultDb.notes[]!:
    requires auth
    return await db.notes.where(r => r.ownerId == uid).orderBy("-version").limit(50).select()?
  -- Keep one explicit legacy `ctx.userId != none` RPC to verify backwards compatibility.
  rpc getNote(noteId: Nat) -> VaultDb.notes?!:
    requires ctx.userId != none
    ensures result.id == noteId
    if let some(uid) = ctx.userId: return await db.notes.where(r => r.id == noteId).where(r => r.ownerId == uid).findOne()?
    return none
  rpc countMyNotes() -> Nat!:
    requires auth
    return await db.notes.where(r => r.ownerId == uid).count()?
  rpc createNote(noteId: Nat, body: String) -> VaultDb.notes!:
    requires auth, 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body, 1 <= result.body.length <= 2000
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.notes.insert(id = noteId, ownerId = uid, body = body, version = 0, status = "draft")?
  rpc editNote(noteId: Nat, body: String) -> VaultDb.notes?!:
    requires auth, 1 <= body.length <= 2000
    ensures result.id == noteId, result.body == body
    return await db.notes.where(r => r.id == noteId and r.ownerId == uid).updateOne(r => { body = body, version = r.version + 1 })?
  rpc publishNote(noteId: Nat) -> VaultDb.notes?!:
    requires auth
    ensures result.id == noteId, result.status == "published"
    return await db.notes
      .where(r => r.id == noteId and r.ownerId == uid)
      .where(r => r.status == "draft")
      .updateOne(r => { status = "published", version = r.version + 1 })?
  rpc deleteNote(noteId: Nat) -> Nat!:
    requires auth
    return await db.notes.where(r => r.id == noteId and r.ownerId == uid).delete()?
  rpc seedBook(bookId: String, title: String, stock: Nat) -> VaultDb.books!:
    requires auth, 1 <= bookId.length <= 64, 1 <= title.length <= 200, stock <= 10000
    return await db.books.insert(id = bookId, title = title, stock = stock)?
  rpc orderBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires auth, 1 <= qty <= 50
    ensures result.id == bookId, result.stock <= 10000
    return await db.books.where(r => r.id == bookId and r.stock >= qty).updateOne(r => { stock = r.stock - qty })?
  rpc restockBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires auth, 1 <= qty <= 50
    return await db.books.where(r => r.id == bookId and r.stock + qty <= 10000).updateOne({ stock += qty })?
  rpc atomicOrderBook(bookId: String, qty: Nat) -> VaultDb.books?!:
    requires auth, 1 <= qty <= 50
    return await db.books.where(r => r.id == bookId and r.stock >= qty).updateOne({ stock -= qty })?
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
bad_db1 "Database read policy `VaultDb.notes.read` failed in `leakNote → VaultDb.notes.findOne`:\n  • must prove: some ownerId = ctx.userId" VaultDb leakNote(noteId: Nat) -> VaultDb.notes?! : return await db.notes.where(r => r.id == noteId).findOne()?
bad_db "Database read policy `VaultDb.notes.read` failed in `dumpAll → VaultDb.notes.select`:\n  • must prove: some ownerId = ctx.userId" VaultDb : rpc dumpAll() -> VaultDb.notes[]!: return await db.notes.select()?
bad_db1 "Database delete policy `VaultDb.notes.delete` failed in `nukeNote → VaultDb.notes.delete`:\n  • must prove: some ownerId = ctx.userId" VaultDb nukeNote(noteId: Nat) -> Nat! : return await db.notes.where(r => r.id == noteId).delete()?
bad_db_auth "Database update policy `VaultDb.notes.update` failed in `hijackEdit → VaultDb.notes.updateOne`:\n  • must prove: some ownerId = ctx.userId\n\nHint: Ensure `.where(r => ...)` implies `some(row.ownerId) == ctx.userId`.\n---\nerror: Database post-update policy `VaultDb.notes.update` (anti-hijack) failed in `hijackEdit → VaultDb.notes.updateOne`:\n  • must prove: some ownerId = ctx.userId" VaultDb hijackEdit(noteId: Nat, body: String) -> VaultDb.notes?! || 1 <= body.length <= 2000 : return await db.notes.where(r => r.id == noteId).updateOne(r => { body = body, version = r.version + 1 })?
bad_db_auth "Database insert policy `VaultDb.notes.insert` failed in `spoofInsert → VaultDb.notes.insert`:\n  • must prove: some \"victim\" = ctx.userId" VaultDb spoofInsert(noteId: Nat, body: String) -> VaultDb.notes! || 1 <= body.length <= 2000 : return await db.notes.insert(id = noteId, ownerId = "victim", body = body, version = 0, status = "draft")?
bad_db1 "cannot update `immutable` column `VaultDb.notes.ownerId` in `stealOwner`" VaultDb stealOwner(noteId: Nat) -> VaultDb.notes?! : return await db.notes.where(r => r.id == noteId and r.ownerId == ctx.userId.getD("")).updateOne(r => { ownerId = "attacker" })?
bad_db_auth "Database table constraint `VaultDb.notes.RowInv` failed in `emptyNote → VaultDb.notes.insert`" VaultDb emptyNote(noteId: Nat) -> VaultDb.notes! : if not (1 <= uid.length <= 64): return fail(.badUser) || return await db.notes.insert(id = noteId, ownerId = uid, body = "", version = 0, status = "draft")?
bad_db1 "Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `downgradeVersion → VaultDb.notes.updateOne`:\n  • must prove: version - 1 >= version" VaultDb downgradeVersion(noteId: Nat) -> VaultDb.notes?! : return await db.notes.where(r => r.id == noteId and r.ownerId == ctx.userId.getD("") and r.version >= 1).updateOne(r => { version = r.version - 1 })?
bad_db1 "Database transition/monotonicity invariant `VaultDb.notes.TransInv` failed in `skipPublish → VaultDb.notes.updateOne`:\n  • must prove: version >= version and ((\"archived\" = \"draft\" or \"archived\" = \"published\") or \"draft\" = \"published\")" VaultDb skipPublish(noteId: Nat) -> VaultDb.notes?! : return await db.notes.where(r => r.id == noteId and r.ownerId == ctx.userId.getD("") and r.status == "draft").updateOne(r => { status = "archived" })?
bad_db1 "Database table constraint `VaultDb.books.RowInv` failed in `restockOverflow → VaultDb.books.updateOne`:\n  • must prove: stock + 5 <= 10000" VaultDb restockOverflow(bookId: String) -> VaultDb.books?! : return await db.books.where(r => r.id == bookId).updateOne(r => { stock = r.stock + 5 })?
bad_comp_sess "RPC `VaultApi.createNote` precondition `1 <= body.length <= 2000` could not be proved here:\n  • must satisfy:  1 <= \"\".length and \"\".length <= 2000" BadClientParam : if user.isSome: let _ = await VaultApi.createNote(1, "") catch: case _: pass
bad_comp_query "reactive `query bad` cannot call mutating server RPC `VaultApi.deleteNote`" BadClientQueryMut bad = VaultApi.deleteNote(1) if user.isSome

/-! ## Extended Verified Database Layer: Richer SQL, FK Joins, Transactions & Migrations -/
database ShopDb:
  url secret("QED_TEST_SHOP_URL")
  dev sqlite ".qed/shop_checks.db"
  table authors:
    id   : String primary_key where 1 <= id.length <= 64
    name : String             where 1 <= name.length <= 120
    policy read requires true
    policy write requires ctx.userId != none
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
server ShopApi:
  use db : ShopDb
  state txOps : Nat = 0
  invariant txOpsNonNeg: txOps >= 0
  rpc searchItems(pfx: String, sub: String, pageOffset: Nat) -> ShopDb.items[]!:
    requires auth
    return await db.items
      .where(r => r.ownerId == uid and r.title.startsWith(pfx) and r.title.contains(sub))
      .orderBy("-price").limit(20).offset(pageOffset)
      .select()?
  rpc filterByIds(ids: String[]) -> ShopDb.items[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid and ids.contains(r.id)).orderBy("id").limit(50).offset(0).select()?
  rpc totalInventoryValue() -> Nat!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).sum("price")?
  rpc cheapestPrice() -> Nat?!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).min("price")?
  rpc highestPrice() -> Nat?!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).max("price")?
  rpc itemsWithAuthors() -> (ShopDb.items, ShopDb.authors)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).join(authors).orderBy("-price").limit(25).offset(0).select()?
  rpc topItemWithAuthor() -> (ShopDb.items, ShopDb.authors)?!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).join(authors).orderBy("-price").findOne()?
  rpc countItemsByAuthor() -> (String, Nat)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).groupBy("authorId").orderBy("-count").limit(10).count()?
  rpc sumPriceByAuthor() -> (String, Nat)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).groupBy("authorId").orderBy("-sum").sum("price")?
  rpc minPriceByAuthor() -> (String, Nat)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).groupBy("authorId").orderBy("authorId").min("price")?
  rpc maxPriceByAuthor() -> (String, Nat)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).groupBy("authorId").orderBy("authorId").max("price")?
  rpc countByOwnerAndAuthor() -> (String, String, Nat)[]!:
    requires auth
    return await db.items.where(r => r.ownerId == uid).groupBy(["ownerId", "authorId"]).orderBy("authorId").count()?
  rpc logsWithProfiles() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]!:
    requires auth
    return await db.secretLogs.where(r => r.ownerId == uid).join(privateProfiles, p => p.ownerId == uid).select()?
  rpc addItem(iid: String, aid: String, title: String, price: Nat) -> ShopDb.items!:
    requires auth, 1 <= iid.length <= 64, 1 <= aid.length <= 64, 1 <= title.length <= 200, price <= 100000
    if not (1 <= uid.length <= 64): return fail(.badUser)
    return await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?
  rpc createAuthorAndItem(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires auth, 1 <= aid.length <= 64, 1 <= aname.length <= 120, 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid, result.price == price
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction: let _a = await db.authors.insert(id = aid, name = aname)?; let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?; atomic: txOps += 1; return created
  rpc createPairDotSyntax(aid: String, aname: String, iid: String, title: String, price: Nat) -> ShopDb.items!:
    requires auth, 1 <= aid.length <= 64, 1 <= aname.length <= 120, 1 <= iid.length <= 64, 1 <= title.length <= 200, price <= 100000
    ensures result.id == iid
    if not (1 <= uid.length <= 64): return fail(.badUser)
    db.transaction:
      let _a = await db.authors.insert(id = aid, name = aname)?
      if price == 99999: return fail(.aborted)
      let created = await db.items.insert(id = iid, authorId = aid, ownerId = uid, title = title, price = price)?
      return created
  rpc insertAuthorOrIgnore(aid: String, aname: String) -> ShopDb.authors?!:
    requires auth, 1 <= aid.length <= 64, 1 <= aname.length <= 120
    return await db.authors.insertOrIgnore(id = aid, name = aname)?
  rpc abortedDupAuthorTx(aid: String) -> Bool!:
    requires auth, 1 <= aid.length <= 64
    db.transaction:
      let _ = await db.authors.insert(id = aid, name = "dup-pk-error")
        catch _e: ShopDb.authors.mk(aid, "fallback")
      return true
  rpc txInsertAuthorOrIgnore(aid: String, aname: String) -> ShopDb.authors?!:
    requires auth, 1 <= aid.length <= 64, 1 <= aname.length <= 120
    db.transaction:
      return await db.authors.insertOrIgnore(id = aid, name = aname)?
bad_db "Database read policy `ShopDb.items.read` failed in `leakSum → ShopDb.items.sum`:\n  • must prove: some ownerId = ctx.userId" ShopDb : rpc leakSum() -> Nat!: return await db.items.sum("price")?
bad_db_auth "Database read policy `ShopDb.privateProfiles.read` (joined table) failed in `leakProfileJoin → ShopDb.secretLogs.select`:\n  • must prove: some ownerId = ctx.userId" ShopDb leakProfileJoin() -> (ShopDb.secretLogs, ShopDb.privateProfiles)[]! : return await db.secretLogs.where(r => r.ownerId == uid).join(privateProfiles).select()?
bad_db_auth "Database insert policy `ShopDb.items.insert` failed in `badTxInsert → ShopDb.items.insert`:\n  • must prove: some \"victim\" = ctx.userId" ShopDb badTxInsert(aid: String, iid: String) -> ShopDb.items! || 1 <= aid.length <= 64, 1 <= iid.length <= 64 : db.transaction: return await db.items.insert(id = iid, authorId = aid, ownerId = "victim", title = "oops", price = 10)?

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
    have hpt : 1 ≤ input.body.val.utf8ByteSize ∧ input.body.val.utf8ByteSize ≤ 200 := input.body.ok; have hsz := Qed.toUTF8_size input.body.val
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

server CipherApi:
  use db : CipherDb
  use vdb : VaultDb
  rpc saveSealed(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes!:
    requires auth
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.sealedNotes.insert(id = noteId, ownerId = uid, ciphertext = sealedNoteMap.encode(input))?
  rpc editSealed(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes?!:
    requires auth
    return await db.sealedNotes.where(r => r.id == noteId and r.ownerId == uid).updateOne(r => { ciphertext = sealedNoteMap.encode(input) })?
  rpc savePlainFromSchema(noteId: Nat, input: PlainNoteInput) -> VaultDb.notes!:
    requires auth
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await vdb.notes.insert(id = noteId, ownerId = uid, body = input.body, version = 0, status = "draft")?

bad_db_auth "Database table constraint `CipherDb.sealedNotes.RowInv` failed in `driftInsert → CipherDb.sealedNotes.insert`" CipherDb driftInsert(noteId: Nat, input: SecretNoteInput) -> CipherDb.sealedNotes! : if not (1 <= uid.length <= 64): return fail(.invalidUser) || return await db.sealedNotes.insert(id = noteId, ownerId = uid, ciphertext = widerCipherMap.encode(input))?

/-! ## Surface `mapping` DSL, Built-in `encrypted(...)` DB Columns & `{field}` View Rendering -/
mapping DollarsToCentsMap:
  from dollars : Nat where dollars <= 10000
  to   cents   : Nat where cents <= 1000000
  encode(d): return d * 100
  decode(c):
    if c % 100 == 0: return c / 100
    fail("must be whole dollars")

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

server EncVaultApi:
  use db : EncVaultDb
  rpc save(noteId: Nat, input: SecretNoteInput, rawOpt: Bytes?) -> EncVaultDb.entries!:
    requires auth
    ensures result.id == noteId
    if not (1 <= uid.length <= 64): return fail(.invalidUser)
    return await db.entries.insert(id = noteId, ownerId = uid, body = input.body, note = "ok", raw = rawOpt)?
  rpc edit(noteId: Nat, input: SecretNoteInput) -> EncVaultDb.entries?!:
    requires auth
    ensures result.id == noteId
    return await db.entries.where(r => r.id == noteId and r.ownerId == uid).updateOne(r => { body = input.body })?
  rpc scaleId(noteId: Nat) -> EncVaultDb.entries?!:
    requires auth
    return await db.entries.where(r => r.id == noteId and r.ownerId == uid).updateOne({ note = "scaled", })?
  rpc get(noteId: Nat) -> EncVaultDb.entries?!:
    requires auth
    ensures result.id == noteId
    return await db.entries.where(r => r.id == noteId and r.ownerId == uid).findOne()?
  rpc list() -> EncVaultDb.entries[]!:
    requires auth
    return await db.entries.where(r => r.ownerId == uid).orderBy("id").select()?
  rpc listFiltered(exactId: Nat?, minId: Nat?) -> EncVaultDb.entries[]!:
    requires auth
    return await db.entries.where(r => r.ownerId == uid and (if let some(id) = exactId: r.id == id elif let some(lo) = minId: r.id >= lo else: true)).orderBy("id").select()?

component FieldRenderCheck:
  state items : SecretNoteInput[] = []
  view: <ul>{for item in items: <li key={item.body}><span>{item.body}</span></li>}</ul>

bad_db1 "cannot reference encrypted column `entries.body` inside SQL `where`" EncVaultDb badWhere(q: String) -> EncVaultDb.entries[]! : return await db.entries.where(r => r.ownerId == ctx.userId.getD("") and r.body == q).select()?
bad_db1 "cannot `orderBy` encrypted column `entries.body`" EncVaultDb badOrder(x: Nat) -> EncVaultDb.entries[]! : return await db.entries.where(r => r.ownerId == ctx.userId.getD("")).orderBy("body").select()?
bad_db1 "cannot compute SQL aggregate on encrypted column `entries.body`" EncVaultDb badAgg(x: Nat) -> String?! : return await db.entries.where(r => r.ownerId == ctx.userId.getD("")).min("body")?
bad_db1 "cannot update encrypted column `EncVaultDb.entries.body` using a row-dependent SQL expression" EncVaultDb badSet(x: Nat) -> EncVaultDb.entries?! : return await db.entries.where(r => r.id == x and r.ownerId == ctx.userId.getD("")).updateOne(r => { body = r.body })?
bad_db_tbl "cannot index encrypted column `bad.body`" BadEncIndexDb bad : id : Nat primary_key || body : encrypted(String, key = secret("K")) || index (body)
bad_db_tbl "encrypted column `bad.body` cannot be `unique`" BadEncUniqueDb bad : id : Nat primary_key || body : encrypted(String, key = secret("K")) unique

/-! ## Track 3 & 4: Unit `enum`, `on_delete`, `backfill`, `upsert`, Table Invariants & `Str.*` Bounds -/
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
    policy read, write requires true
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
    policy read, write requires true
  table services:
    slug    : ServiceSlug primary_key
    port    : ServicePort
    altPort : ServicePort?
    policy read, write requires true
  table scaling:
    id           : String primary_key where 1 <= id.length <= 64
    plan         : String
    minInstances : Nat
    maxInstances : Nat
    policy read, write requires true
    invariant freeScaling:
      minInstances <= maxInstances,
      (plan == "pro" or plan == "enterprise") or (minInstances == 0 and maxInstances <= 1)
  table slots:
    id      : String primary_key where 1 <= id.length <= 64
    ownerId : String immutable   where 1 <= ownerId.length <= 64
    label   : String             where 1 <= label.length <= 64
    tag     : String             where tag.length <= 16
    code    : String             where code.length <= 32
    policy read, write requires some(ownerId) == ctx.userId
  backfill projects set { note = "migrated" } where r => r.note == none

server RoadmapApi:
  use db : RoadmapDb
  rpc createAndUpsert(orgId: String, projId: String, stg: DeployStage) -> RoadmapDb.projects!:
    requires auth, 1 <= orgId.length <= 64, 1 <= projId.length <= 64, stg == .queued
    let _o = await db.orgs.upsert(on = "id", id = orgId, name = "Acme")?
    return await db.projects.where(r => r.ownerId == uid and r.stage == .queued).upsert(on = ["id"], id = projId, orgId = orgId, ownerId = uid, stage = .queued, note = some("ok"))?
  rpc listLive() -> RoadmapDb.projects[]!:
    requires auth
    return await db.projects.where(r => r.ownerId == uid and r.stage == .live).select()?
  rpc advanceToBuilding(projId: String) -> RoadmapDb.projects?!:
    requires auth
    return await db.projects.where(r => r.id == projId and r.ownerId == uid and r.stage == .queued).updateOne({ stage = .building })?
  rpc registerService(rawSlug: String, rawPort: Nat) -> RoadmapDb.services!:
    let s = ServiceSlug.parse(rawSlug)?
    let p = ServicePort.parse(rawPort)?
    return await db.services.insert(slug = s, port = p, altPort = some(ServicePort.make(8443)))?
  rpc registerDefaultService() -> RoadmapDb.services!:
    return await db.services.insert(slug = "api", port = 8080)?
  rpc idempotentOrg(orgId: String, name: String) -> RoadmapDb.orgs?!:
    requires 1 <= orgId.length <= 64, 1 <= name.length <= 64
    return await db.orgs.insertOrIgnore(id = orgId, name = name)?
  rpc insertOrg(orgId: String, name: String) -> RoadmapDb.orgs!:
    requires 1 <= orgId.length <= 64, 1 <= name.length <= 120
    return await db.orgs.insert(id = orgId, name = name)?
  rpc getOrg(orgId: String) -> RoadmapDb.orgs?!:
    return await db.orgs.where(r => r.id == orgId).findOne()?
  rpc abortTxInsertOrg(orgId: String, name: String) -> Bool!:
    requires 1 <= orgId.length <= 64, 1 <= name.length <= 120
    db.transaction:
      let _ = await db.orgs.insert(id = orgId, name = name)?
      return fail(.aborted)
  rpc insertProject(projId: String, orgId: String) -> RoadmapDb.projects!:
    requires auth, 1 <= projId.length <= 64, 1 <= orgId.length <= 64, 1 <= uid.length <= 128
    return await db.projects.insert(id = projId, orgId = orgId, ownerId = uid, stage = .queued, note = none)?
  rpc getProject(projId: String) -> RoadmapDb.projects?!:
    requires auth
    return await db.projects.where(r => r.id == projId and r.ownerId == uid).findOne()?
  rpc upsertBuilding(projId: String, orgId: String, note: String?) -> RoadmapDb.projects!:
    requires auth, 1 <= projId.length <= 64, 1 <= orgId.length <= 64, 1 <= uid.length <= 128
    return await db.projects.where(r => r.ownerId == uid and r.stage == .queued).upsert(on = ["id"], id = projId, orgId = orgId, ownerId = uid, stage = .building, note = note)?
  rpc promoteToLive(projId: String) -> RoadmapDb.projects?!:
    requires auth
    return await db.projects.where(r => r.id == projId and r.ownerId == uid and r.stage == .building).updateOne({ stage = .live })?
  rpc countLive() -> Nat!:
    requires auth
    return await db.projects.where(r => r.ownerId == uid and r.stage == .live).count()?
  rpc deleteProject(projId: String) -> Nat!:
    requires auth
    return await db.projects.where(r => r.id == projId and r.ownerId == uid).delete()?
  rpc insertScaling(id: String, minI: Nat, maxI: Nat) -> RoadmapDb.scaling!:
    requires 1 <= id.length <= 64, minI <= maxI
    return await db.scaling.insert(id = id, plan = "pro", minInstances = minI, maxInstances = maxI)?
  rpc bumpScalingMax(id: String, delta: Nat) -> RoadmapDb.scaling?!:
    return await db.scaling.where(r => r.id == id and r.plan == "pro").updateOne({ maxInstances += delta })?
  rpc decScalingMax(id: String, delta: Nat) -> RoadmapDb.scaling?!:
    return await db.scaling.where(r => r.id == id and r.plan == "pro" and r.maxInstances >= r.minInstances + delta).updateOne({ maxInstances -= delta })?
  rpc findByTrimmedOwner(rawOwner: String) -> RoadmapDb.projects[]!:
    let clean = Qed.Str.truncate(Qed.Str.toLower(Qed.Str.trim(rawOwner)), 64)
    if some(clean) != ctx.userId: return fail(.forbidden)
    return await db.projects.where(r => r.ownerId == clean).select()?
  fn allocSlot(rawId: String, rawLabel: String, rawTag: String, rawCode: String) -> RoadmapDb.slots!:
    requires auth, 1 <= uid.length <= 64, 1 <= rawId.length, 1 <= rawLabel.length, rawCode.length <= 32
    return await db.slots.insert(id = Qed.Str.truncate(rawId, 64), ownerId = uid, label = Qed.Str.truncate(rawLabel, 64), tag = Qed.Str.take(rawTag, 16), code = Qed.Str.toLower(Qed.Str.trim(rawCode)))?
  fn relabelSlot(slotId: String, rawLabel: String, rawTag: String) -> RoadmapDb.slots?!:
    requires auth, 1 <= rawLabel.length
    return await db.slots.where(r => r.id == slotId and r.ownerId == uid).updateOne({ label = Qed.Str.truncate(rawLabel, 64), tag = Qed.Str.take(rawTag, 16) })?

bad_db "Database table constraint `RoadmapDb.scaling.RowInv` failed in `badFreeWarm → RoadmapDb.scaling.insert`" RoadmapDb :
  rpc badFreeWarm(appId: String) -> RoadmapDb.scaling!:
    requires 1 <= appId.length <= 64
    return await db.scaling.insert(id = appId, plan = "free", minInstances = 1, maxInstances = 1)?
bad_db_auth "Nat non-underflow for `books.stock -= ...`" VaultDb badAtomicDec(bookId: String, qty: Nat) -> VaultDb.books?! || 1 <= qty <= 50 : return await db.books.where(r => r.id == bookId).updateOne({ stock -= qty })?
bad_db_auth "Database upsert conflict update policy `RoadmapDb.projects.update` failed in `badUpsert → RoadmapDb.projects.upsert`" RoadmapDb badUpsert(orgId: String, projId: String) -> RoadmapDb.projects! || 1 <= orgId.length <= 64, 1 <= projId.length <= 64 : return await db.projects.upsert(on = "id", id = projId, orgId = orgId, ownerId = uid, stage = .queued, note = none)?
bad_db_def "`on_delete set_null` on `bad.orgId` requires a nullable column (`T?`)" BadSetNullDb :
  table orgs:
    id : String primary_key
  || table bad:
      id    : String primary_key
      orgId : String references orgs(id) on_delete set_null

/-! ## Item 6: Encrypted Column Projections (`Meta`, `selectMeta`, `.columns(...)`) & `prevKeys` Rotation -/
database RotatingVaultDb:
  sqlite ".qed/rotating_vault_checks.db"
  table entries:
    id      : Nat primary_key immutable
    ownerId : String immutable where 1 <= ownerId.length <= 128
    label   : String where 1 <= label.length <= 120
    secret  : encrypted(String, key = secret("VAULT_PRIMARY_KEY"), prevKeys = [secret("VAULT_PREV_KEY"), secret("VAULT_LEGACY_KEY")]) where 1 <= secret.length <= 512
    policy read, write requires some(row.ownerId) == ctx.userId
server RotatingVaultApi:
  use db : RotatingVaultDb
  rpc save(id: Nat, label: String, secret: String) -> RotatingVaultDb.entries!:
    requires auth, 1 <= uid.length <= 128, 1 <= label.length <= 120, 1 <= secret.length <= 512
    return await db.entries.insert(id = id, ownerId = uid, label = label, secret = secret)?
  rpc get(id: Nat) -> RotatingVaultDb.entries?!:
    requires auth
    return await db.entries.where(r => r.id == id and r.ownerId == uid).findOne()?
  rpc rotateValue(id: Nat, secret: String) -> RotatingVaultDb.entries?!:
    requires auth, 1 <= secret.length <= 512
    return await db.entries.where(r => r.id == id and r.ownerId == uid).updateOne({ secret = secret })?
  rpc listMeta() -> RotatingVaultDb.entries.Meta[]!:
    requires auth
    return await db.entries.where(r => r.ownerId == uid).orderBy("id").selectMeta()?
  rpc getMeta(id: Nat) -> RotatingVaultDb.entries.Meta?!:
    requires auth
    return await db.entries.where(r => r.id == id and r.ownerId == uid).findOneMeta()?
  rpc listLabels() -> (Nat, String)[]!:
    requires auth
    return await db.entries.where(r => r.ownerId == uid).orderBy("id").columns(["id", "label"]).select()?
  rpc getLabel(id: Nat) -> String?!:
    requires auth
    return await db.entries.where(r => r.id == id and r.ownerId == uid).columns("label").findOne()?
bad_db_auth "read policy `RotatingVaultDb.entries.read`" RotatingVaultDb leakMeta() -> RotatingVaultDb.entries.Meta[]! : return await db.entries.selectMeta()?
bad_db_auth "unknown column `nope` on table `entries`" RotatingVaultDb badProjCol() -> String[]! : return await db.entries.where(r => r.ownerId == uid).columns(["nope"]).select()?

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
  table deployments:
    id      : String primary_key immutable where 1 <= id.length <= 64
    appId   : String immutable references apps(id) on_delete cascade
    ownerId : String immutable where 1 <= ownerId.length <= 128
    label   : String where 1 <= label.length <= 120
    active  : Bool
    policy read requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.appId and some(m.userId) == ctx.userId and m.status == "accepted") or
      (any a in apps: a.id == row.appId and (any om in org_members: some(om.orgId) == a.orgId and some(om.userId) == ctx.userId))
    policy insert requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"]) or
      (any a in apps: a.id == row.appId and (any om in org_members: some(om.orgId) == a.orgId and some(om.userId) == ctx.userId))
    policy update, delete requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])
    example dep1: id = "d1", appId = "app1", ownerId = "alice", label = "v1", active = true
    example insert ownerCanInsertDep:
      user = "alice"
      row = dep1
    example insert adminCanInsertDep:
      user = "charlie"
      row = dep1
      snap app_members = [MultiTenantDb.app_members.mk("m1", "app1", "charlie", "admin", "accepted")]
    rejects insert viewerCannotInsertDep:
      user = "dave"
      row = dep1
      snap app_members = [MultiTenantDb.app_members.mk("m2", "app1", "dave", "viewer", "accepted")]
  table app_secrets:
    id      : String primary_key immutable where 1 <= id.length <= 64
    appId   : String immutable references apps(id) on_delete cascade
    ownerId : String immutable where 1 <= ownerId.length <= 128
    secret  : encrypted(String, key = secret("MT_SECRET_KEY") ?? "mt-dev-secret-key-32") where 1 <= secret.length <= 200
    policy read, insert, update, delete requires
      some(row.ownerId) == ctx.userId or
      (any m in app_members: m.appId == row.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])

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
    return await db.apps.where(r => r.ownerId == uid).orderBy("id").select()?
  rpc listAccessibleApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps
      .where(r =>
        some(r.ownerId) == ctx.userId or
        (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted") or
        (any om in org_members: some(om.orgId) == r.orgId and some(om.userId) == ctx.userId))
      .orderBy("id").select()?
  rpc listSharedApps() -> MultiTenantDb.apps[]!:
    requires auth
    return await db.apps.where(r => any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted").orderBy("id").select()?
  rpc renameAppAsAdmin(appId: String, newName: String) -> MultiTenantDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps
      .where(r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"]))
      .updateOne(r => { name = newName })?
  rpc renameAppAsSpecificAdmin(appId: String, newName: String) -> MultiTenantDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps
      .where(r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "admin"))
      .updateOne(r => { name = newName })?
  rpc deployAsOwner(depId: String, appId: String, label: String) -> MultiTenantDb.deployments!:
    requires auth, 1 <= depId.length <= 64, 1 <= label.length <= 120, 1 <= uid.length <= 128
    return await db.deployments.insert(id = depId, appId = appId, ownerId = uid, label = label, active = true)?
  rpc deployAsAdmin(depId: String, appId: String, appOwnerId: String, label: String) -> MultiTenantDb.deployments!:
    requires auth, 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128, 1 <= label.length <= 120
    return await db.deployments
      .where(r => any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "admin")
      .insert(id = depId, appId = appId, ownerId = appOwnerId, label = label, active = true)?
  rpc deployAsAdminBareWhere(depId: String, appId: String, appOwnerId: String, label: String) -> MultiTenantDb.deployments!:
    requires auth, 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128, 1 <= label.length <= 120
    return await db.deployments
      .where(_ => any m in app_members: m.appId == appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])
      .insert(id = depId, appId = appId, ownerId = appOwnerId, label = label, active = true)?
  rpc deployAsOrgMember(depId: String, appId: String, appOwnerId: String, label: String) -> MultiTenantDb.deployments!:
    requires auth, 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128, 1 <= label.length <= 120
    return await db.deployments
      .where(r => any a in apps: a.id == r.appId and (any om in org_members: some(om.orgId) == a.orgId and some(om.userId) == ctx.userId))
      .insert(id = depId, appId = appId, ownerId = appOwnerId, label = label, active = true)?
  rpc deployRowAsAdmin(row: MultiTenantDb.deployments) -> MultiTenantDb.deployments!:
    requires auth, 1 <= row.id.length <= 64, 1 <= row.ownerId.length <= 128, 1 <= row.label.length <= 120
    return await db.deployments
      .where(r => any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "admin")
      .insert(row)?
  rpc deployIdempotentAsAdmin(depId: String, appId: String, appOwnerId: String, label: String) -> MultiTenantDb.deployments?!:
    requires auth, 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128, 1 <= label.length <= 120
    return await db.deployments
      .where(r => any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])
      .insertOrIgnore(on = "id", id = depId, appId = appId, ownerId = appOwnerId, label = label, active = true)?
  rpc createSecretAsAdmin(secId: String, appId: String, appOwnerId: String, secretVal: String) -> MultiTenantDb.app_secrets!:
    requires auth, 1 <= secId.length <= 64, 1 <= appOwnerId.length <= 128, 1 <= secretVal.length <= 200
    return await db.app_secrets
      .where(r => some(r.ownerId) == ctx.userId or (any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"]))
      .insert(id = secId, appId = appId, ownerId = appOwnerId, secret = secretVal)?
  rpc listDeployments(appId: String) -> MultiTenantDb.deployments[]!:
    requires auth
    return await db.deployments
      .where(r => r.appId == appId and (
        some(r.ownerId) == ctx.userId or
        (any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted") or
        (any a in apps: a.id == r.appId and (any om in org_members: some(om.orgId) == a.orgId and some(om.userId) == ctx.userId))))
      .orderBy("id").select()?
  rpc listSecrets(appId: String) -> MultiTenantDb.app_secrets[]!:
    requires auth
    return await db.app_secrets
      .where(r => r.appId == appId and (
        some(r.ownerId) == ctx.userId or
        (any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role in ["owner", "admin"])))
      .orderBy("id").select()?
  example adminCanDeployAndViewerRejected:
    with user "charlie"
    with db db.apps = [{ id = "app1", ownerId = "alice", orgId = none, name = "Alpha" }]
    with db db.app_members = [{ id = "m1", appId = "app1", userId = "charlie", role = "admin", status = "accepted" }]
    call deployAsAdmin("d1", "app1", "alice", "v1")
    expect ok
    expect db_count("deployments") == 1
  example viewerDeployRejectedAtRuntime:
    with user "dave"
    with db db.apps = [{ id = "app1", ownerId = "alice", orgId = none, name = "Alpha" }]
    with db db.app_members = [{ id = "m2", appId = "app1", userId = "dave", role = "viewer", status = "accepted" }]
    call deployAsAdmin("d1", "app1", "alice", "v1")
    expect error(403)
    expect db_count("deployments") == 0
  example orgMemberCanDeployNested:
    with user "frank"
    with db db.apps = [{ id = "app2", ownerId = "alice", orgId = some("org1"), name = "Beta" }]
    with db db.org_members = [{ id = "om1", orgId = "org1", userId = "frank" }]
    call deployAsOrgMember("d2", "app2", "alice", "org-rel")
    expect ok
    expect db_count("deployments") == 1
  example outsiderOrgDeployRejected:
    with user "mallory"
    with db db.apps = [{ id = "app2", ownerId = "alice", orgId = some("org1"), name = "Beta" }]
    with db db.org_members = [{ id = "om1", orgId = "org1", userId = "frank" }]
    call deployAsOrgMember("d2", "app2", "alice", "org-rel")
    expect error(403)
    expect db_count("deployments") == 0
  example unauthorizedInsertOrIgnoreReturnsNone:
    with user "dave"
    with db db.apps = [{ id = "app1", ownerId = "alice", orgId = none, name = "Alpha" }]
    with db db.app_members = [{ id = "m2", appId = "app1", userId = "dave", role = "viewer", status = "accepted" }]
    call deployIdempotentAsAdmin("d1", "app1", "alice", "v1")
    expect ok(none)
    expect db_count("deployments") == 0

bad_db_auth "read policy `MultiTenantDb.apps.read`" MultiTenantDb leakAllApps() -> MultiTenantDb.apps[]! : return await db.apps.select()?
bad_db_auth "read policy `MultiTenantDb.apps.read`" MultiTenantDb leakPendingApps() -> MultiTenantDb.apps[]! : return await db.apps.where(r => any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "pending").select()?
bad_db_auth "update policy `MultiTenantDb.apps.update`" MultiTenantDb viewerCannotRename(appId: String, newName: String) -> MultiTenantDb.apps?! || 1 <= newName.length <= 120 : return await db.apps.where(r => r.id == appId and (any m in app_members: m.appId == r.id and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "viewer")).updateOne(r => { name = newName })?
bad_db_auth "For cross-table insert policies, chain `.where(r => any ... in ...:)`" MultiTenantDb unguardedCrossInsert(depId: String, appId: String, appOwnerId: String) -> MultiTenantDb.deployments! || 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128 : return await db.deployments.insert(id = depId, appId = appId, ownerId = appOwnerId, label = "v1", active = true)?
bad_db_auth "insert policy `MultiTenantDb.deployments.insert`" MultiTenantDb viewerCannotDeploy(depId: String, appId: String, appOwnerId: String) -> MultiTenantDb.deployments! || 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128 : return await db.deployments.where(r => any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "viewer").insert(id = depId, appId = appId, ownerId = appOwnerId, label = "v1", active = true)?
bad_db_auth "insert policy `MultiTenantDb.deployments.insert`" MultiTenantDb pendingCannotDeploy(depId: String, appId: String, appOwnerId: String) -> MultiTenantDb.deployments! || 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128 : return await db.deployments.where(r => any m in app_members: m.appId == r.appId and some(m.userId) == ctx.userId and m.status == "pending" and m.role == "admin").insert(id = depId, appId = appId, ownerId = appOwnerId, label = "v1", active = true)?
bad_db_auth "shadows an outer row/table variable" MultiTenantDb shadowedAliasInsert(depId: String, appId: String, appOwnerId: String) -> MultiTenantDb.deployments! || 1 <= depId.length <= 64, 1 <= appOwnerId.length <= 128 : return await db.deployments.where(r => any r in app_members: r.appId == appId and some(r.userId) == ctx.userId and r.status == "accepted" and r.role == "admin").insert(id = depId, appId = appId, ownerId = appOwnerId, label = "v1", active = true)?
bad_db_tbl "unknown table `ghosts` in cross-table `any m in ghosts:`" BadCrossTableRefDb apps : id : String primary_key || policy read requires any m in ghosts: m.appId == row.id
bad_db_def "cannot reference encrypted column `secrets.val` inside cross-table `any s in secrets:`" BadCrossEncDb :
  table apps:
    id : String primary_key
    policy read requires any s in secrets: s.val == row.id
  || table secrets:
      id  : String primary_key
      val : encrypted(String, key = secret("K"))

/-! ## Item 5: Database `example` / `rejects` (rows, transitions, and policies) -/
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
    example transition draftToPaid: draftOrder -> status = "paid", amount = 100
    example transition draftToCancelled: draftOrder -> status = "cancelled"
    rejects transition paidBackToDraft: paidOrder -> status = "draft"
    rejects transition draftSkipToShipped: draftOrder -> status = "shipped"
    example read ownerCanRead:
      user = "u1"
      row = draftOrder
    example read adminCanRead:
      user = "u2"
      role = "admin"
      row = draftOrder
    example read sharedCanRead:
      user = "u3"
      row = draftOrder
      snap shares = [VerifiedExamplesDb.shares.mk("s1", "ord-1", "u3")]
    rejects read strangerDenied:
      user = "u9"
      row = draftOrder
    rejects write nonOwnerDenied:
      user = "u2"
      role = "admin"
      row = draftOrder
  table shares:
    id      : String primary_key immutable where 1 <= id.length <= 64
    orderId : String immutable references orders(id) on_delete cascade
    userId  : String immutable where 1 <= userId.length <= 64
    policy read, write requires ctx.userId != none

bad_db_tbl "Database `example badRow`" BadDbExample items : id : String primary_key where 1 <= id.length <= 16 || example badRow: id = ""
bad_db_tbl "Database `rejects badReject`" BadDbRejects items : id : String primary_key where 1 <= id.length <= 16 || rejects badReject: id = "ok"
bad_db_tbl "Database `example transition badStep`" BadDbTransEx jobs :
  id : String primary_key where 1 <= id.length <= 16 || status : String where status in ["queued", "done"] || invariant flow: transition status: "queued" -> "done" || example doneJob: id = "j1", status = "done" || example transition badStep: doneJob -> status = "queued"
bad_db_tbl "Database `rejects transition badRejStep`" BadDbTransRej jobs :
  id : String primary_key where 1 <= id.length <= 16 || status : String where status in ["queued", "done"] || invariant flow: transition status: "queued" -> "done" || example queuedJob: id = "j1", status = "queued" || rejects transition badRejStep: queuedJob -> status = "done"
bad_db_tbl "Database `example read badAllow`" BadDbPolAllow docs :
  id : String primary_key where 1 <= id.length <= 16 || ownerId : String where 1 <= ownerId.length <= 16 || policy read requires some(ownerId) == ctx.userId || example d1: id = "d1", ownerId = "alice" ||
  example read badAllow:
    user = "bob"
    row = d1
bad_db_tbl "Database `rejects read badDeny`" BadDbPolDeny docs :
  id : String primary_key where 1 <= id.length <= 16 || ownerId : String where 1 <= ownerId.length <= 16 || policy read requires some(ownerId) == ctx.userId || example d1: id = "d1", ownerId = "alice" ||
  rejects read badDeny:
    user = "alice"
    row = d1

/-! ## Transactional and Conditional-Where DB Upgrades -/
database TxLeaseDb:
  sqlite ".qed/tx_lease_checks.db"
  table leases:
    id      : String primary_key where 1 <= id.length <= 32
    ownerId : String immutable   where 1 <= ownerId.length <= 32
    status  : String             where status in ["open", "claimed", "done"]
    retries : Nat                where retries <= 10
    policy read, write requires some(row.ownerId) == ctx.userId
    invariant leaseFlow: transition row.status: "open" -> "claimed" -> "done"
    invariant retriesMono: row.retries >= old(row.retries)
    example openLease: id = "l1", ownerId = "alice", status = "open", retries = 0
    example read ownerCanRead:
      user = "alice"
      row = openLease
    rejects read otherCannotRead:
      user = "bob"
      row = openLease
    rejects write anonCannotWrite:
      row = openLease

server stateless TxLeaseSrv:
  use db : TxLeaseDb
  fn claimInsideTx(tx: db.Tx, leaseId: String, uid: String) -> TxLeaseDb.leases?!:
    requires some(uid) == ctx.userId
    return await tx.leases.where(r => r.id == leaseId and r.ownerId == uid and r.status == "open" and r.retries < 10).updateOne(r => { status = "claimed", retries = r.retries + 1 })?
  rpc claimMyLease(leaseId: String) -> TxLeaseDb.leases?!:
    requires auth
    db.transaction as tx:
      return await claimInsideTx(tx, leaseId, uid)?
  rpc bulkClaimMyOpen(onlyId: String?) -> TxLeaseDb.leases[]!:
    requires auth
    return await db.leases
      .where(r => if let some(lid) = onlyId: r.id == lid and r.ownerId == uid and r.status == "open" and r.retries < 10 else: r.ownerId == uid and r.status == "open" and r.retries < 10)
      .update(r => { status = "claimed", retries = r.retries + 1 })?
  read_only rpc listMyLeases(onlyOpen: Bool, filterId: String?) -> TxLeaseDb.leases[]!:
    requires auth
    return await db.leases.where(r => if onlyOpen: (r.id == filterId.getD("") if filterId != none else true) and r.ownerId == uid and r.status == "open" else: r.ownerId == uid).select()?
  read_only fn countMyLeases(onlyOpen: Bool) -> Nat!:
    requires auth
    return await db.leases.where(r => r.ownerId == uid and (r.status == "open" if onlyOpen else true)).count()?
  read_only fn countLeasesByStatus() -> (String, Nat)[]!:
    requires auth
    return await db.leases.where(r => r.ownerId == uid).groupBy("status").orderBy("-count").count()?
  read_only fn maxRetriesByStatus() -> (String, Nat)[]!:
    requires auth
    return await db.leases.where(r => r.ownerId == uid).groupBy("status").orderBy("status").max("retries")?
  example ownerCanCount:
    with user "alice"
    with db db.leases = [{ id = "l1", ownerId = "alice", status = "open", retries = 0 }, { id = "l2", ownerId = "alice", status = "done", retries = 1 }, { id = "l3", ownerId = "bob", status = "open", retries = 0 }]
    call countMyLeases(true)
    expect ok(1)
  example ownerCanGroupByInEval:
    with user "alice"
    with db db.leases = [{ id = "l1", ownerId = "alice", status = "open", retries = 2 }, { id = "l2", ownerId = "alice", status = "open", retries = 5 }, { id = "l3", ownerId = "alice", status = "done", retries = 1 }, { id = "l4", ownerId = "bob", status = "open", retries = 9 }]
    call countLeasesByStatus()
    expect ok([("open", 2), ("done", 1)])
    call maxRetriesByStatus()
    expect ok([("done", 1), ("open", 5)])
  example ownerConditionalSelect:
    with user "alice"
    with db db.leases = [{ id = "l1", ownerId = "alice", status = "open", retries = 0 }, { id = "l2", ownerId = "alice", status = "done", retries = 1 }]
    call listMyLeases(true, none)
    expect ok([{ id = "l1", ownerId = "alice", status = "open", retries = 0 }])

bad_db "Database read policy `TxLeaseDb.leases.read` failed in `sneakyReadAll → TxLeaseDb.leases.select`" TxLeaseDb : rpc sneakyReadAll() -> TxLeaseDb.leases[]!: return await db.leases.select()?
bad_db_auth "Database read policy `TxLeaseDb.leases.read` failed in `leakySelect → TxLeaseDb.leases.select`" TxLeaseDb [ro] leakySelect(onlyOpen: Bool) -> TxLeaseDb.leases[]! : return await db.leases.where(r => if onlyOpen: r.ownerId == uid and r.status == "open" else: r.status == "done").select()?
bad_svc "Database update policy `TxLeaseDb.leases.update` failed in `badTxUpdate → TxLeaseDb.leases.updateOne`" BadTxPolicyHelper : use db : TxLeaseDb || fn badTxUpdate(tx: db.Tx, leaseId: String) -> TxLeaseDb.leases?!: return await tx.leases.where(r => r.id == leaseId and r.status == "open" and r.retries < 10).updateOne(r => { status = "claimed" })?
bad_svc "Database transition/monotonicity invariant `TxLeaseDb.leases.TransInv` failed in `invalidReopen → TxLeaseDb.leases.updateOne`" BadTxTransInv : use db : TxLeaseDb ||
  fn invalidReopen(leaseId: String) -> TxLeaseDb.leases?!:
    requires auth
    return await db.leases.where(r => r.id == leaseId and r.ownerId == uid and r.status == "done").updateOne(r => { status = "open" })?

/-! ## Issue #22 Item 2: `SqlIdent.ofString?`, `sql!"..."`, Dynamic Read-Only `Db.postgres`, & `pg_catalog` Introspection -/

fn parseDbIdent(s: String) -> SqlIdent?:
  ensures result.isSome == Qed.Server.Db.isSafeSqlIdent(s)
  example okIdent: parseDbIdent("public_users_2").isSome == true
  example rejectEmpty: parseDbIdent("") == none
  example rejectInject: parseDbIdent("users; DROP TABLE users") == none
  example rejectLeadDigit: parseDbIdent("1users") == none
  example rejectTooLong: parseDbIdent("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == none
  return Db.sqlIdent?(s)

fn parseDbIdentDirect(s: String) -> SqlIdent?:
  ensures result.isSome == Qed.Server.Db.isSafeSqlIdent(s)
  return SqlIdent.ofString?(s)

fn defaultBrowserCols() -> SqlIdent[]:
  example colCount: defaultBrowserCols.size == 3
  return [sql!"id", sql!"email", sql!"created_at"]

example : ((Qed.Server.Db.SqlQuery.countSchema sql!"public" sql!"users" .litTrue).compile .postgres).1 ==
    "SELECT COUNT(*) FROM \"public\".\"users\" WHERE TRUE" := rfl
example : ((Qed.Server.Db.SqlQuery.selectSchema sql!"public" sql!"users" [sql!"id", sql!"email"] .litTrue none (some 25) none).compile .postgres).1 ==
    "SELECT \"id\", \"email\" FROM \"public\".\"users\" WHERE TRUE LIMIT 25" := rfl
example : ((Qed.Server.Db.SqlQuery.selectSchema sql!"public" sql!"users" [] .litTrue none none none).compile .sqlite).1 ==
    "SELECT * FROM \"public\".\"users\" WHERE 1" := rfl
example : (Qed.fromJson (α := Qed.Server.Db.SqlIdent) (Qed.toJson sql!"audit_logs")) = .ok sql!"audit_logs" := rfl
example : (Qed.fromJson (α := Qed.Server.Db.SqlIdent) (.str "bad;ident")).isOk = false := rfl
example : (Qed.FromProto.fromProtoMsg (α := Qed.Server.Db.SqlIdent) (Qed.ToProto.toProtoMsg sql!"audit_logs")) = .ok sql!"audit_logs" := rfl

server stateless PgBrowserApi:
  read_only rpc listSchemas(url: String) -> String[]!:
    no_db_write, no_http
    let pg = Db.postgres(url)
    return await pg.listSchemas()?

  read_only rpc listPublicTables(url: String) -> PgTableInfo[]!:
    no_db_write, no_http
    let pg = Db.postgres(url, ssrf_guard = true)
    return await pg.listTables("public")?

  read_only rpc inspectTable(url: String, scName: String, tblName: String) -> (PgColumnInfo[], PgIndexInfo[], PgConstraintInfo[], PgTableStat[], Nat)!:
    no_db_write, no_http
    let pg = Db.postgres(url, ssrf_guard = true, name = "browser_pg")
    let sc = Db.sqlIdent?(scName)?
    let tn = Db.sqlIdent?(tblName)?
    let cols = await pg.listColumns(tn, scName)?
    let idxs = await pg.listIndexes(tn, scName)?
    let keys = await pg.listKeyColumns(tn, scName)?
    let stats = await pg.listTableStats(scName)?
    let n = await pg.countRowsInSchema(sc, tn)?
    return (cols, idxs, keys, stats, n)

  read_only rpc previewTable(url: String, sc: SqlIdent, tbl: SqlIdent) -> DbRow[]!:
    no_db_write, no_http
    let pg = Db.postgres(url)
    return await pg.selectSchema(sc, tbl, [sql!"id", sql!"email"])?

service PgBrowserSvc:
  read_only fn listTablesIn(url: String, scName: String) -> PgTableInfo[]!:
    no_db_write, no_http
    let pg = Db.postgres(url)
    return await pg.listTables(scName)?

  read_only fn sampleRows(url: String, tbl: SqlIdent) -> (Nat, DbRow[])!:
    no_db_write, no_http
    let pg = Db.postgres(url)
    let n = await pg.countRows(tbl)?
    let rows = await pg.selectRows(tbl, 10, 0)?
    return (n, rows)

private def pgBrowserEvalState : Qed.Server.Eval.EvalState Unit :=
  let db0 : Qed.Server.Eval.MemDb := {}
  let db1 := db0.seedEncoded "information_schema.schemata" ["schema_name"]
    [[(sql!"schema_name", .text "public")]]
  let db2 := db1.seedEncoded "pg_catalog.pg_tables" ["schemaname", "tablename", "tableowner"]
    [[(sql!"schemaname", .text "public"), (sql!"tablename", .text "users"), (sql!"tableowner", .text "postgres")]]
  let db3 := db2.seedEncoded "information_schema.columns"
    ["table_schema", "table_name", "column_name", "data_type", "is_nullable", "column_default", "ordinal_position"]
    [[(sql!"table_schema", .text "public"), (sql!"table_name", .text "users"),
      (sql!"column_name", .text "id"), (sql!"data_type", .text "bigint"),
      (sql!"is_nullable", .text "NO"), (sql!"column_default", .null), (sql!"ordinal_position", .int 1)]]
  let db4 := db3.seedEncoded "pg_catalog.pg_indexes" ["schemaname", "tablename", "indexname", "indexdef"]
    [[(sql!"schemaname", .text "public"), (sql!"tablename", .text "users"),
      (sql!"indexname", .text "users_pkey"), (sql!"indexdef", .text "CREATE UNIQUE INDEX users_pkey ON public.users (id)")]]
  let db5 := db4.seedEncoded "information_schema.key_column_usage" ["table_schema", "table_name", "constraint_name", "column_name", "ordinal_position"]
    [[(sql!"table_schema", .text "public"), (sql!"table_name", .text "users"),
      (sql!"constraint_name", .text "users_pkey"), (sql!"column_name", .text "id"), (sql!"ordinal_position", .int 1)]]
  let db6 := db5.seedEncoded "pg_catalog.pg_stat_user_tables" ["schemaname", "relname", "n_live_tup"]
    [[(sql!"schemaname", .text "public"), (sql!"relname", .text "users"), (sql!"n_live_tup", .int 2)]]
  let db7 := db6.seedEncoded "public.users" ["id", "email"]
    [[(sql!"id", .int 1), (sql!"email", .text "ada@qed.dev")],
     [(sql!"id", .int 2), (sql!"email", .text "grace@qed.dev")]]
  let db8 := db7.seedEncoded "users" ["id", "email"]
    [[(sql!"id", .int 1), (sql!"email", .text "ada@qed.dev")]]
  { shared := (), db := db8 }

example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserApi.listSchemas_handler {} "postgres://localhost/app")).value
      = .ok #["public"] := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserApi.listPublicTables_handler {} "postgres://localhost/app")).value
      = .ok #[{ schemaName := "public", name := "users", owner := "postgres" }] := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserApi.inspectTable_handler {} "postgres://localhost/app" "public" "users")).value
      = .ok (#[{ name := "id", dataType := "bigint", nullable := false, defaultExpr := none, ordinalPos := 1 }],
             #[{ name := "users_pkey", definition := "CREATE UNIQUE INDEX users_pkey ON public.users (id)" }],
             #[{ name := "users_pkey", columnName := "id", ordinalPos := 1 }],
             #[{ schemaName := "public", name := "users", liveRows := 2 }],
             2) := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserApi.inspectTable_handler {} "postgres://localhost/app" "public; DROP TABLE users" "users")).value
      = .error (Qed.Server.ApiError.notFound "optional value was empty") := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserApi.previewTable_handler {} "postgres://localhost/app" sql!"public" sql!"users")).value
      = .ok #[#[.int 1, .text "ada@qed.dev"], #[.int 2, .text "grace@qed.dev"]] := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserSvc.listTablesIn "postgres://localhost/app" "public")).value
      = .ok #[{ schemaName := "public", name := "users", owner := "postgres" }] := rfl
example :
    (Qed.Server.Eval.evalProg {} pgBrowserEvalState (PgBrowserSvc.sampleRows "postgres://localhost/app" sql!"users")).value
      = .ok (1, #[#[.int 1, .text "ada@qed.dev"]]) := rfl

check_decls [parseDbIdent_ensures, parseDbIdent_example_okIdent, parseDbIdent_example_rejectEmpty,
  parseDbIdent_example_rejectInject, parseDbIdent_example_rejectLeadDigit, parseDbIdent_example_rejectTooLong,
  parseDbIdentDirect_ensures, defaultBrowserCols_example_colCount,
  PgBrowserApi.listSchemas_contract_1, PgBrowserApi.listPublicTables_contract_1,
  PgBrowserApi.inspectTable_contract_1, PgBrowserApi.previewTable_contract_1,
  PgBrowserSvc.listTablesIn_contract_1, PgBrowserSvc.sampleRows_contract_1]

expect_err "Server.Db.isSafeSqlIdent \"users; DROP TABLE users\" = true" in
  fn badSqlIdentLit() -> SqlIdent:
    return sql!"users; DROP TABLE users"

expect_err "Tactic `decide` proved that the proposition" in
  def badPgWriteQuery : Qed.Server.ThreadProg Unit (Except Qed.Server.ApiError Qed.Server.Db.DbResult) :=
    (Qed.Server.Db.postgres "postgres://localhost/app").queryReadOnly (.delete sql!"users" .litTrue [])

/-! ## Phase 1 Policy Expressiveness: `database fn`, Two-State `policy update`, `policy count`, `policy read_meta`, `policy read(cols) [by ...]` -/
database CloudPolicyDb:
  sqlite ".qed/cloud_policy_checks.db"
  fn isOperator() -> Bool:
    any acc in accounts: some(acc.id) == ctx.userId and acc.isOperator
  fn canReadApp(appId: String, ownerId: String) -> Bool:
    some(ownerId) == ctx.userId or
    (any m in app_members: m.appId == appId and some(m.userId) == ctx.userId and m.status == "accepted")
  fn canAdminApp(appId: String, ownerId: String) -> Bool:
    some(ownerId) == ctx.userId or
    (any m in app_members: m.appId == appId and some(m.userId) == ctx.userId and m.status == "accepted" and m.role == "admin")
  fn canReadOrOp(appId: String, ownerId: String) -> Bool:
    return canReadApp(appId, ownerId) or isOperator()

  table accounts:
    id         : String primary_key immutable where 1 <= id.length <= 64
    email      : String unique where 3 <= email.length <= 128
    spendCap   : Nat
    isOperator : Bool
    policy read requires some(row.id) == ctx.userId or isOperator()
    policy read(id, email) by email requires ctx.userId != none
    policy read(id, spendCap) requires
      some(row.id) == ctx.userId or
      (any a in apps: a.ownerId == row.id and canReadApp(a.id, a.ownerId))
    policy insert, update, delete requires some(row.id) == ctx.userId or isOperator()
  table apps:
    id        : String primary_key immutable where 1 <= id.length <= 64
    ownerId   : String where 1 <= ownerId.length <= 64
    name      : String where 1 <= name.length <= 120
    suspended : Bool
    policy read requires canReadOrOp(row.id, row.ownerId)
    policy insert requires some(row.ownerId) == ctx.userId
    policy update requires
      (canAdminApp(old.id, old.ownerId) and row.ownerId == old.ownerId) or
      (some(old(row.ownerId)) == ctx.userId and (any a in accounts: a.id == row.ownerId)) or
      isOperator()
    policy delete requires some(row.ownerId) == ctx.userId or isOperator()
    example app1: id = "a1", ownerId = "alice", name = "Alpha", suspended = false
    example app1ForBob from app1: ownerId = "bob"
    example app1ForCharlie from app1: ownerId = "charlie"
    example update ownerCanTransfer:
      user = "alice"
      old = app1
      row = app1ForBob
      snap accounts = [CloudPolicyDb.accounts.mk("bob", "bob@qed.dev", 5000, false)]
    rejects update adminCannotHijackOwner:
      user = "charlie"
      old = app1
      row = app1ForCharlie
      snap app_members = [CloudPolicyDb.app_members.mk("m1", "a1", "charlie", "admin", "accepted")]
      snap accounts = [CloudPolicyDb.accounts.mk("charlie", "c@qed.dev", 0, false)]
    example update operatorCanSuspend:
      user = "op1"
      old = app1
      row = app1
      snap accounts = [CloudPolicyDb.accounts.mk("op1", "op@qed.dev", 0, true)]
  table app_members:
    id     : String primary_key immutable where 1 <= id.length <= 64
    appId  : String immutable references apps(id) on_delete cascade
    userId : String immutable where 1 <= userId.length <= 64
    role   : String where role in ["admin", "viewer"]
    status : String where status in ["accepted", "pending"]
    policy read, write requires ctx.userId != none
  table app_dbs:
    id      : String primary_key immutable where 1 <= id.length <= 64
    appId   : String immutable references apps(id) on_delete cascade
    ownerId : String where 1 <= ownerId.length <= 64
    managed : Bool
    policy read requires canReadApp(row.appId, row.ownerId)
    policy count requires
      canReadApp(row.appId, row.ownerId) or
      (any a in apps: a.ownerId == row.ownerId and canReadApp(a.id, a.ownerId))
    policy insert, update, delete requires canAdminApp(row.appId, row.ownerId)
    example db2: id = "db2", appId = "a2", ownerId = "alice", managed = true
    example count collabCanCountOwnersOtherAppDb:
      user = "dave"
      row = db2
      snap apps = [CloudPolicyDb.apps.mk("a1", "alice", "Alpha", false)]
      snap app_members = [CloudPolicyDb.app_members.mk("m2", "a1", "dave", "viewer", "accepted")]
    rejects read collabCannotReadOwnersOtherAppDb:
      user = "dave"
      row = db2
      snap apps = [CloudPolicyDb.apps.mk("a1", "alice", "Alpha", false)]
      snap app_members = [CloudPolicyDb.app_members.mk("m2", "a1", "dave", "viewer", "accepted")]
  table app_secrets:
    id      : String primary_key immutable where 1 <= id.length <= 64
    appId   : String immutable references apps(id) on_delete cascade
    ownerId : String where 1 <= ownerId.length <= 64
    label   : String where 1 <= label.length <= 64
    secret  : encrypted(String, key = secret("CP_SEC_KEY") ?? "cp-dev-secret-key-32") where 1 <= secret.length <= 200
    policy read requires canAdminApp(row.appId, row.ownerId)
    policy read_meta requires canReadApp(row.appId, row.ownerId)
    policy insert, update, delete requires canAdminApp(row.appId, row.ownerId)
    example sec1: id = "s1", appId = "a1", ownerId = "alice", label = "API_KEY", secret = "shh"
    example read_meta viewerCanReadSecretMeta:
      user = "dave"
      row = sec1
      snap app_members = [CloudPolicyDb.app_members.mk("m2", "a1", "dave", "viewer", "accepted")]
    rejects read viewerCannotReadSecretValue:
      user = "dave"
      row = sec1
      snap app_members = [CloudPolicyDb.app_members.mk("m2", "a1", "dave", "viewer", "accepted")]

server stateless CloudPolicyApi:
  use db : CloudPolicyDb
  rpc seedAccount(id: String, email: String, spendCap: Nat, isOp: Bool) -> CloudPolicyDb.accounts!:
    requires auth, 1 <= id.length <= 64, 3 <= email.length <= 128
    return await db.accounts
      .where(r => some(r.id) == ctx.userId or db.isOperator())
      .insert(id = id, email = email, spendCap = spendCap, isOperator = isOp)?
  rpc createApp(id: String, name: String) -> CloudPolicyDb.apps!:
    requires auth, 1 <= id.length <= 64, 1 <= name.length <= 120, 1 <= uid.length <= 64
    return await db.apps.insert(id = id, ownerId = uid, name = name, suspended = false)?
  rpc addMember(id: String, appId: String, userId: String, role: String, status: String) -> CloudPolicyDb.app_members!:
    requires auth, 1 <= id.length <= 64, 1 <= userId.length <= 64, role in ["admin", "viewer"], status in ["accepted", "pending"]
    return await db.app_members.insert(id = id, appId = appId, userId = userId, role = role, status = status)?
  rpc addAppDb(id: String, appId: String, ownerId: String, managed: Bool) -> CloudPolicyDb.app_dbs!:
    requires auth, 1 <= id.length <= 64, 1 <= ownerId.length <= 64
    return await db.app_dbs.where(r => db.canAdminApp(r.appId, r.ownerId)).insert(id = id, appId = appId, ownerId = ownerId, managed = managed)?
  rpc addSecret(id: String, appId: String, ownerId: String, label: String, secretVal: String) -> CloudPolicyDb.app_secrets!:
    requires auth, 1 <= id.length <= 64, 1 <= ownerId.length <= 64, 1 <= label.length <= 64, 1 <= secretVal.length <= 200
    return await db.app_secrets.where(r => db.canAdminApp(r.appId, r.ownerId)).insert(id = id, appId = appId, ownerId = ownerId, label = label, secret = secretVal)?
  -- Uses `fn` inside `.where` + two-state `policy update` keeping `ownerId` unchanged
  rpc renameApp(appId: String, newName: String) -> CloudPolicyDb.apps?!:
    requires auth, 1 <= newName.length <= 120
    return await db.apps.where(r => r.id == appId and db.canAdminApp(r.id, r.ownerId)).updateOne({ name = newName })?
  -- Two-state `policy update` transferring ownership to a verified existing account
  rpc transferApp(appId: String, nextOwnerId: String) -> CloudPolicyDb.apps?!:
    requires auth, 1 <= nextOwnerId.length <= 64
    return await db.apps
      .where(r => r.id == appId and some(r.ownerId) == ctx.userId and (any a in accounts: a.id == nextOwnerId))
      .updateOne({ ownerId = nextOwnerId })?
  -- Operator suspension via `database fn isOperator()`
  rpc operatorSuspendApp(appId: String, suspended: Bool) -> CloudPolicyDb.apps?!:
    requires auth
    return await db.apps.where(r => r.id == appId and db.isOperator()).updateOne({ suspended = suspended })?
  -- Exact-key email lookup via `policy read(id, email) by email`
  read_only rpc lookupUserIdByEmail(email: String) -> (String, String)?!:
    requires auth
    return await db.accounts.where(r => r.email == email).columns(["id", "email"]).findOne()?
  -- Collaborator reads owner's spendCap via `policy read(id, spendCap)` (nested `db.canReadApp` inside `any a in apps:`)
  read_only rpc getOwnerSpendCap(ownerId: String) -> (String, Nat)?!:
    requires auth
    return await db.accounts
      .where(r => r.id == ownerId and (any a in apps: a.ownerId == r.id and db.canReadApp(a.id, a.ownerId)))
      .columns(["id", "spendCap"]).findOne()?
  -- Full-row read disjunct still works when selecting a column subset
  read_only rpc getSelfAccountId() -> String?!:
    requires auth
    return await db.accounts.where(r => r.id == uid).columns("id").findOne()?
  -- Operator reads all accounts via `db.isOperator()`
  read_only rpc listAllAccountsAsOp() -> CloudPolicyDb.accounts[]!:
    requires auth
    return await db.accounts.where(r => db.isOperator()).orderBy("id").select()?
  -- Collaborator counts ALL of owner's managed DBs via `policy count`
  read_only rpc countOwnerManagedDbs(ownerId: String) -> Nat!:
    requires auth
    return await db.app_dbs.where(r => r.ownerId == ownerId and r.managed == true and (any a in apps: a.ownerId == r.ownerId and db.canReadApp(a.id, a.ownerId))).count()?
  -- Viewer reads secret metadata via `policy read_meta`
  read_only rpc listSecretMeta(appId: String) -> CloudPolicyDb.app_secrets.Meta[]!:
    requires auth
    return await db.app_secrets.where(r => r.appId == appId and db.canReadApp(r.appId, r.ownerId)).orderBy("id").selectMeta()?
  -- Multi-row `ColReadPolicy` (`policy read(id, spendCap)`) authorizes `groupBy("id").sum("spendCap")`
  read_only rpc sumSpendCapByOwner(ownerId: String) -> (String, Nat)[]!:
    requires auth
    return await db.accounts
      .where(r => r.id == ownerId and (any a in apps: a.ownerId == r.id and db.canReadApp(a.id, a.ownerId)))
      .groupBy("id").sum("spendCap")?
  example ownerTransfersAppToExistingAccount:
    with user "alice"
    with db db.accounts = [{ id = "alice", email = "a@qed.dev", spendCap = 1000, isOperator = false }, { id = "bob", email = "b@qed.dev", spendCap = 2000, isOperator = false }]
    with db db.apps = [{ id = "a1", ownerId = "alice", name = "Alpha", suspended = false }]
    call transferApp("a1", "bob")
    expect ok
    expect result.map(o => o.map(a => a.ownerId)) == .ok(some("bob"))
  example transferToNonexistentAccountNoOps:
    with user "alice"
    with db db.accounts = [{ id = "alice", email = "a@qed.dev", spendCap = 1000, isOperator = false }]
    with db db.apps = [{ id = "a1", ownerId = "alice", name = "Alpha", suspended = false }]
    call transferApp("a1", "ghost")
    expect ok(none)
  example lookupEmailAndCollabSpendCapAndCount:
    with user "dave"
    with db db.accounts = [{ id = "alice", email = "alice@qed.dev", spendCap = 9900, isOperator = false }, { id = "dave", email = "dave@qed.dev", spendCap = 0, isOperator = false }]
    with db db.apps = [{ id = "a1", ownerId = "alice", name = "Alpha", suspended = false }, { id = "a2", ownerId = "alice", name = "Beta", suspended = false }]
    with db db.app_members = [{ id = "m1", appId = "a1", userId = "dave", role = "viewer", status = "accepted" }]
    with db db.app_dbs = [{ id = "db1", appId = "a1", ownerId = "alice", managed = true }, { id = "db2", appId = "a2", ownerId = "alice", managed = true }]
    call countOwnerManagedDbs("alice")
    expect ok(2)

-- Negative compile-time tests for Phase 1 policy expressiveness & groupBy RLS
bad_db_auth "update policy `CloudPolicyDb.apps.update`" CloudPolicyDb adminHijackOwner(appId: String) -> CloudPolicyDb.apps?! || 1 <= uid.length <= 64 : return await db.apps.where(r => r.id == appId and db.canAdminApp(r.id, r.ownerId)).updateOne({ ownerId = uid })?
bad_db_auth "update policy `CloudPolicyDb.apps.update`" CloudPolicyDb transferWithoutTargetCheck(appId: String, nextOwnerId: String) -> CloudPolicyDb.apps?! || 1 <= nextOwnerId.length <= 64 : return await db.apps.where(r => r.id == appId and some(r.ownerId) == ctx.userId).updateOne({ ownerId = nextOwnerId })?
bad_db_auth "requires `.findOne()` with an exact top-level `r.<col> == <val>` filter" CloudPolicyDb enumerateEmailsSelect(email: String) -> (String, String)[]! : return await db.accounts.where(r => r.email == email).columns(["id", "email"]).select()?
bad_db_auth "requires `.findOne()` with an exact top-level `r.<col> == <val>` filter" CloudPolicyDb enumerateEmailsOr(email: String) -> (String, String)?! : return await db.accounts.where(r => r.email == email or r.id != "").columns(["id", "email"]).findOne()?
bad_db_auth "read policy `CloudPolicyDb.accounts.read`" CloudPolicyDb leakSpendCapByEmail(email: String) -> (String, String, Nat)?! : return await db.accounts.where(r => r.email == email).columns(["id", "email", "spendCap"]).findOne()?
bad_db_auth "read policy `CloudPolicyDb.accounts.read`" CloudPolicyDb leakFullAccountByEmail(email: String) -> CloudPolicyDb.accounts?! : return await db.accounts.where(r => r.email == email).findOne()?
bad_db_auth "read policy `CloudPolicyDb.app_dbs.read`" CloudPolicyDb collabSelectOtherAppDbs(ownerId: String) -> CloudPolicyDb.app_dbs[]! : return await db.app_dbs.where(r => r.ownerId == ownerId and (any a in apps: a.ownerId == r.ownerId and db.canReadApp(a.id, a.ownerId))).select()?
bad_db_auth "read policy `CloudPolicyDb.app_dbs.read`" CloudPolicyDb collabGroupByCountOnlyPolicy(ownerId: String) -> (String, Nat)[]! : return await db.app_dbs.where(r => r.ownerId == ownerId and (any a in apps: a.ownerId == r.ownerId and db.canReadApp(a.id, a.ownerId))).groupBy("appId").count()?
bad_db_auth "read policy `CloudPolicyDb.accounts.read`" CloudPolicyDb groupByByColPolicy(email: String) -> (String, Nat)[]! : return await db.accounts.where(r => r.email == email).groupBy("email").count()?
bad_db_auth "read policy `CloudPolicyDb.app_secrets.read`" CloudPolicyDb viewerSelectSecrets(appId: String) -> CloudPolicyDb.app_secrets[]! : return await db.app_secrets.where(r => r.appId == appId and db.canReadApp(r.appId, r.ownerId)).select()?
bad_db_auth "cannot use encrypted column `app_secrets.secret` in `.groupBy(...)`" CloudPolicyDb groupByEncrypted() -> (String, Nat)[]! : return await db.app_secrets.where(r => db.canAdminApp(r.appId, r.ownerId)).groupBy("secret").count()?
bad_db_auth "must reference a grouped column" CloudPolicyDb groupByBadOrderBy() -> (String, Nat)[]! : return await db.apps.where(r => db.canReadOrOp(r.id, r.ownerId)).groupBy("ownerId").orderBy("name").count()?
bad_db_auth "takes no arguments; chain `.where(r => ...)`" CloudPolicyDb rejectOldWhereKw() -> CloudPolicyDb.apps[]! : return await db.apps.select(where = r => db.canReadOrOp(r.id, r.ownerId))?
bad_db_auth "`.join(...)` is a chain modifier; follow it with `.select()` or `.findOne()`" ShopDb rejectTerminalJoin() -> (ShopDb.items, ShopDb.authors)[]! : return await db.items.where(r => r.ownerId == uid).join(authors)?
bad_db_def "expansion limit exceeded" BadRecDbFn :
  fn loopA(x: String) -> Bool: loopB(x)
  || fn loopB(x: String) -> Bool: loopA(x)
  || table t: id : String primary_key
bad_db_tbl "`policy read_meta` on `table plain` requires both encrypted and non-encrypted columns" BadReadMetaDb plain : id : String primary_key || policy read_meta requires ctx.userId != none
bad_db_tbl "unknown column `bogus` in `policy read(...)`" BadColReadDb items : id : String primary_key || policy read(bogus) requires ctx.userId != none
bad_db_tbl "cannot use encrypted column `vault.sec` in `policy read(...) by ...`" BadByEncDb vault : id : String primary_key || sec : encrypted(String, key = secret("K")) || policy read(id) by sec requires ctx.userId != none
bad_db_def "`row` is not in scope inside `database` `fn`" BadRowInDbFn :
  fn badFn() -> Bool: row.id == "x"
  || table t: id : String primary_key

/-! ## Phase 2: Typed Principals, Cryptographic Webhook/Cron Route Guards & Job Principals -/

database PrincipalDb:
  sqlite ".qed/principal_checks.db"
  fn isBuildSystem() -> Bool:
    ctx.principal in [.system("BuildJobSrv.poll"), .system("reap-and-sweep")]
  table billing_events:
    id     : String primary_key immutable where 1 <= id.length <= 64
    status : String where status in ["paid", "failed"]
    policy read, insert, update requires ctx.principal == .system("stripe")
    policy delete requires false
    example ev1: id = "evt_1", status = "paid"
    example insert stripeCanInsert:
      principal = .system("stripe")
      row = ev1
    rejects insert userCannotInsert:
      user = "alice"
      row = ev1
    rejects insert githubCannotInsert:
      principal = .system("github")
      row = ev1
  table deployments:
    id      : String primary_key immutable where 1 <= id.length <= 64
    ownerId : String immutable where 1 <= ownerId.length <= 64
    status  : String where status in ["queued", "building", "live", "stale"]
    policy read, update requires
      some(row.ownerId) == ctx.userId or
      isBuildSystem() or
      ctx.principal == .system("github")
    policy insert requires
      some(row.ownerId) == ctx.userId or
      ctx.principal == .system("github")
    policy delete requires ctx.principal == .system("cleanup")
    example dep1: id = "dep_1", ownerId = "alice", status = "queued"
    example update jobCanClaim:
      principal = .system("BuildJobSrv.poll")
      row = dep1
    example delete cronCanCleanup:
      principal = .system("cleanup")
      row = dep1
    rejects delete jobCannotCleanup:
      principal = .system("BuildJobSrv.poll")
      row = dep1
    rejects delete userCannotCleanup:
      user = "alice"
      row = dep1

service PrincipalOps:
  use db : PrincipalDb
  fn recordStripeEvent(id: String, status: String) -> PrincipalDb.billing_events!:
    requires ctx.principal == .system("stripe"), 1 <= id.length <= 64, status in ["paid", "failed"]
    return await db.billing_events.insert(id = id, status = status)?
  fn listStripeEvents() -> PrincipalDb.billing_events[]!:
    requires ctx.principal == .system("stripe")
    return await db.billing_events.orderBy("id").select()?
  example stripeCanRecord:
    with principal = .system("stripe")
    call recordStripeEvent("evt_1", "paid")
    expect ok
    expect db_count("billing_events") == 1
  example userRejected403:
    with user "alice"
    call recordStripeEvent("evt_1", "paid")
    expect error(403)
    expect db_count("billing_events") == 0
  example wrongSystemRejected403:
    with principal = .system("github")
    call recordStripeEvent("evt_1", "paid")
    expect error(403)

private def testMockHmacHex (key msg : String) : String :=
  Qed.Proto.encodeHex (Qed.Server.Eval.mockHmacSha256 key.toUTF8 msg.toUTF8)

server stateless PrincipalApi:
  use db : PrincipalDb
  use ops : PrincipalOps
  env stripeSecret = "TEST_STRIPE_WH_SECRET" ?? ""
  env githubSecret = "TEST_GITHUB_WH_SECRET" ?? ""
  env cronSecret   = "TEST_CRON_SECRET" ?? ""
  env bearerSecret = "TEST_BEARER_SECRET" ?? ""

  post "/webhooks/stripe":
    requires system("stripe", stripe = stripeSecret)
    let ev = await ops.recordStripeEvent("evt_stripe_1", "paid")?
    return json({ id = ev.id, status = ev.status })

  post "/webhooks/github":
    requires system("github", hmac_sha256 = githubSecret, header = "x-hub-signature-256", prefix = "sha256=")
    let dep = await db.deployments.insert(id = "dep_gh_1", ownerId = "alice", status = "queued")?
    return json({ id = dep.id, status = dep.status })

  post "/cron/reap":
    requires system("reap-and-sweep", bearer = bearerSecret)
    let upd = await db.deployments.where(r => r.status == "building").updateOne({ status = "stale" })?
    return json({ reaped = upd != none })

  post "/cron/cleanup":
    requires system("cleanup", secret = cronSecret, header = "x-qed-cron-secret")
    let n = await db.deployments.where(r => r.status == "stale").delete()?
    return json({ deleted = n })

  example stripeMissingSecret500:
    with now = 1700000050000
    with body = "{\"type\":\"invoice.paid\"}"
    with header "stripe-signature" = "t=1700000000,v1=0000"
    post "/webhooks/stripe"
    expect status == 500
    expect db_count("billing_events") == 0

  example stripeBadSig401:
    with env "TEST_STRIPE_WH_SECRET" = "whsec_test"
    with now = 1700000050000
    with body = "{\"type\":\"invoice.paid\"}"
    with header "stripe-signature" = "t=1700000000,v1=deadbeef"
    post "/webhooks/stripe"
    expect status == 401
    expect db_count("billing_events") == 0

  example stripeExpiredReplay401:
    with env "TEST_STRIPE_WH_SECRET" = "whsec_test"
    with now = 1700000500000
    with body = "{\"type\":\"invoice.paid\"}"
    with header "stripe-signature" = "t=1700000000,v1=" ++ testMockHmacHex("whsec_test", "1700000000.{\"type\":\"invoice.paid\"}")
    post "/webhooks/stripe"
    expect status == 401
    expect db_count("billing_events") == 0

  example stripeValidMultiV1Sig200:
    with env "TEST_STRIPE_WH_SECRET" = "whsec_test"
    with now = 1700000050000
    with body = "{\"type\":\"invoice.paid\"}"
    with header "stripe-signature" = "t=1700000000,v0=bad,v1=deadbeef,v1=" ++ testMockHmacHex("whsec_test", "1700000000.{\"type\":\"invoice.paid\"}") ++ ",v2=abc=="
    post "/webhooks/stripe"
    expect status == 200
    expect db_count("billing_events") == 1

  example githubValidAndInvalidHmac:
    with env "TEST_GITHUB_WH_SECRET" = "ghsec_test"
    with body = "{\"ref\":\"main\"}"
    with header "x-hub-signature-256" = "sha1=" ++ testMockHmacHex("ghsec_test", "{\"ref\":\"main\"}")
    post "/webhooks/github"
    expect status == 401
    with header "x-hub-signature-256" = "sha256=" ++ testMockHmacHex("ghsec_test", "{\"ref\":\"main\"}")
    post "/webhooks/github"
    expect status == 200
    expect db_count("deployments") == 1

  example cronHeaderAndBearerRoutes:
    with db db.deployments = [{ id = "d1", ownerId = "alice", status = "building" }]
    post "/cron/cleanup"
    expect status == 500
    with env "TEST_BEARER_SECRET" = "cron_bearer_secret"
    with header "authorization" = "Bearer wrong_secret"
    post "/cron/reap"
    expect status == 401
    with header "authorization" = "Bearer cron_bearer_secret"
    post "/cron/reap"
    expect status == 200
    with env "TEST_CRON_SECRET" = "cron_hdr_secret"
    with header "x-qed-cron-secret" = "wrong"
    post "/cron/cleanup"
    expect status == 401
    with header "x-qed-cron-secret" = "cron_hdr_secret"
    post "/cron/cleanup"
    expect status == 200
    expect db_count("deployments") == 0

server stateless BuildJobSrv:
  use db : PrincipalDb
  every 1s poll -> Bool!:
    let claimed = await db.deployments.where(r => r.status == "queued").updateOne({ status = "building" })?
    return claimed != none
  example pollClaimsQueuedDeployment:
    with db db.deployments = [{ id = "d1", ownerId = "alice", status = "queued" }]
    call poll()
    expect ok(true)
    call poll()
    expect ok(false)

-- Negative compile-time tests for Phase 2 principals & route guards
bad_srv "`requires system(...)` is only supported on HTTP routes" [stateless] BadSystemOnRpc :
  use db : PrincipalDb || env s = "S" ?? "" ||
  rpc bad() -> Bool!:
    requires system("stripe", stripe = s)
    return true
bad_svc "`ctx` is already implicitly available as `RequestCtx`" BadExplicitCtxSvc :
  use db : PrincipalDb ||
  fn spoof(ctx: RequestCtx) -> Bool:
    return ctx.userId != none
bad_srv "forbids hardcoded string literals" [stateless] BadLiteralSystemSecret :
  use db : PrincipalDb ||
  post "/hook":
    requires system("stripe", stripe = "hardcoded")
    return text("ok")
bad_srv "unknown `secret` or `env` variable `missingSec`" [stateless] BadUnknownSystemSecret :
  use db : PrincipalDb ||
  post "/hook":
    requires system("stripe", stripe = missingSec)
    return text("ok")
bad_srv "cannot combine `requires auth` with `requires system(...)`" [stateless] BadMixedAuthSystem :
  use db : PrincipalDb || env s = "S" ?? "" ||
  post "/hook":
    requires auth, system("stripe", stripe = s)
    return text("ok")
bad_srv "Database insert policy `PrincipalDb.billing_events.insert` failed" [stateless] BadGithubWritesBilling :
  use db : PrincipalDb || env s = "S" ?? "" ||
  post "/webhooks/github":
    requires system("github", hmac_sha256 = s, header = "x-hub-signature-256", prefix = "sha256=")
    let _ = await db.billing_events.insert(id = "e1", status = "paid")?
    return text("ok")
bad_srv "Database update policy `PrincipalDb.deployments.update` failed" [stateless] WrongJobSrv :
  use db : PrincipalDb ||
  every 1s poll -> Bool!:
    let upd = await db.deployments.where(r => r.status == "queued").updateOne({ status = "building" })?
    return upd != none
bad_srv "Database delete policy `PrincipalDb.deployments.delete` failed" [stateless] BadJobDeletesDeployments :
  use db : PrincipalDb ||
  every 1s poll -> Bool!:
    let _ = await db.deployments.where(r => r.status == "stale").delete()?
    return true
bad_db_tbl "cannot combine `principal = ...` with `user`/`role`/`session`" BadMixedPrincipalEx docs :
  id : String primary_key || policy read requires ctx.principal == .system("stripe") || example d1: id = "d1" ||
  example read badMix:
    user = "alice"
    principal = .system("stripe")
    row = d1

/-! ## Phase 3: Default-Deny Omitted Table Policies -/
database DefaultDenyDb:
  sqlite ".qed/default_deny_checks.db"
  table locked:
    id     : String primary_key where 1 <= id.length <= 64
    secret : String where 1 <= secret.length <= 128
  table narrow:
    id      : String primary_key where 1 <= id.length <= 64
    ownerId : String immutable where 1 <= ownerId.length <= 64
    secret  : encrypted(String, key = secret("DD_KEY") ?? "dd-dev-key-material-32bytes!") where 1 <= secret.length <= 128
    policy count requires some(row.ownerId) == ctx.userId
    policy read_meta requires some(row.ownerId) == ctx.userId
    policy read(id) by id requires ctx.userId != none

server stateless DefaultDenyPartialApi:
  use db : DefaultDenyDb
  rpc countOwn() -> Nat!:
    requires auth
    return await db.narrow.where(r => r.ownerId == uid).count()?
  rpc listMeta() -> DefaultDenyDb.narrow.Meta[]!:
    requires auth
    return await db.narrow.where(r => r.ownerId == uid).selectMeta()?
  rpc lookupId(targetId: String) -> String?!:
    requires auth
    return await db.narrow.where(r => r.id == targetId).columns("id").findOne()?

bad_db_auth "omitted policies default to deny" DefaultDenyDb denyLockedRead() -> DefaultDenyDb.locked[]! : return await db.locked.select()?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyLockedInsert(id: String) -> DefaultDenyDb.locked! || 1 <= id.length <= 64 : return await db.locked.insert(id = id, secret = "x")?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyLockedUpdate(id: String) -> DefaultDenyDb.locked?! : return await db.locked.where(r => r.id == id).updateOne({ secret = "y" })?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyLockedDelete(id: String) -> Nat! : return await db.locked.where(r => r.id == id).delete()?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyNarrowFullRead() -> DefaultDenyDb.narrow[]! : return await db.narrow.where(r => r.ownerId == uid).select()?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyNarrowUnlistedCol(targetId: String) -> (String, String)?! : return await db.narrow.where(r => r.id == targetId).columns(["id", "ownerId"]).findOne()?
bad_db_auth "omitted policies default to deny" DefaultDenyDb denyNarrowMultiRowBy(targetId: String) -> String[]! : return await db.narrow.where(r => r.id == targetId).columns("id").select()?

end DbChecks
