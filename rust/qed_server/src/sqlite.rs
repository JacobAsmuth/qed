use std::{cell::RefCell, collections::HashMap, convert::identity, path::Path, sync::{Arc, Condvar, Mutex, OnceLock, RwLock}, time::Duration};
use rusqlite::{params_from_iter, types::{ToSqlOutput, ValueRef}, Connection, OpenFlags};

use crate::lean_ffi::*;
use crate::{HandleTable, lock_unpoison, read_unpoison, wait_unpoison, write_unpoison};

fn sql_err(ctx: &str, e: rusqlite::Error) -> String { format!("sqlite {ctx} failed: {e}") }
fn tx_err(id: u64) -> String { format!("invalid sqlite transaction handle {id}") }
fn init_conn(conn: &Connection, pragmas: &str) {
    conn.set_prepared_statement_cache_capacity(128);
    let _ = (conn.busy_timeout(Duration::from_secs(5)), conn.execute_batch(pragmas));
}

struct SqliteDbPool { path: String, is_memory: bool, writer: Mutex<Option<Connection>>, writer_cv: Condvar, readers: Mutex<Vec<Connection>> }
impl SqliteDbPool {
    fn checkout_writer(&self) -> Connection {
        let mut g = lock_unpoison(&self.writer); while g.is_none() { g = wait_unpoison(&self.writer_cv, g); } g.take().unwrap()
    }
    fn return_writer(&self, conn: Connection) { *lock_unpoison(&self.writer) = Some(conn); self.writer_cv.notify_one(); }
    fn checkout_reader(&self) -> Result<Connection, String> {
        if let Some(conn) = lock_unpoison(&self.readers).pop() { return Ok(conn); }
        let conn = Connection::open_with_flags(&self.path, OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_NO_MUTEX)
            .map_err(|e| format!("sqlite open read-only `{}` failed: {e}", self.path))?;
        init_conn(&conn, "PRAGMA query_only = ON; PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -2000; PRAGMA mmap_size = 67108864;");
        Ok(conn)
    }
    fn return_reader(&self, conn: Connection) {
        static CAP: OnceLock<usize> = OnceLock::new();
        let cap = *CAP.get_or_init(|| std::thread::available_parallelism().map_or(16, |n| n.get().clamp(8, 32)));
        let mut pool = lock_unpoison(&self.readers);
        if pool.len() < cap { pool.push(conn); }
    }
}

struct ConnGuard<'a>(&'a SqliteDbPool, Option<Connection>, bool);
impl<'a> ConnGuard<'a> {
    fn writer(p: &'a SqliteDbPool) -> Self { Self(p, Some(p.checkout_writer()), true) }
    fn reader(p: &'a SqliteDbPool) -> Result<Self, String> { Ok(Self(p, Some(p.checkout_reader()?), false)) }
    fn conn(&self) -> &Connection { self.1.as_ref().expect("connection checked out") }
}
impl Drop for ConnGuard<'_> {
    fn drop(&mut self) { if let Some(c) = self.1.take() { if self.2 { self.0.return_writer(c); } else { self.0.return_reader(c); } } }
}

struct ActiveSqliteTx { pool: Arc<SqliteDbPool>, conn: Option<Connection> }
impl ActiveSqliteTx {
    fn finish(&mut self, commit: bool) -> Result<(), String> {
        let conn = self.conn.take().ok_or_else(|| "sqlite transaction already finished".to_owned())?;
        let res = if commit { conn.execute_batch("COMMIT;").map_err(|e| sql_err("COMMIT", e)) } else { Ok(()) };
        if !commit || res.is_err() { let _ = conn.execute_batch("ROLLBACK;"); }
        self.pool.return_writer(conn); res
    }
}
impl Drop for ActiveSqliteTx { fn drop(&mut self) { let _ = self.finish(false); } }

static SQLITE_POOL: OnceLock<RwLock<HashMap<String, Arc<SqliteDbPool>>>> = OnceLock::new();
static ACTIVE_TXS: HandleTable<Arc<Mutex<ActiveSqliteTx>>> = HandleTable::new();
thread_local! { static TLS_DB_CACHE: RefCell<Vec<(String, Arc<SqliteDbPool>)>> = const { RefCell::new(Vec::new()) }; }

fn open_db_pool(path: &str) -> Result<Arc<SqliteDbPool>, String> {
    if let Some(db) = TLS_DB_CACHE.with(|c| c.borrow().iter().find(|(k, _)| k == path).map(|(_, v)| v.clone())) { return Ok(db); }
    let pool = SQLITE_POOL.get_or_init(|| RwLock::new(HashMap::new()));
    let hit = read_unpoison(pool).get(path).cloned();
    let db = if let Some(db) = hit { db } else {
        let is_mem = path.is_empty() || path == ":memory:" || path.contains("mode=memory") || path.starts_with("file::memory:");
        if let Some(p) = (!is_mem).then(|| Path::new(path).parent()).flatten().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::create_dir_all(p).map_err(|e| format!("failed to create sqlite directory `{}`: {e}", p.display()))?;
        }
        let conn = if is_mem { Connection::open_in_memory() } else { Connection::open(path) }.map_err(|e| format!("sqlite open `{path}` failed: {e}"))?;
        init_conn(&conn, if is_mem { "PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000;" }
            else { "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000; PRAGMA mmap_size = 67108864; PRAGMA journal_size_limit = 67108864;" });
        let arc = Arc::new(SqliteDbPool { path: path.to_owned(), is_memory: is_mem, writer: Mutex::new(Some(conn)), writer_cv: Condvar::new(), readers: Mutex::new(Vec::new()) });
        write_unpoison(pool).entry(path.to_owned()).or_insert(arc).clone()
    };
    TLS_DB_CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        if !cache.iter().any(|(k, _)| k == path) { if cache.len() >= 4 { cache.remove(0); } cache.push((path.to_owned(), db.clone())); }
    });
    Ok(db)
}

fn exec_ddl(db: &SqliteDbPool, ddl: &str) -> Result<(), String> {
    let r = ConnGuard::writer(db).conn().execute_batch(ddl).map_err(|e| sql_err("ddl", e));
    lock_unpoison(&db.readers).clear(); r
}

/// True iff `sql` is a pure single-statement `SELECT` safe for the concurrent WAL reader pool.
fn is_readonly_select(sql: &str) -> bool {
    const WRITE_WS: &[&[u8]] = &[b"INSERT", b"UPDATE", b"DELETE", b"REPLACE", b"DROP", b"ALTER", b"CREATE", b"ATTACH", b"DETACH"];
    const WRITE_ANY: &[&[u8]] = &[b"VACUUM", b"REINDEX", b"RETURNING"];
    let b = sql.trim_start().as_bytes();
    b.len() >= 7 && b[..6].eq_ignore_ascii_case(b"SELECT") && b[6].is_ascii_whitespace() && !b[7..].iter().enumerate().any(|(i, &c)| {
        c == b';' || (matches!(c | 0x20, b'a' | b'c' | b'd' | b'i' | b'r' | b'u' | b'v') && {
            let r = &b[7 + i..];
            WRITE_WS.iter().any(|k| r.len() > k.len() && r[..k.len()].eq_ignore_ascii_case(k) && r[k.len()].is_ascii_whitespace())
                || WRITE_ANY.iter().any(|k| r.len() >= k.len() && r[..k.len()].eq_ignore_ascii_case(k))
        })
    })
}

// Matches `Qed.Server.Db.SqlVal` (0=null, 1=int, 2=text, 3=bool[u8@0], 4=bytes) & `DbResult` (rows, affected).
unsafe fn decode_params<'a>(arr: *mut LeanObj, stack: &'a mut [ValueRef<'a>; 16], heap: &'a mut Vec<ValueRef<'a>>) -> Result<&'a [ValueRef<'a>], String> {
    let n = qed_lean_array_size(arr);
    let dst = if n <= 16 { &mut stack[..n] } else { heap.resize(n, ValueRef::Null); &mut heap[..] };
    for (i, slot) in dst.iter_mut().enumerate() {
        let el = qed_lean_array_get_core(arr, i);
        *slot = match qed_lean_obj_tag(el) {
            0 => ValueRef::Null,
            1 => { let mut v = 0i64; if qed_lean_int_to_i64_checked(qed_lean_ctor_get(el, 0), &mut v) == 0 { return Err("SQLite integer parameter out of i64 range".into()); } ValueRef::Integer(v) }
            2 => ValueRef::Text(str_slice(qed_lean_ctor_get(el, 0)).as_bytes()),
            3 => ValueRef::Integer(i64::from(qed_lean_ctor_get_u8(el, 0) != 0)),
            4 => ValueRef::Blob(ba_slice(qed_lean_ctor_get(el, 0))),
            tag => return Err(format!("unknown SqlVal constructor tag {tag}")),
        };
    }
    Ok(dst)
}

unsafe fn exec_on_conn(conn: &Connection, sql: &str, params: &[ValueRef<'_>]) -> Result<*mut LeanObj, String> {
    let mut stmt = conn.prepare_cached(sql).map_err(|e| sql_err("prepare", e))?;
    let (bound, cols) = (params_from_iter(params.iter().copied().map(ToSqlOutput::Borrowed)), stmt.column_count());
    if cols > 0 {
        let mut rows = stmt.query(bound).map_err(|e| sql_err("query", e))?;
        let (mut rows_arr, mut count) = (LeanRef(qed_lean_array_with_cap(16)), 0usize);
        while let Some(row) = rows.next().map_err(|e| sql_err("step", e))? {
            let mut row_arr = LeanRef(qed_lean_array_with_cap(cols));
            for ci in 0..cols {
                let val = match row.get_ref_unwrap(ci) {
                    ValueRef::Null => qed_lean_box(0),
                    ValueRef::Integer(i) => qed_lean_mk_ctor_1(1, qed_lean_int64_to_int(i)),
                    ValueRef::Real(f) => qed_lean_mk_ctor_1(2, mk_str(&f.to_string())),
                    ValueRef::Text(bs) => qed_lean_mk_ctor_1(2, mk_str(&String::from_utf8_lossy(bs))),
                    ValueRef::Blob(bs) => qed_lean_mk_ctor_1(4, mk_ba(bs)),
                };
                row_arr.0 = lean_array_push(row_arr.0, val);
            }
            rows_arr.0 = lean_array_push(rows_arr.0, row_arr.into_raw()); count += 1;
        }
        Ok(qed_lean_mk_prod(rows_arr.into_raw(), qed_lean_usize_to_nat(count)))
    } else { Ok(qed_lean_mk_prod(qed_lean_array_with_cap(0), qed_lean_usize_to_nat(stmt.execute(bound).map_err(|e| sql_err("execute", e))?))) }
}

ffi_export! {
    qed_server_sqlite_exec(path_obj: *mut LeanObj, sql_obj: *mut LeanObj, params_arr: *mut LeanObj) => {
        let (path, sql, mut stack, mut heap) = (str_slice(path_obj), str_slice(sql_obj), [ValueRef::Null; 16], Vec::new());
        mk_io_except(decode_params(params_arr, &mut stack, &mut heap).and_then(|params| {
            let db = open_db_pool(path)?;
            let guard = if !db.is_memory && is_readonly_select(sql) { ConnGuard::reader(&db)? } else { ConnGuard::writer(&db) };
            exec_on_conn(guard.conn(), sql, params)
        }), identity)
    };
    qed_server_sqlite_ddl(path_obj: *mut LeanObj, ddl_obj: *mut LeanObj) =>
        mk_io_except_unit(open_db_pool(str_slice(path_obj)).and_then(|db| exec_ddl(&db, str_slice(ddl_obj))));
    qed_server_sqlite_tx_begin(path_obj: *mut LeanObj) => mk_io_except(open_db_pool(str_slice(path_obj)).and_then(|db| {
        let conn = db.checkout_writer();
        if let Err(e) = conn.execute_batch("BEGIN IMMEDIATE;") { db.return_writer(conn); return Err(sql_err("BEGIN", e)); }
        Ok(ACTIVE_TXS.insert(Arc::new(Mutex::new(ActiveSqliteTx { pool: db, conn: Some(conn) }))))
    }), |id| qed_lean_box_u64(id));
    qed_server_sqlite_tx_exec(tx_id: u64, sql_obj: *mut LeanObj, params_arr: *mut LeanObj) => {
        let (sql, mut stack, mut heap) = (str_slice(sql_obj), [ValueRef::Null; 16], Vec::new());
        mk_io_except(decode_params(params_arr, &mut stack, &mut heap).and_then(|params| {
            let tx_arc = ACTIVE_TXS.get(tx_id).ok_or_else(|| tx_err(tx_id))?;
            let tx = lock_unpoison(&tx_arc);
            exec_on_conn(tx.conn.as_ref().ok_or_else(|| "sqlite transaction already finished".to_owned())?, sql, params)
        }), identity)
    };
    qed_server_sqlite_tx_commit(tx_id: u64) =>
        mk_io_except_unit(ACTIVE_TXS.remove(tx_id).ok_or_else(|| tx_err(tx_id)).and_then(|tx| lock_unpoison(&tx).finish(true)));
    qed_server_sqlite_tx_rollback(tx_id: u64) => {
        if let Some(tx) = ACTIVE_TXS.remove(tx_id) { let _ = lock_unpoison(&tx).finish(false); } mk_io_unit()
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{path::PathBuf, time::{SystemTime, UNIX_EPOCH}};

    #[test]
    fn is_readonly_select_cases() {
        for sql in ["SELECT 1", "  \t\nselect\tid, name FROM users WHERE id = ?1", "SeLeCt\r\nCOUNT(*) FROM notes", "SELECT \"created_at\", \"updated_at\", \"deleted_at\" FROM items"] {
            assert!(is_readonly_select(sql), "expected allow: {sql:?}");
        }
        for sql in [
            "", "   ", "SELECT", "SELECTX FROM t", "INSERT INTO t VALUES (1)", "UPDATE t SET a = 1", "DELETE FROM t", "PRAGMA table_info(t)",
            "SELECT 1; DROP TABLE t", "SELECT 1;", "WITH x AS (INSERT INTO t VALUES (1)) SELECT * FROM t",
            "SELECT * FROM (WITH x AS (uPdAtE t SET a = 1) SELECT 1)", "SELECT * FROM (INSERT\tINTO t VALUES (1))",
            "SELECT * FROM t RETURNING id", "select * from t returning *", "SELECT * FROM t VACUUM", "SELECT * FROM t REINDEX",
            "SELECT * FROM t REPLACE INTO x", "SELECT * FROM t DROP TABLE x", "SELECT * FROM t ALTER TABLE x",
            "SELECT * FROM t CREATE TABLE x", "SELECT * FROM t ATTACH 'x'", "SELECT * FROM t DETACH x",
        ] { assert!(!is_readonly_select(sql), "expected deny: {sql:?}"); }
    }

    #[test]
    fn open_db_pool_wal_concurrent_readers_and_ddl_clear() {
        struct TempDir(PathBuf);
        impl Drop for TempDir { fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); } }
        let tmp = TempDir(std::env::temp_dir().join(format!("qed_sqlite_test_{}_{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos())));
        let db_path = tmp.0.join("sub").join("test.db").to_string_lossy().into_owned();
        let db = open_db_pool(&db_path).expect("open_db_pool");
        assert!(Arc::ptr_eq(&db, &open_db_pool(&db_path).expect("tls cache hit")));
        {
            let w = ConnGuard::writer(&db);
            assert_eq!(w.conn().query_row("PRAGMA journal_mode;", [], |r| r.get::<_, String>(0)).unwrap().to_ascii_lowercase(), "wal");
            for p in ["PRAGMA synchronous;", "PRAGMA foreign_keys;"] { assert_eq!(w.conn().query_row(p, [], |r| r.get::<_, i64>(0)).unwrap(), 1); }
            w.conn().execute_batch("CREATE TABLE items (id INTEGER PRIMARY KEY, val TEXT NOT NULL); INSERT INTO items VALUES (1,'a'),(2,'b'),(3,'c');").unwrap();
        }
        std::thread::scope(|s| {
            let p = db_path.as_str();
            s.spawn(move || { ConnGuard::writer(&open_db_pool(p).unwrap()).conn().execute("INSERT INTO items VALUES (4,'d')", []).unwrap(); });
            for _ in 0..8 {
                s.spawn(move || {
                    let pool = open_db_pool(p).unwrap();
                    let r = ConnGuard::reader(&pool).unwrap();
                    let cnt: i64 = r.conn().query_row("SELECT COUNT(*) FROM items", [], |row| row.get(0)).unwrap();
                    assert!((cnt == 3 || cnt == 4) && r.conn().execute("INSERT INTO items VALUES (99,'x')", []).is_err());
                });
            }
        });
        assert!(!lock_unpoison(&db.readers).is_empty());
        exec_ddl(&db, "ALTER TABLE items ADD COLUMN extra INTEGER NOT NULL DEFAULT 7;").expect("ddl");
        assert!(lock_unpoison(&db.readers).is_empty());
        assert_eq!(ConnGuard::reader(&db).unwrap().conn().query_row("SELECT SUM(extra) FROM items", [], |r| r.get::<_, i64>(0)).unwrap(), 28);
        assert_eq!(lock_unpoison(&db.readers).len(), 1);
    }
}
