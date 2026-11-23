use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::identity;
use std::path::Path;
use std::sync::{Arc, Condvar, Mutex, OnceLock, RwLock};
use std::time::Duration;

use rusqlite::types::{ToSqlOutput, ValueRef};
use rusqlite::{params_from_iter, Connection, OpenFlags};

use crate::lean_ffi::*;
use crate::{HandleTable, lock_unpoison, read_unpoison, wait_unpoison, write_unpoison};

const STMT_CACHE_CAPACITY: usize = 128;
const TLS_POOL_CACHE_CAP: usize = 4;
const INLINE_PARAM_CAP: usize = 16;

fn max_readers_per_db() -> usize {
    static CAP: OnceLock<usize> = OnceLock::new();
    *CAP.get_or_init(|| std::thread::available_parallelism().map_or(16, |n| n.get().clamp(8, 32)))
}

fn init_conn(conn: &Connection, pragmas: &str) {
    conn.set_prepared_statement_cache_capacity(STMT_CACHE_CAPACITY);
    let _ = conn.busy_timeout(Duration::from_secs(5));
    let _ = conn.execute_batch(pragmas);
}

struct SqliteDbPool {
    path: String,
    is_memory: bool,
    writer: Mutex<Option<Connection>>,
    writer_cv: Condvar,
    readers: Mutex<Vec<Connection>>,
}

impl SqliteDbPool {
    fn checkout_writer(&self) -> Connection {
        let mut g = lock_unpoison(&self.writer);
        while g.is_none() { g = wait_unpoison(&self.writer_cv, g); }
        g.take().unwrap()
    }

    fn return_writer(&self, conn: Connection) {
        *lock_unpoison(&self.writer) = Some(conn);
        self.writer_cv.notify_one();
    }

    fn checkout_reader(&self) -> Result<Connection, String> {
        if let Some(conn) = lock_unpoison(&self.readers).pop() { return Ok(conn); }
        let flags = OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_NO_MUTEX;
        let conn = Connection::open_with_flags(&self.path, flags)
            .map_err(|e| format!("sqlite open read-only `{}` failed: {e}", self.path))?;
        init_conn(
            &conn,
            "PRAGMA query_only = ON; PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; \
             PRAGMA cache_size = -2000; PRAGMA mmap_size = 67108864;",
        );
        Ok(conn)
    }

    fn return_reader(&self, conn: Connection) {
        let mut pool = lock_unpoison(&self.readers);
        if pool.len() < max_readers_per_db() { pool.push(conn); }
    }
}

struct ConnGuard<'a> { pool: &'a SqliteDbPool, conn: Option<Connection>, is_writer: bool }

impl<'a> ConnGuard<'a> {
    fn writer(pool: &'a SqliteDbPool) -> Self { Self { pool, conn: Some(pool.checkout_writer()), is_writer: true } }
    fn reader(pool: &'a SqliteDbPool) -> Result<Self, String> {
        Ok(Self { pool, conn: Some(pool.checkout_reader()?), is_writer: false })
    }
    fn conn(&self) -> &Connection { self.conn.as_ref().expect("connection checked out") }
}

impl Drop for ConnGuard<'_> {
    fn drop(&mut self) {
        if let Some(conn) = self.conn.take() {
            if self.is_writer { self.pool.return_writer(conn); } else { self.pool.return_reader(conn); }
        }
    }
}

struct ActiveSqliteTx { pool: Arc<SqliteDbPool>, conn: Option<Connection> }

impl ActiveSqliteTx {
    fn finish(&mut self, commit: bool) -> Result<(), String> {
        let conn = self.conn.take().ok_or_else(|| "sqlite transaction already finished".to_owned())?;
        let res = if commit {
            conn.execute_batch("COMMIT;").map_err(|e| format!("sqlite COMMIT failed: {e}"))
        } else { Ok(()) };
        if !commit || res.is_err() { let _ = conn.execute_batch("ROLLBACK;"); }
        self.pool.return_writer(conn);
        res
    }
}

impl Drop for ActiveSqliteTx { fn drop(&mut self) { let _ = self.finish(false); } }

static SQLITE_POOL: OnceLock<RwLock<HashMap<String, Arc<SqliteDbPool>>>> = OnceLock::new();
static ACTIVE_TXS: HandleTable<Arc<Mutex<ActiveSqliteTx>>> = HandleTable::new();

thread_local! {
    static TLS_DB_CACHE: RefCell<Vec<(String, Arc<SqliteDbPool>)>> = const { RefCell::new(Vec::new()) };
}

fn cache_tls_pool(path: &str, db: &Arc<SqliteDbPool>) {
    TLS_DB_CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        if !cache.iter().any(|(k, _)| k == path) {
            if cache.len() >= TLS_POOL_CACHE_CAP { cache.remove(0); }
            cache.push((path.to_owned(), db.clone()));
        }
    });
}

fn open_db_pool(path: &str) -> Result<Arc<SqliteDbPool>, String> {
    if let Some(db) = TLS_DB_CACHE.with(|c| c.borrow().iter().find(|(k, _)| k == path).map(|(_, v)| v.clone())) {
        return Ok(db);
    }
    let pool = SQLITE_POOL.get_or_init(|| RwLock::new(HashMap::new()));
    let hit = read_unpoison(pool).get(path).cloned();
    if let Some(db) = hit {
        cache_tls_pool(path, &db);
        return Ok(db);
    }
    let is_mem = path == ":memory:" || path.is_empty() || path.contains("mode=memory") || path.starts_with("file::memory:");
    if let Some(parent) = (!is_mem).then(|| Path::new(path).parent()).flatten().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("failed to create sqlite directory `{}`: {e}", parent.display()))?;
    }
    let conn = if is_mem { Connection::open_in_memory() } else { Connection::open(path) }
        .map_err(|e| format!("sqlite open `{path}` failed: {e}"))?;
    let pragmas = if is_mem {
        "PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000;"
    } else {
        "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON; \
         PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000; \
         PRAGMA mmap_size = 67108864; PRAGMA journal_size_limit = 67108864;"
    };
    init_conn(&conn, pragmas);
    let arc = Arc::new(SqliteDbPool {
        path: path.to_owned(), is_memory: is_mem,
        writer: Mutex::new(Some(conn)), writer_cv: Condvar::new(), readers: Mutex::new(Vec::new()),
    });
    let db = write_unpoison(pool).entry(path.to_owned()).or_insert_with(|| arc).clone();
    cache_tls_pool(path, &db);
    Ok(db)
}

fn exec_ddl(db: &SqliteDbPool, ddl: &str) -> Result<(), String> {
    let writer = ConnGuard::writer(db);
    let r = writer.conn().execute_batch(ddl).map_err(|e| format!("sqlite ddl failed: {e}"));
    // Drop cached read-only connections so schema changes are immediately visible cleanly.
    lock_unpoison(&db.readers).clear();
    r
}

/// Returns true iff `sql` is a pure single-statement `SELECT` query safe to execute on the
/// concurrent read-only WAL reader pool (no write ops, no `RETURNING`, no stacked statements).
fn is_readonly_select(sql: &str) -> bool {
    const WRITE_WS_TOKS: &[&[u8]] = &[
        b"INSERT", b"UPDATE", b"DELETE", b"REPLACE", b"DROP",
        b"ALTER", b"CREATE", b"ATTACH", b"DETACH",
    ];
    const WRITE_ANY_TOKS: &[&[u8]] = &[b"VACUUM", b"REINDEX", b"RETURNING"];

    let bytes = sql.trim_start().as_bytes();
    if bytes.len() < 7 || !bytes[..6].eq_ignore_ascii_case(b"SELECT") || !bytes[6].is_ascii_whitespace() {
        return false;
    }
    let tail = &bytes[7..];
    for (i, &b) in tail.iter().enumerate() {
        if b == b';' { return false; }
        if matches!(b | 0x20, b'a' | b'c' | b'd' | b'i' | b'r' | b'u' | b'v') {
            let rest = &tail[i..];
            let is_write_ws = WRITE_WS_TOKS.iter().any(|kw| {
                rest.len() > kw.len() && rest[..kw.len()].eq_ignore_ascii_case(kw) && rest[kw.len()].is_ascii_whitespace()
            });
            let is_write_any = WRITE_ANY_TOKS.iter().any(|kw| {
                rest.len() >= kw.len() && rest[..kw.len()].eq_ignore_ascii_case(kw)
            });
            if is_write_ws || is_write_any { return false; }
        }
    }
    true
}

// ---- Direct Lean-Object `SqlVal` / `DbResult` FFI Conversion ----
// Matches `Qed.Server.Db.SqlVal` (tags 0=null, 1=int, 2=text, 3=bool[u8@0], 4=bytes)
// and `Qed.Server.Db.DbResult` (tag 0, 2 objs: rows, affected).

unsafe fn decode_lean_param<'a>(elem: *mut LeanObj) -> Result<ValueRef<'a>, String> {
    match qed_lean_obj_tag(elem) {
        0 => Ok(ValueRef::Null),
        1 => {
            let mut v: i64 = 0;
            if qed_lean_int_to_i64_checked(qed_lean_ctor_get(elem, 0), &mut v) == 0 {
                return Err("SQLite integer parameter out of i64 range".to_owned());
            }
            Ok(ValueRef::Integer(v))
        }
        2 => Ok(ValueRef::Text(str_slice(qed_lean_ctor_get(elem, 0)).as_bytes())),
        3 => Ok(ValueRef::Integer(i64::from(qed_lean_ctor_get_u8(elem, 0) != 0))),
        4 => Ok(ValueRef::Blob(ba_slice(qed_lean_ctor_get(elem, 0)))),
        tag => Err(format!("unknown SqlVal constructor tag {tag}")),
    }
}

unsafe fn with_lean_params<R>(
    params_arr: *mut LeanObj,
    f: impl FnOnce(&[ValueRef<'_>]) -> Result<R, String>,
) -> Result<R, String> {
    let n = qed_lean_array_size(params_arr);
    if n <= INLINE_PARAM_CAP {
        let mut stack = [ValueRef::Null; INLINE_PARAM_CAP];
        for (i, slot) in stack[..n].iter_mut().enumerate() {
            *slot = decode_lean_param(qed_lean_array_get_core(params_arr, i))?;
        }
        f(&stack[..n])
    } else {
        let mut heap = Vec::with_capacity(n);
        for i in 0..n { heap.push(decode_lean_param(qed_lean_array_get_core(params_arr, i))?); }
        f(&heap)
    }
}

unsafe fn sqlite_val_to_lean(v: ValueRef<'_>) -> *mut LeanObj {
    match v {
        ValueRef::Null => qed_lean_box(0),
        ValueRef::Integer(i) => qed_lean_mk_ctor_1(1, qed_lean_int64_to_int(i)),
        ValueRef::Real(f) => qed_lean_mk_ctor_1(2, mk_str(&f.to_string())),
        ValueRef::Text(bs) => qed_lean_mk_ctor_1(2, mk_str(&String::from_utf8_lossy(bs))),
        ValueRef::Blob(bs) => qed_lean_mk_ctor_1(4, mk_ba(bs)),
    }
}

unsafe fn exec_on_conn(conn: &Connection, sql: &str, params: &[ValueRef<'_>]) -> Result<*mut LeanObj, String> {
    let mut stmt = conn.prepare_cached(sql).map_err(|e| format!("sqlite prepare failed: {e}"))?;
    let bound = params_from_iter(params.iter().copied().map(ToSqlOutput::Borrowed));
    let col_count = stmt.column_count();
    if col_count > 0 {
        let mut rows = stmt.query(bound).map_err(|e| format!("sqlite query failed: {e}"))?;
        let mut rows_arr = LeanRef(qed_lean_array_with_cap(16));
        let mut row_count: usize = 0;
        while let Some(row) = rows.next().map_err(|e| format!("sqlite step failed: {e}"))? {
            let mut row_arr = LeanRef(qed_lean_array_with_cap(col_count));
            for ci in 0..col_count {
                row_arr.0 = lean_array_push(row_arr.0, sqlite_val_to_lean(row.get_ref_unwrap(ci)));
            }
            rows_arr.0 = lean_array_push(rows_arr.0, row_arr.into_raw());
            row_count += 1;
        }
        Ok(qed_lean_mk_prod(rows_arr.into_raw(), qed_lean_usize_to_nat(row_count)))
    } else {
        let affected = stmt.execute(bound).map_err(|e| format!("sqlite execute failed: {e}"))?;
        Ok(qed_lean_mk_prod(qed_lean_array_with_cap(0), qed_lean_usize_to_nat(affected)))
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_exec(
    path_obj: *mut LeanObj, sql_obj: *mut LeanObj, params_arr: *mut LeanObj,
) -> *mut LeanObj {
    let (path, sql) = (str_slice(path_obj), str_slice(sql_obj));
    let res = with_lean_params(params_arr, |params| {
        let db = open_db_pool(path)?;
        let guard = if !db.is_memory && is_readonly_select(sql) { ConnGuard::reader(&db)? } else { ConnGuard::writer(&db) };
        exec_on_conn(guard.conn(), sql, params)
    });
    mk_io_except(res, identity)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_ddl(path_obj: *mut LeanObj, ddl_obj: *mut LeanObj) -> *mut LeanObj {
    let res = open_db_pool(str_slice(path_obj)).and_then(|db| exec_ddl(&db, str_slice(ddl_obj)));
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_begin(path_obj: *mut LeanObj) -> *mut LeanObj {
    let res: Result<u64, String> = (|| {
        let db = open_db_pool(str_slice(path_obj))?;
        let conn = db.checkout_writer();
        if let Err(e) = conn.execute_batch("BEGIN IMMEDIATE;") {
            db.return_writer(conn);
            return Err(format!("sqlite BEGIN failed: {e}"));
        }
        Ok(ACTIVE_TXS.insert(Arc::new(Mutex::new(ActiveSqliteTx { pool: db, conn: Some(conn) }))))
    })();
    mk_io_except(res, |id| qed_lean_box_u64(id))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_exec(
    tx_id: u64, sql_obj: *mut LeanObj, params_arr: *mut LeanObj,
) -> *mut LeanObj {
    let sql = str_slice(sql_obj);
    let res = with_lean_params(params_arr, |params| {
        let tx_arc = ACTIVE_TXS.get(tx_id).ok_or_else(|| format!("invalid sqlite transaction handle {tx_id}"))?;
        let tx = lock_unpoison(&tx_arc);
        let conn = tx.conn.as_ref().ok_or_else(|| "sqlite transaction already finished".to_owned())?;
        exec_on_conn(conn, sql, params)
    });
    mk_io_except(res, identity)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_commit(tx_id: u64) -> *mut LeanObj {
    let res = ACTIVE_TXS.remove(tx_id)
        .ok_or_else(|| format!("invalid sqlite transaction handle {tx_id}"))
        .and_then(|tx| lock_unpoison(&tx).finish(true));
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_rollback(tx_id: u64) -> *mut LeanObj {
    if let Some(tx) = ACTIVE_TXS.remove(tx_id) { let _ = lock_unpoison(&tx).finish(false); }
    mk_io_unit()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn is_readonly_select_cases() {
        const ALLOW: &[&str] = &[
            "SELECT 1", "  \t\nselect\tid, name FROM users WHERE id = ?1",
            "SeLeCt\r\nCOUNT(*) FROM notes",
            "SELECT \"created_at\", \"updated_at\", \"deleted_at\" FROM items",
        ];
        const DENY: &[&str] = &[
            "", "   ", "SELECT", "SELECTX FROM t", "INSERT INTO t VALUES (1)",
            "UPDATE t SET a = 1", "DELETE FROM t", "PRAGMA table_info(t)",
            "SELECT 1; DROP TABLE t", "SELECT 1;",
            "WITH x AS (INSERT INTO t VALUES (1)) SELECT * FROM t",
            "SELECT * FROM (WITH x AS (uPdAtE t SET a = 1) SELECT 1)",
            "SELECT * FROM (INSERT\tINTO t VALUES (1))",
            "SELECT * FROM t RETURNING id", "select * from t returning *",
            "SELECT * FROM t VACUUM", "SELECT * FROM t REINDEX",
            "SELECT * FROM t REPLACE INTO x", "SELECT * FROM t DROP TABLE x",
            "SELECT * FROM t ALTER TABLE x", "SELECT * FROM t CREATE TABLE x",
            "SELECT * FROM t ATTACH 'x'", "SELECT * FROM t DETACH x",
        ];
        for &sql in ALLOW { assert!(is_readonly_select(sql), "expected allow: {sql:?}"); }
        for &sql in DENY { assert!(!is_readonly_select(sql), "expected deny: {sql:?}"); }
    }

    #[test]
    fn open_db_pool_wal_concurrent_readers_and_ddl_clear() {
        struct TempDir(PathBuf);
        impl Drop for TempDir { fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); } }
        let uniq = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let tmp = TempDir(std::env::temp_dir().join(format!("qed_sqlite_test_{}_{}", std::process::id(), uniq)));
        let db_path = tmp.0.join("sub").join("test.db").to_string_lossy().into_owned();

        let db = open_db_pool(&db_path).expect("open_db_pool");
        assert!(Arc::ptr_eq(&db, &open_db_pool(&db_path).expect("tls cache hit")));
        {
            let w = ConnGuard::writer(&db);
            let mode: String = w.conn().query_row("PRAGMA journal_mode;", [], |r| r.get(0)).unwrap();
            assert_eq!(mode.to_ascii_lowercase(), "wal");
            for pragma in ["PRAGMA synchronous;", "PRAGMA foreign_keys;"] {
                assert_eq!(w.conn().query_row(pragma, [], |r| r.get::<_, i64>(0)).unwrap(), 1);
            }
            w.conn().execute_batch(
                "CREATE TABLE items (id INTEGER PRIMARY KEY, val TEXT NOT NULL);
                 INSERT INTO items VALUES (1, 'a'), (2, 'b'), (3, 'c');",
            ).unwrap();
        }
        // Concurrent WAL reads + writer across threads & query_only enforcement
        std::thread::scope(|s| {
            let p = db_path.as_str();
            s.spawn(move || {
                ConnGuard::writer(&open_db_pool(p).unwrap()).conn()
                    .execute("INSERT INTO items VALUES (4, 'd')", []).unwrap();
            });
            for _ in 0..8 {
                s.spawn(move || {
                    let pool = open_db_pool(p).unwrap();
                    let r = ConnGuard::reader(&pool).unwrap();
                    let cnt: i64 = r.conn().query_row("SELECT COUNT(*) FROM items", [], |row| row.get(0)).unwrap();
                    assert!(cnt == 3 || cnt == 4, "unexpected row count {cnt}");
                    assert!(r.conn().execute("INSERT INTO items VALUES (99, 'x')", []).is_err());
                });
            }
        });
        assert!(!lock_unpoison(&db.readers).is_empty());

        // DDL must clear cached readers and expose the new column cleanly
        exec_ddl(&db, "ALTER TABLE items ADD COLUMN extra INTEGER NOT NULL DEFAULT 7;").expect("ddl");
        assert!(lock_unpoison(&db.readers).is_empty());
        let sum: i64 = ConnGuard::reader(&db).unwrap().conn()
            .query_row("SELECT SUM(extra) FROM items", [], |r| r.get(0)).unwrap();
        assert_eq!(sum, 28);
        assert_eq!(lock_unpoison(&db.readers).len(), 1);
    }
}
