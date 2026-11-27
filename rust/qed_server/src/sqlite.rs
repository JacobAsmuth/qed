use std::{cell::RefCell, collections::HashMap, convert::identity, ffi::{c_char, c_int, CStr, CString}, fmt::Display, marker::PhantomData, path::Path, ptr, sync::{Arc, Condvar, Mutex, OnceLock, RwLock}};
use libsqlite3_sys as ffi;

use crate::lean_ffi::*;
use crate::{HandleTable, lock_unpoison, read_unpoison, wait_unpoison, write_unpoison};

extern "C" { fn sqlite3_close_v2(db: *mut ffi::sqlite3) -> c_int; }

const STMT_CACHE_CAP: usize = 128;
const OPEN_WRITER: c_int = ffi::SQLITE_OPEN_READWRITE | ffi::SQLITE_OPEN_CREATE | ffi::SQLITE_OPEN_URI | ffi::SQLITE_OPEN_NOMUTEX;
const OPEN_READER: c_int = ffi::SQLITE_OPEN_READONLY | ffi::SQLITE_OPEN_URI | ffi::SQLITE_OPEN_NOMUTEX;
const PRAGMAS_MEM: &str = "PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000;";
const PRAGMAS_WAL: &str = "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -8000; PRAGMA mmap_size = 67108864; PRAGMA journal_size_limit = 67108864;";
const PRAGMAS_RO: &str = "PRAGMA query_only = ON; PRAGMA foreign_keys = ON; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -2000; PRAGMA mmap_size = 67108864;";

const TX_FINISHED: &str = "sqlite transaction already finished";
fn sql_err(ctx: &str, e: impl Display) -> String { format!("sqlite {ctx} failed: {e}") }
fn tx_err(id: u64) -> String { format!("invalid sqlite transaction handle {id}") }
unsafe fn db_errmsg(db: *mut ffi::sqlite3, rc: c_int) -> String {
    let p = Some(if !db.is_null() { ffi::sqlite3_errmsg(db) } else { ptr::null() }).filter(|p| !p.is_null()).unwrap_or_else(|| ffi::sqlite3_errstr(rc));
    if p.is_null() { format!("sqlite error code {rc}") } else { CStr::from_ptr(p).to_string_lossy().into_owned() }
}
#[derive(Clone, Copy)]
enum SqlParam<'a> { Null, Integer(i64), Text(&'a [u8]), Blob(&'a [u8]) }
enum ColRef<'a> { Null, Integer(i64), Real(f64), Text(&'a [u8]), Blob(&'a [u8]) }

struct SqliteConn { db: *mut ffi::sqlite3, cache: HashMap<String, (*mut ffi::sqlite3_stmt, u64)>, tick: u64 }
unsafe impl Send for SqliteConn {}
impl SqliteConn {
    fn open(path: &str, flags: c_int, pragmas: &str) -> Result<Self, String> {
        let c_path = CString::new(path).map_err(|_| "path contains NUL byte".to_owned())?;
        let mut db = ptr::null_mut();
        let rc = unsafe { ffi::sqlite3_open_v2(c_path.as_ptr(), &mut db, flags | ffi::SQLITE_OPEN_EXRESCODE, ptr::null()) };
        if rc != ffi::SQLITE_OK { return Err(unsafe { let m = db_errmsg(db, rc); if !db.is_null() { sqlite3_close_v2(db); } m }); }
        let conn = Self { db, cache: HashMap::new(), tick: 0 };
        unsafe { ffi::sqlite3_busy_timeout(conn.db, 5000); }
        let _ = conn.execute_batch(pragmas); Ok(conn)
    }
    fn execute_batch(&self, sql: &str) -> Result<(), String> {
        let (c_sql, mut errmsg) = (CString::new(sql).map_err(|_| "SQL contains NUL byte".to_owned())?, ptr::null_mut::<c_char>());
        let rc = unsafe { ffi::sqlite3_exec(self.db, c_sql.as_ptr(), None, ptr::null_mut(), &mut errmsg) };
        let err = (!errmsg.is_null()).then(|| unsafe { let s = CStr::from_ptr(errmsg).to_string_lossy().into_owned(); ffi::sqlite3_free(errmsg.cast()); s });
        if rc == ffi::SQLITE_OK { Ok(()) } else { Err(err.unwrap_or_else(|| unsafe { db_errmsg(self.db, rc) })) }
    }
    fn prepare_cached(&mut self, sql: &str) -> Result<PreparedStmt<'_>, String> {
        let key = sql.trim();
        if key.is_empty() { return Err("empty SQL statement".to_owned()); }
        self.tick = self.tick.wrapping_add(1);
        let stmt = if let Some(&mut (stmt, ref mut last)) = self.cache.get_mut(key) { *last = self.tick; stmt } else {
            let (len, mut stmt) = (c_int::try_from(key.len()).map_err(|_| "SQL exceeds maximum length".to_owned())?, ptr::null_mut());
            let rc = unsafe { ffi::sqlite3_prepare_v3(self.db, key.as_ptr().cast(), len, ffi::SQLITE_PREPARE_PERSISTENT, &mut stmt, ptr::null_mut()) };
            if rc != ffi::SQLITE_OK { return Err(unsafe { db_errmsg(self.db, rc) }); }
            if stmt.is_null() { return Err("empty SQL statement".to_owned()); }
            if self.cache.len() >= STMT_CACHE_CAP {
                if let Some(old) = self.cache.iter().min_by_key(|(_, &(_, t))| t).map(|(k, _)| k.clone()).and_then(|k| self.cache.remove(&k)) { unsafe { ffi::sqlite3_finalize(old.0) }; }
            }
            self.cache.insert(key.to_owned(), (stmt, self.tick)); stmt
        };
        Ok(PreparedStmt { db: self.db, stmt, _conn: PhantomData })
    }
    fn clear_cache(&mut self) { for (_, (stmt, _)) in self.cache.drain() { unsafe { ffi::sqlite3_finalize(stmt) }; } }
}
impl Drop for SqliteConn { fn drop(&mut self) { self.clear_cache(); if !self.db.is_null() { unsafe { sqlite3_close_v2(self.db) }; } } }

struct PreparedStmt<'a> { db: *mut ffi::sqlite3, stmt: *mut ffi::sqlite3_stmt, _conn: PhantomData<&'a mut SqliteConn> }
impl Drop for PreparedStmt<'_> { fn drop(&mut self) { unsafe { ffi::sqlite3_reset(self.stmt); ffi::sqlite3_clear_bindings(self.stmt); } } }
impl PreparedStmt<'_> {
    #[inline] fn column_count(&self) -> usize { (unsafe { ffi::sqlite3_column_count(self.stmt) }).max(0) as usize }
    fn bind_params(&mut self, params: &[SqlParam<'_>], ctx: &str) -> Result<(), String> {
        let expected = (unsafe { ffi::sqlite3_bind_parameter_count(self.stmt) }).max(0) as usize;
        if params.len() != expected { return Err(sql_err(ctx, format!("wrong number of parameters: expected {expected}, got {}", params.len()))); }
        let chk = |bs: &[u8], k| c_int::try_from(bs.len()).map_err(|_| sql_err(ctx, format!("{k} parameter exceeds SQLite max length")));
        for (i, &p) in params.iter().enumerate() {
            let idx = (i + 1) as c_int;
            let rc = unsafe { match p {
                SqlParam::Null => ffi::sqlite3_bind_null(self.stmt, idx),
                SqlParam::Integer(v) => ffi::sqlite3_bind_int64(self.stmt, idx, v),
                SqlParam::Text(bs) => match chk(bs, "text")? { 0 => ffi::sqlite3_bind_text(self.stmt, idx, c"".as_ptr(), 0, ffi::SQLITE_STATIC()), n => ffi::sqlite3_bind_text(self.stmt, idx, bs.as_ptr().cast(), n, ffi::SQLITE_TRANSIENT()) },
                SqlParam::Blob(bs) => match chk(bs, "blob")? { 0 => ffi::sqlite3_bind_zeroblob(self.stmt, idx, 0), n => ffi::sqlite3_bind_blob(self.stmt, idx, bs.as_ptr().cast(), n, ffi::SQLITE_TRANSIENT()) },
            }};
            if rc != ffi::SQLITE_OK { return Err(sql_err(ctx, unsafe { db_errmsg(self.db, rc) })); }
        }
        Ok(())
    }
    fn step(&mut self) -> Result<bool, String> {
        match unsafe { ffi::sqlite3_step(self.stmt) } {
            ffi::SQLITE_ROW => Ok(true),
            ffi::SQLITE_DONE => match unsafe { ffi::sqlite3_reset(self.stmt) } { ffi::SQLITE_OK => Ok(false), r => Err(unsafe { db_errmsg(self.db, r) }) },
            rc => Err(unsafe { db_errmsg(self.db, rc) }),
        }
    }
    unsafe fn col_ref(&self, ci: usize) -> ColRef<'_> {
        let bytes = |p: *const u8, n: c_int| if p.is_null() || n <= 0 { &[][..] } else { std::slice::from_raw_parts(p, n as usize) };
        let i = ci as c_int;
        match ffi::sqlite3_column_type(self.stmt, i) {
            ffi::SQLITE_INTEGER => ColRef::Integer(ffi::sqlite3_column_int64(self.stmt, i)),
            ffi::SQLITE_FLOAT => ColRef::Real(ffi::sqlite3_column_double(self.stmt, i)),
            ffi::SQLITE_TEXT => ColRef::Text(bytes(ffi::sqlite3_column_text(self.stmt, i), ffi::sqlite3_column_bytes(self.stmt, i))),
            ffi::SQLITE_BLOB => ColRef::Blob(bytes(ffi::sqlite3_column_blob(self.stmt, i).cast(), ffi::sqlite3_column_bytes(self.stmt, i))),
            _ => ColRef::Null,
        }
    }
}

struct SqliteDbPool { path: String, is_memory: bool, writer: Mutex<Option<SqliteConn>>, writer_cv: Condvar, readers: Mutex<Vec<SqliteConn>> }
impl SqliteDbPool {
    fn checkout_writer(&self) -> SqliteConn { let mut g = lock_unpoison(&self.writer); while g.is_none() { g = wait_unpoison(&self.writer_cv, g); } g.take().unwrap() }
    fn return_writer(&self, conn: SqliteConn) { *lock_unpoison(&self.writer) = Some(conn); self.writer_cv.notify_one(); }
    fn checkout_reader(&self) -> Result<SqliteConn, String> {
        if let Some(conn) = lock_unpoison(&self.readers).pop() { return Ok(conn); }
        SqliteConn::open(&self.path, OPEN_READER, PRAGMAS_RO).map_err(|e| format!("sqlite open read-only `{}` failed: {e}", self.path))
    }
    fn return_reader(&self, conn: SqliteConn) {
        static CAP: OnceLock<usize> = OnceLock::new();
        let cap = *CAP.get_or_init(|| std::thread::available_parallelism().map_or(16, |n| n.get().clamp(8, 32)));
        let mut pool = lock_unpoison(&self.readers); if pool.len() < cap { pool.push(conn); }
    }
}
struct ConnGuard<'a>(&'a SqliteDbPool, Option<SqliteConn>, bool);
impl<'a> ConnGuard<'a> {
    fn writer(p: &'a SqliteDbPool) -> Self { Self(p, Some(p.checkout_writer()), true) }
    fn reader(p: &'a SqliteDbPool) -> Result<Self, String> { Ok(Self(p, Some(p.checkout_reader()?), false)) }
    fn conn_mut(&mut self) -> &mut SqliteConn { self.1.as_mut().expect("connection checked out") }
}
impl Drop for ConnGuard<'_> { fn drop(&mut self) { if let Some(c) = self.1.take() { if self.2 { self.0.return_writer(c); } else { self.0.return_reader(c); } } } }

struct ActiveSqliteTx { pool: Arc<SqliteDbPool>, conn: Option<SqliteConn> }
impl ActiveSqliteTx {
    fn begin(pool: Arc<SqliteDbPool>) -> Result<Self, String> {
        let conn = pool.checkout_writer();
        if let Err(e) = conn.execute_batch("BEGIN IMMEDIATE;") { pool.return_writer(conn); return Err(sql_err("BEGIN", e)); }
        Ok(Self { pool, conn: Some(conn) })
    }
    fn finish(&mut self, commit: bool) -> Result<(), String> {
        let conn = self.conn.take().ok_or_else(|| TX_FINISHED.to_owned())?;
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
        if let Some(p) = (!is_mem && !path.starts_with("file:")).then(|| Path::new(path).parent()).flatten().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::create_dir_all(p).map_err(|e| format!("failed to create sqlite directory `{}`: {e}", p.display()))?;
        }
        let conn = SqliteConn::open(if is_mem && !path.starts_with("file:") { ":memory:" } else { path }, OPEN_WRITER, if is_mem { PRAGMAS_MEM } else { PRAGMAS_WAL })
            .map_err(|e| format!("sqlite open `{path}` failed: {e}"))?;
        let arc = Arc::new(SqliteDbPool { path: path.to_owned(), is_memory: is_mem, writer: Mutex::new(Some(conn)), writer_cv: Condvar::new(), readers: Mutex::new(Vec::new()) });
        write_unpoison(pool).entry(path.to_owned()).or_insert(arc).clone()
    };
    TLS_DB_CACHE.with(|c| { let mut m = c.borrow_mut(); if !m.iter().any(|(k, _)| k == path) { if m.len() >= 4 { m.remove(0); } m.push((path.to_owned(), db.clone())); } });
    Ok(db)
}
fn exec_ddl(db: &SqliteDbPool, ddl: &str) -> Result<(), String> {
    let mut g = ConnGuard::writer(db);
    let r = g.conn_mut().execute_batch(ddl).map_err(|e| sql_err("ddl", e));
    g.conn_mut().clear_cache(); lock_unpoison(&db.readers).clear(); r
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

fn exec_stmt<R>(
    conn: &mut SqliteConn, sql: &str, params: &[SqlParam<'_>],
    init_rows: impl FnOnce(usize) -> R, mut push_row: impl FnMut(&mut R, &PreparedStmt<'_>, usize),
) -> Result<(R, usize), String> {
    let mut stmt = conn.prepare_cached(sql).map_err(|e| sql_err("prepare", e))?;
    let cols = stmt.column_count();
    stmt.bind_params(params, if cols > 0 { "query" } else { "execute" })?;
    if cols == 0 {
        if stmt.step().map_err(|e| sql_err("execute", e))? { return Err(sql_err("execute", "execute returned rows unexpectedly")); }
        return Ok((init_rows(0), (unsafe { ffi::sqlite3_changes(stmt.db) }).max(0) as usize));
    }
    let (mut rows, mut count) = (init_rows(16), 0usize);
    while stmt.step().map_err(|e| sql_err("step", e))? { push_row(&mut rows, &stmt, stmt.column_count()); count += 1; }
    Ok((rows, count))
}

// Matches `Qed.Server.Db.SqlVal` (0=null, 1=int, 2=text, 3=bool[u8@0], 4=bytes) & `DbResult` (rows, affected).
unsafe fn with_decoded_params(sql_obj: *mut LeanObj, arr: *mut LeanObj, f: impl FnOnce(&str, &[SqlParam<'_>]) -> Result<*mut LeanObj, String>) -> *mut LeanObj {
    let (sql, n, mut stack, mut heap) = (str_slice(sql_obj), qed_lean_array_size(arr), [SqlParam::Null; 16], Vec::new());
    mk_io_except((|| {
        let dst = if n <= 16 { &mut stack[..n] } else { heap.resize(n, SqlParam::Null); &mut heap[..] };
        for (i, slot) in dst.iter_mut().enumerate() {
            let el = qed_lean_array_get_core(arr, i);
            *slot = match qed_lean_obj_tag(el) {
                0 => SqlParam::Null,
                1 => { let mut v = 0i64; if qed_lean_int_to_i64_checked(qed_lean_ctor_get(el, 0), &mut v) == 0 { return Err("SQLite integer parameter out of i64 range".into()); } SqlParam::Integer(v) }
                2 => SqlParam::Text(str_slice(qed_lean_ctor_get(el, 0)).as_bytes()),
                3 => SqlParam::Integer(i64::from(qed_lean_ctor_get_u8(el, 0) != 0)),
                4 => SqlParam::Blob(ba_slice(qed_lean_ctor_get(el, 0))),
                tag => return Err(format!("unknown SqlVal constructor tag {tag}")),
            };
        }
        f(sql, dst)
    })(), identity)
}

unsafe fn exec_on_conn(conn: &mut SqliteConn, sql: &str, params: &[SqlParam<'_>]) -> Result<*mut LeanObj, String> {
    let (rows, n) = exec_stmt(conn, sql, params, |c| LeanRef(qed_lean_array_with_cap(c)), |rows, stmt, ncols| {
        let mut row = LeanRef(qed_lean_array_with_cap(ncols));
        for ci in 0..ncols {
            let val = match stmt.col_ref(ci) {
                ColRef::Null => qed_lean_box(0), ColRef::Integer(i) => qed_lean_mk_ctor_1(1, qed_lean_int64_to_int(i)),
                ColRef::Real(f) => qed_lean_mk_ctor_1(2, mk_str(&f.to_string())),
                ColRef::Text(bs) => qed_lean_mk_ctor_1(2, mk_str(&String::from_utf8_lossy(bs))),
                ColRef::Blob(bs) => qed_lean_mk_ctor_1(4, mk_ba(bs)),
            };
            row.0 = lean_array_push(row.0, val);
        }
        rows.0 = lean_array_push(rows.0, row.into_raw());
    })?;
    Ok(qed_lean_mk_prod(rows.into_raw(), qed_lean_usize_to_nat(n)))
}

ffi_export! {
    qed_server_sqlite_exec(path_obj: *mut LeanObj, sql_obj: *mut LeanObj, params_arr: *mut LeanObj) => with_decoded_params(sql_obj, params_arr, |sql, p| {
        let db = open_db_pool(str_slice(path_obj))?;
        let mut g = if !db.is_memory && is_readonly_select(sql) { ConnGuard::reader(&db)? } else { ConnGuard::writer(&db) };
        exec_on_conn(g.conn_mut(), sql, p)
    });
    qed_server_sqlite_ddl(path_obj: *mut LeanObj, ddl_obj: *mut LeanObj) =>
        mk_io_except_unit(open_db_pool(str_slice(path_obj)).and_then(|db| exec_ddl(&db, str_slice(ddl_obj))));
    qed_server_sqlite_tx_begin(path_obj: *mut LeanObj) =>
        mk_io_except(open_db_pool(str_slice(path_obj)).and_then(|db| Ok(ACTIVE_TXS.insert(Arc::new(Mutex::new(ActiveSqliteTx::begin(db)?))))), |id| qed_lean_box_u64(id));
    qed_server_sqlite_tx_exec(tx_id: u64, sql_obj: *mut LeanObj, params_arr: *mut LeanObj) => with_decoded_params(sql_obj, params_arr, |sql, p| {
        let tx = ACTIVE_TXS.get(tx_id).ok_or_else(|| tx_err(tx_id))?;
        let mut g = lock_unpoison(&tx);
        exec_on_conn(g.conn.as_mut().ok_or_else(|| TX_FINISHED.to_owned())?, sql, p)
    });
    qed_server_sqlite_tx_commit(tx_id: u64) =>
        mk_io_except_unit(ACTIVE_TXS.remove(tx_id).ok_or_else(|| tx_err(tx_id)).and_then(|tx| lock_unpoison(&tx).finish(true)));
    qed_server_sqlite_tx_rollback(tx_id: u64) => { if let Some(tx) = ACTIVE_TXS.remove(tx_id) { let _ = lock_unpoison(&tx).finish(false); } mk_io_unit() };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::TempDir;
    use {OwnedVal::{Blob, Int, Null, Text}, SqlParam as P};

    #[derive(Debug, PartialEq)]
    enum OwnedVal { Null, Int(i64), Text(String), Blob(Vec<u8>) }

    fn run_sql(c: &mut SqliteConn, sql: &str, p: &[SqlParam<'_>]) -> Result<(Vec<Vec<OwnedVal>>, usize), String> {
        exec_stmt(c, sql, p, Vec::with_capacity, |rows, s, nc| rows.push((0..nc).map(|i| match unsafe { s.col_ref(i) } {
            ColRef::Null => Null, ColRef::Integer(v) => Int(v), ColRef::Real(f) => Text(f.to_string()),
            ColRef::Text(b) => Text(String::from_utf8_lossy(b).into_owned()), ColRef::Blob(b) => Blob(b.to_vec()),
        }).collect()))
    }
    fn q1(c: &mut SqliteConn, sql: &str) -> OwnedVal { run_sql(c, sql, &[]).unwrap().0.remove(0).remove(0) }
    fn mem_conn(ddl: &str) -> SqliteConn { let c = SqliteConn::open(":memory:", OPEN_WRITER, PRAGMAS_MEM).unwrap(); c.execute_batch(ddl).unwrap(); c }

    #[test]
    fn is_readonly_select_cases() {
        for (want, cases) in [
            (true, &["SELECT 1", "  \t\nselect\tid, name FROM users WHERE id = ?1", "SeLeCt\r\nCOUNT(*) FROM notes", "SELECT \"created_at\", \"updated_at\", \"deleted_at\" FROM items"][..]),
            (false, &["", "   ", "SELECT", "SELECTX FROM t", "INSERT INTO t VALUES (1)", "UPDATE t SET a = 1", "DELETE FROM t", "PRAGMA table_info(t)",
                "SELECT 1; DROP TABLE t", "SELECT 1;", "WITH x AS (INSERT INTO t VALUES (1)) SELECT * FROM t", "SELECT * FROM (WITH x AS (uPdAtE t SET a = 1) SELECT 1)",
                "SELECT * FROM (INSERT\tINTO t VALUES (1))", "SELECT * FROM t RETURNING id", "select * from t returning *", "SELECT * FROM t VACUUM",
                "SELECT * FROM t REINDEX", "SELECT * FROM t REPLACE INTO x", "SELECT * FROM t DROP TABLE x", "SELECT * FROM t ALTER TABLE x",
                "SELECT * FROM t CREATE TABLE x", "SELECT * FROM t ATTACH 'x'", "SELECT * FROM t DETACH x"][..]),
        ] { for &sql in cases { assert_eq!(is_readonly_select(sql), want, "sql={sql:?}"); } }
    }
    #[test]
    fn open_db_pool_wal_concurrent_readers_and_ddl_clear() {
        let tmp = TempDir::new("sqlite_wal");
        let path = tmp.0.join("sub").join("test.db").to_string_lossy().into_owned();
        let db = open_db_pool(&path).expect("open_db_pool");
        assert!(Arc::ptr_eq(&db, &open_db_pool(&path).expect("tls cache hit")));
        {
            let mut w = ConnGuard::writer(&db);
            assert!(matches!(q1(w.conn_mut(), "PRAGMA journal_mode;"), Text(s) if s.eq_ignore_ascii_case("wal")));
            for pr in ["PRAGMA synchronous;", "PRAGMA foreign_keys;"] { assert_eq!(q1(w.conn_mut(), pr), Int(1)); }
            w.conn_mut().execute_batch("CREATE TABLE items (id INTEGER PRIMARY KEY, val TEXT NOT NULL); INSERT INTO items VALUES (1,'a'),(2,'b'),(3,'c');").unwrap();
            assert_eq!(run_sql(w.conn_mut(), "SELECT * FROM items ORDER BY id", &[]).unwrap().0[0].len(), 2);
        }
        std::thread::scope(|s| {
            let p = path.as_str();
            s.spawn(move || { assert_eq!(run_sql(ConnGuard::writer(&open_db_pool(p).unwrap()).conn_mut(), "INSERT INTO items VALUES (4,'d')", &[]).unwrap().1, 1); });
            for _ in 0..8 { s.spawn(move || {
                let pool = open_db_pool(p).unwrap(); let mut r = ConnGuard::reader(&pool).unwrap();
                assert!(matches!(q1(r.conn_mut(), "SELECT COUNT(*) FROM items"), Int(3 | 4)) && run_sql(r.conn_mut(), "INSERT INTO items VALUES (99,'x')", &[]).is_err());
            }); }
        });
        assert!(!lock_unpoison(&db.readers).is_empty());
        exec_ddl(&db, "ALTER TABLE items ADD COLUMN extra INTEGER NOT NULL DEFAULT 7;").expect("ddl");
        assert!(lock_unpoison(&db.readers).is_empty());
        assert_eq!(run_sql(ConnGuard::writer(&db).conn_mut(), "SELECT * FROM items ORDER BY id", &[]).unwrap().0[0].len(), 3);
        assert_eq!(q1(ConnGuard::reader(&db).unwrap().conn_mut(), "SELECT SUM(extra) FROM items"), Int(28));
        assert_eq!(lock_unpoison(&db.readers).len(), 1);
    }
    #[test]
    fn stmt_cache_reuse_lru_eviction_and_reset_on_error() {
        let mut c = mem_conn("CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL);");
        let p1 = c.prepare_cached("SELECT ?1 + 1").unwrap().stmt;
        assert_eq!((p1, c.cache.len()), (c.prepare_cached("  SELECT ?1 + 1\n ").unwrap().stmt, 1));
        for i in 0..(STMT_CACHE_CAP - 1) { assert_eq!(q1(&mut c, &format!("SELECT {i}")), Int(i as i64)); }
        assert_eq!((c.cache.len(), run_sql(&mut c, "SELECT ?1 + 1", &[P::Integer(41)]).unwrap().0, q1(&mut c, "SELECT 9999"), c.cache.len()), (STMT_CACHE_CAP, vec![vec![Int(42)]], Int(9999), STMT_CACHE_CAP));
        assert!(c.cache.contains_key("SELECT ?1 + 1") && !c.cache.contains_key("SELECT 0") && c.cache.contains_key("SELECT 1"));
        let ins = "INSERT INTO t VALUES (?1, ?2)";
        assert_eq!(run_sql(&mut c, ins, &[P::Integer(1), P::Text(b"dup")]).unwrap().1, 1);
        assert!(run_sql(&mut c, ins, &[P::Integer(2), P::Text(b"dup")]).unwrap_err().starts_with("sqlite execute failed:"));
        assert_eq!((run_sql(&mut c, ins, &[P::Integer(2), P::Text(b"ok")]).unwrap().1, q1(&mut c, "SELECT COUNT(*) FROM t")), (1, Int(2)));
    }
    #[test]
    fn value_types_empty_text_blob_real_and_changes() {
        let mut c = mem_conn("CREATE TABLE vals (id INTEGER PRIMARY KEY, n INTEGER, r REAL, t TEXT, b BLOB);");
        for (sql, ps) in [
            ("INSERT INTO vals (id, n, r, t, b) VALUES (?1, ?2, 3.5, ?3, ?4)", &[P::Integer(1), P::Integer(i64::MIN), P::Text(b"hello \xF0\x9F\x94\x92"), P::Blob(&[0, 1, 255])][..]),
            ("INSERT INTO vals (id, n, r, t, b) VALUES (?1, ?2, NULL, ?3, ?4)", &[P::Integer(2), P::Null, P::Text(b""), P::Blob(&[])][..]),
        ] { assert_eq!(run_sql(&mut c, sql, ps).unwrap().1, 1); }
        let t = |s: &str| Text(s.into());
        assert_eq!(run_sql(&mut c, "SELECT id, n, r, t, b, typeof(t), typeof(b) FROM vals ORDER BY id", &[]).unwrap(), (vec![
            vec![Int(1), Int(i64::MIN), t("3.5"), t("hello \u{1f512}"), Blob(vec![0, 1, 255]), t("text"), t("blob")],
            vec![Int(2), Null, Null, t(""), Blob(Vec::new()), t("text"), t("blob")],
        ], 2));
        assert_eq!(run_sql(&mut c, "INSERT INTO vals (id, n, t, b) VALUES (?1, ?2, ?3, ?4) RETURNING id, t", &[P::Integer(3), P::Integer(7), P::Text(b"ret"), P::Blob(&[])]).unwrap(), (vec![vec![Int(3), t("ret")]], 1));
        for (sql, want) in [("UPDATE vals SET n = 9 WHERE id = 999", 0), ("DELETE FROM vals WHERE id >= 2", 2)] { assert_eq!(run_sql(&mut c, sql, &[]).unwrap().1, want); }
    }
    #[test]
    fn memory_uris_transactions_and_error_paths() {
        for p in ["", ":memory:", "file::memory:", "file:qed_mem_uri?mode=memory&cache=shared", "custom_mem?mode=memory"] {
            let pool = open_db_pool(p).expect(p);
            assert!(pool.is_memory && q1(ConnGuard::writer(&pool).conn_mut(), "SELECT 1") == Int(1), "uri={p:?}");
        }
        let tmp = TempDir::new("sqlite_tx");
        let db = open_db_pool(&tmp.0.join("tx.db").to_string_lossy()).unwrap();
        exec_ddl(&db, "CREATE TABLE ledger (v INTEGER NOT NULL);").unwrap();
        for (v, act) in [(10i64, Some(true)), (99, Some(false)), (777, None)] {
            {
                let mut tx = ActiveSqliteTx::begin(db.clone()).unwrap();
                assert_eq!(run_sql(tx.conn.as_mut().unwrap(), "INSERT INTO ledger VALUES (?1)", &[P::Integer(v)]).unwrap().1, 1);
                if let Some(commit) = act { tx.finish(commit).unwrap(); if commit { assert_eq!(tx.finish(true).unwrap_err(), TX_FINISHED); } }
            }
            assert_eq!(q1(ConnGuard::writer(&db).conn_mut(), "SELECT SUM(v) FROM ledger"), Int(10));
        }
        let mut w = ConnGuard::writer(&db);
        for (sql, ps, pfx) in [
            ("SELEC BAD SYNTAX", &[][..], "sqlite prepare failed:"), ("   -- only a comment", &[][..], "sqlite prepare failed:"),
            ("SELECT ?1", &[][..], "sqlite query failed:"), ("INSERT INTO ledger VALUES (?1)", &[P::Integer(1), P::Integer(2)][..], "sqlite execute failed:"),
        ] { assert!(run_sql(w.conn_mut(), sql, ps).unwrap_err().starts_with(pfx), "sql={sql:?}"); }
        assert!(w.conn_mut().execute_batch("SELECT 1\0").is_err()); drop(w);
        assert!(exec_ddl(&db, "NOT VALID DDL;").unwrap_err().starts_with("sqlite ddl failed:"));
        assert!(SqliteConn::open("bad\0path", OPEN_WRITER, PRAGMAS_MEM).is_err() && SqliteConn::open(&tmp.0.join("missing.db").to_string_lossy(), OPEN_READER, PRAGMAS_RO).is_err());
    }
}
