use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::Duration;

use rusqlite::types::{Value, ValueRef};
use rusqlite::{params_from_iter, Connection, OpenFlags};

use crate::lean_ffi::*;
use crate::{HandleTable, lock_unpoison};

const MAX_READERS_PER_DB: usize = 16;

struct SqliteDbPool {
    path: String,
    is_memory: bool,
    writer: Mutex<Option<Connection>>,
    writer_cv: Condvar,
    readers: Mutex<Vec<Connection>>,
}

impl SqliteDbPool {
    fn checkout_writer(&self) -> Connection {
        let mut guard = lock_unpoison(&self.writer);
        loop {
            if let Some(conn) = guard.take() {
                return conn;
            }
            guard = self.writer_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
        }
    }

    fn return_writer(&self, conn: Connection) {
        let mut guard = lock_unpoison(&self.writer);
        *guard = Some(conn);
        self.writer_cv.notify_one();
    }

    fn checkout_reader(&self) -> Result<Connection, String> {
        {
            let mut pool = lock_unpoison(&self.readers);
            if let Some(conn) = pool.pop() {
                return Ok(conn);
            }
        }
        let flags = OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_NO_MUTEX;
        let conn = Connection::open_with_flags(&self.path, flags)
            .map_err(|e| format!("sqlite open read-only `{}` failed: {e}", self.path))?;
        let _ = conn.busy_timeout(Duration::from_secs(5));
        let _ = conn.execute_batch("PRAGMA query_only = ON;");
        Ok(conn)
    }

    fn return_reader(&self, conn: Connection) {
        let mut pool = lock_unpoison(&self.readers);
        if pool.len() < MAX_READERS_PER_DB {
            pool.push(conn);
        }
    }
}

struct ConnGuard<'a> {
    pool: &'a SqliteDbPool,
    conn: Option<Connection>,
    is_writer: bool,
}

impl<'a> ConnGuard<'a> {
    fn writer(pool: &'a SqliteDbPool) -> Self {
        Self { pool, conn: Some(pool.checkout_writer()), is_writer: true }
    }
    fn reader(pool: &'a SqliteDbPool) -> Result<Self, String> {
        Ok(Self { pool, conn: Some(pool.checkout_reader()?), is_writer: false })
    }
    fn conn_mut(&mut self) -> &mut Connection {
        self.conn.as_mut().expect("connection checked out")
    }
}

impl Drop for ConnGuard<'_> {
    fn drop(&mut self) {
        if let Some(conn) = self.conn.take() {
            if self.is_writer { self.pool.return_writer(conn); }
            else { self.pool.return_reader(conn); }
        }
    }
}

struct ActiveSqliteTx {
    pool: Arc<SqliteDbPool>,
    conn: Option<Connection>,
}

impl ActiveSqliteTx {
    fn finish(&mut self, commit: bool) -> Result<(), String> {
        let Some(conn) = self.conn.take() else {
            return Err("sqlite transaction already finished".to_owned());
        };
        let res = if commit {
            conn.execute_batch("COMMIT;").map_err(|e| format!("sqlite COMMIT failed: {e}"))
        } else {
            Ok(())
        };
        if !commit || res.is_err() {
            let _ = conn.execute_batch("ROLLBACK;");
        }
        self.pool.return_writer(conn);
        res
    }
}

impl Drop for ActiveSqliteTx {
    fn drop(&mut self) { let _ = self.finish(false); }
}

static SQLITE_POOL: OnceLock<Mutex<HashMap<String, Arc<SqliteDbPool>>>> = OnceLock::new();
static ACTIVE_TXS: HandleTable<Arc<Mutex<ActiveSqliteTx>>> = HandleTable::new();

fn is_memory_path(path: &str) -> bool {
    path == ":memory:" || path.is_empty() || path.contains("mode=memory") || path.starts_with("file::memory:")
}

fn open_db_pool(path: &str) -> Result<Arc<SqliteDbPool>, String> {
    let pool = SQLITE_POOL.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let map = lock_unpoison(pool);
        if let Some(db) = map.get(path) {
            return Ok(db.clone());
        }
    }
    let is_mem = is_memory_path(path);
    if !is_mem {
        if let Some(parent) = Path::new(path).parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| format!("failed to create sqlite directory `{}`: {e}", parent.display()))?;
            }
        }
    }
    let conn = if is_mem {
        Connection::open_in_memory()
    } else {
        Connection::open(path)
    }
    .map_err(|e| format!("sqlite open `{path}` failed: {e}"))?;
    let _ = conn.busy_timeout(Duration::from_secs(5));
    let _ = conn.execute_batch("PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
    let arc = Arc::new(SqliteDbPool {
        path: path.to_owned(),
        is_memory: is_mem,
        writer: Mutex::new(Some(conn)),
        writer_cv: Condvar::new(),
        readers: Mutex::new(Vec::new()),
    });
    let mut map = lock_unpoison(pool);
    Ok(map.entry(path.to_owned()).or_insert_with(|| arc.clone()).clone())
}

/// Returns true iff `sql` is a pure single-statement `SELECT` query safe to execute on the
/// concurrent read-only WAL reader pool (no write ops, no `RETURNING`, no stacked statements).
fn is_readonly_select(sql: &str) -> bool {
    let trimmed = sql.trim_start();
    if trimmed.contains(';') {
        return false;
    }
    let upper = trimmed.to_ascii_uppercase();
    let starts_select = upper.starts_with("SELECT ") || upper.starts_with("SELECT\t") || upper.starts_with("SELECT\n");
    if !starts_select {
        return false;
    }
    // Reject any mutating clauses (e.g. CTE writes or RETURNING)
    const WRITE_TOKENS: &[&str] = &[
        "INSERT ", "UPDATE ", "DELETE ", "REPLACE ", "DROP ", "ALTER ",
        "CREATE ", "ATTACH ", "DETACH ", "VACUUM", "REINDEX", "RETURNING",
    ];
    !WRITE_TOKENS.iter().any(|kw| upper.contains(kw))
}

// ---- Direct Lean-Object `SqlVal` / `DbResult` FFI Conversion ----
// Matches `Qed.Server.Db.SqlVal` (tags 0=null, 1=int, 2=text, 3=bool[u8@0], 4=bytes)
// and `Qed.Server.Db.DbResult` (tag 0, 2 objs: rows, affected).

unsafe fn params_from_lean(params_arr: *mut LeanObj) -> Result<Vec<Value>, String> {
    let n = qed_lean_array_size(params_arr);
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let elem = LeanRef(qed_lean_array_uget(params_arr, i));
        let val = match qed_lean_obj_tag(elem.0) {
            0 => Value::Null,
            1 => {
                let mut v: i64 = 0;
                if qed_lean_int_to_i64_checked(qed_lean_ctor_get(elem.0, 0), &mut v) == 0 {
                    return Err("SQLite integer parameter out of i64 range".to_owned());
                }
                Value::Integer(v)
            }
            2 => Value::Text(str_slice(qed_lean_ctor_get(elem.0, 0)).to_owned()),
            3 => Value::Integer(if qed_lean_ctor_get_u8(elem.0, 0) != 0 { 1 } else { 0 }),
            4 => Value::Blob(ba_slice(qed_lean_ctor_get(elem.0, 0)).to_vec()),
            tag => return Err(format!("unknown SqlVal constructor tag {tag}")),
        };
        out.push(val);
    }
    Ok(out)
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

unsafe fn exec_on_conn(conn: &Connection, sql: &str, params: &[Value]) -> Result<*mut LeanObj, String> {
    let mut stmt = conn.prepare_cached(sql).map_err(|e| format!("sqlite prepare failed: {e}"))?;
    let col_count = stmt.column_count();
    if col_count > 0 {
        let mut rows = stmt.query(params_from_iter(params.iter()))
            .map_err(|e| format!("sqlite query failed: {e}"))?;
        let mut rows_arr = LeanRef(qed_lean_array_empty());
        let mut row_count: usize = 0;
        while let Some(row) = rows.next().map_err(|e| format!("sqlite step failed: {e}"))? {
            let mut row_arr = LeanRef(qed_lean_array_empty());
            for ci in 0..col_count {
                let v = row.get_ref(ci).map_err(|e| format!("sqlite col {ci} failed: {e}"))?;
                row_arr.0 = qed_lean_array_push(row_arr.0, sqlite_val_to_lean(v));
            }
            rows_arr.0 = qed_lean_array_push(rows_arr.0, row_arr.into_raw());
            row_count += 1;
        }
        Ok(qed_lean_mk_prod(rows_arr.into_raw(), qed_lean_usize_to_nat(row_count)))
    } else {
        let affected = stmt.execute(params_from_iter(params.iter()))
            .map_err(|e| format!("sqlite execute failed: {e}"))?;
        Ok(qed_lean_mk_prod(qed_lean_array_empty(), qed_lean_usize_to_nat(affected)))
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_exec(
    path_obj: *mut LeanObj,
    sql_obj: *mut LeanObj,
    params_arr: *mut LeanObj,
) -> *mut LeanObj {
    let path = str_slice(path_obj);
    let sql = str_slice(sql_obj);

    let res: Result<*mut LeanObj, String> = (|| {
        let params = params_from_lean(params_arr)?;
        let db = open_db_pool(path)?;
        let mut guard = if !db.is_memory && is_readonly_select(sql) {
            ConnGuard::reader(&db)?
        } else {
            ConnGuard::writer(&db)
        };
        exec_on_conn(guard.conn_mut(), sql, &params)
    })();
    mk_io_except(res, |obj| obj)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_ddl(
    path_obj: *mut LeanObj,
    ddl_obj: *mut LeanObj,
) -> *mut LeanObj {
    let path = str_slice(path_obj);
    let ddl = str_slice(ddl_obj);
    let res: Result<(), String> = (|| {
        let db = open_db_pool(path)?;
        let mut writer = ConnGuard::writer(&db);
        let r = writer.conn_mut().execute_batch(ddl).map_err(|e| format!("sqlite ddl failed: {e}"));
        // Drop cached read-only connections so schema changes are immediately visible cleanly.
        lock_unpoison(&db.readers).clear();
        r
    })();
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_begin(path_obj: *mut LeanObj) -> *mut LeanObj {
    let path = str_slice(path_obj);
    let res: Result<u64, String> = (|| {
        let db = open_db_pool(path)?;
        let conn = db.checkout_writer();
        if let Err(e) = conn.execute_batch("BEGIN IMMEDIATE;") {
            db.return_writer(conn);
            return Err(format!("sqlite BEGIN failed: {e}"));
        }
        Ok(ACTIVE_TXS.insert(Arc::new(Mutex::new(ActiveSqliteTx { pool: db, conn: Some(conn) }))))
    })();
    mk_io_except(res, |tx_id| qed_lean_box_u64(tx_id))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_exec(
    tx_id: u64,
    sql_obj: *mut LeanObj,
    params_arr: *mut LeanObj,
) -> *mut LeanObj {
    let sql = str_slice(sql_obj);
    let res: Result<*mut LeanObj, String> = (|| {
        let params = params_from_lean(params_arr)?;
        let tx_arc = ACTIVE_TXS.get(tx_id)
            .ok_or_else(|| format!("invalid sqlite transaction handle {tx_id}"))?;
        let tx = lock_unpoison(&tx_arc);
        let conn = tx.conn.as_ref().ok_or_else(|| "sqlite transaction already finished".to_owned())?;
        exec_on_conn(conn, sql, &params)
    })();
    mk_io_except(res, |obj| obj)
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
    if let Some(tx) = ACTIVE_TXS.remove(tx_id) {
        let _ = lock_unpoison(&tx).finish(false);
    }
    mk_io_unit()
}
