use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::Duration;

use rusqlite::types::{Value, ValueRef};
use rusqlite::{params_from_iter, Connection, OpenFlags};

use crate::lean_ffi::*;
use crate::{encode_hex, HandleTable, lock_unpoison};

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

impl Drop for ActiveSqliteTx {
    fn drop(&mut self) {
        if let Some(conn) = self.conn.take() {
            let _ = conn.execute_batch("ROLLBACK;");
            self.pool.return_writer(conn);
        }
    }
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

// ---- Minimal Zero-Dep Tagged JSON Codec for `SqlVal` ----

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    let bs = s.as_bytes();
    if bs.len() % 2 != 0 {
        return Err("odd hex length".to_owned());
    }
    let mut out = Vec::with_capacity(bs.len() / 2);
    let mut i = 0;
    while i < bs.len() {
        let hi = hex_nibble(bs[i]).ok_or_else(|| "invalid hex".to_owned())?;
        let lo = hex_nibble(bs[i + 1]).ok_or_else(|| "invalid hex".to_owned())?;
        out.push((hi << 4) | lo);
        i += 2;
    }
    Ok(out)
}

fn push_json_str(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                use std::fmt::Write;
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

struct JsonCursor<'a> {
    bs: &'a [u8],
    i: usize,
}

impl<'a> JsonCursor<'a> {
    fn new(s: &'a str) -> Self { Self { bs: s.as_bytes(), i: 0 } }
    fn skip_ws(&mut self) {
        while self.i < self.bs.len() && matches!(self.bs[self.i], b' ' | b'\n' | b'\r' | b'\t') {
            self.i += 1;
        }
    }
    fn peek(&mut self) -> Option<u8> { self.skip_ws(); self.bs.get(self.i).copied() }
    fn expect(&mut self, ch: u8) -> Result<(), String> {
        self.skip_ws();
        if self.bs.get(self.i) == Some(&ch) { self.i += 1; Ok(()) }
        else { Err(format!("expected `{}` at byte {}", ch as char, self.i)) }
    }
    fn parse_str(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let mut out = String::new();
        while self.i < self.bs.len() {
            let b = self.bs[self.i];
            self.i += 1;
            if b == b'"' { return Ok(out); }
            if b == b'\\' {
                if self.i >= self.bs.len() { return Err("unterminated escape".to_owned()); }
                let esc = self.bs[self.i];
                self.i += 1;
                match esc {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'b' => out.push('\x08'),
                    b'f' => out.push('\x0c'),
                    b'u' => {
                        if self.i + 4 > self.bs.len() { return Err("short \\u escape".to_owned()); }
                        let hex = std::str::from_utf8(&self.bs[self.i..self.i + 4]).map_err(|_| "bad utf8")?;
                        let code = u32::from_str_radix(hex, 16).map_err(|_| "bad \\u hex")?;
                        self.i += 4;
                        if (0xD800..=0xDBFF).contains(&code)
                            && self.i + 6 <= self.bs.len()
                            && self.bs[self.i] == b'\\'
                            && self.bs[self.i + 1] == b'u'
                        {
                            let lo_hex = std::str::from_utf8(&self.bs[self.i + 2..self.i + 6]).map_err(|_| "bad utf8")?;
                            if let Ok(lo) = u32::from_str_radix(lo_hex, 16) {
                                if (0xDC00..=0xDFFF).contains(&lo) {
                                    self.i += 6;
                                    let cp = 0x10000 + (((code - 0xD800) << 10) | (lo - 0xDC00));
                                    if let Some(c) = char::from_u32(cp) { out.push(c); continue; }
                                }
                            }
                        }
                        if let Some(c) = char::from_u32(code) { out.push(c); }
                    }
                    _ => return Err("unknown json escape".to_owned()),
                }
            } else {
                // Decode multi-byte UTF-8 sequence directly from slice.
                let start = self.i - 1;
                while self.i < self.bs.len() && self.bs[self.i] != b'"' && self.bs[self.i] != b'\\' {
                    self.i += 1;
                }
                let seg = std::str::from_utf8(&self.bs[start..self.i]).map_err(|_| "invalid utf8 in json")?;
                out.push_str(seg);
            }
        }
        Err("unterminated json string".to_owned())
    }
    fn parse_bool(&mut self) -> Result<bool, String> {
        self.skip_ws();
        if self.bs[self.i..].starts_with(b"true") { self.i += 4; Ok(true) }
        else if self.bs[self.i..].starts_with(b"false") { self.i += 5; Ok(false) }
        else { Err("expected boolean".to_owned()) }
    }
    fn parse_int(&mut self) -> Result<i64, String> {
        self.skip_ws();
        let start = self.i;
        if self.bs.get(self.i) == Some(&b'-') { self.i += 1; }
        while self.i < self.bs.len() && self.bs[self.i].is_ascii_digit() { self.i += 1; }
        let s = std::str::from_utf8(&self.bs[start..self.i]).map_err(|_| "bad int")?;
        s.parse::<i64>().map_err(|e| format!("bad int `{s}`: {e}"))
    }
    fn parse_tagged_param(&mut self) -> Result<Value, String> {
        self.expect(b'{')?;
        let mut tag = String::new();
        let mut val: Option<Value> = None;
        loop {
            if self.peek() == Some(b'}') { self.i += 1; break; }
            let k = self.parse_str()?;
            self.expect(b':')?;
            if k == "t" {
                tag = self.parse_str()?;
            } else if k == "v" {
                match tag.as_str() {
                    "i" => {
                        let iv = if self.peek() == Some(b'"') {
                            let s = self.parse_str()?;
                            s.parse::<i64>().map_err(|e| format!("bad int `{s}`: {e}"))?
                        } else {
                            self.parse_int()?
                        };
                        val = Some(Value::Integer(iv));
                    }
                    "s" => { val = Some(Value::Text(self.parse_str()?)); }
                    "b" => { val = Some(Value::Integer(if self.parse_bool()? { 1 } else { 0 })); }
                    "x" => { val = Some(Value::Blob(decode_hex(&self.parse_str()?)?)); }
                    _ => return Err(format!("unexpected tagged param field before tag `{tag}`")),
                }
            } else {
                return Err(format!("unknown tagged param key `{k}`"));
            }
            if self.peek() == Some(b',') { self.i += 1; } else { self.expect(b'}')?; break; }
        }
        match tag.as_str() {
            "n" => Ok(Value::Null),
            "i" | "s" | "b" | "x" => val.ok_or_else(|| format!("missing value for tag `{tag}`")),
            _ => Err(format!("unknown SqlVal tag `{tag}`")),
        }
    }
    fn parse_params_array(&mut self) -> Result<Vec<Value>, String> {
        self.expect(b'[')?;
        let mut out = Vec::new();
        if self.peek() == Some(b']') { self.i += 1; return Ok(out); }
        loop {
            out.push(self.parse_tagged_param()?);
            if self.peek() == Some(b',') { self.i += 1; } else { self.expect(b']')?; break; }
        }
        Ok(out)
    }
}

fn push_sqlite_val_json(out: &mut String, v: ValueRef<'_>) {
    match v {
        ValueRef::Null => out.push_str("{\"t\":\"n\"}"),
        ValueRef::Integer(i) => {
            out.push_str("{\"t\":\"i\",\"v\":\"");
            out.push_str(&i.to_string());
            out.push_str("\"}");
        }
        ValueRef::Real(f) => {
            out.push_str("{\"t\":\"s\",\"v\":");
            push_json_str(out, &f.to_string());
            out.push('}');
        }
        ValueRef::Text(bs) => {
            let s = String::from_utf8_lossy(bs);
            out.push_str("{\"t\":\"s\",\"v\":");
            push_json_str(out, &s);
            out.push('}');
        }
        ValueRef::Blob(bs) => {
            out.push_str("{\"t\":\"x\",\"v\":\"");
            out.push_str(&encode_hex(bs));
            out.push_str("\"}");
        }
    }
}

fn exec_on_conn(conn: &Connection, sql: &str, params: &[Value]) -> Result<String, String> {
    let mut stmt = conn.prepare_cached(sql).map_err(|e| format!("sqlite prepare failed: {e}"))?;
    let col_count = stmt.column_count();
    if col_count > 0 {
        let mut rows = stmt.query(params_from_iter(params.iter()))
            .map_err(|e| format!("sqlite query failed: {e}"))?;
        let mut out = String::from("{\"rows\":[");
        let mut row_count: usize = 0;
        while let Some(row) = rows.next().map_err(|e| format!("sqlite step failed: {e}"))? {
            if row_count > 0 { out.push(','); }
            out.push('[');
            for ci in 0..col_count {
                if ci > 0 { out.push(','); }
                let v = row.get_ref(ci).map_err(|e| format!("sqlite col {ci} failed: {e}"))?;
                push_sqlite_val_json(&mut out, v);
            }
            out.push(']');
            row_count += 1;
        }
        out.push_str("],\"affected\":");
        out.push_str(&row_count.to_string());
        out.push('}');
        Ok(out)
    } else {
        let affected = stmt.execute(params_from_iter(params.iter()))
            .map_err(|e| format!("sqlite execute failed: {e}"))?;
        Ok(format!("{{\"rows\":[],\"affected\":{affected}}}"))
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_exec(
    path_obj: *mut LeanObj,
    sql_obj: *mut LeanObj,
    params_json_obj: *mut LeanObj,
) -> *mut LeanObj {
    let path = str_slice(path_obj);
    let sql = str_slice(sql_obj);
    let params_json = str_slice(params_json_obj);

    let res: Result<String, String> = (|| {
        let mut cur = JsonCursor::new(params_json);
        let params = cur.parse_params_array()?;
        let db = open_db_pool(path)?;
        let mut guard = if !db.is_memory && is_readonly_select(sql) {
            ConnGuard::reader(&db)?
        } else {
            ConnGuard::writer(&db)
        };
        exec_on_conn(guard.conn_mut(), sql, &params)
    })();
    mk_io_except(res, |json| mk_str(&json))
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
    params_json_obj: *mut LeanObj,
) -> *mut LeanObj {
    let sql = str_slice(sql_obj);
    let params_json = str_slice(params_json_obj);
    let res: Result<String, String> = (|| {
        let mut cur = JsonCursor::new(params_json);
        let params = cur.parse_params_array()?;
        let tx_arc = ACTIVE_TXS.get(tx_id)
            .ok_or_else(|| format!("invalid sqlite transaction handle {tx_id}"))?;
        let tx = lock_unpoison(&tx_arc);
        let conn = tx.conn.as_ref().ok_or_else(|| "sqlite transaction already finished".to_owned())?;
        exec_on_conn(conn, sql, &params)
    })();
    mk_io_except(res, |json| mk_str(&json))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_commit(tx_id: u64) -> *mut LeanObj {
    let res: Result<(), String> = (|| {
        let tx_arc = ACTIVE_TXS.remove(tx_id)
            .ok_or_else(|| format!("invalid sqlite transaction handle {tx_id}"))?;
        let mut tx = lock_unpoison(&tx_arc);
        let Some(conn) = tx.conn.take() else {
            return Err("sqlite transaction already finished".to_owned());
        };
        let r = conn.execute_batch("COMMIT;").map_err(|e| format!("sqlite COMMIT failed: {e}"));
        if r.is_err() {
            let _ = conn.execute_batch("ROLLBACK;");
        }
        tx.pool.return_writer(conn);
        r
    })();
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_sqlite_tx_rollback(tx_id: u64) -> *mut LeanObj {
    if let Some(tx_arc) = ACTIVE_TXS.remove(tx_id) {
        let mut tx = lock_unpoison(&tx_arc);
        if let Some(conn) = tx.conn.take() {
            let _ = conn.execute_batch("ROLLBACK;");
            tx.pool.return_writer(conn);
        }
    }
    qed_lean_io_mk_ok(qed_lean_box(0))
}
