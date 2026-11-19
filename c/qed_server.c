#define _GNU_SOURCE
#include <lean/lean.h>

#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <time.h>
#include <unistd.h>

#ifdef __linux__
#include <sys/epoll.h>
#include <sys/eventfd.h>
#elif defined(__APPLE__)
#include <sys/event.h>
#endif

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>

/* Lean runtime multi-threading hooks exported by libleanrt / libleanshared */
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void lean_runtime_mark_multi_threaded(void);

#ifndef MSG_NOSIGNAL
#define MSG_NOSIGNAL 0
#endif

/* =========================================================================
 * 1. Lean Helper Constructors (`Option`, `Except`, `Prod`, `ByteArray`)
 * ========================================================================= */

static inline lean_object *mk_option_none(void) {
    return lean_box(0);
}

static inline lean_object *mk_option_some(lean_object *val) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, val);
    return o;
}

static inline lean_object *mk_except_err_str(const char *msg) {
    lean_object *e = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(e, 0, lean_mk_string(msg ? msg : "error"));
    return e;
}

static inline lean_object *mk_except_ok(lean_object *val) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, val);
    return o;
}

static inline lean_object *mk_prod(lean_object *fst, lean_object *snd) {
    lean_object *p = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p, 0, fst);
    lean_ctor_set(p, 1, snd);
    return p;
}

static inline lean_object *mk_byte_array_copy(const uint8_t *data, size_t len) {
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len > 0 && data != NULL) {
        memcpy(lean_sarray_cptr(ba), data, len);
    }
    return ba;
}

static inline bool is_http_ws(char c) {
    return c == ' ' || c == '\t';
}

static inline bool parse_u64_prefix(const char *s, uint64_t max_val, bool require_eof, uint64_t *out) {
    if (!s) return false;
    while (is_http_ws(*s)) s++;
    if (*s < '0' || *s > '9') return false;
    uint64_t acc = 0;
    while (*s >= '0' && *s <= '9') {
        uint64_t d = (uint64_t)(*s - '0');
        if (acc > (max_val - d) / 10ULL) return false;
        acc = acc * 10ULL + d;
        s++;
    }
    if (require_eof) {
        while (is_http_ws(*s)) s++;
        if (*s != '\0') return false;
    } else if (*s != '\0' && !is_http_ws(*s)) {
        return false;
    }
    if (out) *out = acc;
    return true;
}

static inline bool parse_strict_u64(const char *s, uint64_t *out) {
    return parse_u64_prefix(s, UINT64_MAX, true, out);
}

static inline bool parse_port_u16(const char *s, uint16_t *out) {
    uint64_t v = 0;
    if (!parse_u64_prefix(s, 65535ULL, true, &v) || v == 0) return false;
    *out = (uint16_t)v;
    return true;
}

static inline bool parse_status_code(const char *s, int *out) {
    uint64_t v = 0;
    if (!parse_u64_prefix(s, 999ULL, false, &v) || v < 100) return false;
    *out = (int)v;
    return true;
}

static inline bool parse_hex_size(const char *s, size_t *out) {
    if (!s) return false;
    while (is_http_ws(*s)) s++;
    size_t acc = 0;
    bool any = false;
    for (;;) {
        char c = *s;
        size_t d = 0;
        if (c >= '0' && c <= '9') d = (size_t)(c - '0');
        else if (c >= 'a' && c <= 'f') d = (size_t)(c - 'a' + 10);
        else if (c >= 'A' && c <= 'F') d = (size_t)(c - 'A' + 10);
        else break;
        if (acc > (SIZE_MAX - d) >> 4) return false;
        acc = (acc << 4) | d;
        any = true;
        s++;
    }
    if (!any) return false;
    while (is_http_ws(*s)) s++;
    if (*s != '\0') return false;
    if (out) *out = acc;
    return true;
}

static void ignore_sigpipe_once_fn(void) {
    signal(SIGPIPE, SIG_IGN);
}

static pthread_once_t g_sigpipe_once = PTHREAD_ONCE_INIT;

static inline void ensure_sigpipe_ignored(void) {
    pthread_once(&g_sigpipe_once, ignore_sigpipe_once_fn);
}

/* =========================================================================
 * 2. RWLock Shared State Box (`StateBox`)
 * ========================================================================= */

typedef struct {
    pthread_rwlock_t lock;
    lean_object *state;
} qed_state_box_t;

static lean_external_class *g_state_box_class = NULL;
static pthread_once_t g_state_box_once = PTHREAD_ONCE_INIT;

static void qed_state_box_finalize(void *ptr) {
    qed_state_box_t *b = (qed_state_box_t *)ptr;
    if (b != NULL) {
        if (b->state != NULL) {
            lean_dec(b->state);
            b->state = NULL;
        }
        pthread_rwlock_destroy(&b->lock);
        free(b);
    }
}

static void qed_state_box_foreach(void *ptr, b_lean_obj_arg fn) {
    qed_state_box_t *b = (qed_state_box_t *)ptr;
    if (b != NULL && b->state != NULL) {
        lean_inc(fn);
        lean_inc(b->state);
        lean_object *r = lean_apply_1(fn, b->state);
        lean_dec(r);
    }
}

static void init_state_box_class(void) {
    g_state_box_class = lean_register_external_class(qed_state_box_finalize, qed_state_box_foreach);
}

LEAN_EXPORT lean_object *qed_server_state_new(lean_object *init) {
    pthread_once(&g_state_box_once, init_state_box_class);
    qed_state_box_t *b = (qed_state_box_t *)calloc(1, sizeof(qed_state_box_t));
    if (!b) {
        lean_dec(init);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("out of memory allocating StateBox")));
    }
    pthread_rwlock_init(&b->lock, NULL);
    lean_mark_mt(init);
    b->state = init;
    lean_object *ext = lean_alloc_external(g_state_box_class, b);
    return lean_io_result_mk_ok(ext);
}

LEAN_EXPORT lean_object *qed_server_state_read(b_lean_obj_arg box, lean_obj_arg f) {
    qed_state_box_t *b = (qed_state_box_t *)lean_get_external_data(box);
    pthread_rwlock_rdlock(&b->lock);
    lean_object *snap = b->state;
    lean_inc(snap);
    lean_object *res = lean_apply_1(f, snap);
    pthread_rwlock_unlock(&b->lock);
    return lean_io_result_mk_ok(res);
}

LEAN_EXPORT lean_object *qed_server_state_modify(b_lean_obj_arg box, lean_obj_arg f) {
    qed_state_box_t *b = (qed_state_box_t *)lean_get_external_data(box);
    pthread_rwlock_wrlock(&b->lock);
    lean_object *cur = b->state;
    b->state = NULL;
    lean_object *pair = lean_apply_1(f, cur);
    lean_object *new_st = lean_ctor_get(pair, 0);
    lean_object *ret_val = lean_ctor_get(pair, 1);
    lean_inc(new_st);
    lean_inc(ret_val);
    lean_dec_ref(pair);
    lean_mark_mt(new_st);
    b->state = new_st;
    pthread_rwlock_unlock(&b->lock);
    return lean_io_result_mk_ok(ret_val);
}

/* =========================================================================
 * 3. Environment, Clock, CSPRNG & HMAC-SHA256
 * ========================================================================= */

LEAN_EXPORT lean_object *qed_server_get_env(b_lean_obj_arg name) {
    const char *c_name = lean_string_cstr(name);
    const char *val = getenv(c_name);
    if (val == NULL) {
        return lean_io_result_mk_ok(mk_option_none());
    }
    return lean_io_result_mk_ok(mk_option_some(lean_mk_string(val)));
}

LEAN_EXPORT lean_object *qed_server_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t ms = (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)(ts.tv_nsec >= 0 ? ts.tv_nsec / 1000000L : 0L);
    return lean_io_result_mk_ok(lean_box_uint64(ms));
}

LEAN_EXPORT lean_object *qed_server_random_hex(uint32_t num_bytes) {
    if (num_bytes == 0) {
        return lean_io_result_mk_ok(lean_mk_string(""));
    }
    if (num_bytes > 65536) {
        num_bytes = 65536;
    }
    uint8_t *raw = (uint8_t *)malloc(num_bytes);
    char *hex = (char *)malloc((size_t)num_bytes * 2 + 1);
    if (!raw || !hex) {
        free(raw);
        free(hex);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("out of memory in randomHex")));
    }
    if (RAND_bytes(raw, (int)num_bytes) != 1) {
        free(raw);
        free(hex);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("OpenSSL RAND_bytes failed")));
    }
    static const char kHex[] = "0123456789abcdef";
    for (uint32_t i = 0; i < num_bytes; i++) {
        hex[2 * i]     = kHex[(raw[i] >> 4) & 0x0F];
        hex[2 * i + 1] = kHex[raw[i] & 0x0F];
    }
    hex[2 * num_bytes] = '\0';
    lean_object *s = lean_mk_string_from_bytes(hex, (size_t)num_bytes * 2);
    free(raw);
    free(hex);
    return lean_io_result_mk_ok(s);
}

LEAN_EXPORT lean_object *qed_server_hmac_sha256(b_lean_obj_arg key, b_lean_obj_arg msg) {
    const uint8_t *k_ptr = lean_sarray_cptr((lean_object *)key);
    size_t k_len = lean_sarray_size(key);
    const uint8_t *m_ptr = lean_sarray_cptr((lean_object *)msg);
    size_t m_len = lean_sarray_size(msg);
    if (k_len > (size_t)INT_MAX) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("HMAC key too large")));
    }
    uint8_t digest[32];
    unsigned int digest_len = 0;
    if (HMAC(EVP_sha256(), k_ptr, (int)k_len, m_ptr, m_len, digest, &digest_len) == NULL || digest_len != 32) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("OpenSSL HMAC-SHA256 failed")));
    }
    return lean_io_result_mk_ok(mk_byte_array_copy(digest, digest_len));
}

/* =========================================================================
 * 4. Growable Byte Buffer
 * ========================================================================= */

typedef struct {
    uint8_t *data;
    size_t len;
    size_t cap;
} qed_buf_t;

static bool buf_init(qed_buf_t *b, size_t initial_cap) {
    size_t cap = initial_cap > 0 ? initial_cap : 1024;
    b->len = 0;
    b->data = (uint8_t *)malloc(cap);
    if (!b->data) {
        b->cap = 0;
        return false;
    }
    b->cap = cap;
    return true;
}

static bool buf_reserve(qed_buf_t *b, size_t extra) {
    if (extra > SIZE_MAX - b->len) return false;
    size_t needed = b->len + extra;
    if (b->data != NULL && needed <= b->cap) return true;
    size_t next = (b->cap > 0) ? b->cap : 1024;
    while (next < needed) {
        if (next > SIZE_MAX / 2) {
            next = needed;
            break;
        }
        next *= 2;
    }
    uint8_t *p = (uint8_t *)realloc(b->data, next);
    if (!p) return false;
    b->data = p;
    b->cap = next;
    return true;
}

static bool buf_append(qed_buf_t *b, const void *src, size_t n) {
    if (n == 0) return true;
    if (!buf_reserve(b, n)) return false;
    memcpy(b->data + b->len, src, n);
    b->len += n;
    return true;
}

static bool buf_append_cstr(qed_buf_t *b, const char *s) {
    return buf_append(b, s, strlen(s));
}

static bool buf_append_fmt(qed_buf_t *b, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    if (n < 0 || !buf_reserve(b, (size_t)n + 1)) return false;
    va_start(ap, fmt);
    vsnprintf((char *)(b->data + b->len), (size_t)n + 1, fmt, ap);
    va_end(ap);
    b->len += (size_t)n;
    return true;
}

static void buf_consume(qed_buf_t *b, size_t n) {
    if (n >= b->len) {
        b->len = 0;
        return;
    }
    if (n > 0) {
        memmove(b->data, b->data + n, b->len - n);
        b->len -= n;
    }
}

static void buf_free(qed_buf_t *b) {
    free(b->data);
    b->data = NULL;
    b->len = 0;
    b->cap = 0;
}

/* =========================================================================
 * 5. Outbound HTTP/1.1 + OpenSSL Keep-Alive Client Pool & SSRF Guard
 * ========================================================================= */

static SSL_CTX *g_ssl_ctx = NULL;
static pthread_once_t g_ssl_once = PTHREAD_ONCE_INIT;

static void init_ssl_global(void) {
    SSL_library_init();
    SSL_load_error_strings();
    OpenSSL_add_all_algorithms();
    g_ssl_ctx = SSL_CTX_new(TLS_client_method());
    if (g_ssl_ctx != NULL) {
        SSL_CTX_set_min_proto_version(g_ssl_ctx, TLS1_2_VERSION);
        SSL_CTX_set_default_verify_paths(g_ssl_ctx);
        const char *skip = getenv("QED_INSECURE_SKIP_TLS_VERIFY");
        if (skip != NULL && strcmp(skip, "1") == 0) {
            SSL_CTX_set_verify(g_ssl_ctx, SSL_VERIFY_NONE, NULL);
        } else {
            SSL_CTX_set_verify(g_ssl_ctx, SSL_VERIFY_PEER, NULL);
        }
    }
}

static bool is_blocked_ipv4_host_order(uint32_t ip) {
    if ((ip & 0xFF000000U) == 0x00000000U) return true; /* 0.0.0.0/8 */
    if ((ip & 0xFF000000U) == 0x0A000000U) return true; /* 10.0.0.0/8 */
    if ((ip & 0xFFC00000U) == 0x64400000U) return true; /* 100.64.0.0/10 */
    if ((ip & 0xFF000000U) == 0x7F000000U) return true; /* 127.0.0.0/8 */
    if ((ip & 0xFFFF0000U) == 0xA9FE0000U) return true; /* 169.254.0.0/16 (cloud metadata) */
    if ((ip & 0xFFF00000U) == 0xAC100000U) return true; /* 172.16.0.0/12 */
    if ((ip & 0xFFFF0000U) == 0xC0A80000U) return true; /* 192.168.0.0/16 */
    if ((ip & 0xE0000000U) == 0xE0000000U) return true; /* multicast & reserved */
    return false;
}

static inline uint32_t ipv4_be32(const uint8_t *b) {
    return ((uint32_t)b[0] << 24) | ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] << 8)  | (uint32_t)b[3];
}

static inline bool is_zero_bytes(const uint8_t *b, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (b[i] != 0) return false;
    }
    return true;
}

static bool is_blocked_sockaddr(const struct sockaddr *sa) {
    if (sa->sa_family == AF_INET) {
        const struct sockaddr_in *sin = (const struct sockaddr_in *)sa;
        return is_blocked_ipv4_host_order(ntohl(sin->sin_addr.s_addr));
    }
    if (sa->sa_family == AF_INET6) {
        const uint8_t *b = ((const struct sockaddr_in6 *)sa)->sin6_addr.s6_addr;
        static const uint8_t kNat64Prefix[12] = { 0x00, 0x64, 0xFF, 0x9B, 0, 0, 0, 0, 0, 0, 0, 0 };
        if (is_zero_bytes(b, 12)) {
            uint32_t ip = ipv4_be32(b + 12);
            return ip <= 1 || is_blocked_ipv4_host_order(ip);
        }
        if ((b[0] & 0xFE) == 0xFC) return true;
        if (b[0] == 0xFE && (b[1] & 0xC0) == 0x80) return true;
        if (b[0] == 0xFF) return true;
        if (is_zero_bytes(b, 10) && b[10] == 0xFF && b[11] == 0xFF) {
            return is_blocked_ipv4_host_order(ipv4_be32(b + 12));
        }
        if (memcmp(b, kNat64Prefix, sizeof(kNat64Prefix)) == 0) {
            return is_blocked_ipv4_host_order(ipv4_be32(b + 12));
        }
        return false;
    }
    return true;
}

typedef struct {
    bool in_use;
    bool is_tls;
    uint16_t port;
    char host[256];
    int fd;
    SSL *ssl;
    time_t last_used;
} qed_pool_conn_t;

#define QED_POOL_SIZE 8
static __thread qed_pool_conn_t tls_pool[QED_POOL_SIZE];

static void close_pool_entry(qed_pool_conn_t *e) {
    if (e->ssl != NULL) {
        SSL_shutdown(e->ssl);
        SSL_free(e->ssl);
        e->ssl = NULL;
    }
    if (e->fd >= 0 && e->in_use) {
        close(e->fd);
    }
    e->fd = -1;
    e->in_use = false;
}

static bool socket_is_alive(int fd) {
    char c;
    ssize_t r = recv(fd, &c, 1, MSG_PEEK | MSG_DONTWAIT);
    /* An idle pooled socket must have no unread data (0 = EOF, >0 = unsolicited data or TLS close_notify) */
    if (r >= 0) return false;
    if (errno != EAGAIN && errno != EWOULDBLOCK) return false;
    return true;
}

static bool has_ctl_or_crlf(const char *s, bool allow_htab) {
    if (!s) return true;
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        if (*p == '\r' || *p == '\n' || *p == 127) return true;
        if (*p < 32 && !(allow_htab && *p == '\t')) return true;
    }
    return false;
}

static bool is_valid_http_token(const char *s) {
    if (!s || *s == '\0') return false;
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        unsigned char c = *p;
        if (c <= 32 || c >= 127) return false;
        if (strchr("()<>@,;:\\\"/[]?={}", (char)c) != NULL) return false;
    }
    return true;
}

static bool parse_http_url(
    const char *url,
    bool *is_tls,
    char *host, size_t host_cap,
    bool *is_ipv6_host,
    uint16_t *port,
    char *path, size_t path_cap)
{
    if (!url || has_ctl_or_crlf(url, false)) return false;
    for (const unsigned char *u = (const unsigned char *)url; *u; u++) {
        if (*u == ' ') return false;
    }
    if (is_ipv6_host) *is_ipv6_host = false;

    const char *p = NULL;
    if (strncmp(url, "https://", 8) == 0) {
        *is_tls = true;
        *port = 443;
        p = url + 8;
    } else if (strncmp(url, "http://", 7) == 0) {
        *is_tls = false;
        *port = 80;
        p = url + 7;
    } else {
        return false;
    }
    const char *slash = strchr(p, '/');
    const char *qmark = strchr(p, '?');
    const char *frag = strchr(p, '#');
    const char *authority_end = slash;
    if (qmark != NULL && (authority_end == NULL || qmark < authority_end)) {
        authority_end = qmark;
    }
    if (frag != NULL && (authority_end == NULL || frag < authority_end)) {
        return false;
    }
    size_t auth_len = authority_end ? (size_t)(authority_end - p) : strlen(p);
    if (auth_len == 0 || auth_len >= host_cap) return false;

    char auth[300];
    if (auth_len >= sizeof(auth)) return false;
    memcpy(auth, p, auth_len);
    auth[auth_len] = '\0';
    if (strchr(auth, '@') != NULL) return false;

    if (auth[0] == '[') {
        char *rb = strchr(auth, ']');
        if (!rb) return false;
        size_t hlen = (size_t)(rb - (auth + 1));
        if (hlen == 0 || hlen >= host_cap) return false;
        memcpy(host, auth + 1, hlen);
        host[hlen] = '\0';
        if (rb[1] == ':') {
            if (!parse_port_u16(rb + 2, port)) return false;
        } else if (rb[1] != '\0') {
            return false;
        }
        if (is_ipv6_host) *is_ipv6_host = true;
    } else {
        char *colon = strrchr(auth, ':');
        if (colon != NULL) {
            *colon = '\0';
            if (!parse_port_u16(colon + 1, port)) return false;
        }
        if (strlen(auth) == 0 || strlen(auth) >= host_cap) return false;
        strcpy(host, auth);
    }

    if (authority_end == NULL) {
        if (path_cap < 2) return false;
        strcpy(path, "/");
    } else if (*authority_end == '?') {
        size_t qlen = strlen(authority_end);
        if (qlen + 1 >= path_cap) return false;
        path[0] = '/';
        memcpy(path + 1, authority_end, qlen + 1);
    } else {
        if (strlen(authority_end) >= path_cap) return false;
        strcpy(path, authority_end);
    }
    return true;
}

static bool acquire_outbound_conn(
    bool is_tls, const char *host, uint16_t port, uint8_t ssrf_guard,
    int *out_fd, SSL **out_ssl, bool *was_reused,
    char *err, size_t err_cap)
{
    time_t now = time(NULL);
    *was_reused = false;
    if (!ssrf_guard) {
        for (int i = 0; i < QED_POOL_SIZE; i++) {
            qed_pool_conn_t *e = &tls_pool[i];
            if (e->in_use && e->is_tls == is_tls && e->port == port && strcmp(e->host, host) == 0) {
                if (now - e->last_used <= 30 && socket_is_alive(e->fd)) {
                    *out_fd = e->fd;
                    *out_ssl = e->ssl;
                    e->in_use = false;
                    e->fd = -1;
                    e->ssl = NULL;
                    *was_reused = true;
                    return true;
                } else {
                    close_pool_entry(e);
                }
            }
        }
    }

    char port_str[16];
    snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_family = AF_UNSPEC;

    struct addrinfo *res = NULL;
    int gai = getaddrinfo(host, port_str, &hints, &res);
    if (gai != 0 || res == NULL) {
        snprintf(err, err_cap, "DNS resolution failed for %s: %s", host, gai_strerror(gai));
        return false;
    }

    if (ssrf_guard) {
        for (struct addrinfo *rp = res; rp != NULL; rp = rp->ai_next) {
            if (is_blocked_sockaddr(rp->ai_addr)) {
                freeaddrinfo(res);
                snprintf(err, err_cap, "SSRF guard blocked private, loopback, or metadata IP for host %s", host);
                return false;
            }
        }
    }

    int fd = -1;
    for (struct addrinfo *rp = res; rp != NULL; rp = rp->ai_next) {
        fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (fd < 0) continue;
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
        struct timeval tv;
        tv.tv_sec = 15;
        tv.tv_usec = 0;
        setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
        setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
        if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0) {
            break;
        }
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);

    if (fd < 0) {
        snprintf(err, err_cap, "TCP connect failed to %s:%u", host, (unsigned)port);
        return false;
    }

    SSL *ssl = NULL;
    if (is_tls) {
        pthread_once(&g_ssl_once, init_ssl_global);
        if (!g_ssl_ctx) {
            close(fd);
            snprintf(err, err_cap, "OpenSSL SSL_CTX initialization failed");
            return false;
        }
        ssl = SSL_new(g_ssl_ctx);
        if (!ssl) {
            close(fd);
            snprintf(err, err_cap, "SSL_new failed");
            return false;
        }
        struct in_addr v4tmp;
        struct in6_addr v6tmp;
        bool is_ip_literal = (inet_pton(AF_INET, host, &v4tmp) == 1) || (inet_pton(AF_INET6, host, &v6tmp) == 1);
        if (!is_ip_literal) {
            SSL_set_tlsext_host_name(ssl, host);
        }
        X509_VERIFY_PARAM *param = SSL_get0_param(ssl);
        if (param != NULL) {
            if (is_ip_literal) {
                X509_VERIFY_PARAM_set1_ip_asc(param, host);
            } else {
                X509_VERIFY_PARAM_set1_host(param, host, 0);
            }
        }
        SSL_set_fd(ssl, fd);
        if (SSL_connect(ssl) != 1) {
            SSL_free(ssl);
            close(fd);
            snprintf(err, err_cap, "TLS handshake failed with %s:%u", host, (unsigned)port);
            return false;
        }
    }

    *out_fd = fd;
    *out_ssl = ssl;
    return true;
}

static void release_outbound_conn(bool keep_alive, bool is_tls, const char *host, uint16_t port, int fd, SSL *ssl) {
    if (!keep_alive || fd < 0) {
        if (ssl != NULL) {
            SSL_shutdown(ssl);
            SSL_free(ssl);
        }
        if (fd >= 0) close(fd);
        return;
    }
    int slot = -1;
    time_t oldest = 0;
    int oldest_idx = 0;
    for (int i = 0; i < QED_POOL_SIZE; i++) {
        if (!tls_pool[i].in_use) {
            slot = i;
            break;
        }
        if (i == 0 || tls_pool[i].last_used < oldest) {
            oldest = tls_pool[i].last_used;
            oldest_idx = i;
        }
    }
    if (slot < 0) {
        close_pool_entry(&tls_pool[oldest_idx]);
        slot = oldest_idx;
    }
    qed_pool_conn_t *e = &tls_pool[slot];
    e->in_use = true;
    e->is_tls = is_tls;
    e->port = port;
    snprintf(e->host, sizeof(e->host), "%s", host);
    e->fd = fd;
    e->ssl = ssl;
    e->last_used = time(NULL);
}

static bool conn_write_all(int fd, SSL *ssl, const uint8_t *buf, size_t len) {
    size_t off = 0;
    while (off < len) {
        size_t rem = len - off;
        ssize_t n;
        if (ssl != NULL) {
            int chunk = (rem > (size_t)INT_MAX) ? INT_MAX : (int)rem;
            n = SSL_write(ssl, buf + off, chunk);
        } else {
            n = send(fd, buf + off, rem, MSG_NOSIGNAL);
        }
        if (n <= 0) {
            if (ssl == NULL && errno == EINTR) continue;
            return false;
        }
        off += (size_t)n;
    }
    return true;
}

static ssize_t conn_read_some(int fd, SSL *ssl, uint8_t *buf, size_t cap) {
    for (;;) {
        ssize_t n;
        if (ssl != NULL) {
            int chunk = (cap > (size_t)INT_MAX) ? INT_MAX : (int)cap;
            n = SSL_read(ssl, buf, chunk);
        } else {
            n = recv(fd, buf, cap, 0);
        }
        if (n < 0 && ssl == NULL && errno == EINTR) continue;
        return n;
    }
}

typedef struct {
    char *key;
    char *val;
} qed_hdr_pair_t;

typedef struct {
    int status;
    qed_buf_t body;
    qed_hdr_pair_t *headers;
    size_t header_count;
} qed_raw_resp_t;

static void free_raw_resp(qed_raw_resp_t *r) {
    buf_free(&r->body);
    for (size_t i = 0; i < r->header_count; i++) {
        free(r->headers[i].key);
        free(r->headers[i].val);
    }
    free(r->headers);
    r->headers = NULL;
    r->header_count = 0;
}

static ssize_t find_crlfcrlf(const uint8_t *d, size_t n) {
    if (n < 4) return -1;
    for (size_t i = 0; i + 3 < n; i++) {
        if (d[i] == '\r' && d[i + 1] == '\n' && d[i + 2] == '\r' && d[i + 3] == '\n') {
            return (ssize_t)i;
        }
    }
    return -1;
}

static bool split_header_kv(char *line, char **out_val) {
    char *colon = strchr(line, ':');
    if (!colon) return false;
    *colon = '\0';
    char *val = colon + 1;
    while (*val == ' ' || *val == '\t') val++;
    *out_val = val;
    return true;
}

static lean_object *mk_lean_headers(const qed_hdr_pair_t *hdrs, size_t n) {
    lean_object *arr = lean_mk_empty_array_with_capacity(lean_usize_to_nat(n));
    for (size_t i = 0; i < n; i++) {
        lean_object *k = lean_mk_string(hdrs[i].key ? hdrs[i].key : "");
        lean_object *v = lean_mk_string(hdrs[i].val ? hdrs[i].val : "");
        arr = lean_array_push(arr, mk_prod(k, v));
    }
    return arr;
}

static bool conn_read_until(int fd, SSL *ssl, qed_buf_t *b, size_t target_len) {
    while (b->len < target_len) {
        uint8_t tmp[8192];
        size_t rem = target_len - b->len;
        ssize_t got = conn_read_some(fd, ssl, tmp, rem < sizeof(tmp) ? rem : sizeof(tmp));
        if (got <= 0 || !buf_append(b, tmp, (size_t)got)) return false;
    }
    return true;
}

static char *next_crlf_line(char **cursor, char *end, bool *bare_cr_or_lf) {
    char *p = *cursor;
    if (p >= end) return NULL;
    char *s = p;
    while (p < end) {
        if (*p == '\r') {
            if (p + 1 < end && p[1] == '\n') {
                *p = '\0';
                *cursor = p + 2;
                return s;
            }
            if (bare_cr_or_lf) *bare_cr_or_lf = true;
            return NULL;
        }
        if (*p == '\n') {
            if (bare_cr_or_lf) *bare_cr_or_lf = true;
            return NULL;
        }
        p++;
    }
    *cursor = end;
    return s;
}

static bool read_chunk_crlf_line(
    int fd, SSL *ssl, qed_buf_t *raw_buf,
    size_t *cursor, size_t max_bytes, size_t *out_line_len)
{
    size_t start = *cursor;
    for (;;) {
        for (size_t i = *cursor; i + 1 < raw_buf->len; i++) {
            if (raw_buf->data[i] == '\r' && raw_buf->data[i + 1] == '\n') {
                *out_line_len = i - start;
                *cursor = i + 2;
                return true;
            }
        }
        if (raw_buf->len - start > max_bytes) return false;
        uint8_t tmp[4096];
        ssize_t got = conn_read_some(fd, ssl, tmp, sizeof(tmp));
        if (got <= 0 || !buf_append(raw_buf, tmp, (size_t)got)) return false;
    }
}

static bool decode_chunked_stream(
    int fd, SSL *ssl,
    qed_buf_t *raw_buf, size_t cursor,
    qed_buf_t *out_body,
    bool *out_clean_eof)
{
    if (out_clean_eof) *out_clean_eof = false;
    for (;;) {
        size_t line_start = cursor;
        size_t slen = 0;
        if (!read_chunk_crlf_line(fd, ssl, raw_buf, &cursor, 16384, &slen)) return false;

        char size_line[64];
        const uint8_t *line_ptr = raw_buf->data + line_start;
        const uint8_t *semi_ptr = (const uint8_t *)memchr(line_ptr, ';', slen);
        size_t hex_len = semi_ptr ? (size_t)(semi_ptr - line_ptr) : slen;
        if (hex_len == 0 || hex_len >= sizeof(size_line)) return false;
        memcpy(size_line, line_ptr, hex_len);
        size_line[hex_len] = '\0';

        size_t chunk_sz = 0;
        if (!parse_hex_size(size_line, &chunk_sz)) return false;

        if (chunk_sz == 0) {
            size_t trailer_bytes = 0;
            for (;;) {
                size_t tlen = 0;
                if (!read_chunk_crlf_line(fd, ssl, raw_buf, &cursor, 65536, &tlen)) return false;
                trailer_bytes += tlen + 2;
                if (trailer_bytes > 65536) return false;
                if (tlen == 0) {
                    if (out_clean_eof) *out_clean_eof = (raw_buf->len == cursor);
                    return true;
                }
            }
        }

        if (chunk_sz > (256ULL * 1024ULL * 1024ULL)) return false;
        if (cursor > SIZE_MAX - 2 || chunk_sz > SIZE_MAX - cursor - 2) return false;

        size_t need_end = cursor + chunk_sz + 2;
        if (!conn_read_until(fd, ssl, raw_buf, need_end)) return false;
        if (raw_buf->data[cursor + chunk_sz] != '\r' || raw_buf->data[cursor + chunk_sz + 1] != '\n') {
            return false;
        }
        if (!buf_append(out_body, raw_buf->data + cursor, chunk_sz)) return false;
        cursor = need_end;

        if (cursor >= 65536) {
            buf_consume(raw_buf, cursor);
            cursor = 0;
        }
    }
}

static bool raw_http_execute(
    const char *method,
    const char *url,
    const qed_hdr_pair_t *req_hdrs,
    size_t req_hdr_count,
    const uint8_t *req_body,
    size_t req_body_len,
    uint8_t ssrf_guard,
    qed_raw_resp_t *out,
    char *err,
    size_t err_cap)
{
    ensure_sigpipe_ignored();
    memset(out, 0, sizeof(*out));
    if (!buf_init(&out->body, 1024)) {
        snprintf(err, err_cap, "out of memory");
        return false;
    }
    if (!is_valid_http_token(method)) {
        buf_free(&out->body);
        snprintf(err, err_cap, "invalid outbound HTTP method");
        return false;
    }

    bool is_tls = false;
    bool is_ipv6_host = false;
    char host[256];
    uint16_t port = 80;
    char path[4096];
    if (!parse_http_url(url, &is_tls, host, sizeof(host), &is_ipv6_host, &port, path, sizeof(path))) {
        buf_free(&out->body);
        snprintf(err, err_cap, "invalid outbound HTTP URL: %.200s", url ? url : "");
        return false;
    }
    for (size_t i = 0; i < req_hdr_count; i++) {
        if (!is_valid_http_token(req_hdrs[i].key) || has_ctl_or_crlf(req_hdrs[i].val, true)) {
            buf_free(&out->body);
            snprintf(err, err_cap, "invalid outbound HTTP header (CRLF/control chars)");
            return false;
        }
    }

    size_t init_cap = 512 + (req_body_len <= 64 * 1024 * 1024 ? req_body_len : 0);
    qed_buf_t req_wire;
    if (!buf_init(&req_wire, init_cap)) {
        buf_free(&out->body);
        snprintf(err, err_cap, "out of memory building HTTP request");
        return false;
    }

    bool default_port = (is_tls && port == 443) || (!is_tls && port == 80);
    bool wire_ok = buf_append_fmt(&req_wire, "%s %s HTTP/1.1\r\nHost: %s%s%s",
                                  method, path, is_ipv6_host ? "[" : "", host, is_ipv6_host ? "]" : "");
    if (wire_ok && !default_port) wire_ok = buf_append_fmt(&req_wire, ":%u", (unsigned)port);
    if (wire_ok) wire_ok = buf_append_fmt(&req_wire, "\r\nConnection: keep-alive\r\nContent-Length: %zu\r\n", req_body_len);
    for (size_t i = 0; wire_ok && i < req_hdr_count; i++) {
        const char *k = req_hdrs[i].key;
        if (strcasecmp(k, "Host") == 0 || strcasecmp(k, "Content-Length") == 0 || strcasecmp(k, "Connection") == 0) {
            continue;
        }
        wire_ok = buf_append_fmt(&req_wire, "%s: %s\r\n", k, req_hdrs[i].val);
    }
    if (wire_ok) wire_ok = buf_append_cstr(&req_wire, "\r\n");
    if (wire_ok && req_body_len > 0) wire_ok = buf_append(&req_wire, req_body, req_body_len);
    if (!wire_ok) {
        buf_free(&req_wire);
        buf_free(&out->body);
        snprintf(err, err_cap, "out of memory building HTTP request");
        return false;
    }

    for (int attempt = 0; attempt < 2; attempt++) {
        int fd = -1;
        SSL *ssl = NULL;
        bool was_reused = false;
        if (!acquire_outbound_conn(is_tls, host, port, ssrf_guard, &fd, &ssl, &was_reused, err, err_cap)) {
            buf_free(&req_wire);
            buf_free(&out->body);
            return false;
        }

        if (!conn_write_all(fd, ssl, req_wire.data, req_wire.len)) {
            release_outbound_conn(false, is_tls, host, port, fd, ssl);
            if (was_reused && attempt == 0) continue;
            buf_free(&req_wire);
            buf_free(&out->body);
            snprintf(err, err_cap, "failed sending HTTP request to %s", host);
            return false;
        }

        qed_buf_t rx;
        if (!buf_init(&rx, 4096)) {
            release_outbound_conn(false, is_tls, host, port, fd, ssl);
            buf_free(&req_wire);
            buf_free(&out->body);
            snprintf(err, err_cap, "out of memory");
            return false;
        }
        ssize_t hdr_end = -1;
        bool read_failed = false;
        while ((hdr_end = find_crlfcrlf(rx.data, rx.len)) < 0) {
            uint8_t tmp[4096];
            ssize_t got = (rx.len > 65536) ? -1 : conn_read_some(fd, ssl, tmp, sizeof(tmp));
            if (got <= 0 || !buf_append(&rx, tmp, (size_t)got)) {
                read_failed = true;
                break;
            }
        }
        if (read_failed) {
            buf_free(&rx);
            release_outbound_conn(false, is_tls, host, port, fd, ssl);
            if (was_reused && attempt == 0) continue;
            buf_free(&req_wire);
            buf_free(&out->body);
            snprintf(err, err_cap, "EOF or malformed response header from %s", host);
            return false;
        }
        buf_free(&req_wire);

        if (memchr(rx.data, '\0', (size_t)hdr_end) != NULL) {
            snprintf(err, err_cap, "NUL byte in HTTP response headers from %s", host);
            goto fail_rx_conn;
        }
        rx.data[hdr_end] = '\0';

        char *cursor = (char *)rx.data;
        char *hdr_limit = (char *)rx.data + hdr_end;
        bool bare_crlf = false;
        char *line = next_crlf_line(&cursor, hdr_limit, &bare_crlf);
        char *sp = line ? strchr(line, ' ') : NULL;
        int status_val = 0;
        if (!line || bare_crlf || strncmp(line, "HTTP/", 5) != 0 || !sp || !parse_status_code(sp + 1, &status_val)) {
            snprintf(err, err_cap, "invalid HTTP status line from %s", host);
            goto fail_rx_conn;
        }
        out->status = status_val;

        bool is_chunked = false;
        bool conn_close = false;
        bool has_content_len = false;
        bool bad_resp_hdr = false;
        uint64_t content_len_u64 = 0;
        size_t hdr_cap = 16;
        out->headers = (qed_hdr_pair_t *)calloc(hdr_cap, sizeof(qed_hdr_pair_t));
        if (!out->headers) {
            snprintf(err, err_cap, "out of memory allocating headers");
            goto fail_rx_conn;
        }

        char *val = NULL;
        while ((line = next_crlf_line(&cursor, hdr_limit, &bare_crlf)) != NULL) {
            if (!split_header_kv(line, &val)) continue;
            if (strcasecmp(line, "Content-Length") == 0) {
                uint64_t parsed_cl = 0;
                if (!parse_strict_u64(val, &parsed_cl) || (has_content_len && parsed_cl != content_len_u64)) {
                    bad_resp_hdr = true;
                    break;
                }
                has_content_len = true;
                content_len_u64 = parsed_cl;
            } else if (strcasecmp(line, "Transfer-Encoding") == 0 && strcasestr(val, "chunked") != NULL) {
                is_chunked = true;
            } else if (strcasecmp(line, "Connection") == 0 && strcasestr(val, "close") != NULL) {
                conn_close = true;
            }
            if (out->header_count == hdr_cap) {
                if (hdr_cap > SIZE_MAX / 2 / sizeof(qed_hdr_pair_t)) { bad_resp_hdr = true; break; }
                size_t new_cap = hdr_cap * 2;
                qed_hdr_pair_t *nh = (qed_hdr_pair_t *)realloc(out->headers, new_cap * sizeof(qed_hdr_pair_t));
                if (!nh) { bad_resp_hdr = true; break; }
                out->headers = nh;
                hdr_cap = new_cap;
            }
            out->headers[out->header_count].key = strdup(line);
            out->headers[out->header_count].val = strdup(val);
            if (!out->headers[out->header_count].key || !out->headers[out->header_count].val) {
                free(out->headers[out->header_count].key);
                free(out->headers[out->header_count].val);
                bad_resp_hdr = true;
                break;
            }
            out->header_count++;
        }
        if (bare_crlf || bad_resp_hdr) {
            snprintf(err, err_cap, "malformed HTTP response header from %s", host);
            goto fail_rx_conn;
        }

        size_t body_start = (size_t)hdr_end + 4;
        bool can_reuse = !conn_close && !ssrf_guard;

        if (strcmp(method, "HEAD") == 0 || out->status == 204 || out->status == 304) {
            if (rx.len > body_start) can_reuse = false;
        } else if (is_chunked) {
            bool clean_eof = false;
            if (!decode_chunked_stream(fd, ssl, &rx, body_start, &out->body, &clean_eof)) {
                snprintf(err, err_cap, "failed decoding chunked response from %s", host);
                goto fail_rx_conn;
            }
            if (!clean_eof) can_reuse = false;
        } else if (has_content_len) {
            if (content_len_u64 > (uint64_t)(SIZE_MAX / 2)) {
                snprintf(err, err_cap, "Content-Length too large from %s", host);
                goto fail_rx_conn;
            }
            size_t content_len = (size_t)content_len_u64;
            size_t have = rx.len - body_start;
            if (have > content_len) {
                have = content_len;
                can_reuse = false;
            }
            if ((have > 0 && !buf_append(&out->body, rx.data + body_start, have)) ||
                !conn_read_until(fd, ssl, &out->body, content_len)) {
                snprintf(err, err_cap, "truncated HTTP body from %s", host);
                goto fail_rx_conn;
            }
        } else {
            can_reuse = false;
            if (rx.len > body_start && !buf_append(&out->body, rx.data + body_start, rx.len - body_start)) {
                snprintf(err, err_cap, "out of memory buffering HTTP body");
                goto fail_rx_conn;
            }
            for (;;) {
                uint8_t tmp[8192];
                ssize_t got = conn_read_some(fd, ssl, tmp, sizeof(tmp));
                if (got == 0) break;
                if (got < 0 || !buf_append(&out->body, tmp, (size_t)got)) {
                    snprintf(err, err_cap, "error reading close-delimited HTTP body from %s", host);
                    goto fail_rx_conn;
                }
            }
        }

        buf_free(&rx);
        release_outbound_conn(can_reuse, is_tls, host, port, fd, ssl);
        return true;

    fail_rx_conn:
        buf_free(&rx);
        release_outbound_conn(false, is_tls, host, port, fd, ssl);
        free_raw_resp(out);
        return false;
    }

    buf_free(&req_wire);
    buf_free(&out->body);
    snprintf(err, err_cap, "HTTP call failed");
    return false;
}

LEAN_EXPORT lean_object *qed_server_http_call(
    b_lean_obj_arg method,
    b_lean_obj_arg url,
    b_lean_obj_arg headers,
    b_lean_obj_arg body,
    uint8_t ssrf_guard)
{
    ensure_sigpipe_ignored();
    size_t hdr_n = lean_array_size(headers);
    qed_hdr_pair_t *req_hdrs = hdr_n > 0 ? (qed_hdr_pair_t *)calloc(hdr_n, sizeof(qed_hdr_pair_t)) : NULL;
    if (hdr_n > 0 && !req_hdrs) {
        return lean_io_result_mk_ok(mk_except_err_str("out of memory allocating request headers"));
    }
    for (size_t i = 0; i < hdr_n; i++) {
        lean_object *pair = lean_array_uget_borrowed(headers, i);
        req_hdrs[i].key = (char *)lean_string_cstr(lean_ctor_get(pair, 0));
        req_hdrs[i].val = (char *)lean_string_cstr(lean_ctor_get(pair, 1));
    }

    qed_raw_resp_t resp;
    char err_msg[512] = "";
    bool ok = raw_http_execute(
        lean_string_cstr(method), lean_string_cstr(url),
        req_hdrs, hdr_n, lean_sarray_cptr((lean_object *)body), lean_sarray_size(body),
        ssrf_guard, &resp, err_msg, sizeof(err_msg));
    free(req_hdrs);
    if (!ok) return lean_io_result_mk_ok(mk_except_err_str(err_msg));

    lean_object *hdr_arr = mk_lean_headers(resp.headers, resp.header_count);
    lean_object *ba = mk_byte_array_copy(resp.body.data, resp.body.len);
    lean_object *status_nat = lean_usize_to_nat((size_t)(resp.status > 0 ? resp.status : 0));
    free_raw_resp(&resp);
    return lean_io_result_mk_ok(mk_except_ok(mk_prod(status_nat, mk_prod(ba, hdr_arr))));
}

/* =========================================================================
 * 6. GCP Service Account RS256 JWT Signing & Cached OAuth2 Bearer Exchange
 * ========================================================================= */

static bool buf_append_b64url(qed_buf_t *b, const uint8_t *in, size_t in_len) {
    static const char kTbl[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    size_t enc_len = ((in_len + 2) / 3) * 4;
    if (!buf_reserve(b, enc_len + 1)) return false;
    char *out = (char *)(b->data + b->len);
    size_t j = 0, i = 0;
    while (i + 3 <= in_len) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i + 1] << 8) | (uint32_t)in[i + 2];
        out[j++] = kTbl[(v >> 18) & 0x3F];
        out[j++] = kTbl[(v >> 12) & 0x3F];
        out[j++] = kTbl[(v >> 6) & 0x3F];
        out[j++] = kTbl[v & 0x3F];
        i += 3;
    }
    if (in_len - i > 0) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((in_len - i == 2) ? ((uint32_t)in[i + 1] << 8) : 0U);
        out[j++] = kTbl[(v >> 18) & 0x3F];
        out[j++] = kTbl[(v >> 12) & 0x3F];
        if (in_len - i == 2) out[j++] = kTbl[(v >> 6) & 0x3F];
    }
    out[j] = '\0';
    b->len += j;
    return true;
}

static bool buf_append_json_escaped(qed_buf_t *b, const char *s) {
    static const char kRaw[] = "\"\\\b\f\n\r\t";
    static const char kEsc[] = "\"\\bfnrt";
    if (!s) return true;
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        unsigned char c = *p;
        const char *hit = (c != 0) ? strchr(kRaw, (char)c) : NULL;
        if (hit) {
            char pair[2] = { '\\', kEsc[hit - kRaw] };
            if (!buf_append(b, pair, 2)) return false;
        } else if (c < 0x20) {
            if (!buf_append_fmt(b, "\\u%04x", (unsigned)c)) return false;
        } else {
            if (!buf_append(b, &c, 1)) return false;
        }
    }
    return true;
}

static const char *json_find_val(const char *json, const char *key) {
    if (!json || !key) return NULL;
    size_t key_len = strlen(key);
    int depth = 0;
    const char *p = json;
    while (*p) {
        char c = *p;
        if (c == '{' || c == '[') {
            depth++;
            p++;
        } else if (c == '}' || c == ']') {
            depth--;
            p++;
        } else if (c == '"') {
            const char *str_start = p + 1;
            p++;
            bool has_escape = false;
            while (*p && *p != '"') {
                if (*p == '\\' && p[1] != '\0') {
                    has_escape = true;
                    p += 2;
                } else {
                    p++;
                }
            }
            if (*p != '"') return NULL;
            size_t str_len = (size_t)(p - str_start);
            p++; /* past closing quote */
            if (depth == 1 && !has_escape && str_len == key_len && memcmp(str_start, key, key_len) == 0) {
                const char *q = p;
                while (*q == ' ' || *q == '\t' || *q == '\r' || *q == '\n') q++;
                if (*q == ':') {
                    q++;
                    while (*q == ' ' || *q == '\t' || *q == '\r' || *q == '\n') q++;
                    return q;
                }
            }
        } else {
            p++;
        }
    }
    return NULL;
}

static bool parse_hex4(const char *p, uint32_t *out) {
    uint32_t v = 0;
    for (int i = 0; i < 4; i++) {
        char c = p[i];
        uint32_t d;
        if (c >= '0' && c <= '9') d = (uint32_t)(c - '0');
        else if (c >= 'a' && c <= 'f') d = (uint32_t)(c - 'a' + 10);
        else if (c >= 'A' && c <= 'F') d = (uint32_t)(c - 'A' + 10);
        else return false;
        v = (v << 4) | d;
    }
    *out = v;
    return true;
}

static bool append_utf8_cp(char *out, size_t out_cap, size_t *j, uint32_t cp) {
    if (cp == 0 || cp > 0x10FFFF) return false;
    char tmp[4];
    size_t n = 0;
    if (cp <= 0x7F) {
        tmp[n++] = (char)cp;
    } else if (cp <= 0x7FF) {
        tmp[n++] = (char)(0xC0 | (cp >> 6));
        tmp[n++] = (char)(0x80 | (cp & 0x3F));
    } else if (cp <= 0xFFFF) {
        tmp[n++] = (char)(0xE0 | (cp >> 12));
        tmp[n++] = (char)(0x80 | ((cp >> 6) & 0x3F));
        tmp[n++] = (char)(0x80 | (cp & 0x3F));
    } else {
        tmp[n++] = (char)(0xF0 | (cp >> 18));
        tmp[n++] = (char)(0x80 | ((cp >> 12) & 0x3F));
        tmp[n++] = (char)(0x80 | ((cp >> 6) & 0x3F));
        tmp[n++] = (char)(0x80 | (cp & 0x3F));
    }
    if (*j + n >= out_cap) return false;
    memcpy(out + *j, tmp, n);
    *j += n;
    return true;
}

static bool json_extract_string(const char *json, const char *key, char *out, size_t out_cap) {
    if (out_cap == 0) return false;
    const char *p = json_find_val(json, key);
    if (!p || *p != '"') return false;
    p++;
    size_t j = 0;
    while (*p && *p != '"') {
        if (*p == '\\' && p[1] != '\0') {
            p++;
            char ch = *p++;
            if (ch == 'u') {
                uint32_t cp = 0;
                if (!parse_hex4(p, &cp)) return false;
                p += 4;
                if (cp >= 0xD800 && cp <= 0xDBFF && p[0] == '\\' && p[1] == 'u') {
                    uint32_t low = 0;
                    if (!parse_hex4(p + 2, &low) || low < 0xDC00 || low > 0xDFFF) return false;
                    p += 6;
                    cp = 0x10000 + (((cp - 0xD800) << 10) | (low - 0xDC00));
                }
                if (!append_utf8_cp(out, out_cap, &j, cp)) return false;
            } else {
                char mapped = ch;
                if (ch == 'n') mapped = '\n';
                else if (ch == 'r') mapped = '\r';
                else if (ch == 't') mapped = '\t';
                else if (ch == 'b') mapped = '\b';
                else if (ch == 'f') mapped = '\f';
                if (j + 1 >= out_cap) return false;
                out[j++] = mapped;
            }
        } else {
            if (j + 1 >= out_cap) return false;
            out[j++] = *p++;
        }
    }
    if (*p != '"') return false;
    out[j] = '\0';
    return true;
}

static long json_extract_long(const char *json, const char *key, long fallback) {
    const char *p = json_find_val(json, key);
    if (!p || *p < '0' || *p > '9') return fallback;
    uint64_t acc = 0;
    while (*p >= '0' && *p <= '9') {
        uint64_t d = (uint64_t)(*p - '0');
        if (acc > (86400ULL * 365ULL - d) / 10ULL) return 86400L * 365L;
        acc = acc * 10ULL + d;
        p++;
    }
    return (acc > 0) ? (long)acc : fallback;
}

typedef struct {
    bool valid;
    char client_email[256];
    char scope[2048];
    char token_url[512];
    char access_token[2048];
    time_t expires_at;
} qed_gcp_cache_entry_t;

#define QED_GCP_CACHE_SIZE 8
static pthread_mutex_t g_gcp_mu = PTHREAD_MUTEX_INITIALIZER;
static qed_gcp_cache_entry_t g_gcp_cache[QED_GCP_CACHE_SIZE];

LEAN_EXPORT lean_object *qed_server_gcp_bearer_token(b_lean_obj_arg sa_json_obj, b_lean_obj_arg scope_obj) {
    ensure_sigpipe_ignored();
    const char *sa_json = lean_string_cstr(sa_json_obj);
    const char *scope = lean_string_cstr(scope_obj);

    char client_email[256];
    char private_key[8192];
    char token_uri[512];

    if (!json_extract_string(sa_json, "client_email", client_email, sizeof(client_email))) {
        return lean_io_result_mk_ok(mk_except_err_str("GCP service account JSON missing `client_email`"));
    }
    if (!json_extract_string(sa_json, "private_key", private_key, sizeof(private_key))) {
        return lean_io_result_mk_ok(mk_except_err_str("GCP service account JSON missing `private_key`"));
    }
    const char *env_tok_url = getenv("QED_GCP_TOKEN_URL");
    if (env_tok_url != NULL && env_tok_url[0] != '\0') {
        if (strlen(env_tok_url) >= sizeof(token_uri)) {
            return lean_io_result_mk_ok(mk_except_err_str("QED_GCP_TOKEN_URL too long"));
        }
        snprintf(token_uri, sizeof(token_uri), "%s", env_tok_url);
    } else if (!json_extract_string(sa_json, "token_uri", token_uri, sizeof(token_uri))) {
        snprintf(token_uri, sizeof(token_uri), "https://oauth2.googleapis.com/token");
    }

    time_t now = time(NULL);
    bool can_cache = (strlen(scope) < sizeof(g_gcp_cache[0].scope));
    if (can_cache) {
        pthread_mutex_lock(&g_gcp_mu);
        for (int i = 0; i < QED_GCP_CACHE_SIZE; i++) {
            qed_gcp_cache_entry_t *e = &g_gcp_cache[i];
            if (e->valid && e->expires_at > now + 60 &&
                strcmp(e->client_email, client_email) == 0 &&
                strcmp(e->scope, scope) == 0 &&
                strcmp(e->token_url, token_uri) == 0)
            {
                lean_object *tok = lean_mk_string(e->access_token);
                pthread_mutex_unlock(&g_gcp_mu);
                return lean_io_result_mk_ok(mk_except_ok(tok));
            }
        }
        pthread_mutex_unlock(&g_gcp_mu);
    }

    static const char *kJwtHdr = "{\"alg\":\"RS256\",\"typ\":\"JWT\"}";
    static const char *kGrantPrefix = "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion=";
    char err_msg[600] = "OOM building JWT claims";
    qed_buf_t claims_buf = {0};
    qed_buf_t jwt_buf = {0};
    qed_buf_t form_buf = {0};
    BIO *bio = NULL;
    EVP_PKEY *pkey = NULL;
    EVP_MD_CTX *mdctx = NULL;
    qed_raw_resp_t resp = {0};
    bool has_resp = false;

    if (!buf_init(&claims_buf, 1024) ||
        !buf_append_cstr(&claims_buf, "{\"iss\":\"") ||
        !buf_append_json_escaped(&claims_buf, client_email) ||
        !buf_append_cstr(&claims_buf, "\",\"scope\":\"") ||
        !buf_append_json_escaped(&claims_buf, scope) ||
        !buf_append_cstr(&claims_buf, "\",\"aud\":\"") ||
        !buf_append_json_escaped(&claims_buf, token_uri) ||
        !buf_append_fmt(&claims_buf, "\",\"iat\":%ld,\"exp\":%ld}", (long)now, (long)(now + 3600))) {
        goto fail;
    }

    if (!buf_init(&jwt_buf, 1024) ||
        !buf_append_b64url(&jwt_buf, (const uint8_t *)kJwtHdr, strlen(kJwtHdr)) ||
        !buf_append_cstr(&jwt_buf, ".") ||
        !buf_append_b64url(&jwt_buf, claims_buf.data, claims_buf.len)) {
        goto fail;
    }
    buf_free(&claims_buf);

    bio = BIO_new_mem_buf(private_key, -1);
    if (!bio) {
        snprintf(err_msg, sizeof(err_msg), "BIO_new_mem_buf failed for GCP private_key");
        goto fail;
    }
    pkey = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
    BIO_free(bio);
    bio = NULL;
    if (!pkey) {
        snprintf(err_msg, sizeof(err_msg), "PEM_read_bio_PrivateKey failed for GCP private_key");
        goto fail;
    }

    mdctx = EVP_MD_CTX_new();
    size_t sig_len = 0;
    uint8_t sig_buf[1024];
    if (!mdctx ||
        EVP_DigestSignInit(mdctx, NULL, EVP_sha256(), NULL, pkey) != 1 ||
        EVP_DigestSignUpdate(mdctx, jwt_buf.data, jwt_buf.len) != 1 ||
        EVP_DigestSignFinal(mdctx, NULL, &sig_len) != 1 ||
        sig_len > sizeof(sig_buf) ||
        EVP_DigestSignFinal(mdctx, sig_buf, &sig_len) != 1) {
        snprintf(err_msg, sizeof(err_msg), "EVP_DigestSign RS256 failed");
        goto fail;
    }
    EVP_MD_CTX_free(mdctx);
    mdctx = NULL;
    EVP_PKEY_free(pkey);
    pkey = NULL;

    if (!buf_init(&form_buf, jwt_buf.len + 1600) ||
        !buf_append_cstr(&form_buf, kGrantPrefix) ||
        !buf_append(&form_buf, jwt_buf.data, jwt_buf.len) ||
        !buf_append_cstr(&form_buf, ".") ||
        !buf_append_b64url(&form_buf, sig_buf, sig_len)) {
        goto fail;
    }
    buf_free(&jwt_buf);

    qed_hdr_pair_t hdrs[1] = { { "Content-Type", "application/x-www-form-urlencoded" } };
    if (!raw_http_execute("POST", token_uri, hdrs, 1, form_buf.data, form_buf.len, 0, &resp, err_msg, sizeof(err_msg))) {
        goto fail;
    }
    has_resp = true;
    buf_free(&form_buf);

    if (memchr(resp.body.data, '\0', resp.body.len) != NULL || !buf_append(&resp.body, "", 1)) {
        snprintf(err_msg, sizeof(err_msg), "invalid GCP OAuth2 response");
        goto fail;
    }
    if (resp.status < 200 || resp.status >= 300) {
        snprintf(err_msg, sizeof(err_msg), "OAuth2 HTTP %d: %.400s", resp.status, (char *)resp.body.data);
        goto fail;
    }

    char access_token[2048];
    if (!json_extract_string((const char *)resp.body.data, "access_token", access_token, sizeof(access_token))) {
        snprintf(err_msg, sizeof(err_msg), "GCP OAuth2 response missing `access_token`");
        goto fail;
    }
    long expires_in = json_extract_long((const char *)resp.body.data, "expires_in", 3600);
    free_raw_resp(&resp);

    if (can_cache) {
        pthread_mutex_lock(&g_gcp_mu);
        int slot = 0;
        for (int i = 0; i < QED_GCP_CACHE_SIZE; i++) {
            if (!g_gcp_cache[i].valid) { slot = i; break; }
            if (g_gcp_cache[i].expires_at < g_gcp_cache[slot].expires_at) slot = i;
        }
        qed_gcp_cache_entry_t *dst = &g_gcp_cache[slot];
        dst->valid = true;
        snprintf(dst->client_email, sizeof(dst->client_email), "%s", client_email);
        snprintf(dst->scope, sizeof(dst->scope), "%s", scope);
        snprintf(dst->token_url, sizeof(dst->token_url), "%s", token_uri);
        snprintf(dst->access_token, sizeof(dst->access_token), "%s", access_token);
        dst->expires_at = time(NULL) + (time_t)expires_in;
        pthread_mutex_unlock(&g_gcp_mu);
    }

    return lean_io_result_mk_ok(mk_except_ok(lean_mk_string(access_token)));

fail:
    if (mdctx) EVP_MD_CTX_free(mdctx);
    if (pkey) EVP_PKEY_free(pkey);
    if (bio) BIO_free(bio);
    if (has_resp) free_raw_resp(&resp);
    buf_free(&claims_buf);
    buf_free(&jwt_buf);
    buf_free(&form_buf);
    return lean_io_result_mk_ok(mk_except_err_str(err_msg));
}

/* =========================================================================
 * 7. Multi-Core `SO_REUSEPORT` + `epoll` / `kqueue` HTTP/1.1 Server
 * ========================================================================= */

#define QED_MAX_REQ_HDR_BYTES 65536U
#define QED_MAX_REQ_BODY_BYTES (32ULL * 1024ULL * 1024ULL)
#define QED_MAX_TX_QUEUE_BYTES (64ULL * 1024ULL * 1024ULL)
#define QED_MAX_STATIC_FILE_BYTES (256ULL * 1024ULL * 1024ULL)
#define QED_MAX_WORKER_CONNS 4096U
#define QED_CONN_IDLE_TIMEOUT_SEC 30
#define QED_MAX_WS_MSG_BYTES (4ULL * 1024ULL * 1024ULL)
#define QED_MAX_WS_SUBS_PER_CONN 64U
#define QED_WS_PING_INTERVAL_SEC 25
#define QED_WS_DEAD_TIMEOUT_SEC 65
#define QED_TOPIC_BUCKETS 256U

static volatile sig_atomic_t g_stop_server = 0;

static void handle_stop_signal(int sig) {
    (void)sig;
    g_stop_server = 1;
}

static const char *status_reason(int code) {
    switch (code) {
        case 200: return "OK";
        case 201: return "Created";
        case 204: return "No Content";
        case 301: return "Moved Permanently";
        case 302: return "Found";
        case 304: return "Not Modified";
        case 400: return "Bad Request";
        case 401: return "Unauthorized";
        case 403: return "Forbidden";
        case 404: return "Not Found";
        case 405: return "Method Not Allowed";
        case 413: return "Payload Too Large";
        case 431: return "Request Header Fields Too Large";
        case 500: return "Internal Server Error";
        case 501: return "Not Implemented";
        default:  return "OK";
    }
}

static const char *guess_mime_type(const char *path) {
    const char *dot = strrchr(path, '.');
    if (!dot) return NULL;
    if (strcmp(dot, ".mjs") == 0 || strcmp(dot, ".js") == 0) return "text/javascript; charset=utf-8";
    if (strcmp(dot, ".css") == 0)  return "text/css; charset=utf-8";
    if (strcmp(dot, ".html") == 0) return "text/html; charset=utf-8";
    if (strcmp(dot, ".json") == 0 || strcmp(dot, ".map") == 0) return "application/json; charset=utf-8";
    if (strcmp(dot, ".svg") == 0)  return "image/svg+xml";
    if (strcmp(dot, ".png") == 0)  return "image/png";
    if (strcmp(dot, ".jpg") == 0 || strcmp(dot, ".jpeg") == 0) return "image/jpeg";
    if (strcmp(dot, ".webp") == 0) return "image/webp";
    if (strcmp(dot, ".ico") == 0)  return "image/x-icon";
    if (strcmp(dot, ".wasm") == 0) return "application/wasm";
    if (strcmp(dot, ".woff2") == 0) return "font/woff2";
    if (strcmp(dot, ".txt") == 0)  return "text/plain; charset=utf-8";
    return NULL;
}

typedef struct {
    uint32_t sub_id;
    char    *channel;
    uint8_t *params;
    size_t   params_len;
    char    *topic;
    size_t   topic_len;
} qed_ws_sub_t;

typedef struct qed_client_conn {
    int fd;
    int loop_fd;
    bool has_loop;
    bool rx_armed;
    bool tx_armed;
    bool peer_eof;
    bool close_after_tx;
    bool is_ws;
    bool ws_in_frag;
    uint8_t ws_frag_op;
    lean_object *ws_ctx;
    qed_buf_t ws_frag;
    qed_ws_sub_t *subs;
    size_t sub_cnt;
    size_t sub_cap;
    time_t last_ping_sent;
    char ip[64];
    qed_buf_t rx;
    qed_buf_t tx;
    size_t tx_off;
    time_t last_active;
    struct qed_client_conn *prev;
    struct qed_client_conn *next;
} qed_client_conn_t;

static void update_loop_write_interest(qed_client_conn_t *c, bool want_write) {
    if (!c->has_loop) return;
    bool want_read = !c->close_after_tx && !c->peer_eof;
    if (c->tx_armed == want_write && c->rx_armed == want_read) return;
#ifdef __linux__
    struct epoll_event ev;
    ev.data.ptr = c;
    ev.events = (want_read ? (uint32_t)(EPOLLIN | EPOLLRDHUP) : 0U) | (want_write ? (uint32_t)EPOLLOUT : 0U);
    if (epoll_ctl(c->loop_fd, EPOLL_CTL_MOD, c->fd, &ev) == 0) {
        c->tx_armed = want_write;
        c->rx_armed = want_read;
    }
#elif defined(__APPLE__)
    struct kevent kev[2];
    int n = 0;
    if (c->tx_armed != want_write) {
        EV_SET(&kev[n++], c->fd, EVFILT_WRITE, want_write ? (EV_ADD | EV_ENABLE) : EV_DELETE, 0, 0, c);
    }
    if (c->rx_armed != want_read && !want_read) {
        EV_SET(&kev[n++], c->fd, EVFILT_READ, EV_DELETE, 0, 0, c);
    }
    if (n > 0 && kevent(c->loop_fd, kev, n, NULL, 0, NULL) == 0) {
        c->tx_armed = want_write;
        c->rx_armed = want_read;
    }
#endif
}

static bool queue_or_writev(
    qed_client_conn_t *c,
    const char *hdr, size_t hdr_len,
    const uint8_t *body, size_t body_len)
{
    struct iovec iov[2];
    iov[0].iov_base = (void *)hdr;
    iov[0].iov_len  = hdr_len;
    iov[1].iov_base = (void *)body;
    iov[1].iov_len  = body_len;
    int iovcnt = (body_len > 0 && body != NULL) ? 2 : 1;
    int idx = 0;

    if (c->tx.len == 0) {
        while (idx < iovcnt) {
            ssize_t n = writev(c->fd, &iov[idx], iovcnt - idx);
            if (n < 0) {
                if (errno == EINTR) continue;
                if (errno == EAGAIN || errno == EWOULDBLOCK) break;
                return false;
            }
            c->last_active = time(NULL);
            size_t rem = (size_t)n;
            while (idx < iovcnt && rem >= iov[idx].iov_len) {
                rem -= iov[idx].iov_len;
                idx++;
            }
            if (idx < iovcnt && rem > 0) {
                iov[idx].iov_base = (uint8_t *)iov[idx].iov_base + rem;
                iov[idx].iov_len -= rem;
            }
        }
        if (idx == iovcnt) return true;
        c->tx_off = 0;
    }

    size_t pending = c->tx.len - c->tx_off;
    size_t need = 0;
    for (int k = idx; k < iovcnt; k++) {
        if (iov[k].iov_len > QED_MAX_TX_QUEUE_BYTES - pending - need) return false;
        need += iov[k].iov_len;
    }
    if (c->tx.data == NULL && !buf_init(&c->tx, need < 4096 ? 4096 : need)) return false;
    if (c->tx_off > 0 && c->tx_off >= c->tx.len / 2) {
        buf_consume(&c->tx, c->tx_off);
        c->tx_off = 0;
    }
    for (int k = idx; k < iovcnt; k++) {
        if (!buf_append(&c->tx, iov[k].iov_base, iov[k].iov_len)) return false;
    }
    update_loop_write_interest(c, true);
    return true;
}

static bool flush_client_tx(qed_client_conn_t *c) {
    while (c->tx_off < c->tx.len) {
        ssize_t n = send(c->fd, c->tx.data + c->tx_off, c->tx.len - c->tx_off, MSG_NOSIGNAL);
        if (n < 0) {
            if (errno == EINTR) continue;
            if (errno == EAGAIN || errno == EWOULDBLOCK) return true;
            return false;
        }
        if (n == 0) return false;
        c->tx_off += (size_t)n;
        c->last_active = time(NULL);
    }
    c->tx.len = 0;
    c->tx_off = 0;
    update_loop_write_interest(c, false);
    return true;
}

static bool send_http_response(
    qed_client_conn_t *c, int status, const char *content_type,
    const uint8_t *body, size_t body_len,
    bool head_only, bool keep_alive, bool no_store)
{
    if (!content_type || has_ctl_or_crlf(content_type, false)) {
        content_type = "application/octet-stream";
    }
    char hdr[1024];
    int hlen = snprintf(
        hdr, sizeof(hdr),
        "HTTP/1.1 %d %s\r\n"
        "Content-Type: %s\r\n"
        "Content-Length: %zu\r\n"
        "Connection: %s\r\n"
        "%s"
        "\r\n",
        status, status_reason(status),
        content_type,
        body_len,
        keep_alive ? "keep-alive" : "close",
        no_store ? "Cache-Control: no-store\r\n" : "");
    if (hlen <= 0 || (size_t)hlen >= sizeof(hdr)) return false;
    return queue_or_writev(c, hdr, (size_t)hlen, head_only ? NULL : body, head_only ? 0 : body_len);
}

static int reject_request(qed_client_conn_t *c, int status, const char *msg) {
    (void)send_http_response(c, status, "text/plain; charset=utf-8",
                             (const uint8_t *)msg, strlen(msg),
                             false, false, true);
    c->close_after_tx = true;
    return -1;
}

static bool read_regular_file_nofollow(const char *path, bool head_only, uint8_t **out_data, size_t *out_len) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return false;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size < 0 ||
        (uint64_t)st.st_size > QED_MAX_STATIC_FILE_BYTES) {
        close(fd);
        return false;
    }
    size_t fsize = (size_t)st.st_size;
    *out_data = NULL;
    *out_len = fsize;
    if (!head_only && fsize > 0) {
        *out_data = (uint8_t *)malloc(fsize);
        if (!*out_data) { close(fd); return false; }
        size_t off = 0;
        while (off < fsize) {
            ssize_t r = read(fd, *out_data + off, fsize - off);
            if (r < 0) {
                if (errno == EINTR) continue;
                free(*out_data);
                *out_data = NULL;
                close(fd);
                return false;
            }
            if (r == 0) break;
            off += (size_t)r;
        }
        *out_len = off;
    }
    close(fd);
    return true;
}

static bool is_within_static_dir(const char *static_dir, const char *candidate_path) {
    char real_dir[PATH_MAX];
    char real_file[PATH_MAX];
    if (!realpath(static_dir, real_dir)) return false;
    if (!realpath(candidate_path, real_file)) return false;
    size_t dlen = strlen(real_dir);
    if (strncmp(real_file, real_dir, dlen) != 0) return false;
    if (dlen > 0 && real_dir[dlen - 1] == '/') return real_file[dlen] != '\0';
    return real_file[dlen] == '/';
}

static bool try_serve_static_c(
    qed_client_conn_t *c,
    const char *static_dir,
    uint8_t dev_mode,
    const char *method,
    const char *target,
    bool keep_alive,
    bool *out_write_ok)
{
    *out_write_ok = true;
    bool is_get = (strcmp(method, "GET") == 0);
    bool is_head = (strcmp(method, "HEAD") == 0);
    if (!is_get && !is_head) return false;

    char path_only[2048];
    const char *q = strchr(target, '?');
    size_t plen = q ? (size_t)(q - target) : strlen(target);
    if (plen == 0 || plen >= sizeof(path_only)) return false;
    if (target[0] != '/') return false;
    if (memchr(target, '\\', plen) != NULL) return false;
    memcpy(path_only, target, plen);
    path_only[plen] = '\0';

    if (strncmp(path_only, "/_qed/", 6) == 0 || strstr(path_only, "..") != NULL) return false;

    char full[PATH_MAX];
    int flen = snprintf(full, sizeof(full), "%s%s", static_dir, path_only);
    if (flen <= 0 || (size_t)flen >= sizeof(full)) return false;

    if (dev_mode && strcmp(path_only, "/__build_id") == 0) {
        uint8_t *data = NULL;
        size_t len = 0;
        if (is_within_static_dir(static_dir, full) && read_regular_file_nofollow(full, is_head, &data, &len)) {
            *out_write_ok = send_http_response(c, 200, "text/plain; charset=utf-8", data, len, is_head, keep_alive, true);
            free(data);
        } else {
            *out_write_ok = send_http_response(c, 200, "text/plain; charset=utf-8", (const uint8_t *)"0", 1, is_head, keep_alive, true);
        }
        return true;
    }

    const char *mime = guess_mime_type(path_only);
    if (!mime) return false;

    if (!is_within_static_dir(static_dir, full)) return false;
    uint8_t *data = NULL;
    size_t fsize = 0;
    if (!read_regular_file_nofollow(full, is_head, &data, &fsize)) return false;
    *out_write_ok = send_http_response(c, 200, mime, data, fsize, is_head, keep_alive, dev_mode != 0);
    free(data);
    return true;
}

static void set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static int create_reuseport_listener(uint16_t port, bool allow_reuseport) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
#ifdef SO_REUSEPORT
    if (allow_reuseport) setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one));
#endif
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(port);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) != 0 || listen(fd, 4096) != 0) {
        close(fd);
        return -1;
    }
    set_nonblocking(fd);
    return fd;
}

/* =========================================================================
 * 7b. Multiplexed RFC 6455 WebSockets & Zero-Copy Cross-Worker Broadcast Hub
 * ========================================================================= */

typedef struct {
    char *topic;
    size_t topic_len;
    uint8_t *payload;
    size_t payload_len;
    _Atomic uint32_t refcnt;
} qed_ws_bcast_msg_t;

typedef struct qed_ws_bcast_node {
    qed_ws_bcast_msg_t *msg;
    struct qed_ws_bcast_node *next;
} qed_ws_bcast_node_t;

typedef struct {
    pthread_mutex_t mu;
    qed_ws_bcast_node_t *head;
    qed_ws_bcast_node_t *tail;
    int wake_fd;
    int loop_fd;
} qed_worker_inbox_t;

static pthread_mutex_t g_bcast_mu = PTHREAD_MUTEX_INITIALIZER;
static qed_worker_inbox_t *g_inboxes = NULL;
static uint32_t g_num_inboxes = 0;

static void bcast_msg_unref(qed_ws_bcast_msg_t *m) {
    if (!m) return;
    if (atomic_fetch_sub_explicit(&m->refcnt, 1, memory_order_acq_rel) == 1) {
        free(m->topic);
        free(m->payload);
        free(m);
    }
}

LEAN_EXPORT lean_object *qed_server_ws_broadcast(b_lean_obj_arg topic_obj, b_lean_obj_arg payload_obj) {
    const char *topic_str = lean_string_cstr(topic_obj);
    size_t topic_len = strlen(topic_str);
    const uint8_t *pay_ptr = lean_sarray_cptr((lean_object *)payload_obj);
    size_t pay_len = lean_sarray_size(payload_obj);

    pthread_mutex_lock(&g_bcast_mu);
    uint32_t nworkers = g_num_inboxes;
    qed_worker_inbox_t *inboxes = g_inboxes;
    if (nworkers == 0 || inboxes == NULL) {
        pthread_mutex_unlock(&g_bcast_mu);
        return lean_io_result_mk_ok(lean_box(0));
    }

    qed_ws_bcast_msg_t *msg = (qed_ws_bcast_msg_t *)calloc(1, sizeof(qed_ws_bcast_msg_t));
    if (!msg) {
        pthread_mutex_unlock(&g_bcast_mu);
        return lean_io_result_mk_ok(lean_box(0));
    }
    msg->topic = (char *)malloc(topic_len + 1);
    msg->payload = pay_len > 0 ? (uint8_t *)malloc(pay_len) : NULL;
    if (!msg->topic || (pay_len > 0 && !msg->payload)) {
        free(msg->topic);
        free(msg->payload);
        free(msg);
        pthread_mutex_unlock(&g_bcast_mu);
        return lean_io_result_mk_ok(lean_box(0));
    }
    memcpy(msg->topic, topic_str, topic_len + 1);
    msg->topic_len = topic_len;
    if (pay_len > 0) memcpy(msg->payload, pay_ptr, pay_len);
    msg->payload_len = pay_len;
    atomic_init(&msg->refcnt, nworkers);

    for (uint32_t i = 0; i < nworkers; i++) {
        qed_ws_bcast_node_t *node = (qed_ws_bcast_node_t *)malloc(sizeof(qed_ws_bcast_node_t));
        if (!node) {
            bcast_msg_unref(msg);
            continue;
        }
        node->msg = msg;
        node->next = NULL;
        pthread_mutex_lock(&inboxes[i].mu);
        bool was_empty = (inboxes[i].head == NULL);
        if (inboxes[i].tail) inboxes[i].tail->next = node;
        else inboxes[i].head = node;
        inboxes[i].tail = node;
        int wfd = inboxes[i].wake_fd;
        int lfd = inboxes[i].loop_fd;
        (void)wfd;
        (void)lfd;
        pthread_mutex_unlock(&inboxes[i].mu);

        if (was_empty) {
#ifdef __linux__
            if (wfd >= 0) {
                uint64_t one = 1;
                ssize_t _w = write(wfd, &one, sizeof(one));
                (void)_w;
            }
#elif defined(__APPLE__)
            if (lfd >= 0) {
                struct kevent kev;
                EV_SET(&kev, 1, EVFILT_USER, 0, NOTE_TRIGGER, 0, (void *)(uintptr_t)1);
                kevent(lfd, &kev, 1, NULL, 0, NULL);
            }
            (void)wfd;
#else
            (void)wfd; (void)lfd;
#endif
        }
    }
    pthread_mutex_unlock(&g_bcast_mu);
    return lean_io_result_mk_ok(lean_box(0));
}

typedef struct qed_topic_entry {
    qed_client_conn_t *conn;
    uint32_t sub_id;
    char *topic;
    size_t topic_len;
    uint64_t hash;
    struct qed_topic_entry *next;
} qed_topic_entry_t;

typedef struct {
    qed_topic_entry_t *buckets[QED_TOPIC_BUCKETS];
} qed_topic_table_t;

static inline uint64_t fnv1a_hash(const char *s, size_t len) {
    uint64_t h = 14695981039346656037ULL;
    for (size_t i = 0; i < len; i++) {
        h ^= (uint8_t)s[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static bool topic_table_add(qed_topic_table_t *tbl, qed_client_conn_t *conn,
                            uint32_t sub_id, const char *topic, size_t topic_len) {
    uint64_t h = fnv1a_hash(topic, topic_len);
    size_t b = (size_t)(h & (QED_TOPIC_BUCKETS - 1));
    qed_topic_entry_t *e = (qed_topic_entry_t *)malloc(sizeof(qed_topic_entry_t));
    if (!e) return false;
    e->topic = (char *)malloc(topic_len + 1);
    if (!e->topic) { free(e); return false; }
    memcpy(e->topic, topic, topic_len + 1);
    e->conn = conn;
    e->sub_id = sub_id;
    e->topic_len = topic_len;
    e->hash = h;
    e->next = tbl->buckets[b];
    tbl->buckets[b] = e;
    return true;
}

static void topic_table_remove_sub(qed_topic_table_t *tbl, qed_client_conn_t *conn,
                                   uint32_t sub_id, const char *topic, size_t topic_len) {
    uint64_t h = fnv1a_hash(topic, topic_len);
    size_t b = (size_t)(h & (QED_TOPIC_BUCKETS - 1));
    qed_topic_entry_t **pp = &tbl->buckets[b];
    while (*pp) {
        qed_topic_entry_t *cur = *pp;
        if (cur->conn == conn && cur->sub_id == sub_id &&
            cur->hash == h && cur->topic_len == topic_len &&
            memcmp(cur->topic, topic, topic_len) == 0) {
            *pp = cur->next;
            free(cur->topic);
            free(cur);
            return;
        }
        pp = &cur->next;
    }
}

static void topic_table_free(qed_topic_table_t *tbl) {
    for (size_t b = 0; b < QED_TOPIC_BUCKETS; b++) {
        qed_topic_entry_t *cur = tbl->buckets[b];
        while (cur) {
            qed_topic_entry_t *nxt = cur->next;
            free(cur->topic);
            free(cur);
            cur = nxt;
        }
        tbl->buckets[b] = NULL;
    }
}

static bool ws_send_raw_frame(
    qed_client_conn_t *c, uint8_t opcode,
    const uint8_t *extra, size_t extra_len,
    const uint8_t *payload, size_t payload_len)
{
    uint64_t total_len = (uint64_t)extra_len + (uint64_t)payload_len;
    uint8_t hdr[24];
    size_t hlen = 0;
    hdr[hlen++] = (uint8_t)(0x80U | (opcode & 0x0FU));
    if (total_len <= 125ULL) {
        hdr[hlen++] = (uint8_t)total_len;
    } else if (total_len <= 65535ULL) {
        hdr[hlen++] = 126;
        hdr[hlen++] = (uint8_t)((total_len >> 8) & 0xFFU);
        hdr[hlen++] = (uint8_t)(total_len & 0xFFU);
    } else {
        hdr[hlen++] = 127;
        for (int shift = 56; shift >= 0; shift -= 8) {
            hdr[hlen++] = (uint8_t)((total_len >> shift) & 0xFFU);
        }
    }
    if (extra_len > 0 && extra != NULL) {
        if (hlen + extra_len > sizeof(hdr)) return false;
        memcpy(hdr + hlen, extra, extra_len);
        hlen += extra_len;
    }
    return queue_or_writev(c, (const char *)hdr, hlen, payload, payload_len);
}

static bool ws_send_mux_frame(
    qed_client_conn_t *c, uint8_t mux_op, uint32_t sub_id,
    const uint8_t *payload, size_t payload_len)
{
    uint8_t mh[5];
    mh[0] = mux_op;
    mh[1] = (uint8_t)((sub_id >> 24) & 0xFFU);
    mh[2] = (uint8_t)((sub_id >> 16) & 0xFFU);
    mh[3] = (uint8_t)((sub_id >> 8) & 0xFFU);
    mh[4] = (uint8_t)(sub_id & 0xFFU);
    return ws_send_raw_frame(c, 0x02, mh, 5, payload, payload_len);
}

static void ws_send_close(qed_client_conn_t *c, uint16_t code) {
    uint8_t body[2];
    body[0] = (uint8_t)((code >> 8) & 0xFFU);
    body[1] = (uint8_t)(code & 0xFFU);
    (void)ws_send_raw_frame(c, 0x08, body, 2, NULL, 0);
    c->close_after_tx = true;
}

static void topic_table_broadcast(qed_topic_table_t *tbl, const qed_ws_bcast_msg_t *msg) {
    uint64_t h = fnv1a_hash(msg->topic, msg->topic_len);
    size_t b = (size_t)(h & (QED_TOPIC_BUCKETS - 1));
    for (qed_topic_entry_t *e = tbl->buckets[b]; e != NULL; e = e->next) {
        if (e->hash == h && e->topic_len == msg->topic_len &&
            memcmp(e->topic, msg->topic, msg->topic_len) == 0) {
            if (!e->conn->close_after_tx && e->conn->is_ws) {
                if (!ws_send_mux_frame(e->conn, 0x12, e->sub_id, msg->payload, msg->payload_len)) {
                    e->conn->close_after_tx = true;
                    update_loop_write_interest(e->conn, true);
                }
            }
        }
    }
}

static char *ws_build_topic_key(const char *channel, const uint8_t *params, size_t params_len, size_t *out_len) {
    size_t ch_len = strlen(channel);
    size_t total = ch_len + 1 + params_len * 2;
    char *buf = (char *)malloc(total + 1);
    if (!buf) return NULL;
    memcpy(buf, channel, ch_len);
    buf[ch_len] = ':';
    static const char kHex[] = "0123456789abcdef";
    for (size_t i = 0; i < params_len; i++) {
        buf[ch_len + 1 + 2 * i]     = kHex[(params[i] >> 4) & 0x0F];
        buf[ch_len + 1 + 2 * i + 1] = kHex[params[i] & 0x0F];
    }
    buf[total] = '\0';
    if (out_len) *out_len = total;
    return buf;
}

static void ws_free_sub(qed_ws_sub_t *s) {
    free(s->channel);
    free(s->params);
    free(s->topic);
    s->channel = NULL;
    s->params = NULL;
    s->topic = NULL;
}

static bool ws_origin_allowed(const char *origin, const char *host) {
    if (!origin || *origin == '\0') return true;
    const char *allowed = getenv("QED_WS_ALLOWED_ORIGINS");
    if (allowed && *allowed != '\0') {
        if (strcmp(allowed, "*") == 0) return true;
        const char *p = allowed;
        size_t olen = strlen(origin);
        while (*p) {
            while (*p == ' ' || *p == ',') p++;
            const char *start = p;
            while (*p && *p != ',') p++;
            const char *end = p;
            while (end > start && end[-1] == ' ') end--;
            if ((size_t)(end - start) == olen && strncasecmp(start, origin, olen) == 0) return true;
        }
        return false;
    }
    if (!host || *host == '\0') return false;
    const char *o_host = NULL;
    if (strncasecmp(origin, "http://", 7) == 0) o_host = origin + 7;
    else if (strncasecmp(origin, "https://", 8) == 0) o_host = origin + 8;
    else return false;
    size_t o_len = strlen(o_host);
    while (o_len > 0 && o_host[o_len - 1] == '/') o_len--;
    if (o_len == 0 || memchr(o_host, '/', o_len) != NULL) return false;
    return strlen(host) == o_len && strncasecmp(o_host, host, o_len) == 0;
}

static bool ws_compute_accept(const char *sec_key, char out_b64[36]) {
    static const char kGuid[] = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
    size_t klen = strlen(sec_key);
    if (klen == 0 || klen > 64) return false;
    char combined[128];
    memcpy(combined, sec_key, klen);
    memcpy(combined + klen, kGuid, sizeof(kGuid) - 1);
    uint8_t digest[20];
    unsigned int dlen = 0;
    if (EVP_Digest(combined, klen + sizeof(kGuid) - 1, digest, &dlen, EVP_sha1(), NULL) != 1 || dlen != 20) {
        return false;
    }
    int n = EVP_EncodeBlock((unsigned char *)out_b64, digest, 20);
    if (n <= 0 || n >= 36) return false;
    out_b64[n] = '\0';
    return true;
}

typedef struct {
    uint32_t worker_idx;
    uint16_t port;
    int initial_listen_fd;
    const char *static_dir;
    uint8_t dev_mode;
    lean_object *handler;
    const char *ws_path;
    lean_object *ws_upgrade;
    lean_object *ws_action;
    qed_worker_inbox_t *inbox;
    pthread_t tid;
    bool started;
} qed_worker_arg_t;

static void ws_send_mux_err(qed_client_conn_t *c, uint32_t sub_id, const char *msg) {
    (void)ws_send_mux_frame(c, 0x13, sub_id, (const uint8_t *)msg, strlen(msg));
}

static lean_object *ws_call_action(
    const qed_worker_arg_t *arg, qed_client_conn_t *c, uint8_t kind,
    const char *channel, const uint8_t *params, size_t params_len,
    const uint8_t *payload, size_t payload_len)
{
    lean_inc(arg->ws_action);
    lean_inc(c->ws_ctx);
    return lean_apply_6(
        arg->ws_action,
        c->ws_ctx,
        lean_box(kind),
        lean_mk_string(channel),
        mk_byte_array_copy(params, params_len),
        mk_byte_array_copy(payload, payload_len),
        lean_box(0));
}

static void ws_invoke_leave(const qed_worker_arg_t *arg, qed_client_conn_t *c, const qed_ws_sub_t *sub) {
    if (!arg || !arg->ws_action || !c->ws_ctx || !sub->channel) return;
    lean_dec_ref(ws_call_action(arg, c, 3, sub->channel, sub->params, sub->params_len, NULL, 0));
}

static void ws_unsub_by_id(qed_client_conn_t *c, uint32_t sub_id,
                           const qed_worker_arg_t *arg, qed_topic_table_t *tbl) {
    for (size_t i = 0; i < c->sub_cnt; i++) {
        if (c->subs[i].sub_id == sub_id) {
            qed_ws_sub_t sub = c->subs[i];
            c->subs[i] = c->subs[c->sub_cnt - 1];
            c->sub_cnt--;
            topic_table_remove_sub(tbl, c, sub.sub_id, sub.topic, sub.topic_len);
            ws_invoke_leave(arg, c, &sub);
            ws_free_sub(&sub);
            return;
        }
    }
}

static void handle_ws_mux_msg(
    qed_client_conn_t *c, const uint8_t *data, size_t len,
    const qed_worker_arg_t *arg, qed_topic_table_t *tbl)
{
    if (len < 5 || !arg->ws_action || !c->ws_ctx) return;
    uint8_t op = data[0];
    uint32_t sid = ((uint32_t)data[1] << 24) | ((uint32_t)data[2] << 16) |
                   ((uint32_t)data[3] << 8)  | (uint32_t)data[4];
    const uint8_t *rest = data + 5;
    size_t rest_len = len - 5;

    if (op == 0x01) { /* SUB */
        if (rest_len < 2) { ws_send_mux_err(c, sid, "malformed subscribe frame"); return; }
        uint16_t ch_len = (uint16_t)(((uint16_t)rest[0] << 8) | (uint16_t)rest[1]);
        if ((size_t)ch_len + 2 > rest_len || ch_len == 0 || ch_len > 256) {
            ws_send_mux_err(c, sid, "invalid channel name length");
            return;
        }
        char ch_buf[260];
        memcpy(ch_buf, rest + 2, ch_len);
        ch_buf[ch_len] = '\0';
        const uint8_t *params = rest + 2 + ch_len;
        size_t params_len = rest_len - 2 - ch_len;

        ws_unsub_by_id(c, sid, arg, tbl);
        if (c->sub_cnt >= QED_MAX_WS_SUBS_PER_CONN) {
            ws_send_mux_err(c, sid, "too many subscriptions on connection");
            return;
        }

        lean_object *io_res = ws_call_action(arg, c, 1, ch_buf, params, params_len, NULL, 0);
        if (lean_io_result_is_ok(io_res)) {
            lean_object *exc = lean_io_result_get_value(io_res);
            if (lean_obj_tag(exc) == 1) { /* Except.ok snapshotBytes */
                lean_object *snap_ba = lean_ctor_get(exc, 0);
                size_t tlen = 0;
                char *topic = ws_build_topic_key(ch_buf, params, params_len, &tlen);
                if (!topic) {
                    lean_dec_ref(io_res);
                    ws_send_mux_err(c, sid, "out of memory");
                    return;
                }
                if (c->sub_cnt == c->sub_cap) {
                    size_t ncap = c->sub_cap ? c->sub_cap * 2 : 4;
                    qed_ws_sub_t *ns = (qed_ws_sub_t *)realloc(c->subs, ncap * sizeof(qed_ws_sub_t));
                    if (!ns) { free(topic); lean_dec_ref(io_res); return; }
                    c->subs = ns;
                    c->sub_cap = ncap;
                }
                qed_ws_sub_t *sub = &c->subs[c->sub_cnt];
                memset(sub, 0, sizeof(*sub));
                sub->sub_id = sid;
                sub->channel = strdup(ch_buf);
                sub->params = params_len > 0 ? (uint8_t *)malloc(params_len) : NULL;
                if (params_len > 0 && sub->params) memcpy(sub->params, params, params_len);
                sub->params_len = params_len;
                sub->topic = topic;
                sub->topic_len = tlen;
                if (!sub->channel || (params_len > 0 && !sub->params) ||
                    !topic_table_add(tbl, c, sid, topic, tlen)) {
                    ws_free_sub(sub);
                    lean_dec_ref(io_res);
                    return;
                }
                c->sub_cnt++;
                (void)ws_send_mux_frame(c, 0x11, sid, lean_sarray_cptr(snap_ba), lean_sarray_size(snap_ba));
            } else { /* Except.error errMsg */
                ws_send_mux_err(c, sid, lean_string_cstr(lean_ctor_get(exc, 0)));
            }
        }
        lean_dec_ref(io_res);
    } else if (op == 0x02) { /* UNSUB */
        ws_unsub_by_id(c, sid, arg, tbl);
    } else if (op == 0x03) { /* SEND */
        for (size_t i = 0; i < c->sub_cnt; i++) {
            if (c->subs[i].sub_id == sid) {
                lean_dec_ref(ws_call_action(arg, c, 2, c->subs[i].channel,
                    c->subs[i].params, c->subs[i].params_len, rest, rest_len));
                return;
            }
        }
    }
}

/* Returns: 1 = ok, 0 = need more bytes, -1 = close connection */
static int process_ws_frames(qed_client_conn_t *c, const qed_worker_arg_t *arg, qed_topic_table_t *tbl) {
    for (;;) {
        if (c->close_after_tx) return -1;
        if (c->rx.len < 2) return 0;
        const uint8_t *p = c->rx.data;
        uint8_t b0 = p[0], b1 = p[1];
        bool fin = (b0 & 0x80U) != 0;
        uint8_t rsv = (b0 >> 4) & 0x07U;
        uint8_t opcode = b0 & 0x0FU;
        bool masked = (b1 & 0x80U) != 0;
        uint64_t plen = (uint64_t)(b1 & 0x7FU);
        if (rsv != 0 || !masked) {
            ws_send_close(c, 1002);
            return -1;
        }
        size_t off = 2;
        if (plen == 126) {
            if (c->rx.len < 4) return 0;
            plen = ((uint64_t)p[2] << 8) | (uint64_t)p[3];
            off = 4;
        } else if (plen == 127) {
            if (c->rx.len < 10) return 0;
            if ((p[2] & 0x80U) != 0) { ws_send_close(c, 1002); return -1; }
            plen = 0;
            for (int i = 0; i < 8; i++) plen = (plen << 8) | (uint64_t)p[2 + i];
            off = 10;
        }
        if ((opcode >= 0x08 && (plen > 125 || !fin)) || plen > QED_MAX_WS_MSG_BYTES) {
            ws_send_close(c, plen > QED_MAX_WS_MSG_BYTES ? 1009 : 1002);
            return -1;
        }
        size_t frame_total = off + 4 + (size_t)plen;
        if (c->rx.len < frame_total) return 0;

        uint8_t mask[4];
        memcpy(mask, p + off, 4);
        uint8_t *payload = c->rx.data + off + 4;
        for (size_t i = 0; i < (size_t)plen; i++) payload[i] ^= mask[i & 3U];
        c->last_active = time(NULL);

        if (opcode == 0x08) { /* Close */
            ws_send_close(c, 1000);
            buf_consume(&c->rx, frame_total);
            return -1;
        } else if (opcode == 0x09) { /* Ping -> Pong */
            (void)ws_send_raw_frame(c, 0x0A, NULL, 0, payload, (size_t)plen);
        } else if (opcode == 0x0A) { /* Pong */
            /* last_active already updated */
        } else if (opcode == 0x01 || opcode == 0x02) {
            if (c->ws_in_frag) { ws_send_close(c, 1002); return -1; }
            if (fin) {
                if (opcode == 0x02) handle_ws_mux_msg(c, payload, (size_t)plen, arg, tbl);
            } else {
                c->ws_in_frag = true;
                c->ws_frag_op = opcode;
                c->ws_frag.len = 0;
                if (!buf_append(&c->ws_frag, payload, (size_t)plen)) { ws_send_close(c, 1011); return -1; }
            }
        } else if (opcode == 0x00) { /* Continuation */
            if (!c->ws_in_frag) { ws_send_close(c, 1002); return -1; }
            if (c->ws_frag.len + (size_t)plen > QED_MAX_WS_MSG_BYTES) { ws_send_close(c, 1009); return -1; }
            if (!buf_append(&c->ws_frag, payload, (size_t)plen)) { ws_send_close(c, 1011); return -1; }
            if (fin) {
                c->ws_in_frag = false;
                if (c->ws_frag_op == 0x02) {
                    handle_ws_mux_msg(c, c->ws_frag.data, c->ws_frag.len, arg, tbl);
                }
                c->ws_frag.len = 0;
            }
        } else {
            ws_send_close(c, 1002);
            return -1;
        }

        buf_consume(&c->rx, frame_total);
        if (c->rx.len == 0) return 1;
    }
}

static void drain_worker_inbox(qed_worker_inbox_t *inbox, qed_topic_table_t *tbl) {
    if (!inbox) return;
#ifdef __linux__
    if (inbox->wake_fd >= 0) {
        uint64_t val = 0;
        while (read(inbox->wake_fd, &val, sizeof(val)) > 0) {}
    }
#endif
    pthread_mutex_lock(&inbox->mu);
    qed_ws_bcast_node_t *list = inbox->head;
    inbox->head = NULL;
    inbox->tail = NULL;
    pthread_mutex_unlock(&inbox->mu);

    while (list) {
        qed_ws_bcast_node_t *nxt = list->next;
        if (tbl) topic_table_broadcast(tbl, list->msg);
        bcast_msg_unref(list->msg);
        free(list);
        list = nxt;
    }
}

/* Returns: 1 = continue keep-alive, 0 = need more bytes, -1 = close connection */
static int process_buffered_requests(
    qed_client_conn_t *c,
    const qed_worker_arg_t *arg,
    qed_topic_table_t *tbl)
{
    for (;;) {
        if (c->is_ws) return process_ws_frames(c, arg, tbl);

        ssize_t hdr_end = find_crlfcrlf(c->rx.data, c->rx.len);
        if (hdr_end < 0) {
            return (c->rx.len > QED_MAX_REQ_HDR_BYTES) ? reject_request(c, 431, "request headers too large") : 0;
        }

        size_t hdr_bytes = (size_t)hdr_end + 4;
        if ((size_t)hdr_end > QED_MAX_REQ_HDR_BYTES) return reject_request(c, 431, "request headers too large");
        if (memchr(c->rx.data, '\0', (size_t)hdr_end) != NULL) return reject_request(c, 400, "invalid NUL byte in headers");

        char hdr_copy[QED_MAX_REQ_HDR_BYTES + 4];
        memcpy(hdr_copy, c->rx.data, (size_t)hdr_end);
        hdr_copy[hdr_end] = '\0';

        char *cursor = hdr_copy;
        char *hdr_limit = hdr_copy + hdr_end;
        bool bare_crlf = false;
        char *req_line = next_crlf_line(&cursor, hdr_limit, &bare_crlf);
        if (!req_line || bare_crlf || *req_line == '\0') return reject_request(c, 400, "malformed request line");

        char *sp1 = strchr(req_line, ' ');
        if (!sp1) return reject_request(c, 400, "malformed request line");
        *sp1 = '\0';
        char *method = req_line;
        char *target = sp1 + 1;
        char *sp2 = strchr(target, ' ');
        if (!sp2) return reject_request(c, 400, "malformed request line");
        *sp2 = '\0';
        char *http_ver = sp2 + 1;
        if (*method == '\0' || *target == '\0' || strchr(http_ver, ' ') != NULL) {
            return reject_request(c, 400, "malformed request line");
        }
        bool is_http_11 = (strcmp(http_ver, "HTTP/1.1") == 0);
        if (!is_http_11 && strcmp(http_ver, "HTTP/1.0") != 0) {
            return reject_request(c, 400, "unsupported HTTP version");
        }

        bool keep_alive = is_http_11;
        bool has_content_len = false;
        size_t content_len = 0;
        qed_hdr_pair_t parsed_hdrs[96];
        size_t parsed_cnt = 0;
        const char *hdr_upgrade = NULL;
        const char *hdr_conn = NULL;
        const char *hdr_ws_key = NULL;
        const char *hdr_ws_ver = NULL;
        const char *hdr_origin = NULL;
        const char *hdr_host = NULL;

        char *hline = NULL, *val = NULL;
        while ((hline = next_crlf_line(&cursor, hdr_limit, &bare_crlf)) != NULL) {
            if (!split_header_kv(hline, &val)) return reject_request(c, 400, "malformed header");
            if (strcasecmp(hline, "Transfer-Encoding") == 0) {
                return reject_request(c, 501, "Transfer-Encoding not supported");
            }
            if (strcasecmp(hline, "Content-Length") == 0) {
                uint64_t cl_u64 = 0;
                if (!parse_strict_u64(val, &cl_u64)) return reject_request(c, 400, "invalid Content-Length");
                if (has_content_len && cl_u64 != (uint64_t)content_len) {
                    return reject_request(c, 400, "conflicting Content-Length headers");
                }
                if (cl_u64 > QED_MAX_REQ_BODY_BYTES) return reject_request(c, 413, "payload too large");
                has_content_len = true;
                content_len = (size_t)cl_u64;
            } else if (strcasecmp(hline, "Connection") == 0) {
                hdr_conn = val;
                if (strcasestr(val, "close") != NULL) keep_alive = false;
                else if (strcasestr(val, "keep-alive") != NULL) keep_alive = true;
            } else if (strcasecmp(hline, "Upgrade") == 0) {
                hdr_upgrade = val;
            } else if (strcasecmp(hline, "Sec-WebSocket-Key") == 0) {
                hdr_ws_key = val;
            } else if (strcasecmp(hline, "Sec-WebSocket-Version") == 0) {
                hdr_ws_ver = val;
            } else if (strcasecmp(hline, "Origin") == 0) {
                hdr_origin = val;
            } else if (strcasecmp(hline, "Host") == 0) {
                hdr_host = val;
            }
            if (parsed_cnt < 96) {
                parsed_hdrs[parsed_cnt].key = hline;
                parsed_hdrs[parsed_cnt].val = val;
                parsed_cnt++;
            }
        }
        if (bare_crlf) return reject_request(c, 400, "bare CR/LF in headers");

        /* RFC 6455 WebSocket Upgrade on `/_qed/ws/<Server>` */
        if (arg->ws_path && arg->ws_path[0] != '\0' && arg->ws_upgrade && arg->ws_action &&
            strcmp(method, "GET") == 0 && hdr_upgrade && strcasecmp(hdr_upgrade, "websocket") == 0) {
            const char *q = strchr(target, '?');
            size_t tlen = q ? (size_t)(q - target) : strlen(target);
            if (strlen(arg->ws_path) == tlen && memcmp(target, arg->ws_path, tlen) == 0) {
                if (!is_http_11 || !hdr_conn || strcasestr(hdr_conn, "upgrade") == NULL ||
                    !hdr_ws_ver || strcmp(hdr_ws_ver, "13") != 0 || !hdr_ws_key) {
                    return reject_request(c, 400, "invalid WebSocket upgrade headers");
                }
                if (!ws_origin_allowed(hdr_origin, hdr_host)) {
                    return reject_request(c, 403, "cross-origin WebSocket upgrade rejected");
                }
                char accept_b64[36];
                if (!ws_compute_accept(hdr_ws_key, accept_b64)) {
                    return reject_request(c, 400, "invalid Sec-WebSocket-Key");
                }
                lean_inc(arg->ws_upgrade);
                lean_object *ctx_res = lean_apply_3(
                    arg->ws_upgrade,
                    mk_lean_headers(parsed_hdrs, parsed_cnt),
                    lean_mk_string(c->ip),
                    lean_box(0));
                if (!lean_io_result_is_ok(ctx_res)) {
                    lean_dec_ref(ctx_res);
                    return reject_request(c, 500, "WebSocket auth context error");
                }
                lean_object *ws_ctx = lean_io_result_get_value(ctx_res);
                lean_inc(ws_ctx);
                lean_dec_ref(ctx_res);

                char up_hdr[256];
                int ulen = snprintf(
                    up_hdr, sizeof(up_hdr),
                    "HTTP/1.1 101 Switching Protocols\r\n"
                    "Upgrade: websocket\r\n"
                    "Connection: Upgrade\r\n"
                    "Sec-WebSocket-Accept: %s\r\n\r\n",
                    accept_b64);
                if (ulen <= 0 || (size_t)ulen >= sizeof(up_hdr) ||
                    !queue_or_writev(c, up_hdr, (size_t)ulen, NULL, 0)) {
                    lean_dec(ws_ctx);
                    return -1;
                }
                c->ws_ctx = ws_ctx;
                c->is_ws = true;
                c->last_active = time(NULL);
                c->last_ping_sent = c->last_active;
                buf_consume(&c->rx, hdr_bytes);
                if (c->rx.len == 0) return 1;
                continue;
            }
        }

        size_t total_needed = hdr_bytes + content_len;
        if (c->rx.len < total_needed) return 0;

        bool static_write_ok = true;
        if (try_serve_static_c(c, arg->static_dir, arg->dev_mode, method, target, keep_alive, &static_write_ok)) {
            if (!static_write_ok) return -1;
        } else {
            lean_inc(arg->handler);
            lean_object *io_res = lean_apply_6(
                arg->handler,
                lean_mk_string(method),
                lean_mk_string(target),
                mk_lean_headers(parsed_hdrs, parsed_cnt),
                mk_byte_array_copy(c->rx.data + hdr_bytes, content_len),
                lean_mk_string(c->ip),
                lean_box(0));

            if (lean_io_result_is_ok(io_res)) {
                lean_object *tup1 = lean_io_result_get_value(io_res);
                size_t status = lean_usize_of_nat(lean_ctor_get(tup1, 0));
                lean_object *tup2 = lean_ctor_get(tup1, 1);
                const char *ctype = lean_string_cstr(lean_ctor_get(tup2, 0));
                lean_object *resp_ba = lean_ctor_get(tup2, 1);
                int status_i = (status >= 100 && status <= 599) ? (int)status : 500;
                bool sent = send_http_response(
                    c, status_i, ctype,
                    lean_sarray_cptr(resp_ba), lean_sarray_size(resp_ba),
                    strcmp(method, "HEAD") == 0, keep_alive, false);
                lean_dec_ref(io_res);
                if (!sent) return -1;
            } else {
                lean_dec_ref(io_res);
                return reject_request(c, 500, "internal server error");
            }
        }

        buf_consume(&c->rx, total_needed);
        if (!keep_alive) {
            c->close_after_tx = true;
            return -1;
        }
        if (c->rx.len == 0) return 1;
    }
}

static void close_client_conn(
    qed_client_conn_t **conn_head, uint32_t *conn_cnt,
    qed_client_conn_t *c, const qed_worker_arg_t *arg, qed_topic_table_t *tbl)
{
    if (!c) return;
    if (c->is_ws) {
        for (size_t i = 0; i < c->sub_cnt; i++) {
            if (tbl && c->subs[i].topic) {
                topic_table_remove_sub(tbl, c, c->subs[i].sub_id, c->subs[i].topic, c->subs[i].topic_len);
            }
            ws_invoke_leave(arg, c, &c->subs[i]);
            ws_free_sub(&c->subs[i]);
        }
        free(c->subs);
        c->subs = NULL;
        c->sub_cnt = 0;
        c->sub_cap = 0;
        buf_free(&c->ws_frag);
        if (c->ws_ctx) {
            lean_dec(c->ws_ctx);
            c->ws_ctx = NULL;
        }
    }
    if (c->prev) c->prev->next = c->next;
    else if (conn_head && *conn_head == c) *conn_head = c->next;
    if (c->next) c->next->prev = c->prev;
    if (conn_cnt && *conn_cnt > 0) (*conn_cnt)--;

    if (c->has_loop) {
#ifdef __linux__
        epoll_ctl(c->loop_fd, EPOLL_CTL_DEL, c->fd, NULL);
#elif defined(__APPLE__)
        struct kevent kev[2];
        EV_SET(&kev[0], c->fd, EVFILT_READ, EV_DELETE, 0, 0, NULL);
        EV_SET(&kev[1], c->fd, EVFILT_WRITE, EV_DELETE, 0, 0, NULL);
        kevent(c->loop_fd, kev, 2, NULL, 0, NULL);
#endif
    }
    close(c->fd);
    buf_free(&c->rx);
    buf_free(&c->tx);
    free(c);
}

static qed_client_conn_t *accept_one_client(int listen_fd) {
    struct sockaddr_in cli_addr;
    socklen_t cli_len = sizeof(cli_addr);
#ifdef __linux__
    int cfd = accept4(listen_fd, (struct sockaddr *)&cli_addr, &cli_len, SOCK_NONBLOCK | SOCK_CLOEXEC);
    if (cfd < 0) return NULL;
#else
    int cfd = accept(listen_fd, (struct sockaddr *)&cli_addr, &cli_len);
    if (cfd < 0) return NULL;
    set_nonblocking(cfd);
#endif
    int one = 1;
    setsockopt(cfd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    qed_client_conn_t *conn = (qed_client_conn_t *)calloc(1, sizeof(qed_client_conn_t));
    if (!conn) { close(cfd); return NULL; }
    conn->fd = cfd;
    conn->loop_fd = -1;
    conn->last_active = time(NULL);
    inet_ntop(AF_INET, &cli_addr.sin_addr, conn->ip, sizeof(conn->ip));
    if (!buf_init(&conn->rx, 2048)) {
        close(cfd);
        free(conn);
        return NULL;
    }
    return conn;
}

static void handle_client_io(
    qed_client_conn_t **conn_head,
    uint32_t *conn_cnt,
    qed_client_conn_t *conn,
    bool peer_eof,
    bool fatal_err,
    const qed_worker_arg_t *arg,
    qed_topic_table_t *tbl)
{
    if (peer_eof) conn->peer_eof = true;
    if (fatal_err) conn->peer_eof = true;

    bool read_err = false;
    if (!conn->close_after_tx) {
        for (;;) {
            uint8_t tmp[8192];
            ssize_t n = recv(conn->fd, tmp, sizeof(tmp), 0);
            if (n > 0) {
                conn->last_active = time(NULL);
                size_t rx_cap_limit = conn->is_ws
                    ? (QED_MAX_WS_MSG_BYTES + 65536U)
                    : (QED_MAX_REQ_HDR_BYTES + QED_MAX_REQ_BODY_BYTES);
                if ((size_t)n > rx_cap_limit - conn->rx.len) {
                    if (conn->is_ws) ws_send_close(conn, 1009);
                    else (void)reject_request(conn, 413, "payload too large");
                    break;
                }
                if (!buf_append(&conn->rx, tmp, (size_t)n)) {
                    read_err = true;
                    break;
                }
                if (!conn->is_ws && conn->rx.len > QED_MAX_REQ_HDR_BYTES &&
                    find_crlfcrlf(conn->rx.data, conn->rx.len) < 0) {
                    (void)reject_request(conn, 431, "request headers too large");
                    break;
                }
            } else if (n == 0) {
                conn->peer_eof = true;
                break;
            } else {
                if (errno == EINTR) continue;
                if (errno == EAGAIN || errno == EWOULDBLOCK) break;
                read_err = true;
                break;
            }
        }
    }

    if (read_err) {
        close_client_conn(conn_head, conn_cnt, conn, arg, tbl);
        return;
    }

    if (!conn->close_after_tx && conn->rx.len > 0) {
        if (process_buffered_requests(conn, arg, tbl) < 0) {
            conn->close_after_tx = true;
        }
    }

    if (conn->close_after_tx || conn->peer_eof) {
        if (conn->tx.len == 0) {
            close_client_conn(conn_head, conn_cnt, conn, arg, tbl);
        } else {
            conn->close_after_tx = true;
            update_loop_write_interest(conn, true);
        }
    }
}

static void sweep_idle_conns(
    qed_client_conn_t **conn_head, uint32_t *conn_cnt,
    time_t *last_sweep, const qed_worker_arg_t *arg, qed_topic_table_t *tbl)
{
    time_t now = time(NULL);
    if (now - *last_sweep < 5) return;
    *last_sweep = now;
    qed_client_conn_t *c = *conn_head;
    while (c != NULL) {
        qed_client_conn_t *nxt = c->next;
        if (c->is_ws) {
            if (now - c->last_active > QED_WS_DEAD_TIMEOUT_SEC) {
                close_client_conn(conn_head, conn_cnt, c, arg, tbl);
            } else if (now - c->last_ping_sent >= QED_WS_PING_INTERVAL_SEC && !c->close_after_tx) {
                c->last_ping_sent = now;
                if (!ws_send_raw_frame(c, 0x09, NULL, 0, NULL, 0)) {
                    close_client_conn(conn_head, conn_cnt, c, arg, tbl);
                }
            }
        } else if (now - c->last_active > QED_CONN_IDLE_TIMEOUT_SEC) {
            close_client_conn(conn_head, conn_cnt, c, arg, tbl);
        }
        c = nxt;
    }
}

static void register_accepted_conns(int listen_fd, int loop_fd, qed_client_conn_t **conn_head, uint32_t *conn_cnt) {
    qed_client_conn_t *conn;
    while ((conn = accept_one_client(listen_fd)) != NULL) {
        bool added = false;
        if (*conn_cnt < QED_MAX_WORKER_CONNS) {
#ifdef __linux__
            struct epoll_event cev = { .events = EPOLLIN | EPOLLRDHUP, .data.ptr = conn };
            added = (epoll_ctl(loop_fd, EPOLL_CTL_ADD, conn->fd, &cev) == 0);
#elif defined(__APPLE__)
            struct kevent kev;
            EV_SET(&kev, conn->fd, EVFILT_READ, EV_ADD | EV_ENABLE, 0, 0, conn);
            added = (kevent(loop_fd, &kev, 1, NULL, 0, NULL) == 0);
#endif
        }
        if (!added) {
            close(conn->fd);
            buf_free(&conn->rx);
            free(conn);
            continue;
        }
        conn->loop_fd = loop_fd;
        conn->has_loop = true;
        conn->rx_armed = true;
        conn->next = *conn_head;
        if (*conn_head) (*conn_head)->prev = conn;
        *conn_head = conn;
        (*conn_cnt)++;
    }
}

static bool handle_client_writable(
    qed_client_conn_t **conn_head, uint32_t *conn_cnt,
    qed_client_conn_t *conn, const qed_worker_arg_t *arg, qed_topic_table_t *tbl)
{
    if (!flush_client_tx(conn) ||
        (conn->tx.len == 0 && (conn->close_after_tx || (conn->peer_eof && conn->rx.len == 0)))) {
        close_client_conn(conn_head, conn_cnt, conn, arg, tbl);
        return false;
    }
    return true;
}

static void *worker_thread_main(void *raw_arg) {
    qed_worker_arg_t *arg = (qed_worker_arg_t *)raw_arg;
    if (arg->worker_idx > 0) lean_initialize_thread();

    int listen_fd = arg->initial_listen_fd >= 0 ? arg->initial_listen_fd : create_reuseport_listener(arg->port, true);
    if (listen_fd < 0) {
        if (arg->worker_idx > 0) lean_finalize_thread();
        return NULL;
    }

    qed_client_conn_t *conn_head = NULL;
    uint32_t conn_cnt = 0;
    time_t last_sweep = time(NULL);
    qed_topic_table_t topic_tbl;
    memset(&topic_tbl, 0, sizeof(topic_tbl));

#ifdef __linux__
    int epfd = epoll_create1(EPOLL_CLOEXEC);
    if (epfd >= 0) {
        if (arg->inbox) {
            pthread_mutex_lock(&arg->inbox->mu);
            arg->inbox->loop_fd = epfd;
            int wfd = arg->inbox->wake_fd;
            pthread_mutex_unlock(&arg->inbox->mu);
            if (wfd >= 0) {
                struct epoll_event wev = { .events = EPOLLIN, .data.ptr = (void *)(uintptr_t)1 };
                epoll_ctl(epfd, EPOLL_CTL_ADD, wfd, &wev);
            }
        }
        struct epoll_event ev = { .events = EPOLLIN, .data.ptr = NULL };
        epoll_ctl(epfd, EPOLL_CTL_ADD, listen_fd, &ev);
        struct epoll_event events[128];
        while (!g_stop_server) {
            int nfds = epoll_wait(epfd, events, 128, 200);
            if (nfds < 0) { if (errno == EINTR) continue; break; }
            for (int i = 0; i < nfds; i++) {
                if (events[i].data.ptr == NULL) {
                    register_accepted_conns(listen_fd, epfd, &conn_head, &conn_cnt);
                } else if (events[i].data.ptr == (void *)(uintptr_t)1) {
                    drain_worker_inbox(arg->inbox, &topic_tbl);
                } else {
                    qed_client_conn_t *conn = (qed_client_conn_t *)events[i].data.ptr;
                    uint32_t evs = events[i].events;
                    if ((evs & EPOLLOUT) && !handle_client_writable(&conn_head, &conn_cnt, conn, arg, &topic_tbl)) continue;
                    if (evs & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) {
                        handle_client_io(&conn_head, &conn_cnt, conn,
                                         (evs & (EPOLLRDHUP | EPOLLHUP)) != 0,
                                         (evs & EPOLLERR) != 0, arg, &topic_tbl);
                    }
                }
            }
            drain_worker_inbox(arg->inbox, &topic_tbl);
            sweep_idle_conns(&conn_head, &conn_cnt, &last_sweep, arg, &topic_tbl);
        }
        while (conn_head != NULL) close_client_conn(&conn_head, &conn_cnt, conn_head, arg, &topic_tbl);
        drain_worker_inbox(arg->inbox, NULL);
        close(epfd);
    }
#elif defined(__APPLE__)
    int kq = kqueue();
    if (kq >= 0) {
        if (arg->inbox) {
            pthread_mutex_lock(&arg->inbox->mu);
            arg->inbox->loop_fd = kq;
            pthread_mutex_unlock(&arg->inbox->mu);
            struct kevent uev;
            EV_SET(&uev, 1, EVFILT_USER, EV_ADD | EV_CLEAR, 0, 0, (void *)(uintptr_t)1);
            kevent(kq, &uev, 1, NULL, 0, NULL);
        }
        struct kevent kev;
        EV_SET(&kev, listen_fd, EVFILT_READ, EV_ADD | EV_ENABLE, 0, 0, NULL);
        kevent(kq, &kev, 1, NULL, 0, NULL);
        struct kevent events[128];
        while (!g_stop_server) {
            struct timespec ts = { .tv_sec = 0, .tv_nsec = 200000000L };
            int nfds = kevent(kq, NULL, 0, events, 128, &ts);
            if (nfds < 0) { if (errno == EINTR) continue; break; }
            for (int i = 0; i < nfds; i++) {
                if (events[i].udata == NULL) {
                    register_accepted_conns(listen_fd, kq, &conn_head, &conn_cnt);
                } else if (events[i].udata == (void *)(uintptr_t)1) {
                    drain_worker_inbox(arg->inbox, &topic_tbl);
                } else {
                    qed_client_conn_t *conn = (qed_client_conn_t *)events[i].udata;
                    if (events[i].filter == EVFILT_WRITE) {
                        (void)handle_client_writable(&conn_head, &conn_cnt, conn, arg, &topic_tbl);
                    } else if (events[i].filter == EVFILT_READ) {
                        handle_client_io(&conn_head, &conn_cnt, conn,
                                         (events[i].flags & EV_EOF) != 0,
                                         (events[i].flags & EV_ERROR) != 0, arg, &topic_tbl);
                    }
                }
            }
            drain_worker_inbox(arg->inbox, &topic_tbl);
            sweep_idle_conns(&conn_head, &conn_cnt, &last_sweep, arg, &topic_tbl);
        }
        while (conn_head != NULL) close_client_conn(&conn_head, &conn_cnt, conn_head, arg, &topic_tbl);
        drain_worker_inbox(arg->inbox, NULL);
        close(kq);
    }
#endif

    topic_table_free(&topic_tbl);
    for (int i = 0; i < QED_POOL_SIZE; i++) {
        if (tls_pool[i].in_use) close_pool_entry(&tls_pool[i]);
    }
    close(listen_fd);
    if (arg->worker_idx > 0) lean_finalize_thread();
    return NULL;
}

static lean_object *qed_server_run_impl(
    uint16_t port,
    uint32_t num_workers,
    b_lean_obj_arg static_dir_obj,
    uint8_t dev_mode,
    lean_obj_arg handler,
    const char *ws_path_in,
    lean_obj_arg ws_upgrade,
    lean_obj_arg ws_action)
{
    ensure_sigpipe_ignored();
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = handle_stop_signal;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    g_stop_server = 0;

    pthread_once(&g_ssl_once, init_ssl_global);

    if (num_workers == 0) {
        long cores = sysconf(_SC_NPROCESSORS_ONLN);
        if (cores <= 0) cores = 2;
        if (cores > 16) cores = 16;
        num_workers = (uint32_t)cores;
    }

    int first_fd = create_reuseport_listener(port, num_workers > 1);
    if (first_fd < 0) {
        lean_dec(handler);
        if (ws_upgrade) lean_dec(ws_upgrade);
        if (ws_action) lean_dec(ws_action);
        fprintf(stderr, "✗ failed to bind port %u: %s\n", (unsigned)port, strerror(errno));
        return lean_io_result_mk_ok(lean_box_uint32(1));
    }

    if (port == 0) {
        struct sockaddr_in bound_addr;
        socklen_t blen = sizeof(bound_addr);
        if (getsockname(first_fd, (struct sockaddr *)&bound_addr, &blen) == 0) {
            port = ntohs(bound_addr.sin_port);
        }
    }

    char *static_dir_copy = strdup(lean_string_cstr(static_dir_obj));
    char *ws_path_copy = strdup(ws_path_in ? ws_path_in : "");
    qed_worker_arg_t *args = (qed_worker_arg_t *)calloc(num_workers, sizeof(qed_worker_arg_t));
    qed_worker_inbox_t *inboxes = (qed_worker_inbox_t *)calloc(num_workers, sizeof(qed_worker_inbox_t));
    if (!static_dir_copy || !ws_path_copy || !args || !inboxes) {
        free(inboxes);
        free(args);
        free(ws_path_copy);
        free(static_dir_copy);
        close(first_fd);
        lean_dec(handler);
        if (ws_upgrade) lean_dec(ws_upgrade);
        if (ws_action) lean_dec(ws_action);
        return lean_io_result_mk_ok(lean_box_uint32(1));
    }

    for (uint32_t i = 0; i < num_workers; i++) {
        pthread_mutex_init(&inboxes[i].mu, NULL);
        inboxes[i].loop_fd = -1;
#ifdef __linux__
        inboxes[i].wake_fd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
#else
        inboxes[i].wake_fd = -1;
#endif
    }
    pthread_mutex_lock(&g_bcast_mu);
    g_inboxes = inboxes;
    g_num_inboxes = num_workers;
    pthread_mutex_unlock(&g_bcast_mu);

    lean_mark_mt(handler);
    if (ws_upgrade) lean_mark_mt(ws_upgrade);
    if (ws_action) lean_mark_mt(ws_action);
    if (num_workers > 1) {
        lean_runtime_mark_multi_threaded();
    }

    fprintf(stdout, "▸ qed native server listening on http://127.0.0.1:%u (%u worker%s)\n",
            (unsigned)port, (unsigned)num_workers, num_workers == 1 ? "" : "s");
    fflush(stdout);

    for (uint32_t i = 0; i < num_workers; i++) {
        args[i].worker_idx = i;
        args[i].port = port;
        args[i].initial_listen_fd = (i == 0) ? first_fd : -1;
        args[i].static_dir = static_dir_copy;
        args[i].dev_mode = dev_mode;
        args[i].handler = handler;
        args[i].ws_path = ws_path_copy;
        args[i].ws_upgrade = ws_upgrade;
        args[i].ws_action = ws_action;
        args[i].inbox = &inboxes[i];
    }

    for (uint32_t i = 1; i < num_workers; i++) {
        if (pthread_create(&args[i].tid, NULL, worker_thread_main, &args[i]) == 0) {
            args[i].started = true;
        }
    }
    worker_thread_main(&args[0]);

    for (uint32_t i = 1; i < num_workers; i++) {
        if (args[i].started) pthread_join(args[i].tid, NULL);
    }

    pthread_mutex_lock(&g_bcast_mu);
    g_inboxes = NULL;
    g_num_inboxes = 0;
    pthread_mutex_unlock(&g_bcast_mu);

    for (uint32_t i = 0; i < num_workers; i++) {
        drain_worker_inbox(&inboxes[i], NULL);
        if (inboxes[i].wake_fd >= 0) close(inboxes[i].wake_fd);
        pthread_mutex_destroy(&inboxes[i].mu);
    }

    free(inboxes);
    free(args);
    free(ws_path_copy);
    free(static_dir_copy);
    lean_dec(handler);
    if (ws_upgrade) lean_dec(ws_upgrade);
    if (ws_action) lean_dec(ws_action);
    return lean_io_result_mk_ok(lean_box_uint32(0));
}

LEAN_EXPORT lean_object *qed_server_run(
    uint16_t port,
    uint32_t num_workers,
    b_lean_obj_arg static_dir_obj,
    uint8_t dev_mode,
    lean_obj_arg handler)
{
    return qed_server_run_impl(port, num_workers, static_dir_obj, dev_mode, handler, "", NULL, NULL);
}

LEAN_EXPORT lean_object *qed_server_run_ws(
    uint16_t port,
    uint32_t num_workers,
    b_lean_obj_arg static_dir_obj,
    uint8_t dev_mode,
    lean_obj_arg handler,
    b_lean_obj_arg ws_path_obj,
    lean_obj_arg ws_upgrade,
    lean_obj_arg ws_action)
{
    return qed_server_run_impl(
        port, num_workers, static_dir_obj, dev_mode, handler,
        lean_string_cstr(ws_path_obj), ws_upgrade, ws_action);
}
