#define _GNU_SOURCE
#include <lean/lean.h>

#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <signal.h>
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

static inline int64_t parse_dec_i64(const char *s, bool *ok) {
    while (*s == ' ' || *s == '\t') s++;
    bool neg = false;
    if (*s == '-') { neg = true; s++; }
    else if (*s == '+') { s++; }
    if (*s < '0' || *s > '9') {
        if (ok) *ok = false;
        return 0;
    }
    uint64_t acc = 0;
    while (*s >= '0' && *s <= '9') {
        acc = acc * 10U + (uint64_t)(*s - '0');
        s++;
    }
    if (ok) *ok = true;
    return neg ? -(int64_t)acc : (int64_t)acc;
}

static inline size_t parse_hex_size(const char *s, bool *ok) {
    while (*s == ' ' || *s == '\t') s++;
    size_t acc = 0;
    bool any = false;
    for (;;) {
        char c = *s;
        size_t d = 0;
        if (c >= '0' && c <= '9') d = (size_t)(c - '0');
        else if (c >= 'a' && c <= 'f') d = (size_t)(c - 'a' + 10);
        else if (c >= 'A' && c <= 'F') d = (size_t)(c - 'A' + 10);
        else break;
        acc = (acc << 4) | d;
        any = true;
        s++;
    }
    if (ok) *ok = any;
    return acc;
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
    uint64_t ms = (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)(ts.tv_nsec / 1000000ULL);
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
    uint8_t digest[32];
    unsigned int digest_len = 0;
    if (HMAC(EVP_sha256(), k_ptr, (int)k_len, m_ptr, m_len, digest, &digest_len) == NULL) {
        memset(digest, 0, sizeof(digest));
        digest_len = 32;
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

static void buf_init(qed_buf_t *b, size_t initial_cap) {
    b->len = 0;
    b->cap = initial_cap > 0 ? initial_cap : 1024;
    b->data = (uint8_t *)malloc(b->cap);
}

static bool buf_reserve(qed_buf_t *b, size_t extra) {
    if (b->len + extra <= b->cap) return true;
    size_t next = b->cap ? b->cap * 2 : 1024;
    while (next < b->len + extra) next *= 2;
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

static bool is_blocked_sockaddr(const struct sockaddr *sa) {
    if (sa->sa_family == AF_INET) {
        const struct sockaddr_in *sin = (const struct sockaddr_in *)sa;
        uint32_t ip = ntohl(sin->sin_addr.s_addr);
        return is_blocked_ipv4_host_order(ip);
    } else if (sa->sa_family == AF_INET6) {
        const struct sockaddr_in6 *sin6 = (const struct sockaddr_in6 *)sa;
        const uint8_t *b = sin6->sin6_addr.s6_addr;
        bool all_zero = true;
        for (int i = 0; i < 15; i++) {
            if (b[i] != 0) all_zero = false;
        }
        if (all_zero && (b[15] == 0 || b[15] == 1)) return true; /* :: or ::1 */
        if ((b[0] & 0xFE) == 0xFC) return true; /* fc00::/7 ULA */
        if (b[0] == 0xFE && (b[1] & 0xC0) == 0x80) return true; /* fe80::/10 link-local */
        if (b[0] == 0xFF) return true; /* multicast */
        /* IPv4-mapped ::ffff:a.b.c.d */
        bool v4_mapped = true;
        for (int i = 0; i < 10; i++) if (b[i] != 0) v4_mapped = false;
        if (v4_mapped && b[10] == 0xFF && b[11] == 0xFF) {
            uint32_t ip = ((uint32_t)b[12] << 24) | ((uint32_t)b[13] << 16) |
                          ((uint32_t)b[14] << 8)  | (uint32_t)b[15];
            return is_blocked_ipv4_host_order(ip);
        }
    }
    return false;
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
    if (r == 0) return false;
    if (r < 0 && errno != EAGAIN && errno != EWOULDBLOCK) return false;
    return true;
}

static bool parse_http_url(
    const char *url,
    bool *is_tls,
    char *host, size_t host_cap,
    uint16_t *port,
    char *path, size_t path_cap)
{
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
    const char * authority_end = slash;
    if (qmark != NULL && (authority_end == NULL || qmark < authority_end)) {
        authority_end = qmark;
    }
    size_t auth_len = authority_end ? (size_t)(authority_end - p) : strlen(p);
    if (auth_len == 0 || auth_len >= host_cap) return false;

    char auth[300];
    if (auth_len >= sizeof(auth)) return false;
    memcpy(auth, p, auth_len);
    auth[auth_len] = '\0';

    if (auth[0] == '[') {
        char *rb = strchr(auth, ']');
        if (!rb) return false;
        size_t hlen = (size_t)(rb - (auth + 1));
        if (hlen >= host_cap) return false;
        memcpy(host, auth + 1, hlen);
        host[hlen] = '\0';
        if (rb[1] == ':') {
            int pv = (int)parse_dec_i64(rb + 2, NULL);
            if (pv <= 0 || pv > 65535) return false;
            *port = (uint16_t)pv;
        }
    } else {
        char *colon = strrchr(auth, ':');
        if (colon != NULL) {
            *colon = '\0';
            int pv = (int)parse_dec_i64(colon + 1, NULL);
            if (pv <= 0 || pv > 65535) return false;
            *port = (uint16_t)pv;
        }
        if (strlen(auth) == 0 || strlen(auth) >= host_cap) return false;
        strcpy(host, auth);
    }

    if (authority_end == NULL) {
        snprintf(path, path_cap, "/");
    } else if (*authority_end == '?') {
        snprintf(path, path_cap, "/%s", authority_end);
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
        SSL_set_tlsext_host_name(ssl, host);
        X509_VERIFY_PARAM *param = SSL_get0_param(ssl);
        if (param != NULL) {
            X509_VERIFY_PARAM_set1_host(param, host, 0);
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
        ssize_t n;
        if (ssl != NULL) {
            n = SSL_write(ssl, buf + off, (int)(len - off));
        } else {
            n = send(fd, buf + off, len - off, MSG_NOSIGNAL);
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
            n = SSL_read(ssl, buf, (int)cap);
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

static bool decode_chunked_stream(
    int fd, SSL *ssl,
    qed_buf_t *raw_buf, size_t cursor,
    qed_buf_t *out_body)
{
    for (;;) {
        ssize_t line_end = -1;
        for (;;) {
            for (size_t i = cursor; i + 1 < raw_buf->len; i++) {
                if (raw_buf->data[i] == '\r' && raw_buf->data[i + 1] == '\n') {
                    line_end = (ssize_t)i;
                    break;
                }
            }
            if (line_end >= 0) break;
            uint8_t tmp[4096];
            ssize_t got = conn_read_some(fd, ssl, tmp, sizeof(tmp));
            if (got <= 0 || !buf_append(raw_buf, tmp, (size_t)got)) return false;
        }

        char size_line[64];
        size_t slen = (size_t)line_end - cursor;
        if (slen >= sizeof(size_line)) slen = sizeof(size_line) - 1;
        memcpy(size_line, raw_buf->data + cursor, slen);
        size_line[slen] = '\0';
        char *semi = strchr(size_line, ';');
        if (semi) *semi = '\0';

        bool hex_ok = false;
        size_t chunk_sz = parse_hex_size(size_line, &hex_ok);
        if (!hex_ok) return false;

        cursor = (size_t)line_end + 2;
        if (chunk_sz == 0) {
            (void)conn_read_until(fd, ssl, raw_buf, cursor + 2);
            return true;
        }

        if (!conn_read_until(fd, ssl, raw_buf, cursor + chunk_sz + 2)) return false;
        if (!buf_append(out_body, raw_buf->data + cursor, chunk_sz)) return false;
        cursor += chunk_sz + 2;
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
    memset(out, 0, sizeof(*out));
    buf_init(&out->body, 1024);

    bool is_tls = false;
    char host[256];
    uint16_t port = 80;
    char path[4096];
    if (!parse_http_url(url, &is_tls, host, sizeof(host), &port, path, sizeof(path))) {
        buf_free(&out->body);
        snprintf(err, err_cap, "invalid outbound HTTP URL: %s", url);
        return false;
    }

    qed_buf_t req_wire;
    buf_init(&req_wire, 512 + req_body_len);
    char first_line[4600];
    bool default_port = (is_tls && port == 443) || (!is_tls && port == 80);
    if (default_port) {
        snprintf(first_line, sizeof(first_line),
                 "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: keep-alive\r\nContent-Length: %zu\r\n",
                 method, path, host, req_body_len);
    } else {
        snprintf(first_line, sizeof(first_line),
                 "%s %s HTTP/1.1\r\nHost: %s:%u\r\nConnection: keep-alive\r\nContent-Length: %zu\r\n",
                 method, path, host, (unsigned)port, req_body_len);
    }
    buf_append_cstr(&req_wire, first_line);
    for (size_t i = 0; i < req_hdr_count; i++) {
        const char *k = req_hdrs[i].key;
        if (strcasecmp(k, "Host") == 0 || strcasecmp(k, "Content-Length") == 0 || strcasecmp(k, "Connection") == 0) {
            continue;
        }
        buf_append_cstr(&req_wire, k);
        buf_append_cstr(&req_wire, ": ");
        buf_append_cstr(&req_wire, req_hdrs[i].val);
        buf_append_cstr(&req_wire, "\r\n");
    }
    buf_append_cstr(&req_wire, "\r\n");
    if (req_body_len > 0) buf_append(&req_wire, req_body, req_body_len);

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
        buf_init(&rx, 4096);
        ssize_t hdr_end = -1;
        bool read_failed = false;
        while ((hdr_end = find_crlfcrlf(rx.data, rx.len)) < 0) {
            uint8_t tmp[4096];
            ssize_t got = (rx.len > 65536) ? -1 : conn_read_some(fd, ssl, tmp, sizeof(tmp));
            if (got <= 0 || !buf_append(&rx, tmp, (size_t)got)) { read_failed = true; break; }
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

        rx.data[hdr_end] = '\0';
        char *saveptr = NULL;
        char *line = strtok_r((char *)rx.data, "\r\n", &saveptr);
        if (!line || strncmp(line, "HTTP/", 5) != 0) {
            buf_free(&rx);
            release_outbound_conn(false, is_tls, host, port, fd, ssl);
            buf_free(&out->body);
            snprintf(err, err_cap, "invalid HTTP status line from %s", host);
            return false;
        }
        char *sp = strchr(line, ' ');
        out->status = sp ? (int)parse_dec_i64(sp + 1, NULL) : 0;

        bool is_chunked = false;
        bool conn_close = false;
        ssize_t content_len = -1;
        size_t hdr_cap = 16;
        out->headers = (qed_hdr_pair_t *)calloc(hdr_cap, sizeof(qed_hdr_pair_t));

        char *val = NULL;
        while ((line = strtok_r(NULL, "\r\n", &saveptr)) != NULL) {
            if (!split_header_kv(line, &val)) continue;
            if (strcasecmp(line, "Content-Length") == 0) {
                content_len = (ssize_t)parse_dec_i64(val, NULL);
            } else if (strcasecmp(line, "Transfer-Encoding") == 0 && strcasestr(val, "chunked") != NULL) {
                is_chunked = true;
            } else if (strcasecmp(line, "Connection") == 0 && strcasestr(val, "close") != NULL) {
                conn_close = true;
            }
            if (out->header_count == hdr_cap) {
                hdr_cap *= 2;
                qed_hdr_pair_t *nh = (qed_hdr_pair_t *)realloc(out->headers, hdr_cap * sizeof(qed_hdr_pair_t));
                if (nh) out->headers = nh;
            }
            if (out->headers && out->header_count < hdr_cap) {
                out->headers[out->header_count].key = strdup(line);
                out->headers[out->header_count].val = strdup(val);
                out->header_count++;
            }
        }

        size_t body_start = (size_t)hdr_end + 4;
        bool can_reuse = !conn_close && !ssrf_guard;

        if (strcmp(method, "HEAD") == 0 || out->status == 204 || out->status == 304) {
            /* Empty body */
        } else if (is_chunked) {
            if (!decode_chunked_stream(fd, ssl, &rx, body_start, &out->body)) {
                buf_free(&rx);
                release_outbound_conn(false, is_tls, host, port, fd, ssl);
                free_raw_resp(out);
                snprintf(err, err_cap, "failed decoding chunked response from %s", host);
                return false;
            }
        } else if (content_len >= 0) {
            size_t have = rx.len - body_start;
            if (have > (size_t)content_len) have = (size_t)content_len;
            if (have > 0) buf_append(&out->body, rx.data + body_start, have);
            if (!conn_read_until(fd, ssl, &out->body, (size_t)content_len)) {
                buf_free(&rx);
                release_outbound_conn(false, is_tls, host, port, fd, ssl);
                free_raw_resp(out);
                snprintf(err, err_cap, "truncated HTTP body from %s", host);
                return false;
            }
        } else {
            can_reuse = false;
            if (rx.len > body_start) buf_append(&out->body, rx.data + body_start, rx.len - body_start);
            for (;;) {
                uint8_t tmp[8192];
                ssize_t got = conn_read_some(fd, ssl, tmp, sizeof(tmp));
                if (got <= 0) break;
                buf_append(&out->body, tmp, (size_t)got);
            }
        }

        buf_free(&rx);
        release_outbound_conn(can_reuse, is_tls, host, port, fd, ssl);
        return true;
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
    size_t hdr_n = lean_array_size(headers);
    qed_hdr_pair_t *req_hdrs = hdr_n > 0 ? (qed_hdr_pair_t *)calloc(hdr_n, sizeof(qed_hdr_pair_t)) : NULL;
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

static void base64url_encode(const uint8_t *in, size_t in_len, char *out) {
    static const char kTbl[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    size_t j = 0, i = 0;
    while (i + 3 <= in_len) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i + 1] << 8) | (uint32_t)in[i + 2];
        out[j++] = kTbl[(v >> 18) & 0x3F];
        out[j++] = kTbl[(v >> 12) & 0x3F];
        out[j++] = kTbl[(v >> 6) & 0x3F];
        out[j++] = kTbl[v & 0x3F];
        i += 3;
    }
    if (in_len - i == 1) {
        uint32_t v = ((uint32_t)in[i] << 16);
        out[j++] = kTbl[(v >> 18) & 0x3F];
        out[j++] = kTbl[(v >> 12) & 0x3F];
    } else if (in_len - i == 2) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i + 1] << 8);
        out[j++] = kTbl[(v >> 18) & 0x3F];
        out[j++] = kTbl[(v >> 12) & 0x3F];
        out[j++] = kTbl[(v >> 6) & 0x3F];
    }
    out[j] = '\0';
}

static const char *json_find_val(const char *json, const char *key) {
    char pat[128];
    snprintf(pat, sizeof(pat), "\"%s\"", key);
    const char *p = strstr(json, pat);
    if (!p) return NULL;
    p += strlen(pat);
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    if (*p != ':') return NULL;
    p++;
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    return p;
}

static bool json_extract_string(const char *json, const char *key, char *out, size_t out_cap) {
    const char *p = json_find_val(json, key);
    if (!p || *p != '"') return false;
    p++;
    size_t j = 0;
    while (*p && *p != '"') {
        if (j + 2 >= out_cap) return false;
        if (*p == '\\' && p[1] != '\0') {
            p++;
            switch (*p) {
                case 'n': out[j++] = '\n'; break;
                case 'r': out[j++] = '\r'; break;
                case 't': out[j++] = '\t'; break;
                default:  out[j++] = *p;   break;
            }
            p++;
        } else {
            out[j++] = *p++;
        }
    }
    if (*p != '"') return false;
    out[j] = '\0';
    return true;
}

static long json_extract_long(const char *json, const char *key, long fallback) {
    const char *p = json_find_val(json, key);
    if (!p) return fallback;
    bool num_ok = false;
    int64_t v = parse_dec_i64(p, &num_ok);
    return (num_ok && v > 0) ? (long)v : fallback;
}

typedef struct {
    bool valid;
    char client_email[256];
    char scope[512];
    char token_url[512];
    char access_token[2048];
    time_t expires_at;
} qed_gcp_cache_entry_t;

#define QED_GCP_CACHE_SIZE 8
static pthread_mutex_t g_gcp_mu = PTHREAD_MUTEX_INITIALIZER;
static qed_gcp_cache_entry_t g_gcp_cache[QED_GCP_CACHE_SIZE];

LEAN_EXPORT lean_object *qed_server_gcp_bearer_token(b_lean_obj_arg sa_json_obj, b_lean_obj_arg scope_obj) {
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
        snprintf(token_uri, sizeof(token_uri), "%s", env_tok_url);
    } else if (!json_extract_string(sa_json, "token_uri", token_uri, sizeof(token_uri))) {
        snprintf(token_uri, sizeof(token_uri), "https://oauth2.googleapis.com/token");
    }

    time_t now = time(NULL);
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

    /* Construct RS256 JWT */
    static const char *kJwtHdr = "{\"alg\":\"RS256\",\"typ\":\"JWT\"}";
    char claims[2048];
    snprintf(claims, sizeof(claims),
             "{\"iss\":\"%s\",\"scope\":\"%s\",\"aud\":\"%s\",\"iat\":%ld,\"exp\":%ld}",
             client_email, scope, token_uri, (long)now, (long)(now + 3600));

    char b64_hdr[128];
    char b64_claims[3072];
    base64url_encode((const uint8_t *)kJwtHdr, strlen(kJwtHdr), b64_hdr);
    base64url_encode((const uint8_t *)claims, strlen(claims), b64_claims);

    char signing_input[3300];
    int si_len = snprintf(signing_input, sizeof(signing_input), "%s.%s", b64_hdr, b64_claims);

    BIO *bio = BIO_new_mem_buf(private_key, -1);
    if (!bio) {
        return lean_io_result_mk_ok(mk_except_err_str("BIO_new_mem_buf failed for GCP private_key"));
    }
    EVP_PKEY *pkey = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
    BIO_free(bio);
    if (!pkey) {
        return lean_io_result_mk_ok(mk_except_err_str("PEM_read_bio_PrivateKey failed for GCP private_key"));
    }

    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    size_t sig_len = 0;
    uint8_t sig_buf[1024];
    bool sign_ok = false;
    if (mdctx != NULL &&
        EVP_DigestSignInit(mdctx, NULL, EVP_sha256(), NULL, pkey) == 1 &&
        EVP_DigestSignUpdate(mdctx, signing_input, (size_t)si_len) == 1 &&
        EVP_DigestSignFinal(mdctx, NULL, &sig_len) == 1 &&
        sig_len <= sizeof(sig_buf) &&
        EVP_DigestSignFinal(mdctx, sig_buf, &sig_len) == 1)
    {
        sign_ok = true;
    }
    if (mdctx) EVP_MD_CTX_free(mdctx);
    EVP_PKEY_free(pkey);

    if (!sign_ok) {
        return lean_io_result_mk_ok(mk_except_err_str("EVP_DigestSign RS256 failed"));
    }

    char b64_sig[1500];
    base64url_encode(sig_buf, sig_len, b64_sig);

    char form_body[5200];
    int fb_len = snprintf(
        form_body, sizeof(form_body),
        "grant_type=urn%%3Aietf%%3Aparams%%3Aoauth%%3Agrant-type%%3Ajwt-bearer&assertion=%s.%s",
        signing_input, b64_sig);

    qed_hdr_pair_t hdrs[1];
    hdrs[0].key = "Content-Type";
    hdrs[0].val = "application/x-www-form-urlencoded";

    qed_raw_resp_t resp;
    char err_msg[512];
    if (!raw_http_execute("POST", token_uri, hdrs, 1, (const uint8_t *)form_body, (size_t)fb_len, 0, &resp, err_msg, sizeof(err_msg))) {
        return lean_io_result_mk_ok(mk_except_err_str(err_msg));
    }

    if (!buf_append(&resp.body, "", 1)) {
        free_raw_resp(&resp);
        return lean_io_result_mk_ok(mk_except_err_str("OOM reading GCP OAuth2 response"));
    }

    if (resp.status < 200 || resp.status >= 300) {
        char fail_buf[600];
        snprintf(fail_buf, sizeof(fail_buf), "OAuth2 HTTP %d: %.400s", resp.status, (char *)resp.body.data);
        free_raw_resp(&resp);
        return lean_io_result_mk_ok(mk_except_err_str(fail_buf));
    }

    char access_token[2048];
    if (!json_extract_string((const char *)resp.body.data, "access_token", access_token, sizeof(access_token))) {
        free_raw_resp(&resp);
        return lean_io_result_mk_ok(mk_except_err_str("GCP OAuth2 response missing `access_token`"));
    }
    long expires_in = json_extract_long((const char *)resp.body.data, "expires_in", 3600);
    free_raw_resp(&resp);

    pthread_mutex_lock(&g_gcp_mu);
    int slot = 0;
    for (int i = 0; i < QED_GCP_CACHE_SIZE; i++) {
        if (!g_gcp_cache[i].valid) { slot = i; break; }
        if (g_gcp_cache[i].expires_at < g_gcp_cache[slot].expires_at) slot = i;
    }
    qed_gcp_cache_entry_t * dst = &g_gcp_cache[slot];
    dst->valid = true;
    snprintf(dst->client_email, sizeof(dst->client_email), "%s", client_email);
    snprintf(dst->scope, sizeof(dst->scope), "%s", scope);
    snprintf(dst->token_url, sizeof(dst->token_url), "%s", token_uri);
    snprintf(dst->access_token, sizeof(dst->access_token), "%s", access_token);
    dst->expires_at = time(NULL) + expires_in;
    pthread_mutex_unlock(&g_gcp_mu);

    return lean_io_result_mk_ok(mk_except_ok(lean_mk_string(access_token)));
}

/* =========================================================================
 * 7. Multi-Core `SO_REUSEPORT` + `epoll` / `kqueue` HTTP/1.1 Server
 * ========================================================================= */

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
        case 500: return "Internal Server Error";
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

static bool writev_all(int fd, const char *hdr, size_t hdr_len, const uint8_t *body, size_t body_len) {
    struct iovec iov[2];
    iov[0].iov_base = (void *)hdr;
    iov[0].iov_len  = hdr_len;
    iov[1].iov_base = (void *)body;
    iov[1].iov_len  = body_len;
    int iovcnt = (body_len > 0 && body != NULL) ? 2 : 1;
    int idx = 0;
    while (idx < iovcnt) {
        ssize_t n = writev(fd, &iov[idx], iovcnt - idx);
        if (n < 0) {
            if (errno == EINTR) continue;
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                usleep(500);
                continue;
            }
            return false;
        }
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
    return true;
}

static bool send_http_response(
    int fd, int status, const char *content_type,
    const uint8_t *body, size_t body_len,
    bool head_only, bool keep_alive, bool no_store)
{
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
    return writev_all(fd, hdr, (size_t)hlen, head_only ? NULL : body, head_only ? 0 : body_len);
}

static bool read_regular_file(const char *path, bool head_only, uint8_t **out_data, size_t *out_len) {
    struct stat st;
    if (stat(path, &st) != 0 || !S_ISREG(st.st_mode)) return false;
    size_t fsize = (size_t)st.st_size;
    *out_data = NULL;
    *out_len = fsize;
    if (!head_only && fsize > 0) {
        FILE *fp = fopen(path, "rb");
        if (!fp) return false;
        *out_data = (uint8_t *)malloc(fsize);
        if (!*out_data) { fclose(fp); return false; }
        *out_len = fread(*out_data, 1, fsize, fp);
        fclose(fp);
    }
    return true;
}

static bool try_serve_static_c(
    int client_fd,
    const char *static_dir,
    uint8_t dev_mode,
    const char *method,
    const char *target,
    bool keep_alive)
{
    bool is_get = (strcmp(method, "GET") == 0);
    bool is_head = (strcmp(method, "HEAD") == 0);
    if (!is_get && !is_head) return false;

    char path_only[2048];
    const char *q = strchr(target, '?');
    size_t plen = q ? (size_t)(q - target) : strlen(target);
    if (plen == 0 || plen >= sizeof(path_only)) return false;
    memcpy(path_only, target, plen);
    path_only[plen] = '\0';

    if (strncmp(path_only, "/_qed/", 6) == 0 || strstr(path_only, "..") != NULL) return false;

    char full[4096];
    snprintf(full, sizeof(full), "%s%s", static_dir, path_only);

    if (dev_mode && strcmp(path_only, "/__build_id") == 0) {
        uint8_t *data = NULL;
        size_t len = 0;
        if (read_regular_file(full, is_head, &data, &len)) {
            send_http_response(client_fd, 200, "text/plain; charset=utf-8", data, len, is_head, keep_alive, true);
            free(data);
        } else {
            send_http_response(client_fd, 200, "text/plain; charset=utf-8", (const uint8_t *)"0", 1, is_head, keep_alive, true);
        }
        return true;
    }

    const char *mime = guess_mime_type(path_only);
    if (!mime) return false;

    uint8_t *data = NULL;
    size_t fsize = 0;
    if (!read_regular_file(full, is_head, &data, &fsize)) return false;
    send_http_response(client_fd, 200, mime, data, fsize, is_head, keep_alive, dev_mode != 0);
    free(data);
    return true;
}

typedef struct qed_client_conn {
    int fd;
    char ip[64];
    qed_buf_t rx;
} qed_client_conn_t;

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

/* Returns: 1 = continue keep-alive, 0 = need more bytes, -1 = close connection */
static int process_buffered_requests(
    qed_client_conn_t *c,
    const char *static_dir,
    uint8_t dev_mode,
    lean_object *handler)
{
    for (;;) {
        ssize_t hdr_end = find_crlfcrlf(c->rx.data, c->rx.len);
        if (hdr_end < 0) return (c->rx.len > 65536) ? -1 : 0;

        size_t hdr_bytes = (size_t)hdr_end + 4;
        char hdr_copy[65540];
        if (hdr_bytes >= sizeof(hdr_copy)) return -1;
        memcpy(hdr_copy, c->rx.data, (size_t)hdr_end);
        hdr_copy[hdr_end] = '\0';

        char *saveptr = NULL;
        char *req_line = strtok_r(hdr_copy, "\r\n", &saveptr);
        if (!req_line) return -1;

        char *sp1 = strchr(req_line, ' ');
        if (!sp1) return -1;
        *sp1 = '\0';
        char *method = req_line;
        char *target = sp1 + 1;
        char *sp2 = strchr(target, ' ');
        if (!sp2) return -1;
        *sp2 = '\0';
        char *http_ver = sp2 + 1;

        bool keep_alive = (strstr(http_ver, "1.1") != NULL);
        size_t content_len = 0;

        qed_hdr_pair_t parsed_hdrs[96];
        size_t parsed_cnt = 0;

        char *hline = NULL, *val = NULL;
        while ((hline = strtok_r(NULL, "\r\n", &saveptr)) != NULL) {
            if (!split_header_kv(hline, &val)) continue;
            if (strcasecmp(hline, "Content-Length") == 0) {
                int64_t cl = parse_dec_i64(val, NULL);
                if (cl < 0 || cl > (32LL * 1024LL * 1024LL)) return -1;
                content_len = (size_t)cl;
            } else if (strcasecmp(hline, "Connection") == 0) {
                if (strcasestr(val, "close") != NULL) keep_alive = false;
                else if (strcasestr(val, "keep-alive") != NULL) keep_alive = true;
            }
            if (parsed_cnt < 96) {
                parsed_hdrs[parsed_cnt].key = hline;
                parsed_hdrs[parsed_cnt].val = val;
                parsed_cnt++;
            }
        }

        size_t total_needed = hdr_bytes + content_len;
        if (c->rx.len < total_needed) return 0;

        if (!try_serve_static_c(c->fd, static_dir, dev_mode, method, target, keep_alive)) {
            lean_inc(handler);
            lean_object *io_res = lean_apply_6(
                handler,
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
                bool sent = send_http_response(
                    c->fd, (int)status, ctype,
                    lean_sarray_cptr(resp_ba), lean_sarray_size(resp_ba),
                    strcmp(method, "HEAD") == 0, keep_alive, false);
                lean_dec_ref(io_res);
                if (!sent) return -1;
            } else {
                lean_dec_ref(io_res);
                const char *msg = "internal server error";
                send_http_response(c->fd, 500, "text/plain; charset=utf-8", (const uint8_t *)msg, strlen(msg), false, false, true);
                return -1;
            }
        }

        size_t rem = c->rx.len - total_needed;
        if (rem > 0) memmove(c->rx.data, c->rx.data + total_needed, rem);
        c->rx.len = rem;

        if (!keep_alive) return -1;
        if (c->rx.len == 0) return 1;
    }
}

typedef struct {
    uint32_t worker_idx;
    uint16_t port;
    int initial_listen_fd;
    const char *static_dir;
    uint8_t dev_mode;
    lean_object *handler;
} qed_worker_arg_t;

static void close_client_conn(int loop_fd, qed_client_conn_t *c) {
    if (!c) return;
#ifdef __linux__
    epoll_ctl(loop_fd, EPOLL_CTL_DEL, c->fd, NULL);
#else
    (void)loop_fd;
#endif
    close(c->fd);
    buf_free(&c->rx);
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
    inet_ntop(AF_INET, &cli_addr.sin_addr, conn->ip, sizeof(conn->ip));
    buf_init(&conn->rx, 2048);
    return conn;
}

static void handle_client_io(int loop_fd, qed_client_conn_t *conn, bool peer_eof, const qed_worker_arg_t *arg) {
    bool closed = false;
    for (;;) {
        uint8_t tmp[8192];
        ssize_t n = recv(conn->fd, tmp, sizeof(tmp), 0);
        if (n > 0) {
            if (!buf_append(&conn->rx, tmp, (size_t)n)) { closed = true; break; }
        } else if (n == 0) {
            closed = true;
            break;
        } else {
            if (errno == EINTR) continue;
            if (errno == EAGAIN || errno == EWOULDBLOCK) break;
            closed = true;
            break;
        }
    }
    if (!closed && conn->rx.len > 0) {
        if (process_buffered_requests(conn, arg->static_dir, arg->dev_mode, arg->handler) < 0) closed = true;
    }
    if (closed || peer_eof) close_client_conn(loop_fd, conn);
}

static void *worker_thread_main(void *raw_arg) {
    qed_worker_arg_t *arg = (qed_worker_arg_t *)raw_arg;
    if (arg->worker_idx > 0) lean_initialize_thread();

    int listen_fd = arg->initial_listen_fd >= 0 ? arg->initial_listen_fd : create_reuseport_listener(arg->port, true);
    if (listen_fd < 0) {
        if (arg->worker_idx > 0) lean_finalize_thread();
        return NULL;
    }

#ifdef __linux__
    int epfd = epoll_create1(EPOLL_CLOEXEC);
    if (epfd >= 0) {
        struct epoll_event ev = { .events = EPOLLIN, .data.ptr = NULL };
        epoll_ctl(epfd, EPOLL_CTL_ADD, listen_fd, &ev);
        struct epoll_event events[128];
        while (!g_stop_server) {
            int nfds = epoll_wait(epfd, events, 128, 200);
            if (nfds < 0) { if (errno == EINTR) continue; break; }
            for (int i = 0; i < nfds; i++) {
                if (events[i].data.ptr == NULL) {
                    qed_client_conn_t *conn;
                    while ((conn = accept_one_client(listen_fd)) != NULL) {
                        struct epoll_event cev = { .events = EPOLLIN | EPOLLRDHUP, .data.ptr = conn };
                        epoll_ctl(epfd, EPOLL_CTL_ADD, conn->fd, &cev);
                    }
                } else {
                    qed_client_conn_t *conn = (qed_client_conn_t *)events[i].data.ptr;
                    if (events[i].events & (EPOLLERR | EPOLLHUP)) close_client_conn(epfd, conn);
                    else handle_client_io(epfd, conn, (events[i].events & EPOLLRDHUP) != 0, arg);
                }
            }
        }
        close(epfd);
    }
#elif defined(__APPLE__)
    int kq = kqueue();
    if (kq >= 0) {
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
                    qed_client_conn_t *conn;
                    while ((conn = accept_one_client(listen_fd)) != NULL) {
                        EV_SET(&kev, conn->fd, EVFILT_READ, EV_ADD | EV_ENABLE, 0, 0, conn);
                        kevent(kq, &kev, 1, NULL, 0, NULL);
                    }
                } else {
                    handle_client_io(kq, (qed_client_conn_t *)events[i].udata, (events[i].flags & EV_EOF) != 0, arg);
                }
            }
        }
        close(kq);
    }
#endif

    for (int i = 0; i < QED_POOL_SIZE; i++) {
        if (tls_pool[i].in_use) close_pool_entry(&tls_pool[i]);
    }
    close(listen_fd);
    if (arg->worker_idx > 0) lean_finalize_thread();
    return NULL;
}

LEAN_EXPORT lean_object *qed_server_run(
    uint16_t port,
    uint32_t num_workers,
    b_lean_obj_arg static_dir_obj,
    uint8_t dev_mode,
    lean_obj_arg handler)
{
    signal(SIGPIPE, SIG_IGN);
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
        fprintf(stderr, "✗ failed to bind port %u: %s\n", (unsigned)port, strerror(errno));
        return lean_io_result_mk_ok(lean_box_uint32(1));
    }

    char *static_dir_copy = strdup(lean_string_cstr(static_dir_obj));
    lean_mark_mt(handler);
    if (num_workers > 1) {
        lean_runtime_mark_multi_threaded();
    }

    fprintf(stdout, "▸ qed native server listening on http://127.0.0.1:%u (%u worker%s)\n",
            (unsigned)port, (unsigned)num_workers, num_workers == 1 ? "" : "s");
    fflush(stdout);

    pthread_t *threads = (pthread_t *)calloc(num_workers, sizeof(pthread_t));
    qed_worker_arg_t *args = (qed_worker_arg_t *)calloc(num_workers, sizeof(qed_worker_arg_t));

    for (uint32_t i = 0; i < num_workers; i++) {
        args[i].worker_idx = i;
        args[i].port = port;
        args[i].initial_listen_fd = (i == 0) ? first_fd : -1;
        args[i].static_dir = static_dir_copy;
        args[i].dev_mode = dev_mode;
        args[i].handler = handler;
    }

    for (uint32_t i = 1; i < num_workers; i++) {
        pthread_create(&threads[i], NULL, worker_thread_main, &args[i]);
    }
    worker_thread_main(&args[0]);

    for (uint32_t i = 1; i < num_workers; i++) {
        pthread_join(threads[i], NULL);
    }

    free(threads);
    free(args);
    free(static_dir_copy);
    lean_dec(handler);
    return lean_io_result_mk_ok(lean_box_uint32(0));
}
