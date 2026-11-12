/*
 * The ws-leaf prover (harness/PROVER.md is its interface). It walks no chain and hashes nothing.
 *
 * The verifier (lean/WlVerifier.lean) recomputes every leaf statement itself, so a step only
 * copies its inputs into a "derived" proof and signs it:
 *
 *   π = header ‖ the library's node encoding (WitnessSending.encode) with zero statement slots
 *   header (88 bytes) = u64 tag ‖ sA ‖ u64 nA ‖ sB ‖ u64 nB
 *
 *   prover first DIR   tag 3: both children are leaf proofs of chainA.json, chainB.json; both
 *                      statements are derived (sA, nA, sB, nB from the chain files)
 *   prover step DIR    tag 2: the left child is prev.bin with statement prev.stmt (sent), the
 *                      right child is the leaf proof of chain.json, its statement derived
 *                      (sA = 0, nA = 0)
 *
 * A leaf proof is the library's 48-byte encoding u64 0 ‖ s ‖ u64 n, with an empty trace. Every
 * trace is empty (the verifier asks no query). Each signed proof, the output and each leaf child,
 * gets its own SIGN (service/PROTOCOL.md §2.2: "a prover asks SIGN once per proof"); the requests
 * go out on separate connections at once, before the inputs are read.
 *
 * Adapted from the core's toy prover (harness/toy-prover/toy.c, Apache-2.0): the SIGN request and
 * the file layout; the chain, the statements and the child re-encoding are dropped.
 */
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>

static void die(const char *m) {
    fprintf(stderr, "ws-leaf prover: %s\n", m);
    exit(1);
}
static void put64(uint8_t *p, uint64_t x) {
    for (int i = 0; i < 8; i++) p[i] = (uint8_t)(x >> (8 * i));
}
static uint64_t get64(const uint8_t *p) {
    uint64_t x = 0;
    for (int i = 7; i >= 0; i--) x = x << 8 | p[i];
    return x;
}

/* ---- files ----------------------------------------------------------------------------------- */
typedef struct { uint8_t *p; size_t n; } buf;
static buf readfile(const char *path) {
    int fd = open(path, O_RDONLY);
    if (fd < 0) die(path);
    struct stat st;
    if (fstat(fd, &st)) die(path);
    buf b = {malloc((size_t)st.st_size + 1), 0};
    if (!b.p) die("out of memory");
    while (b.n < (size_t)st.st_size) {
        ssize_t k = read(fd, b.p + b.n, (size_t)st.st_size - b.n);
        if (k <= 0) die(path);
        b.n += (size_t)k;
    }
    close(fd);
    b.p[b.n] = 0;
    return b;
}
static void writefile(const char *path, const uint8_t *p, size_t n) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) die(path);
    while (n) {
        ssize_t k = write(fd, p, n);
        if (k <= 0) die(path);
        p += k;
        n -= (size_t)k;
    }
    if (close(fd)) die(path);
}
static int unhex(uint8_t *out, const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) {
        int v = 0;
        for (int j = 0; j < 2; j++) {
            char c = s[2 * i + j];
            int d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10
                  : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
            if (d < 0) return -1;
            v = v << 4 | d;
        }
        out[i] = (uint8_t)v;
    }
    return 0;
}
/* A chain file {"n": N, "start": "HEX"}. */
static void read_chain(const char *path, uint8_t s[32], uint64_t *n) {
    buf j = readfile(path);
    char *p = strstr((char *)j.p, "\"n\":"), *q = strstr((char *)j.p, "\"start\":");
    if (!p || !q) die(path);
    q = strchr(q + 8, '"');
    if (!q || unhex(s, q + 1, 32)) die(path);
    *n = strtoull(p + 4, NULL, 10);
    free(j.p);
}
static void read_stmt(uint8_t c[32], const char *path) {
    buf b = readfile(path);
    if (b.n < 64 || unhex(c, (char *)b.p, 32)) die(path);
    free(b.p);
}

/* ---- the oracle service: SIGN of the empty trace (toy.c's request) --------------------------- */
#define SIG_WIRE 4772 /* idx:u32 ‖ 133 × 32 ‖ 16 × 32 */
/* Open a connection and send one SIGN with no items; the answer is read by sign_recv. */
static int sign_send(void) {
    const char *path = getenv("RF_ORACLE");
    if (!path) die("RF_ORACLE unset");
    struct sockaddr_un a;
    memset(&a, 0, sizeof a);
    a.sun_family = AF_UNIX;
    strncpy(a.sun_path, path, sizeof a.sun_path - 1);
    int svc = socket(AF_UNIX, SOCK_STREAM, 0);
    if (svc < 0 || connect(svc, (struct sockaddr *)&a, sizeof a)) die("cannot connect to the oracle");
    uint8_t h[16] = {2}; /* SIGN, count 0, body 0 */
    if (write(svc, h, 16) != 16) die("SIGN write");
    return svc;
}
static void read_all(int fd, uint8_t *p, size_t n) {
    size_t got = 0;
    while (got < n) {
        ssize_t k = read(fd, p + got, n - got);
        if (k <= 0) die("SIGN read");
        got += (size_t)k;
    }
}
static void sign_recv(int svc, uint8_t sig[SIG_WIRE]) {
    uint8_t h[16];
    read_all(svc, h, 16);
    if (h[0] != 0 || get64(h + 8) != SIG_WIRE) die("SIGN refused");
    read_all(svc, sig, SIG_WIRE);
    close(svc);
}

/* ---- the derived proof ------------------------------------------------------------------------ */
#define SIGW (8 + 149 * 32)      /* u64 idx ‖ 133 ots ‖ 16 path: the signature's words */
#define LEAFW (8 + 48 + 8 + SIGW) /* a leaf child's signedWords: |π|, π, empty trace, σ */

/* The signature's words from the wire: u64 idx ‖ ots ‖ path. */
static uint8_t *put_sig(uint8_t *o, const uint8_t sig[SIG_WIRE]) {
    uint32_t idx = sig[0] | sig[1] << 8 | sig[2] << 16 | (uint32_t)sig[3] << 24;
    put64(o, idx);
    memcpy(o + 8, sig + 4, SIG_WIRE - 4);
    return o + SIGW;
}
/* A leaf child's signedWords: u64 48 ‖ u64 0 ‖ s ‖ u64 n ‖ u64 0 (no trace) ‖ σ. */
static uint8_t *put_leaf(uint8_t *o, const uint8_t s[32], uint64_t n, const uint8_t sig[SIG_WIRE]) {
    put64(o, 48);
    put64(o + 8, 0);
    memcpy(o + 16, s, 32);
    put64(o + 48, n);
    put64(o + 56, 0);
    return put_sig(o + 64, sig);
}
/* The header: u64 tag ‖ sA ‖ u64 nA ‖ sB ‖ u64 nB, then the node's tag word and its two slots. */
static uint8_t *put_head(uint8_t *o, uint64_t tag, const uint8_t sA[32], uint64_t nA,
                         const uint8_t sB[32], uint64_t nB, const uint8_t c1[32]) {
    put64(o, tag);
    memcpy(o + 8, sA, 32);
    put64(o + 40, nA);
    memcpy(o + 48, sB, 32);
    put64(o + 80, nB);
    put64(o + 88, 1);
    memcpy(o + 96, c1, 32);
    memset(o + 128, 0, 32);
    return o + 160;
}

static void handshake(void) {
    char line[64];
    printf("ready\n");
    fflush(stdout);
    if (!fgets(line, sizeof line, stdin) || strncmp(line, "go", 2)) die("no go");
}

/* proof.bin = u64 |π| ‖ π ‖ u64 0 (no trace) ‖ σ, with π = head ‖ left ‖ right. */
static void emit(uint8_t *f, size_t pin, const uint8_t sig[SIG_WIRE]) {
    put64(f, pin);
    put64(f + 8 + pin, 0);
    put_sig(f + 16 + pin, sig);
    writefile("proof.bin", f, 16 + pin + SIGW);
}

static int mode_first(void) {
    static const uint8_t Z[32] = {0};
    handshake();
    uint8_t sig[SIG_WIRE], sigA[SIG_WIRE], sigB[SIG_WIRE], sA[32], sB[32];
    uint64_t nA, nB;
    int k0 = sign_send(), kA = sign_send(), kB = sign_send();
    read_chain("chainA.json", sA, &nA);
    read_chain("chainB.json", sB, &nB);
    size_t pin = 160 + 2 * LEAFW;
    uint8_t *f = malloc(16 + pin + SIGW);
    if (!f) die("out of memory");
    sign_recv(k0, sig);
    sign_recv(kA, sigA);
    sign_recv(kB, sigB);
    uint8_t *o = put_head(f + 8, 3, sA, nA, sB, nB, Z);
    o = put_leaf(o, sA, nA, sigA);
    put_leaf(o, sB, nB, sigB);
    emit(f, pin, sig);
    printf("done\n");
    fflush(stdout);
    return 0;
}

static int mode_step(void) {
    static const uint8_t Z[32] = {0};
    handshake();
    uint8_t sig[SIG_WIRE], sigB[SIG_WIRE], c1[32], sB[32];
    uint64_t nB;
    int k0 = sign_send(), kB = sign_send();
    read_stmt(c1, "prev.stmt");
    read_chain("chain.json", sB, &nB);
    buf prev = readfile("prev.bin");
    /* prev.bin is a child's signedWords byte for byte: its π is a whole number of words (every
       proof this prover writes is) and its trace is empty. */
    if (prev.n < 8 || get64(prev.p) % 8 != 0) die("prev.bin: π not word-aligned");
    size_t pin = 160 + prev.n + LEAFW;
    uint8_t *f = malloc(16 + pin + SIGW);
    if (!f) die("out of memory");
    sign_recv(k0, sig);
    sign_recv(kB, sigB);
    uint8_t *o = put_head(f + 8, 2, Z, 0, sB, nB, c1);
    memcpy(o, prev.p, prev.n);
    put_leaf(o + prev.n, sB, nB, sigB);
    emit(f, pin, sig);
    printf("done\n");
    fflush(stdout);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) die("usage: prover setup|first|step DIR");
    if (chdir(argv[2])) die("cannot enter DIR");
    if (!strcmp(argv[1], "setup")) return 0;
    if (!strcmp(argv[1], "first")) return mode_first();
    if (!strcmp(argv[1], "step")) return mode_step();
    die("unknown mode");
    return 2;
}
