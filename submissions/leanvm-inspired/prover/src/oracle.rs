//! The random oracle the prover hashes with (BLUEPRINT §2.2): every Fiat–Shamir step and every
//! Merkle hash is a query `q ↦ Keccak-256(k ‖ q)` to the service (`service.rs`), or, for tests and
//! measurements without a service, to the same keyed hash in-process (`Local`).
//!
//! One oracle per process, installed once (`install`) and reached from anywhere (`get`), because
//! leanVM's Merkle builder hashes from inside the encoder's worker threads. Every query is counted
//! by class (told apart by length, BLUEPRINT §2.2): requests, queries, bytes, the service's
//! permutations `⌊(32 + |q|)/136⌋ + 1`, and the time the prover spent waiting.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

pub use crate::keccak::Digest;
use crate::keccak::{Keyed, oracle_perms};

/// A trace: queries and their answers, in order.
pub type Trace = Vec<(Vec<u8>, Digest)>;

/// Writes query `i` into the buffer (`build(i, buf)`; the buffer is not cleared by the callee).
pub type Builder<'a> = dyn Fn(usize, &mut Vec<u8>) + Sync + 'a;

pub trait Oracle: Sync + Send {
    /// The answer to one query (a Fiat–Shamir step: sequential, latency-bound).
    fn ask(&self, q: &[u8]) -> Digest;
    /// `out[i] = H(q_i)` for the queries `build` writes, on the calling thread (one connection).
    fn ask_many_here(&self, out: &mut [Digest], build: &Builder) {
        let mut buf = Vec::new();
        for (i, o) in out.iter_mut().enumerate() {
            buf.clear();
            build(i, &mut buf);
            *o = self.ask(&buf);
        }
    }
    /// `out[i] = H(0^pad ‖ rows[i·row_bytes ..][.. row_bytes])` on the calling thread: `ask_many_here` on those
    /// queries (the service overrides it and sends the rows without copying them).
    fn ask_rows_here(&self, out: &mut [Digest], rows: &[u8], row_bytes: usize, pad: usize) {
        self.ask_many_here(out, &|i, buf: &mut Vec<u8>| {
            buf.resize(buf.len() + pad, 0);
            buf.extend_from_slice(&rows[i * row_bytes..][..row_bytes]);
        })
    }
}

/// P-QUICK lever 6: items at least this long go through `ask_rows_here` (the leaves); shorter ones (the
/// 64-byte nodes) are cheaper to copy than to describe by `iovec`s.
const ROWS_MIN: usize = 256;

/// The service's keyed hash computed in-process (no service): `Keccak-256(k ‖ q)`.
pub struct Local(Keyed);

impl Local {
    pub fn keyed(key: &[u8; 32]) -> Self {
        Self(Keyed::new(key))
    }
}

impl Oracle for Local {
    fn ask(&self, q: &[u8]) -> Digest {
        self.0.hash(q)
    }
}

static ORACLE: OnceLock<Box<dyn Oracle>> = OnceLock::new();

/// Install the process's oracle (once).
pub fn install(o: Box<dyn Oracle>) {
    if ORACLE.set(o).is_err() {
        panic!("the oracle is installed once");
    }
}

pub fn get() -> &'static dyn Oracle {
    ORACLE.get().expect("no oracle installed").as_ref()
}

// ------------------------------------------------------------------ statistics

/// Query classes of BLUEPRINT §2.2, by length.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// `q₀` (7 bytes) and the seed
    Seed,
    /// absorb+squeeze `st ‖ msg` and positions `st`
    Fs,
    /// a Merkle leaf (512 or 384 bytes)
    Leaf,
    /// a Merkle node `left ‖ right` (64 bytes)
    Node,
    /// PI-GRIND: a grinding attempt `st ‖ nonce` (56 bytes; not in `V`'s trace, only its accepted one, as `Fs`)
    Grind,
}

pub const CLASSES: [Class; 5] = [Class::Seed, Class::Fs, Class::Leaf, Class::Node, Class::Grind];

struct Counter {
    requests: AtomicU64,
    queries: AtomicU64,
    bytes: AtomicU64,
    perms: AtomicU64,
    wait_ns: AtomicU64,
}

const Z: AtomicU64 = AtomicU64::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const C0: Counter = Counter { requests: Z, queries: Z, bytes: Z, perms: Z, wait_ns: Z };
static STATS: [Counter; 5] = [C0, C0, C0, C0, C0];

fn counter(c: Class) -> &'static Counter {
    &STATS[c as usize]
}

/// A snapshot of one class's counters.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stat {
    pub requests: u64,
    pub queries: u64,
    pub bytes: u64,
    pub perms: u64,
    pub wait_s: f64,
}

pub fn stat(c: Class) -> Stat {
    let k = counter(c);
    let g = |a: &AtomicU64| a.load(Ordering::Relaxed);
    Stat {
        requests: g(&k.requests),
        queries: g(&k.queries),
        bytes: g(&k.bytes),
        perms: g(&k.perms),
        wait_s: g(&k.wait_ns) as f64 * 1e-9,
    }
}

pub fn reset_stats() {
    GRIND_WALL_NS.store(0, Ordering::Relaxed);
    for k in &STATS {
        for a in [&k.requests, &k.queries, &k.bytes, &k.perms, &k.wait_ns] {
            a.store(0, Ordering::Relaxed);
        }
    }
}

fn note(c: Class, requests: u64, lens: impl Iterator<Item = usize>, t: Instant) {
    let k = counter(c);
    let (mut n, mut b, mut p) = (0u64, 0u64, 0u64);
    for len in lens {
        n += 1;
        b += len as u64;
        p += oracle_perms(len);
    }
    k.requests.fetch_add(requests, Ordering::Relaxed);
    k.queries.fetch_add(n, Ordering::Relaxed);
    k.bytes.fetch_add(b, Ordering::Relaxed);
    k.perms.fetch_add(p, Ordering::Relaxed);
    k.wait_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
}

/// The class of a Fiat–Shamir-side query (seed or not).
pub fn ask(c: Class, q: &[u8]) -> Digest {
    let t = Instant::now();
    let a = get().ask(q);
    note(c, 1, std::iter::once(q.len()), t);
    a
}

/// PI-GRIND: the grinding rounds' wall time (the class's `wait_s` is thread-seconds, as for the other classes).
static GRIND_WALL_NS: AtomicU64 = AtomicU64::new(0);

/// PI-GRIND: one round of `n` grinding attempts (56 bytes each) in `tasks` batches on as many threads, which
/// took since `t`.
pub fn note_grind(n: usize, tasks: usize, t: Instant) {
    let wall = t.elapsed().as_nanos() as u64;
    let k = counter(Class::Grind);
    let per = n.div_ceil(tasks.max(1));
    k.requests.fetch_add(tasks as u64 * requests_for(per, 56 * per), Ordering::Relaxed);
    k.queries.fetch_add(n as u64, Ordering::Relaxed);
    k.bytes.fetch_add(56 * n as u64, Ordering::Relaxed);
    k.perms.fetch_add(n as u64 * oracle_perms(56), Ordering::Relaxed);
    k.wait_ns.fetch_add(tasks as u64 * wall, Ordering::Relaxed);
    GRIND_WALL_NS.fetch_add(wall, Ordering::Relaxed);
}

/// PI-GRIND: the grinding rounds' wall time so far, in seconds.
pub fn grind_wall_s() -> f64 {
    GRIND_WALL_NS.load(Ordering::Relaxed) as f64 * 1e-9
}

/// Items of a batch request (`service.rs` `BATCH_ITEMS`, `BATCH_BYTES`), for the request count.
fn requests_for(items: usize, bytes: usize) -> u64 {
    let by_items = items.div_ceil(crate::service::BATCH_ITEMS);
    let by_bytes = bytes.div_ceil(crate::service::batch_bytes());
    by_items.max(by_bytes).max(usize::from(items > 0)) as u64
}

/// `out[i] = H(item_i)` for the fixed-size items of `data` (`len` bytes each), on this thread.
pub fn hash_items(c: Class, data: &[u8], len: usize, out: &mut [Digest]) {
    assert_eq!(data.len(), len * out.len());
    let t = Instant::now();
    if len >= ROWS_MIN {
        get().ask_rows_here(out, data, len, 0);
    } else {
        get().ask_many_here(out, &|i, buf: &mut Vec<u8>| buf.extend_from_slice(&data[i * len..][..len]));
    }
    note(c, requests_for(out.len(), data.len()), std::iter::repeat_n(len, out.len()), t);
}

/// `out[i] = H(0^(leaf_bytes - row_bytes) ‖ row_i)` for the rows of `rows` (`row_bytes` each).
pub fn hash_padded(c: Class, rows: &[u8], row_bytes: usize, leaf_bytes: usize, out: &mut [Digest]) {
    assert_eq!(rows.len(), row_bytes * out.len());
    assert!(row_bytes <= leaf_bytes);
    let pad = leaf_bytes - row_bytes;
    let t = Instant::now();
    if row_bytes >= ROWS_MIN {
        get().ask_rows_here(out, rows, row_bytes, pad);
    } else {
        get().ask_many_here(out, &|i, buf: &mut Vec<u8>| {
            buf.resize(buf.len() + pad, 0);
            buf.extend_from_slice(&rows[i * row_bytes..][..row_bytes]);
        });
    }
    note(c, requests_for(out.len(), leaf_bytes * out.len()), std::iter::repeat_n(leaf_bytes, out.len()), t);
}

pub fn report() -> String {
    let mut s = String::new();
    let mut tot = Stat::default();
    for c in CLASSES {
        let x = stat(c);
        s += &format!(
            "  oracle {:<5} requests {:>9} queries {:>10} bytes {:>13} perms {:>11} wait {:>8.3} s\n",
            format!("{c:?}"),
            x.requests,
            x.queries,
            x.bytes,
            x.perms,
            x.wait_s
        );
        tot.requests += x.requests;
        tot.queries += x.queries;
        tot.bytes += x.bytes;
        tot.perms += x.perms;
        tot.wait_s += x.wait_s;
    }
    s += &format!(
        "  oracle total requests {:>9} queries {:>10} bytes {:>13} perms {:>11} wait {:>8.3} s (thread-seconds)\n",
        tot.requests, tot.queries, tot.bytes, tot.perms, tot.wait_s
    );
    s
}
