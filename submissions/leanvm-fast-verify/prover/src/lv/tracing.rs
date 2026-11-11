//! A stand-in for the `tracing` crate's `info_span!`, the only part leanVM's prover crates use.
//! A span is a named timer: with `LVM_PROF=1` every closed span adds its wall time to a table
//! that `report` prints (top-level spans of the same name are summed); otherwise it is free.

use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering};
use std::time::Instant;

static ON: AtomicU8 = AtomicU8::new(2);
static TABLE: Mutex<Vec<(&'static str, f64, u64)>> = Mutex::new(Vec::new());

pub fn enabled() -> bool {
    match ON.load(Ordering::Relaxed) {
        2 => {
            let on = std::env::var("LVM_PROF").is_ok_and(|v| v == "1");
            ON.store(on as u8, Ordering::Relaxed);
            on
        }
        v => v == 1,
    }
}

pub struct Span {
    name: &'static str,
    start: Option<Instant>,
}

impl Span {
    pub fn new(name: &'static str) -> Self {
        Self { name, start: None }
    }
    pub fn in_scope<R>(&self, f: impl FnOnce() -> R) -> R {
        let t = enabled().then(Instant::now);
        let r = f();
        if let Some(t) = t {
            add(self.name, t.elapsed().as_secs_f64());
        }
        r
    }
    /// Timed from here to the drop.
    pub fn entered(mut self) -> Self {
        self.start = enabled().then(Instant::now);
        self
    }
}

impl Drop for Span {
    fn drop(&mut self) {
        if let Some(t) = self.start.take() {
            add(self.name, t.elapsed().as_secs_f64());
        }
    }
}

fn add(name: &'static str, s: f64) {
    let mut t = TABLE.lock().unwrap();
    match t.iter_mut().find(|e| e.0 == name) {
        Some(e) => {
            e.1 += s;
            e.2 += 1;
        }
        None => t.push((name, s, 1)),
    }
}

/// Record a named interval measured elsewhere (the drivers' own stages).
pub fn record(name: &'static str, s: f64) {
    if enabled() {
        add(name, s);
    }
}

pub fn report() -> String {
    let t = TABLE.lock().unwrap();
    t.iter().map(|(n, s, c)| format!("  span {n:<24} {:>9.3} s  ×{c}\n", s)).collect()
}

macro_rules! info_span {
    ($name:expr $(, $($rest:tt)*)?) => {
        $crate::lv::tracing::Span::new($name)
    };
}
pub(crate) use info_span;
