//! leanVM's `leanvm_core` (0b850750): only the bus and table-sumcheck provers (`gkr`, `leaf`, `constraints`,
//! `transcript`), vendored by WP-15b with `tools/vendor.py`'s path rewrites; the module root is new (the
//! items of leanVM's `lib.rs` and `witness::stack_offsets` these files use). Edits: `lv/PATCHES.md`.

pub mod constraints;
pub mod gkr;
pub mod leaf;
pub mod transcript;

/// leanVM `lib.rs`: the target soundness in bits.
pub const SECURITY_BITS: u32 = 128;

/// leanVM `lib.rs`: below this many items a pass runs serially.
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// leanVM `lib.rs`: one named prover stage inside its `tracing` span.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        crate::lv::tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

pub(crate) use crate::lv::primitives::{log2_ceil_usize, log2_strict_usize};

/// leanVM `witness.rs`: largest-first aligned offsets of blocks of `2^kappa` words (`None`: not placed).
pub mod witness {
    pub(crate) fn stack_offsets(kappas: &[Option<usize>]) -> (Vec<usize>, usize) {
        let n = kappas.len();
        let mut order: Vec<usize> = (0..n).filter(|&i| kappas[i].is_some()).collect();
        order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)));
        let mut offsets = vec![0usize; n];
        let mut off = 0usize;
        for &i in &order {
            let kappa = kappas[i].unwrap();
            assert!(kappa < usize::BITS as usize, "kappa {kappa} is a log-size, not a length");
            offsets[i] = off;
            off += 1 << kappa;
        }
        (offsets, off)
    }
}
