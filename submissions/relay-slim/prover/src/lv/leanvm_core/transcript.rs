// Vendored from leanVM 0b850750 `crates/leanvm_core/src/transcript.rs` (path rewrites as tools/vendor.py; edits: lv/PATCHES.md).
//! The shared Fiat-Shamir transcript (see [`fiat_shamir`] for the state and
//! the prover's transport): the Keccak reduction's functions take this same `ps`
//! state, so the whole stack shares ONE transcript. Scalars ride its stream;
//! the stacked opening's Merkle data rides its opening phases.
pub use crate::lv::fiat_shamir::{FiatShamirState, RATE_SCALARS};

pub type Proof = crate::lv::fiat_shamir::transcript::Proof;
pub type ProverState = crate::lv::fiat_shamir::transcript::ProverState;
