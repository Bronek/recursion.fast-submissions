//! The bus and table-sumcheck phases with no flush yet (WP-15a; the null instance sent to WP-11a): the push,
//! pull and count trees are all ONE over `2^bus_depth` leaves, so the grand-product GKR (leanVM
//! `verify_gkr_grand_products`, the Lean `gpI`) has roots 1, 1, count 1, every round polynomial constant
//! (sent tail all zero) and every child 1; the leaf decomposition sends `leafdec_reads` zeros; the tables owe
//! nothing (totals 0), so the table sumcheck runs from 0 with zero round polynomials and zero evaluations.
//! WP-15b replaces this by the real leaves (LoopIR, BITS, the memory view) through leanVM's `gkr`/`leaf`/
//! `constraints`; the transcript shape is the schedule's either way.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::primitives::field::F192;
use crate::lvm::params::{BUS_BITS, Params};

pub fn prove_null_bus(ps: &mut ProverState, p: &Params) {
    let _alphas = ps.sample_vec(BUS_BITS);
    let _beta = ps.sample();
    ps.add_scalars(&[F192::ONE, F192::ONE]);
    let (mut layer, mut point) = (p.bus_depth, 0usize);
    while layer > 0 {
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let _combiner = ps.sample();
        for _ in 0..point {
            ps.add_scalars(&vec![F192::ZERO; 1 << step]);
            ps.sample();
        }
        ps.add_scalars(&vec![F192::ONE; 3 << step]);
        ps.sample_vec(step);
        point += step;
        layer -= step;
    }
    ps.add_scalars(&vec![F192::ZERO; p.leafdec_reads]);
}

/// Returns the table point (round `j` binds variable `τ* − 1 − j`).
pub fn prove_null_tables(ps: &mut ProverState, p: &Params) -> Vec<F192> {
    let _xi = ps.sample();
    let mut r = vec![F192::ZERO; p.table_rounds];
    for j in 0..p.table_rounds {
        ps.add_scalars(&[F192::ZERO; 3]);
        r[p.table_rounds - 1 - j] = ps.sample();
    }
    ps.add_scalars(&vec![F192::ZERO; p.table_evals]);
    r
}
