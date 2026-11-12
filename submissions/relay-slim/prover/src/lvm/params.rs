//! The parameter record and the schedule, transcribed from the Lean verifier (`LvmParams.lean`,
//! `LvmSchedule.lean` on lvm/VQ; WP-0's `ref/params.py`). The Lean `V_S` is normative; this copy is used
//! to build the WHIR configurations and to check, after every proof, that the prover produced exactly
//! the schedule's sizes (`piSize`, `qS`, the query lengths in order).

/// One queried oracle of a WHIR opening (`Level`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    pub level: usize,
    pub fold: usize,
    pub kappa: usize,
    pub rate: usize,
    pub height: usize,
    pub cap: usize,
    pub path: usize,
    pub t: usize,
    pub row: usize,
}

/// `udQueries sec R`: the least `t` with `(2^R + 1)^t · 2^sec ≤ 2^((R+1) t)`.
pub fn ud_queries(sec: usize, r: usize) -> usize {
    (1..).find(|&t| exact_ok(sec, r, t)).unwrap()
}

/// `(2^R + 1)^t · 2^sec ≤ 2^((R+1) t)` with a small big-integer.
fn exact_ok(sec: usize, r: usize, t: usize) -> bool {
    // base-2^32 limbs
    let mut x: Vec<u64> = vec![1];
    let mul = |x: &mut Vec<u64>, m: u64| {
        let mut carry = 0u64;
        for l in x.iter_mut() {
            let v = *l * m + carry;
            *l = v & 0xffff_ffff;
            carry = v >> 32;
        }
        while carry > 0 {
            x.push(carry & 0xffff_ffff);
            carry >>= 32;
        }
    };
    for _ in 0..t {
        mul(&mut x, (1u64 << r) + 1);
    }
    let bits = |x: &Vec<u64>| -> usize {
        let top = *x.last().unwrap();
        32 * (x.len() - 1) + (64 - top.leading_zeros() as usize)
    };
    // x · 2^sec ≤ 2^e  ⟺  x ≤ 2^(e - sec)
    let e = (r + 1) * t;
    if e < sec {
        return false;
    }
    let k = e - sec;
    let b = bits(&x);
    let popcount: u32 = x.iter().map(|l| l.count_ones()).sum();
    b <= k || (b == k + 1 && popcount == 1)
}

/// The levels of `spec`; `t` is `udQueries sec R`, or `ts[i]` when `ts` is non-empty (JB-VQP J1: `C_main` at the
/// Johnson radius, the query counts given by the record).
fn mk_levels(sec: usize, nu: usize, spec: &[(usize, usize, usize)], ts: &[usize]) -> Vec<Level> {
    assert!(ts.is_empty() || ts.len() == spec.len(), "one query count per level");
    let mut k = nu;
    spec.iter()
        .enumerate()
        .map(|(i, &(l, r, c))| {
            k -= l;
            let h = k + r;
            Level {
                level: i,
                fold: l,
                kappa: k,
                rate: r,
                height: h,
                cap: c,
                path: h - c,
                t: if ts.is_empty() { ud_queries(sec, r) } else { ts[i] },
                row: if i == 0 { 8 << l } else { 24 << l },
            }
        })
        .collect()
}

pub const GKR_DEPTH: usize = 12;
/// S2: the chain tape's GKR is one segment of 24 rounds (`Shape { log_n, 24 }`).
pub const TAPE_DEPTH: usize = 24;
/// `Pad43`'s digest offset in the state (`Λ`: digest bit `p` to state bit `8 + p`).
pub const PAD_SHIFT: usize = 8;
pub const SLOT_LOG: usize = 6;
pub const REC_STREAM_COLS: usize = 17;
pub const REC_COLS: usize = 32;
pub const POSITIONS_PER_ANSWER: usize = 8;
pub const BUS_BITS: usize = 4;
pub const RING_STAGES: usize = 6;
pub const K_BITS: usize = 64;
pub const LANES: usize = 25;
pub const LANE_BITS: usize = 5;
pub const PACK_BITS: usize = 4;
pub const PRODUCT_BITS: usize = 47;
pub const LOCAL_BITS: usize = 11;
pub const SEGMENT_BITS: usize = 1;
pub const E_BYTES: usize = 24;
pub const NODE_BYTES: usize = 32;
pub const SIG_BYTES: usize = 8 + 133 * 32 + 16 * 32;
/// The header up to `σ_leaf` (4,928 B); the accumulator `acc_in` (`D + 1` `E` scalars) follows (A23).
pub const HEADER_BASE: usize = 8 + 8 + 32 + 32 + 32 + 8 + 32 + SIG_BYTES;

/// `D = accVars`: the variables of the fixed-column polynomial `Φ` (A23; `LvmParams.accVars`), the table
/// point's `tableRounds` then the column index's `accLog = D − tableRounds`.
pub const ACC_VARS: usize = 28;

/// The header's length: [`HEADER_BASE`] + `acc_in` (`D + 1` scalars): 5,624 B (`LvmParams.headerBytes`).
pub fn header_bytes(_p: &Params) -> usize {
    HEADER_BASE + E_BYTES * (ACC_VARS + 1)
}

/// The seed query's length: the first answer and the header from byte 8.
pub fn seed_len(p: &Params) -> usize {
    32 + header_bytes(p) - 8
}

/// The parameter record (`Params`).
#[derive(Clone, Debug)]
pub struct Params {
    pub name: &'static str,
    pub log_n: usize,
    pub ks_log: usize,
    pub bits_log: usize,
    pub nu_main: usize,
    pub rec_rows_log: usize,
    pub sec_bits: usize,
    /// PI-GRIND: grinding bits `g` at every WHIR level of both openings (0: none, the v1/S2 schedule). The query
    /// counts are `udQueries (sec − g) R`.
    pub grind: usize,
    pub main_levels: Vec<Level>,
    /// JB-VQP J1 (`whirLevelsJ`, JB-L §3): `C_main`'s opening takes one OOD sample on every level with a next
    /// level (after the next cap: `κ` samples, the value `y`, the intro polynomial's two scalars). `C_rec` takes none.
    pub main_ood: bool,
    pub rec_levels: Vec<Level>,
    pub bus_depth: usize,
    pub leafdec_reads: usize,
    pub table_rounds: usize,
    pub table_evals: usize,
    /// The header array `PUB`'s index among the sumcheck tables (A23: its value column is the one fixed
    /// column outside `Φ`; `LvmParams.pubTab`).
    pub pub_tab: usize,
}

impl Params {
    /// `D`, the variables of `Φ` (= [`ACC_VARS`]).
    pub fn acc_d(&self) -> usize {
        ACC_VARS
    }
    /// `dk = D − tableRounds`: the batching challenges `κ` (`Params.accLog`).
    pub fn acc_log(&self) -> usize {
        ACC_VARS - self.table_rounds
    }
    pub fn nu_rec(&self) -> usize {
        self.rec_rows_log + 5
    }
    pub fn main_final_log(&self) -> usize {
        self.main_levels.last().unwrap().kappa
    }
    pub fn rec_final_log(&self) -> usize {
        self.rec_levels.last().unwrap().kappa
    }
    pub fn levels(&self, com: Com) -> &[Level] {
        match com {
            Com::Main => &self.main_levels,
            Com::Rec => &self.rec_levels,
        }
    }
    pub fn by_name(name: &str) -> Option<Params> {
        match name {
            "P20" | "p20" => Some(p20()),
            "P8" | "p8" => Some(p8()),
            _ => None,
        }
    }
}

/// `main` is the `C_main` levels, any number (S2: three, v1: four), in `refreeze2.py`'s form `[(fold, rate, cap), …]`;
/// `main_t` their query counts (`[]`: `udQueries (sec − g) R`), `main_ood` [`Params::main_ood`].
#[allow(clippy::too_many_arguments)]
fn mk(
    name: &'static str,
    log_n: usize,
    sec: usize,
    grind: usize,
    rec_rows_log: usize,
    nu_main: usize,
    main: impl AsRef<[(usize, usize, usize)]>,
    rec: impl AsRef<[(usize, usize, usize)]>,
    ks_log: usize,
    bits_log: usize,
    fb: (usize, usize, usize, usize),
    pub_tab: usize,
    main_t: impl AsRef<[usize]>,
    main_ood: bool,
) -> Params {
    assert!(grind <= 64 && grind < sec, "{name}: {grind} grinding bits (at most 64, and below sec = {sec})");
    Params {
        name,
        log_n,
        ks_log,
        bits_log,
        nu_main,
        rec_rows_log,
        sec_bits: sec,
        grind,
        main_levels: mk_levels(sec - grind, nu_main, main.as_ref(), main_t.as_ref()),
        main_ood,
        rec_levels: mk_levels(sec - grind, rec_rows_log + 5, rec.as_ref(), &[]),
        bus_depth: fb.0,
        leafdec_reads: fb.1,
        table_rounds: fb.2,
        table_evals: fb.3,
        pub_tab,
    }
}

/// PI-GRIND's grinding bits per set (`LVM_GRIND=std`): P20 14, P8 4.
pub const GRIND_P20: usize = 14;
pub const GRIND_P8: usize = 4;

/// The frozen records' grinding bits (`refreeze2.py` writes them; the default when `LVM_GRIND` is unset).
pub const FROZEN_GRIND_P20: usize = 14;
pub const FROZEN_GRIND_P8: usize = 4;

/// PI-GRIND's switch: `LVM_GRIND` unset gives the frozen record's bits (`frozen`); `std` gives the set's grinding
/// bits ([`GRIND_P20`], [`GRIND_P8`]); empty or `0` gives none; a number `g` gives `g` bits at either set.
pub fn grind_env(std_bits: usize, frozen: usize) -> usize {
    match std::env::var("LVM_GRIND") {
        Err(_) => frozen,
        Ok(v) if v == "std" => std_bits,
        Ok(v) if v.is_empty() => 0,
        Ok(v) => v.parse().unwrap_or_else(|_| panic!("LVM_GRIND: std or a number of bits, not {v:?}")),
    }
}

/// `P20` (BLUEPRINT §3.1); the M3 numbers `(busDepth, leafdecReads, tableRounds, tableEvals)` are INT-2's
/// freeze (`LvmParams.P20`, A21). Grinding bits from `LVM_GRIND` ([`grind_env`]; the frozen record's by default).
pub fn p20() -> Params {
    p20_g(grind_env(GRIND_P20, FROZEN_GRIND_P20))
}

/// `P20` with `g` grinding bits.
pub fn p20_g(g: usize) -> Params {
    // S2 (BLUEPRINT2 §1.4): C_main at ν = 24, three levels
    mk("P20", 20, 129, g, 14, 24, [(6, 1, 8), (4, 2, 7), (4, 3, 7)], [(6, 2, 7), (4, 3, 7)], 15, 13, (21, 1, 16, 2851), 127, [230, 115, 77], true)
}

/// `P8` (WP-0's test set). Grinding bits from `LVM_GRIND` ([`grind_env`]; the frozen record's by default).
pub fn p8() -> Params {
    p8_g(grind_env(GRIND_P8, FROZEN_GRIND_P8))
}

/// `P8` with `g` grinding bits.
pub fn p8_g(g: usize) -> Params {
    // S2 P8 (FRZ-0): rec rows 2^13 and KS 2^14 (the tape's trace overflows 2^12 blocks), three C_main levels
    mk("P8", 9, 20, g, 13, 23, [(6, 1, 4), (4, 2, 4), (4, 3, 4)], [(6, 2, 4), (4, 3, 4)], 14, 12, (21, 1, 16, 2522), 108, [33, 17, 11], true)
}

/// `p` with `C_main` in the unique-decoding regime (PI-GRIND-P's S2G record): `t = udQueries (sec − g) R`, no OOD.
pub fn ud_main(p: Params) -> Params {
    let sec = p.sec_bits - p.grind;
    let main_levels = p.main_levels.iter().map(|l| Level { t: ud_queries(sec, l.rate), ..*l }).collect();
    Params { main_levels, main_ood: false, ..p }
}

// ------------------------------------------------------------------------------------------- the schedule

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Com {
    Main,
    Rec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Item {
    Read(usize),
    Cap(usize, Com, usize),
    Sample,
    Positions(Com, usize),
    Opening(Com, usize),
}

fn rd(m: usize) -> Vec<Item> {
    if m == 0 { vec![] } else { vec![Item::Read(m)] }
}
fn smp(n: usize) -> Vec<Item> {
    vec![Item::Sample; n]
}
fn sumcheck_i(rounds: usize, d: usize) -> Vec<Item> {
    (0..rounds).flat_map(|_| [rd(d), vec![Item::Sample]].concat()).collect()
}
fn keccak_layer_i(point: usize) -> Vec<Item> {
    [rd(PRODUCT_BITS), smp(1), sumcheck_i(point, 2), sumcheck_i(LOCAL_BITS, 3), rd(3), smp(1)].concat()
}
fn tape_layers_i(log_n: usize) -> Vec<Item> {
    (0..TAPE_DEPTH).flat_map(|_| keccak_layer_i(log_n - PACK_BITS)).collect()
}
fn keccak_i(log_steps: usize) -> Vec<Item> {
    let mut v = [smp(SEGMENT_BITS + LANE_BITS), rd(1)].concat();
    for _ in 0..GKR_DEPTH {
        v.extend(keccak_layer_i(log_steps - PACK_BITS + SEGMENT_BITS));
    }
    v.extend([sumcheck_i(SLOT_LOG, 2), rd(1), sumcheck_i(PACK_BITS, 2), sumcheck_i(SLOT_LOG, 2), rd(K_BITS)].concat());
    v
}
fn gp_layers_i(layer: usize, point: usize) -> Vec<Item> {
    if layer == 0 {
        return vec![];
    }
    let step = if layer % 2 == 1 { 1 } else { 2 };
    let mut v = smp(1);
    for _ in 0..point {
        v.extend(rd(1 << step));
        v.extend(smp(1));
    }
    v.extend(rd(3 << step));
    v.extend(smp(step));
    v.extend(gp_layers_i(layer - step, point + step));
    v
}
fn tail_i(n: usize) -> Vec<Item> {
    let mut v = vec![];
    for j in 0..n {
        v.push(Item::Sample);
        if j + 1 < n {
            v.push(Item::Read(2));
        }
    }
    v
}
/// PI-GRIND: a level's separating sample, nonce and PoW sample (none when `g = 0`).
fn grind_i(g: usize) -> Vec<Item> {
    if g == 0 { vec![] } else { [smp(1), rd(1), smp(1)].concat() }
}
fn whir_i(com: Com, levels: &[Level], final_log: usize, g: usize, ood: bool) -> Vec<Item> {
    let mut v = rd(2);
    for (i, l) in levels.iter().enumerate() {
        for _ in 0..l.fold {
            v.extend(smp(1));
            v.extend(rd(2));
        }
        let next = levels.get(i + 1);
        match next {
            None => v.extend(rd(1 << final_log)),
            Some(n) => {
                v.push(Item::Cap(n.cap, com, l.level + 1));
                if ood {
                    // JB-L §3: the OOD point (κ samples, κ = the folded message's variables), `y`, the intro poly
                    v.extend(smp(l.kappa));
                    v.extend(rd(1));
                    v.extend(rd(2));
                }
            }
        }
        v.extend(grind_i(g));
        v.push(Item::Positions(com, l.level));
        v.extend(smp(1));
        v.push(Item::Opening(com, l.level));
        v.extend(rd(2));
        if next.is_none() {
            v.extend(tail_i(final_log));
        }
    }
    v
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Commit,
    Bus,
    Tables,
    /// A23 phase 3b: `κ` (dk samples), `h` (D + 1), `t`, one zero scalar.
    Acc,
    /// S2: T1 (output claim) and T2 (the depth-24 GKR) on the chain digests `D`.
    Tape,
    /// S2: T3 (wiring sumcheck) and T4 (`D` slot reduction, ring switch).
    Wire,
    Ks,
    KsLink,
    OpenRec,
    OpenMain,
}

pub fn phases(p: &Params) -> Vec<(Phase, Vec<Item>)> {
    vec![
        (Phase::Commit, vec![Item::Cap(p.main_levels[0].cap, Com::Main, 0), Item::Cap(p.rec_levels[0].cap, Com::Rec, 0)]),
        (Phase::Bus, [smp(BUS_BITS + 1), rd(2), gp_layers_i(p.bus_depth, 0), rd(p.leafdec_reads)].concat()),
        (Phase::Tables, [smp(1), sumcheck_i(p.table_rounds, 3), rd(p.table_evals)].concat()),
        (Phase::Acc, [smp(p.acc_log()), rd(p.acc_d() + 1), smp(1), rd(1)].concat()),
        (Phase::Tape, [smp(p.log_n), rd(LANES), smp(LANE_BITS), tape_layers_i(p.log_n)].concat()),
        (Phase::Wire, [sumcheck_i(p.log_n, 2), rd(1), sumcheck_i(2, 2), rd(K_BITS), smp(RING_STAGES)].concat()),
        (Phase::Ks, [smp(p.ks_log), rd(LANES), keccak_i(p.ks_log), smp(RING_STAGES)].concat()),
        (Phase::KsLink, [smp(p.ks_log + LANE_BITS), sumcheck_i(p.ks_log, 2), rd(4)].concat()),
        (Phase::OpenRec, [smp(1), whir_i(Com::Rec, &p.rec_levels, p.rec_final_log(), p.grind, false)].concat()),
        (Phase::OpenMain, [smp(1), whir_i(Com::Main, &p.main_levels, p.main_final_log(), p.grind, p.main_ood)].concat()),
    ]
}

pub fn schedule(p: &Params) -> Vec<Item> {
    phases(p).into_iter().flat_map(|(_, v)| v).collect()
}

/// The query classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QClass {
    Q0,
    Seed,
    Fs,
    Leaf,
    Node,
}

/// The query sequence (`queryList`): class and length of every query `V_S` asks.
pub fn query_list(p: &Params) -> Vec<(QClass, usize)> {
    let mut out = vec![(QClass::Q0, 7), (QClass::Seed, seed_len(p))];
    let mut pend = 0usize;
    for it in schedule(p) {
        match it {
            Item::Read(m) => pend += E_BYTES * m,
            Item::Cap(c, _, _) => pend += NODE_BYTES << c,
            Item::Sample => {
                out.push((QClass::Fs, 32 + pend));
                pend = 0;
            }
            Item::Positions(com, lv) => {
                let l = p.levels(com)[lv];
                let n = l.t.div_ceil(POSITIONS_PER_ANSWER);
                out.push((QClass::Fs, 32 + pend));
                pend = 0;
                for _ in 1..n {
                    out.push((QClass::Fs, 32));
                }
            }
            Item::Opening(com, lv) => {
                let l = p.levels(com)[lv];
                for _ in 0..l.t {
                    out.push((QClass::Leaf, l.row));
                    for _ in 0..l.path {
                        out.push((QClass::Node, 64));
                    }
                }
            }
        }
    }
    out
}

/// S2 dev check: `piSize`, `qS` and trace sponge blocks against `2^rec`, for P20 and P8: the frozen records (J1:
/// `C_main` at the Johnson radius with OOD, at `FROZEN_GRIND_*`), then `C_main` in UD at PI-GRIND's bits and without
/// grinding (with the query counts `t` and the positions queries `Σ ⌈t/8⌉`).
pub fn print_numbers() {
    for p in [
        p20_g(FROZEN_GRIND_P20),
        p8_g(FROZEN_GRIND_P8),
        ud_main(p20_g(GRIND_P20)),
        ud_main(p8_g(GRIND_P8)),
        ud_main(p20_g(0)),
        ud_main(p8_g(0)),
    ] {
        let ql = query_list(&p);
        let l: usize = 1 + ql.iter().map(|(_, len)| 40 + len).sum::<usize>();
        let ts: Vec<usize> = p.rec_levels.iter().chain(&p.main_levels).map(|l| l.t).collect();
        let pos: usize = ts.iter().map(|t| t.div_ceil(POSITIONS_PER_ANSWER)).sum();
        println!(
            "{} g {} main_ood {} piSize {} qS {} t (rec; main) {:?} positions queries {} trace blocks {} (2^rec = {})",
            p.name, p.grind, p.main_ood, pi_size(&p), ql.len(), ts, pos, l / 136 + 1, 1usize << p.rec_rows_log
        );
    }
}

/// `piSize`.
pub fn pi_size(p: &Params) -> usize {
    let mut s = header_bytes(p);
    for it in schedule(p) {
        match it {
            Item::Read(m) => s += E_BYTES * m,
            Item::Cap(c, _, _) => s += NODE_BYTES << c,
            Item::Opening(com, lv) => {
                let l = p.levels(com)[lv];
                s += l.t * (l.row + l.path * NODE_BYTES);
            }
            _ => {}
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn frozen_numbers() {
        // the frozen records (`refreeze2.py` writes their numbers and `FROZEN_GRIND_*`); `grind_numbers` names its
        // sets `pg`/`qg` so that refreeze2's rewrites of `p`/`q` do not reach them
        let p = p20_g(FROZEN_GRIND_P20);
        assert_eq!(p.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![230, 115, 77]);
        assert_eq!(p.rec_levels[0].t, 170);
        // A21's record + A23 (D = 28: header + 696 B, phase 3b 12 queries and 30 scalars)
        // S2 (T-P1; BLUEPRINT2 §2.2's model: 9,916 and 1,103,704)
        assert_eq!(query_list(&p).len(), 8295);
        assert_eq!(pi_size(&p), 783192);
        let q = p8_g(FROZEN_GRIND_P8);
        assert_eq!(q.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![33, 17, 11]);
        // S2 P8 (FRZ-0)
        assert_eq!(query_list(&q).len(), 2321);
        assert_eq!(pi_size(&q), 277760);
        // JB-VQP J1: C_main's OOD (P20 κ 18, 14; P8 κ 17, 13) and the trace's sponge blocks
        assert!(p.main_ood && q.main_ood);
        let blocks = |p: &Params| (1 + query_list(p).iter().map(|(_, len)| 40 + len).sum::<usize>()) / 136 + 1;
        assert_eq!((blocks(&p), blocks(&q)), (10533, 3926));
    }

    #[test]
    fn grind_numbers() {
        // PI-GRIND Gate §3: t = udQueries (129 − 14) R (C_main in UD, the S2G record)
        let pg = ud_main(p20_g(GRIND_P20));
        assert_eq!(pg.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![278, 170, 139]);
        assert_eq!(pg.rec_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![170, 139]);
        // PI-GRIND-P's record at g > 0 (dev `s2check`)
        assert_eq!((query_list(&pg).len(), pi_size(&pg)), (9844, 897192));
        let qg = ud_main(p8_g(GRIND_P8));
        assert_eq!(qg.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![39, 24, 20]);
        assert_eq!(qg.rec_levels[0].t, 24);
        assert_eq!((query_list(&qg).len(), pi_size(&qg)), (2547, 294288));
    }
}
