-- New for lvm2 (T-Q): the wire gadget's closed forms (`LvmQEqWire`) against V_S's `FE` evaluators
-- (T-V's `msEvalF`, `thrEvalF`, through `FE.toExt3` and T-K's `msEvalA_bitsE`, `thrEvalA_bitsE`).
import LvmQEqWire
import LvmVEqWire
import LvmQSigDefs

/-!
# The wire gadget against V_S (`LvmQWireSound`)

The rows compute T-K's circuit twins: `q4E (msStepC …) = msStepA …`, `p2E (thrTailC …) = thrTailA …`,
`toExt3 (msC …) = msEvalA … 1`, `toExt3 (thrC …) = thrEvalA …`. With the bits of `m` in the cells
(`toExt3` of them is `bitsE m w`), T-K's `*_bitsE` and T-V's `toExt3_*F` give
**`msC_eq_msEvalF`** and **`thrC_eq_thrEvalF`**: the circuit's values are V_S's.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM Lvm.VEq Lvm.VEq.Wr

local notation "tE" => FE.toExt3

/-! ## `msEvalA` -/

/-- Four `FE` entries as T-K's automaton vector over `E`. -/
def q4E (q : Q4F) : Lvm.WK.MS4 := ⟨tE q.1, tE q.2.1, tE q.2.2.1, tE q.2.2.2⟩

theorem q4E_msStepC (a r b : FE) (q : Q4F) :
    q4E (msStepC a r b q) = Lvm.WK.msStepA (tE a) (tE r) (tE b) (q4E q) := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  unfold q4E msStepC mixC msStepTC Lvm.WK.msStepA Lvm.WK.msStep
  simp only [Lvm.WK.nextS, Lvm.WK.eqBit, Lvm.WK.MS4.get, Bool.not_true, Bool.not_false, ite_true,
    Bool.false_eq_true, ite_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false]
  simp only [M3.tE_add, M3.tE_mul, M3.tE_one, Lvm.WK.MS4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem q4E_msTailC : ∀ (σ ρ tb : List FE),
    q4E (msTailC σ ρ tb) = Lvm.WK.msTailA (σ.map tE) (ρ.map tE) (tb.map tE)
  | a :: σ, r :: ρ, b :: tb => by
    rw [msTailC, q4E_msStepC, q4E_msTailC σ ρ tb]; rfl
  | [], _, _ => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]
  | _ :: _, [], _ => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]
  | _ :: _, _ :: _, [] => by
    show (⟨tE 1, tE 0, tE 0, tE 0⟩ : Lvm.WK.MS4) = ⟨1, 0, 0, 0⟩
    rw [M3.tE_one, M3.tE_zero]

theorem tE_listSum : ∀ (l : List FE), tE l.sum = (l.map tE).sum
  | [] => M3.tE_zero
  | x :: l => by rw [List.sum_cons, M3.tE_add, tE_listSum l, List.map_cons, List.sum_cons]

theorem tE_eqAt (A : List FE) {i : Nat} (hi : i < 2 ^ A.length) :
    tE (eqAt A i) = LeanVM.Protocol.KeccakGkr.eqAt (A.map tE) i := getD_eqKernel A hi

theorem tE_ltC {tb4 : List FE} (h4 : tb4.length = 4) {e : Nat} (he : e ≤ 16) :
    tE (ltC tb4 e) = Lvm.WK.ltE (tb4.map tE) e := by
  rw [ltC, tE_listSum, Lvm.WK.ltE, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  exact tE_eqAt _ (by rw [h4]; have := List.mem_range.mp hj; omega)

theorem tE_getD (l : List FE) (i : Nat) : tE (l.getD i 0) = (l.map tE).getD i 0 := (getD_map_toExt3 l i).symm

/-- **The rows' `msEvalA`**: `toExt3 (msC ρ μ σ tb) = msEvalA ρ μ σ tb 1` (`|σ| = |tb| ≥ 4`). -/
theorem tE_msC {ρ μ σ tb : List FE} (hσ : 4 ≤ σ.length) (htb : 4 ≤ tb.length) :
    tE (msC ρ μ σ tb) = Lvm.WK.msEvalA (ρ.map tE) (μ.map tE) (σ.map tE) (tb.map tE) 1 := by
  have h4 : (σ.take 4).length = 4 := by rw [List.length_take]; omega
  have ht4 : (tb.take 4).length = 4 := by rw [List.length_take]; omega
  have hq := q4E_msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)
  have h00 := congrArg Lvm.WK.MS4.v00 hq
  have h01 := congrArg Lvm.WK.MS4.v01 hq
  have h10 := congrArg Lvm.WK.MS4.v10 hq
  simp only [q4E] at h00 h01 h10
  unfold Lvm.WK.msEvalA
  rw [List.length_map, ← List.map_drop, ← List.map_take, ← List.map_drop]
  dsimp only
  rw [← h00, ← h01, ← h10, one_mul,
    LeanVM.Protocol.KeccakGkr.sumE_eq_sum, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, ← List.map_take, ← List.map_take]
  unfold msC
  simp only [M3.tE_add, M3.tE_mul, tE_listSum, List.map_map]
  have hA : ∀ d < 16, tE (eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0) =
      LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d * (μ.map tE).getD ((d + 1) % 16) 0 := by
    intro d hd; rw [M3.tE_mul, tE_eqAt _ (by rw [h4]; omega), tE_getD]
  rw [tE_eqAt _ (by rw [h4]; omega), tE_getD, show (15 + 1) % 16 = 0 from rfl]
  have s1 : (List.range 15).map (tE ∘ fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * ltC (tb.take 4) (d + 1)) =
      (List.range 15).map fun d => LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d *
        (μ.map tE).getD ((d + 1) % 16) 0 * Lvm.WK.ltE ((tb.take 4).map tE) (d + 1) :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [M3.tE_mul, hA d (by omega), tE_ltC ht4 (by omega)]
  have s2 : (List.range 15).map (tE ∘ fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0) =
      (List.range 15).map fun d => LeanVM.Protocol.KeccakGkr.eqAt ((σ.take 4).map tE) d *
        (μ.map tE).getD ((d + 1) % 16) 0 :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [hA d (by omega)]
  rw [s1, s2]
  ring

/-! ## `thrEvalA` -/

theorem p2E_thrStepC (r b : FE) (q : FE × FE) :
    p2E (thrStepC r b q) =
      (tE b * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).1) + (1 + tE b) * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).2),
        tE b * ((1 + tE r) * (p2E q).1 + tE r * (p2E q).2) + (1 + tE b) * ((1 + tE r) * (p2E q).2 + tE r * (p2E q).2)) := by
  obtain ⟨q1, q2⟩ := q
  simp only [p2E, thrStepC, M3.tE_add, M3.tE_mul, Prod.mk.injEq]
  constructor
  · linear_combination (-(tE b * tE q1 + tE b * tE r * tE q1)) * (CharTwo.two_eq_zero (R := LeanVM.Parameters.E))
  · linear_combination (-(tE r * tE q2 + tE b * tE r * tE q2)) * (CharTwo.two_eq_zero (R := LeanVM.Parameters.E))

theorem p2E_thrTailC : ∀ (ρ tb : List FE), p2E (thrTailC ρ tb) = Lvm.WK.thrTailA (ρ.map tE) (tb.map tE)
  | r :: ρ, b :: tb => by
    rw [thrTailC, p2E_thrStepC, p2E_thrTailC ρ tb]
    simp only [List.map_cons, Lvm.WK.thrTailA, Lvm.WK.nextS, Bool.false_and, Bool.true_and, Bool.false_or,
      Bool.true_or, ite_true, Bool.false_eq_true, ite_false]
  | [], _ => by show (tE 1, tE 0) = (1, 0); rw [M3.tE_one, M3.tE_zero]
  | _ :: _, [] => by show (tE 1, tE 0) = (1, 0); rw [M3.tE_one, M3.tE_zero]

/-- **The rows' `thrEvalA`**. -/
theorem tE_thrC {ρ μ tb : List FE} (hμ : μ.length = 16) (htb : 4 ≤ tb.length) :
    tE (thrC ρ μ tb) = Lvm.WK.thrEvalA (ρ.map tE) (μ.map tE) (tb.map tE) := by
  have ht4 : (tb.take 4).length = 4 := by rw [List.length_take]; omega
  have hq := p2E_thrTailC ρ (tb.drop 4)
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  simp only [p2E] at h1 h2
  unfold Lvm.WK.thrEvalA
  rw [← List.map_drop]
  dsimp only
  rw [← h1, ← h2, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, LeanVM.Protocol.KeccakGkr.sumE_eq_sum,
    ← List.map_take]
  unfold thrC
  simp only [M3.tE_add, M3.tE_mul, tE_listSum, List.map_map]
  have s1 : (List.range 16).map (tE ∘ fun d => μ.getD d 0 * ltC (tb.take 4) d) =
      (List.range 16).map fun d => (μ.map tE).getD d 0 * Lvm.WK.ltE ((tb.take 4).map tE) d :=
    List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [M3.tE_mul, tE_getD, tE_ltC ht4 (by omega)]
  have s2 : μ.map tE = (List.range 16).map fun d => (μ.map tE).getD d 0 := by
    apply List.ext_getElem (by simp [hμ])
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, show i < μ.length by simpa using h1]
  have s3 : (μ.map tE).sum = ((List.range 16).map fun d => (μ.map tE).getD d 0).sum := congrArg List.sum s2
  rw [s1, s3]
  ring

/-! ## The bits of `m` and V_S's evaluators -/

/-- Bit `j` of `t` as an `FE` (`0` or `1`; the borrow chain's cells, HAR's `bitE`). -/
def bitF (t j : Nat) : FE := if t.testBit j then 1 else 0

theorem bitsF_E : ∀ (t w : Nat), ((List.range w).map (bitF t)).map tE = LeanVM.Protocol.KeccakGkr.bitsE t w
  | _, 0 => rfl
  | t, w + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, LeanVM.Protocol.KeccakGkr.bitsE]
    congr 1
    · simp only [bitF, Nat.testBit_zero]
      split_ifs with h1 h2 h2
      · exact M3.tE_one
      · simp at h1; omega
      · simp at h1; omega
      · exact M3.tE_zero
    · rw [← bitsF_E (t / 2) w, List.map_map, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, bitF, Nat.testBit_succ]

theorem bitsF_length (t w : Nat) : ((List.range w).map (bitF t)).length = w := by simp

/-- **`K̃_ch(σ)` in the circuit is V_S's**: the rows' `msC` on the bits of `m` is `msEvalF ρ μ σ 0 m`
(`|σ| = |ρ| + 4`, `m < 2^|σ|`). -/
theorem msC_eq_msEvalF {ρ μ σ : List FE} {m : Nat} (hσ : σ.length = ρ.length + 4) (hm : m < 2 ^ σ.length) :
    msC ρ μ σ ((List.range σ.length).map (bitF m)) = msEvalF ρ μ σ 0 m := by
  apply FE.toExt3_injective
  rw [tE_msC (by omega) (by simp; omega), toExt3_msEvalF, bitsF_E,
    ← Lvm.WK.msEvalA_bitsE _ _ _ 0 m (by simp; omega) (by simp; omega) (by simpa using hm)]
  congr 1
  · simp
  · rw [List.length_map, hσ, Nat.add_sub_cancel, List.drop_eq_nil_of_le (by simp)]; rfl

/-- **`Σ_{i ≤ m} ι(i)` in the circuit is V_S's** (`m < 2^(|ρ| + 4)`). -/
theorem thrC_eq_thrEvalF {ρ μ : List FE} {m : Nat} (hμ : μ.length = 16) (hm : m < 2 ^ (ρ.length + 4)) :
    thrC ρ μ ((List.range (ρ.length + 4)).map (bitF m)) = thrEvalF ρ μ m := by
  apply FE.toExt3_injective
  rw [tE_thrC hμ (by simp), toExt3_thrEvalF, bitsF_E]
  have := Lvm.WK.thrEvalA_bitsE (ρ.map tE) (μ.map tE) m (by simpa using hm)
  rwa [List.length_map] at this

/-! ## The wiring target -/

theorem eqAtF_zero : ∀ (ρ : List FE), eqAtF ρ 0 = (ρ.map (1 + ·)).prod
  | [] => rfl
  | r :: ρ => by
    rw [eqAtF, eqAtF_zero ρ, List.map_cons, List.prod_cons]
    simp

/-- `ω_j` of a represented (non-first) claim is `wOm` of its carried `a`, `B`. -/
theorem wOm_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) {j : Nat} (hj : j < 1600) :
    wOm (repA P cv) (repB P cv) j = C.weights.getD j 0 := by
  rw [hR.weights, if_neg (by decide), lt_pos _ _ hj, wOm]
  rfl

theorem c43_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) :
    wC43 (repA P cv) (repB P cv) = c43DotF C.weights.toArray := by
  simp only [wC43, c43DotF, array_getD_toArray', wOm_rep hR (by norm_num : (0 : Nat) < 1600),
    wOm_rep hR (by norm_num : (1 : Nat) < 1600), wOm_rep hR (by norm_num : (6 : Nat) < 1600),
    wOm_rep hR (by norm_num : (264 : Nat) < 1600), wOm_rep hR (by norm_num : (1087 : Nat) < 1600)]

/-- The bits of a digest's four lanes as `FE` (`0`/`1`), bit `p` of lane `p / 64`. -/
def digBitsF (d : List FK) : List FE :=
  (List.range 256).map fun q => if (d.getD (q / 64) 0).val.toNat.testBit (q % 64) then 1 else 0

theorem padDot_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) (d : List FK) :
    wC43 (repA P cv) (repB P cv) + ((List.range 256).map fun q =>
      wOm (repA P cv) (repB P cv) (8 + q) * (digBitsF d).getD q 0).sum = padDotF C.weights.toArray d := by
  rw [padDotF, c43_rep hR, sumE_eq_sum]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  have hq' := List.mem_range.mp hq
  rw [wOm_rep hR (by omega), array_getD_toArray']
  simp only [digBitsF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq', Option.map_some,
    Option.getD_some]
  split_ifs <;> simp

/-- **The rows' target is V_S's `wireTargetF`**, for a represented claim with `|ρ| = P + 1`, `m`'s bits and
`s`'s bits. -/
theorem wTgt_eq {P : Nat} {cv : Nat → FE} {C : KeccakClaim} (hR : Rep P cv C false) (s : List FK) {n : Nat}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ (P + 5)) :
    wTgt (cv 0) ((List.range 16).map fun i => cv (1 + i)) ((List.range (P + 1)).map fun i => cv (18 + i))
      (repA P cv) (repB P cv) ((List.range (P + 5)).map (bitF (n - 1))) (digBitsF s) =
      wireTargetF s n C := by
  have hpt : C.point.length = P + 1 := by rw [← hR.point]; simp
  have hmu : C.mu.length = 16 := by rw [← hR.mu]; simp
  unfold wTgt wireTargetF
  rw [show ((List.range (P + 1)).map fun i => cv (18 + i)) = C.point from hR.point,
    show ((List.range 16).map fun i => cv (1 + i)) = C.mu from hR.mu, hR.value,
    show P + 5 = C.point.length + 4 by omega, thrC_eq_thrEvalF hmu (by rw [hpt, show P + 1 + 4 = P + 5 by omega]; omega),
    padDot_rep hR, c43_rep hR]
  simp only [Lvm.iotaF, Nat.zero_div, Nat.zero_mod, eqAtF_zero]
  ring

/-! ## The bits of the child's `s` (S2's `sSpec` class) -/

/-- **The `BITS` outputs of `s`'s lanes** (`sSpec`): bit `z` of the stream lane `hd + 9 + l` at
`sb + 64 l + z`. -/
def SBitsS (v : Nat → FK) (hd sb : Nat) : Prop :=
  ∀ l < 4, ∀ z < 64, Lvm.QSig.Out1 v (hd + 9 + l) (.bit z) (sb + 64 * l + z)

theorem bitWord (w : UInt64) {z : Nat} (hz : z < 64) :
    (Lvm.Bits.BOut.bit z).word w = if w.toNat.testBit z then 1 else 0 := by
  simp only [Lvm.Bits.BOut.word]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hz' : z.toUInt64.toNat % 64 = z := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [hz', show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split_ifs with h <;> simp [Nat.testBit, Nat.shiftRight_eq_div_pow] at h ⊢ <;> omega

/-- **The `s` bit cells hold `digBitsF` of `s`'s lanes.** -/
theorem sbits_vals {v : Nat → FK} {hd sb : Nat} (h : SBitsS v hd sb) :
    ((List.range 256).map fun q => FE.ofK (v (sb + q))) = digBitsF ((List.range 4).map fun l => v (hd + 9 + l)) := by
  unfold digBitsF
  refine List.map_congr_left fun q hq => ?_
  have hq' := List.mem_range.mp hq
  have h1 := h (q / 64) (by omega) (q % 64) (Nat.mod_lt _ (by omega))
  rw [show sb + 64 * (q / 64) + q % 64 = sb + q by omega] at h1
  unfold Lvm.QSig.Out1 at h1
  rw [h1, bitWord _ (Nat.mod_lt _ (by omega))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show q / 64 < 4 by omega),
    Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- **`dRange` needs no circuit**: Q_sig's `ChildOk` already asserts `1 ≤ n' ∧ n' ≤ 2^ln` on the child's header
lane `n'` (`LvmQSigDefs.ChildOk`, `ln = logN` in `cfg20`/`cfg8`), so V_S's range `require` keeps the flag. -/
theorem dRange_run (pp : Params) (pub : Pub) (sig : ByteArray) (s : RS) (h1 : 1 ≤ pub.n)
    (h2 : pub.n ≤ 2 ^ pp.logN) : dRange pp pub sig s = ((), s) := by
  unfold dRange
  rw [require_run]
  simp [h1, h2]

/-! ## The gadget -/

section gadget

open Lvm.Loop Lvm.Loop.Build Lvm.Har

theorem log2_cover (w : Nat) (hw : 1 ≤ w) : w ≤ 2 ^ Nat.log2 (2 * w - 1) := by
  have h := Nat.lt_log2_self (n := 2 * w - 1)
  rw [Nat.pow_succ] at h
  omega

theorem tassert_one {ins : List Ins} {M : Mem} {p : Ptr} :
    SegsAssert M p (loop [] (tplOf ins) p).2 ↔ TAssert (iterXv M ⟨p, [], tplOf ins⟩ 0) (iterF M ⟨p, [], tplOf ins⟩ 0) ins := by
  rw [segsAssert_loop_iff]
  exact ⟨fun h => h 0 (by simp), fun h jf hjf => by rw [show jf = 0 by simpa using hjf]; exact h⟩

/-- **The wire gadget's cells and assertions**, in the stream's values (`v = feAt Σ`): the wiring
challenges are `F`'s sumcheck challenges from the rows' target, `g_D` and the slices are the stream's
scalars, the slot challenges are the slot sumcheck's from `g_D`, the ring switch's cells are
`ringG_spec`'s; with the gate `1`, the assertions hold iff the two checks do (the final check with
the rows' `msC`, the slot check with the rows' `ω`). -/
theorem wire_core {c : Ctx} {M : Mem} {p : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : wireEnd P qw + 2 ≤ T) (hmb : mb.length = P + 5) (hsb : sb.length = 256) (hzE : M.e zE = 0)
    (h : SegsHold c M p (wireGadget P qw cv mb sb b zE p).2) :
    let tgt := wTgt ((cv 0).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
      ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 6).map fun i => (cv (44 + P + i)).val M)
      ((List.range 25).map fun l => (cv (19 + P + l)).val M) (vs M mb) (vs M sb)
    let sc := scSpec (feAt sig) 3 (8 * qw - 40) tgt (List.replicate (P + 5) none)
    let g := feAt sig (8 * (qw + 15 * (P + 5)))
    let sl := scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40) g (List.replicate 2 none)
    vs M (wireGadget P qw cv mb sb b zE p).1.sigma = sc.1 ∧
    (wireGadget P qw cv mb sb b zE p).1.gD.val M = g ∧
    vs M (wireGadget P qw cv mb sb b zE p).1.tau = sl.1 ∧
    vs M (wireGadget P qw cv mb sb b zE p).1.ring.cs = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) ∧
    (wireGadget P qw cv mb sb b zE p).1.ring.target.val M =
      polyEval ((slAt sig (qw + 15 * (P + 5) + 33)).map (phiMap · (chsAt sig (qw + 15 * (P + 5) + 225)))) gen ∧
    (b.val M = 1 → SegsAssert M p (wireGadget P qw cv mb sb b zE p).2 →
      msC ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
          sc.1 (vs M mb) * g + sc.2 = 0 ∧
      sl.2 + ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0).sum = 0) := by
  intro tgt sc g sl
  have hTe : wireEnd P qw = qw + 15 * (P + 5) + 225 + 54 := rfl
  simp only [wireGadget, hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq] at h ⊢
  obtain ⟨hPre, hSc, hPost, hSl, hSlot, hRing, -⟩ := h
  -- the target block
  set G := preW P (fun j => gkS (cv j)) (mb.map gkS) (sb.map gkS) (gkS b) 0 with hG
  have hpre0 := thold_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨ez, fz, eo, fo, eom, fom, elt, flt, etg, ftg⟩ :=
    preW_spec (P := P) (cv := fun j => gkS (cv j)) (mb := mb.map gkS) (sb := sb.map gkS) (b := gkS b)
      (by simp [hmb]) (by simp [hsb]) hpre0
  have hvs : ∀ l : List Cell, vals (iterXv M ⟨p, [], tplOf G.2⟩ 0) (iterF M ⟨p, [], tplOf G.2⟩ 0) (l.map gkS) = vs M l :=
    fun l => by simp only [vals, List.map_map, vs]; exact List.map_congr_left fun x _ => gkS_valF M _ 0 _ x
  simp only [gkS_valF, hvs] at etg eom
  have htg : (G.1.target.gkCell ⟨p, [], tplOf G.2⟩).val M = tgt := by rw [gkCell_val M _ ftg, etg]
  simp only [gk_loop_fst] at hSc hPost hSl hSlot hRing ⊢
  generalize p.adv (loop [] (tplOf G.2) p).2 = p1 at hSc hPost hSl hSlot hRing ⊢
  -- the wiring sumcheck
  obtain ⟨hc1, hv1⟩ := gk_sc_lists (D := Nat.log2 (2 * (P + 5) - 1)) (R := P + 5) (log2_cover _ (by omega))
    (by omega) hq hS (by simp only [roundLanes]; omega) hSc
  rw [htg] at hc1 hv1
  set pre : LoopOut := ⟨p, [], tplOf G.2⟩ with hpre
  set scO := (scGadget (Nat.log2 (2 * (P + 5) - 1)) 2 qw .plain (G.1.target.gkCell pre) p1).1 with hscO
  generalize p1.adv (scGadget (Nat.log2 (2 * (P + 5) - 1)) 2 qw .plain (G.1.target.gkCell pre) p1).2 = p2
    at hPost hSl hSlot hRing ⊢
  -- the final check block
  set H := postW P (qw + 15 * (P + 5)) (fun j => gkS (cv j)) (mb.map gkS)
    (((List.range (P + 5)).map fun i => scO.cell 2 i).map gkS) (G.1.lt.map (Src.gkOut pre)) (G.1.z.gkOut pre)
    (G.1.one.gkOut pre) (gkS (scO.cell 5 (P + 5 - 1))) (gkS b) 0 with hH
  have hpost0 := thold_of_loop hPost (jf := 0) (by simp)
  rw [gk_loop_fst] at hpost0
  set post : LoopOut := ⟨p2, [], tplOf H.2⟩ with hpost
  have hpv : ∀ (o : LoopOut), vals (iterXv M o 0) (iterF M o 0) ((mb.map gkS).take 4) = (vs M mb).take 4 :=
    fun o => by
      simp only [vals, List.map_take, List.map_map, vs]
      rw [List.map_congr_left (l := mb) (f := Src.valF (iterXv M o 0) (iterF M o 0) ∘ gkS) (g := Cell.val M)
        fun x _ => gkS_valF M o 0 _ x]
  have hltP : vals (iterXv M post 0) (iterF M post 0) (G.1.lt.map (Src.gkOut pre)) =
      (List.range 17).map (ltC (vals (iterXv M post 0) (iterF M post 0) ((mb.map gkS).take 4))) := by
    have e : vals (iterXv M post 0) (iterF M post 0) (G.1.lt.map (Src.gkOut pre)) =
        vals (iterXv M pre 0) (iterF M pre 0) G.1.lt := by
      simp only [vals, List.map_map]
      exact List.map_congr_left fun x hx => gkOut_val M pre post 0 _ (flt x hx)
    rw [e, elt, hpv, hpv]
  have hzP : (G.1.z.gkOut pre).valF (iterXv M post 0) (iterF M post 0) = 0 := by rw [gkOut_val M pre post 0 _ fz, ez]
  have hoP : (G.1.one.gkOut pre).valF (iterXv M post 0) (iterF M post 0) = 1 := by rw [gkOut_val M pre post 0 _ fo, eo]
  obtain ⟨egD, hApost⟩ := postW_spec hzP hoP (by simp) hltP hpost0
  have hfxH : Fx H.1 := by
    show Fx (postW _ _ _ _ _ _ _ _ _ _ 0).1
    simp only [postW, tb_bind, tb_pure]
    exact fx_emit _ _
  have hgv : (H.1.gkCell post).val M = g := by
    rw [gkCell_val M _ hfxH, egD, gk_lv_fix hS post 0 _ (by simp only [wireEnd] at hT; omega)]
  generalize p2.adv (loop [] (tplOf H.2) p2).2 = p3 at hSl hSlot hRing ⊢
  -- the slot sumcheck
  obtain ⟨hc2, hv2⟩ := gk_sc_lists (D := 1) (R := 2) (by norm_num) (by norm_num) (by omega) hS
    (by simp only [roundLanes, wireEnd] at hT ⊢; omega) hSl
  rw [hgv] at hc2 hv2
  set slO := (scGadget 1 2 (qw + 15 * (P + 5) + 3) .plain (H.1.gkCell post) p3).1 with hslO
  generalize p3.adv (scGadget 1 2 (qw + 15 * (P + 5) + 3) .plain (H.1.gkCell post) p3).2 = p4 at hSlot hRing ⊢
  -- the slot check block
  set Sb := slotW (qw + 15 * (P + 5) + 33) (G.1.om.map (Src.gkOut pre))
    (((List.range 2).map fun i => slO.cell 2 i).map gkS) (G.1.z.gkOut pre) (G.1.one.gkOut pre)
    (gkS (slO.cell 5 1)) (gkS b) 0 with hSb
  have hslot0 := thold_of_loop hSlot (jf := 0) (by simp)
  rw [gk_loop_fst] at hslot0
  set slb : LoopOut := ⟨p4, [], tplOf Sb.2⟩ with hslb
  have hzS : (G.1.z.gkOut pre).valF (iterXv M slb 0) (iterF M slb 0) = 0 := by rw [gkOut_val M pre slb 0 _ fz, ez]
  have hoS : (G.1.one.gkOut pre).valF (iterXv M slb 0) (iterF M slb 0) = 1 := by rw [gkOut_val M pre slb 0 _ fo, eo]
  have hAslot := slotW_spec hzS hoS (by simp) hslot0
  generalize p4.adv (loop [] (tplOf Sb.2) p4).2 = p5 at hRing ⊢
  -- the ring switch
  obtain ⟨hcs, htgt⟩ := ringG_spec hS (by simp only [wireEnd] at hT; omega) (by simp only [wireEnd] at hT; omega)
    hzE hRing
  refine ⟨by rw [vs, List.map_map]; exact hc1.symm, hgv, by rw [vs, List.map_map]; exact hc2.symm, hcs, htgt, ?_⟩
  rintro hb ⟨-, -, hAP, -, hAS, -, -⟩
  have hbv : (gkS b).valF (iterXv M post 0) (iterF M post 0) = 1 := by rw [gkS_valF, hb]
  have hbv' : (gkS b).valF (iterXv M slb 0) (iterF M slb 0) = 1 := by rw [gkS_valF, hb]
  constructor
  · have e := hApost.mp (tassert_one.mp hAP)
    rw [hbv, one_mul, gk_lv_fix hS post 0 _ (by simp only [wireEnd] at hT; omega), gkS_valF, ← hv1] at e
    have e1 : ((List.range (P + 1)).map fun i => (gkS (cv (18 + i))).valF (iterXv M post 0) (iterF M post 0)) =
        (List.range (P + 1)).map fun i => (cv (18 + i)).val M := List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e2 : ((List.range 16).map fun i => (gkS (cv (1 + i))).valF (iterXv M post 0) (iterF M post 0)) =
        (List.range 16).map fun i => (cv (1 + i)).val M := List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e3 : vals (iterXv M post 0) (iterF M post 0) (((List.range (P + 5)).map fun i => scO.cell 2 i).map gkS) = sc.1 := by
      rw [hc1]; simp only [vals, List.map_map]; exact List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have e4 : vals (iterXv M post 0) (iterF M post 0) (mb.map gkS) = vs M mb := by
      simp only [vals, List.map_map, vs]; exact List.map_congr_left fun x _ => gkS_valF M _ 0 _ _
    rw [e1, e2, e3, e4] at e
    exact e
  · have e := hAslot.mp (tassert_one.mp hAS)
    rw [hbv', one_mul, gkS_valF, ← hv2] at e
    have hτ : vals (iterXv M slb 0) (iterF M slb 0) (((List.range 2).map fun i => slO.cell 2 i).map gkS) = sl.1 := by
      rw [hc2]; simp only [vals, List.map_map]; exact List.map_congr_left fun i _ => gkS_valF M _ 0 _ _
    have homL : G.1.om.length = 261 := by
      have := congrArg List.length eom; simp only [vals, List.length_map, wPos_length] at this; exact this
    have hom : ∀ o < 4, ∀ zz < 64, ((G.1.om.map (Src.gkOut pre)).getD (wIx (64 * o + zz)) default).valF
        (iterXv M slb 0) (iterF M slb 0) = wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M)
          ((List.range 25).map fun l => (cv (19 + P + l)).val M) (8 + 64 * o + zz) := by
      intro o ho zz hzz
      have hk : wIx (64 * o + zz) < G.1.om.length := by rw [homL]; simp only [wIx]; omega
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
        gkOut_val M pre slb 0 _ (fom _ (List.getElem_mem hk)), ← List.getD_eq_getElem _ default hk,
        getD_vals _ hk, eom, wPos_map_getD _ (by simp only [wIx]; omega), wPos_getD_ix (by omega)]
      rw [show 8 + (64 * o + zz) = 8 + 64 * o + zz by omega]
    rw [hτ] at e
    have hs : ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
        ((G.1.om.map (Src.gkOut pre)).getD (wIx (64 * o + zz)) default).valF (iterXv M slb 0) (iterF M slb 0)).sum *
          lv (iterXv M slb 0) [] (qw + 15 * (P + 5) + 33 + 3 * zz)) =
        (List.range 64).map fun zz => ((List.range 4).map fun o => eqAt sl.1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0 := by
      refine List.map_congr_left fun zz hzz => ?_
      have hzz' := List.mem_range.mp hzz
      rw [gk_lv_fix hS slb 0 _ (by simp only [wireEnd] at hT; omega)]
      have h1 := congrArg List.sum (List.map_congr_left (l := List.range 4) fun o ho =>
        congrArg (eqAt sl.1 o * ·) (hom o (List.mem_range.mp ho) zz hzz'))
      have h2 : feAt sig (8 * (qw + 15 * (P + 5) + 33 + 3 * zz)) = (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0 := by
        simp only [slAt, kBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzz',
          Option.map_some, Option.getD_some]
      rw [h1, h2]
    rw [hs] at e
    have hsl : sl = scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40) g (List.replicate 2 none) := rfl
    rw [hsl]
    exact e

/-- `F`'s ring switch on a view (`ringSwitch_run`, HAR's, restated below the v1 phase cut). -/
theorem ringSwitch_runW (sig : ByteArray) (point sv : List FE) (st : RS) :
    ringSwitch point sv sig st =
      ((polyEval (sv.map (phiMap · (sampAt (feAt sig) (st.ent + st.msg) ringStages))) gen,
        fun r' => ringWeight point r' (ringCoefficients (sampAt (feAt sig) (st.ent + st.msg) ringStages))),
        ⟨st.ent + st.msg + 72 * ringStages, 0, st.ok⟩) := by
  rw [show ringSwitch point sv = (samples ringStages >>= fun challenges =>
    pure (polyEval (sv.map (phiMap · challenges)) gen,
      fun rPrime => ringWeight point rPrime (ringCoefficients challenges))) from rfl,
    bind_run, show ringStages = 5 + 1 from rfl, gk_samples_run sig 5 st _ rfl, pure_run]

theorem sampAt_chs (sig : ByteArray) {q : Nat} (hq : 5 ≤ q) :
    sampAt (feAt sig) (8 * q - 40) ringStages = chsAt sig q := by
  simp only [sampAt, chsAt]
  exact List.map_congr_left fun i _ => congrArg _ (by omega)

/-- **T-V's `dWire` on a view, replayed by the wire gadget** (`logN = P + 5`): from the wire's position
`8 qw − 40` (the tape's end), with the input claim represented by the cells `cv`, `m`'s bits in `mb` and
`s`'s bits in `sb`, `F`'s wiring point, `g_D`, slot point and ring switch are the gadget's cells, `F`'s
position after is the gadget's last lane, and with the gate `1` the gadget's assertions keep `F`'s flag. -/
theorem wire_spec {c : Ctx} {M : Mem} {p : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : wireEnd P qw + 2 ≤ T) (hzE : M.e zE = 0)
    (h : SegsHold c M p (wireGadget P qw cv mb sb b zE p).2)
    (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub) (hn : 1 ≤ pub.n) (hN : pub.n ≤ 2 ^ (P + 5))
    {claim : KeccakClaim} (hR : Rep P (fun j => (cv j).val M) claim false)
    (hmb : vs M mb = (List.range (P + 5)).map (bitF (pub.n - 1))) (hsb : vs M sb = digBitsF pub.s)
    (s : RS) (hs : s.ent + s.msg = 8 * qw - 40) :
    (dWire pp pub claim sig s).1.sc.1 = vs M (wireGadget P qw cv mb sb b zE p).1.sigma ∧
    (dWire pp pub claim sig s).1.g = [(wireGadget P qw cv mb sb b zE p).1.gD.val M] ∧
    (dWire pp pub claim sig s).1.sl.1 = vs M (wireGadget P qw cv mb sb b zE p).1.tau ∧
    (dWire pp pub claim sig s).1.sc.2 =
      (scSpec (feAt sig) 3 (8 * qw - 40) (wireTargetF pub.s pub.n claim) (List.replicate (P + 5) none)).2 ∧
    (dWire pp pub claim sig s).1.sl.2 = (scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40)
      (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).2 ∧
    (dWire pp pub claim sig s).1.sv = slAt sig (qw + 15 * (P + 5) + 33) ∧
    (dWire pp pub claim sig s).1.ring.1 = (wireGadget P qw cv mb sb b zE p).1.ring.target.val M ∧
    (dWire pp pub claim sig s).1.ring.2 = (fun r' => ringWeight
      ((dWire pp pub claim sig s).1.sc.1 ++ (dWire pp pub claim sig s).1.sl.1 ++ selectorPoint (dSel pp) (dSelBits pp))
      r' (vs M (wireGadget P qw cv mb sb b zE p).1.ring.cs)) ∧
    (dWire pp pub claim sig s).2.ent = 8 * wireEnd P qw - 40 ∧ (dWire pp pub claim sig s).2.msg = 0 ∧
    (b.val M = 1 → SegsAssert M p (wireGadget P qw cv mb sb b zE p).2 → (dWire pp pub claim sig s).2.ok = s.ok) := by
  have hmbL : mb.length = P + 5 := by have := congrArg List.length hmb; simpa [vs] using this
  have hsbL : sb.length = 256 := by have := congrArg List.length hsb; simpa [vs, digBitsF] using this
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := wire_core hq hS hT hmbL hsbL hzE h
  have htgt : wTgt ((cv 0).val M) ((List.range 16).map fun i => (cv (1 + i)).val M)
      ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) ((List.range 6).map fun i => (cv (44 + P + i)).val M)
      ((List.range 25).map fun l => (cv (19 + P + l)).val M) (vs M mb) (vs M sb) = wireTargetF pub.s pub.n claim := by
    rw [hmb, hsb]; exact wTgt_eq hR pub.s hn hN
  rw [htgt] at e1 e6
  have hst1 : scState 3 s (List.replicate (P + 5) none) = ⟨8 * qw - 40 + (P + 5) * roundLen 3, 0, s.ok⟩ := by
    rw [show P + 5 = (P + 4) + 1 from rfl, List.replicate_succ]
    show (⟨s.ent + s.msg + _, 0, s.ok⟩ : RS) = _
    rw [hs, List.length_cons, List.length_replicate]
  have hrl : roundLen 3 = 120 := rfl
  unfold dWire
  rw [hlog, bind_run, sumcheck_run sig 3 (by norm_num), hs, hst1, bind_run, readEs_run, bind_run, require_run,
    bind_run, sumcheck_run sig 3 (by norm_num), bind_run, readEs_run, bind_run, require_run, bind_run,
    ringSwitch_runW, pure_run]
  simp only [scState, List.length_cons, List.length_nil, hrl]
  have hg : scalarsAt (feAt sig) (8 * qw - 40 + (P + 5) * 120 + 0 + 40) 1 = [feAt sig (8 * (qw + 15 * (P + 5)))] := by
    simp only [scalarsAt, List.range_one, List.map_cons, List.map_nil]
    exact congrArg (fun x => [feAt sig x]) (by omega)
  have hp1 : 8 * qw - 40 + (P + 5) * 120 + (0 + 24 * 1) = 8 * (qw + 15 * (P + 5) + 3) - 40 := by omega
  have hsv : scalarsAt (feAt sig) (8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + 0 + 40) kBits =
      slAt sig (qw + 15 * (P + 5) + 33) := by
    simp only [scalarsAt, slAt]
    exact List.map_congr_left fun k _ => congrArg _ (by omega)
  have hpr : 8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + (0 + 24 * kBits) =
      8 * (qw + 15 * (P + 5) + 225) - 40 := by simp only [kBits]; omega
  have hend : 8 * (qw + 15 * (P + 5) + 225) - 40 + 72 * ringStages = 8 * wireEnd P qw - 40 := by
    simp only [ringStages, wireEnd]; omega
  rw [hg, hp1, hsv, hpr, sampAt_chs sig (by omega), hend]
  simp only [List.getD_cons_zero]
  refine ⟨e1.symm, by rw [e2], e3.symm, trivial, trivial, trivial, e5.symm, by rw [e4], trivial, trivial, fun hb hA => ?_⟩
  obtain ⟨c1, c2⟩ := e6 hb hA
  have hσL : (scSpec (feAt sig) 3 (8 * qw - 40) (wireTargetF pub.s pub.n claim) (List.replicate (P + 5) none)).1.length =
      claim.point.length + 4 := by
    rw [gk_scSpec_length, List.length_replicate, ← hR.point]; simp
  have hptv : ((List.range (P + 1)).map fun i => (cv (18 + i)).val M) = claim.point := hR.point
  have hmuv : ((List.range 16).map fun i => (cv (1 + i)).val M) = claim.mu := hR.mu
  have hm := msC_eq_msEvalF (μ := claim.mu) (m := pub.n - 1) hσL
    (by rw [gk_scSpec_length, List.length_replicate]; omega)
  rw [gk_scSpec_length, List.length_replicate] at hm
  rw [hptv, hmuv, hmb, hm, gk_add_eq_zero] at c1
  have hd : dot (slotWF claim.weights.toArray (scSpec (feAt sig) 3 (8 * (qw + 15 * (P + 5) + 3) - 40)
      (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).1) (slAt sig (qw + 15 * (P + 5) + 33)) =
      ((List.range 64).map fun zz => ((List.range 4).map fun o => eqAt (scSpec (feAt sig) 3
        (8 * (qw + 15 * (P + 5) + 3) - 40) (feAt sig (8 * (qw + 15 * (P + 5)))) [none, none]).1 o *
          wOm ((List.range 6).map fun i => (cv (44 + P + i)).val M) ((List.range 25).map fun l => (cv (19 + P + l)).val M)
            (8 + 64 * o + zz)).sum * (slAt sig (qw + 15 * (P + 5) + 33)).getD zz 0).sum := by
    rw [gk_dot_eq_sum (n := 64) (by simp [slotWF]) (by simp [slAt, kBits])]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    congr 1
    simp only [slotWF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hzz', Option.map_some,
      Option.getD_some, sumE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
    have ho' := List.mem_range.mp ho
    rw [array_getD_toArray', ← wOm_rep hR (by omega)]
    rfl
  rw [show (List.replicate 2 none : List (Option FE)) = [none, none] from rfl, ← hd, gk_add_eq_zero] at c2
  rw [(gk_fe_beq _ _).mpr c2, (gk_fe_beq _ _).mpr c1.symm]
  simp

end gadget

end Lvm.Q1
