-- WP-14d (EXQ). New for lvm (O6, first pieces): the structural and numeric parts of instantiating
-- WP-14's glue (`LvmCertSMid.midSpecOf`/`midShapeOf`) with WP-14a's middle phases `midS`
-- (`LvmVEqMid`): no commitment and no proof of work in V_S phases 4–7 (`kgProgS`, after WP-9b's
-- `noCG_lbusTableCheckProg` pattern), `MidShape (midS tabs)` from the `C_rec` claims'
-- multiaffinity, WP-8 `kgSpec`'s error side conditions at `εS` with one candidate pair, and the
-- invariance of `MidSpec` under an equivalent `Good`.
import LvmCertSMid
import LvmM3MidCert
import LvmVEqMid
import LvmAccSpecMid

/-!
# O6 parts for `midS`

* `cg_verifyKeccak`, `cg_ringSwitch`, `cg_callerProg`, `cg_chLinkProg`, `cg_ksLinkProg`,
  **`cg_kgProgS`**, **`cg_midS`**: `NoCommit ∧ NoGrind` (WP-9b's `NoCG`);
* **`midShape_midS`**: `MidShape (midS tabs)` given the `C_rec` claims' multiaffinity;
* **`kg_errs`**: `kgSpec`'s side conditions `h46 h2 hr0 hrK hrL hrKL` at `εmax = εS`, `L₀ = 1`, P20's
  `P = 16`, `Pk = 11`, and its lead `≤ εS`;
* `midSpec_congr`: `MidSpec` depends on `Good` only up to pointwise equivalence (WP-14c's
  `GoodN = GoodB ∧ GoodK` against `midSpecOf`'s `Gb x ∧ Gk`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges
  cg_roundPoly cg_sumcheck noCG_lbusTableCheckProg)
open scoped ENNReal

/-! ## No commitment, no proof of work -/

theorem cg_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    NoCG (LeanVM.Protocol.Verifier.keccakPackRounds rs value scale)
  | [], _, _ => cg_ret _
  | r :: rs, value, scale => by
    unfold LeanVM.Protocol.Verifier.keccakPackRounds
    refine NoCG.bind (cg_roundPoly _ _ _) fun _ ↦ NoCG.bind cg_sample fun _ ↦
      NoCG.bind (cg_keccakPackRounds rs _ _) fun t ↦ ?_
    obtain ⟨v, s, pt⟩ := t
    exact cg_ret _

theorem cg_verifyKeccakLayer (logSteps step : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) :
    NoCG (LeanVM.Protocol.Verifier.verifyKeccakLayer logSteps step claim) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccakLayer
  refine NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_keccakPackRounds _ _ _) fun t ↦ ?_
  obtain ⟨v, s, pt⟩ := t
  refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨lp, v'⟩ := u
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim),
    NoCG (LeanVM.Protocol.Verifier.keccakLayers logSteps steps claim)
  | [], _ => cg_ret _
  | s :: steps, claim => by
    unfold LeanVM.Protocol.Verifier.keccakLayers
    exact NoCG.bind (cg_verifyKeccakLayer _ _ _) fun _ ↦ cg_keccakLayers logSteps steps _

theorem cg_keccakOpen (logSteps : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) (first count : ℕ) (value : E) :
    NoCG (LeanVM.Protocol.Verifier.keccakOpen logSteps claim first count value) := by
  unfold LeanVM.Protocol.Verifier.keccakOpen
  refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨slot, v⟩ := u
  exact cg_ret _

theorem cg_ite {α : Type} {c : Prop} [Decidable c] {p q : VerifierProgram α} (hp : NoCG p)
    (hq : NoCG q) : NoCG (if c then p else q) := by
  split <;> assumption

theorem cg_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCG (LeanVM.Protocol.Verifier.verifyKeccak logSteps inst output) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccak
  refine NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_sampleChallenges _) fun _ ↦
    NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_keccakLayers _ _ _) fun _ ↦
      NoCG.bind (cg_keccakOpen _ _ _ _ _) fun t ↦ ?_
  obtain ⟨slot, w, v⟩ := t
  refine NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ ?_
  first
    | refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
    | refine NoCG.bind (cg_ret _) fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨low, v'⟩ := u
  refine NoCG.bind (cg_keccakOpen _ _ _ _ _) fun t' ↦ ?_
  obtain ⟨slot', w', v''⟩ := t'
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_ringSwitch (point s : List E) : NoCG (LeanVM.Protocol.Verifier.ringSwitch point s) := by
  unfold LeanVM.Protocol.Verifier.ringSwitch
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_ret _

theorem cg_callerProg (h : ℕ) : NoCG (Lvm.KG.callerProg h) := by
  unfold Lvm.KG.callerProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_verifyKeccak _ _ _) fun _ ↦ NoCG.bind (cg_ringSwitch _ _) fun _ ↦ cg_ret _

theorem cg_chLinkProg (h ys : ℕ) : NoCG (Lvm.KG.chLinkProg h ys) := by
  unfold Lvm.KG.chLinkProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun _ ↦
    NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_ringSwitch _ _) fun _ ↦
      NoCG.bind (cg_sumcheck _ _ _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
        NoCG.bind (cg_ringSwitch _ _) fun _ ↦ NoCG.bind (cg_sampleChallenges _) fun _ ↦
          NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_ksLinkProg (hk r : ℕ) (rows : List ℕ) : NoCG (Lvm.KG.ksLinkProg hk r rows) := by
  unfold Lvm.KG.ksLinkProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun _ ↦
    NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

/-- **V_S phases 4–7 commit nothing and ask no proof of work.** -/
theorem cg_kgProgS : NoCG Lvm.VEq.kgProgS :=
  NoCG.bind (NoCG.bind (cg_callerProg _) fun _ ↦ NoCG.bind (cg_chLinkProg _ _) fun _ ↦ cg_ret _)
    fun _ ↦ NoCG.bind (NoCG.bind (cg_callerProg _) fun _ ↦ NoCG.bind (cg_ksLinkProg _ _ _) fun _ ↦
      cg_ret _) fun _ ↦ cg_ret _

/-- **The middle phases commit nothing and ask no proof of work.** -/
theorem cg_midS (tabs : Lvm.Pub → List Lvm.M3.Tab) (x : List UInt8) : NoCG (Lvm.VEq.midS tabs x) :=
  NoCG.bind (Lvm.Acc.noCG_lbusTableAccProg _ _ _ _) fun _ ↦ NoCG.bind cg_kgProgS fun _ ↦ cg_ret _

/-- **`MidShape (midS tabs)`** given the multiaffinity of the `C_rec` claims it returns. -/
theorem midShape_midS (tabs : Lvm.Pub → List Lvm.M3.Tab)
    (hrec : ∀ x l cl, (Lvm.VEq.midS tabs x).after l = some (.ret cl) →
      ∀ c ∈ cl.1, IsMultiaffine 19 c.1) : MidShape (Lvm.VEq.midS tabs) where
  noCommit x := (cg_midS tabs x).1
  noGrind x := (cg_midS tabs x).2
  recAffine := hrec

/-! ## `kgSpec`'s error side conditions at `εS` -/

theorem errE_le_εS {d : ℕ} (hd : d ≤ 2 ^ 63) : errE d ≤ εS := by
  unfold errE εS
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (d : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 63 := by exact_mod_cast hd
  have h2 : (2 : ℝ≥0∞) ^ 63 * ((2 : ℝ≥0∞) ^ 192)⁻¹ = (2 : ℝ≥0∞)⁻¹ ^ 129 := by
    rw [show (192 : ℕ) = 63 + 129 from rfl, pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
      ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
      one_mul, ENNReal.inv_pow]
  calc (d : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ≤ (2 : ℝ≥0∞) ^ 63 * ((2 : ℝ≥0∞) ^ 192)⁻¹ := by gcongr
    _ = _ := h2

theorem errE_add (a b : ℕ) : errE a + errE b = errE (a + b) := by
  unfold errE; push_cast; rw [add_mul]

theorem errE_smul (n d : ℕ) : (n : ℝ≥0∞) * errE d = errE (n * d) := by
  unfold errE; push_cast; rw [mul_assoc]

theorem sum6 : (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) = errE 6 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_one, one_mul,
    show ((6 : ℕ) : ℝ≥0∞) = (6 : ℝ≥0∞) from rfl, ← Nat.cast_ofNat, errE_smul]

/-- **`kgSpec`'s side conditions at P20 with one candidate pair** (`L₀ = 1`, `P + 4 = 20`,
`Pk + 4 = 15`), and its lead `20 · errE 1 ≤ εS`. -/
theorem kg_errs :
    ((1 : ℕ) : ℝ≥0∞) * errE 46 ≤ εS ∧ ((1 : ℕ) : ℝ≥0∞) * errE 2 + 0 ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) + 0 ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) +
      (((11 + 4 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * errE 1) + 0) ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) +
      (((16 + 4 + 9 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * errE 1) + 0) ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) +
      (((11 + 4 + 5 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * errE 1) + 0) ≤ εS ∧
    ((16 + 4 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * errE 1) + 0 ≤ εS := by
  simp only [Nat.cast_one, one_mul, add_zero]
  rw [show (∑ _i ∈ Finset.range 6, errE 1) = errE 6 by simpa using sum6]
  simp only [errE_smul, errE_add]
  exact ⟨errE_le_εS (by norm_num), errE_le_εS (by norm_num), errE_le_εS (by norm_num),
    errE_le_εS (by norm_num), errE_le_εS (by norm_num), errE_le_εS (by norm_num),
    errE_le_εS (by norm_num)⟩

/-- **`kgSpec`'s structural arguments at P20**: `ys = 52`, `Pk + 4 = r + 1`, and the continuation
rows `contRows P20` are distinct and inside `[1, 2^15)`. -/
theorem kg_struct : 52 % 4 = 0 ∧ 52 / 4 < 16 ∧ 11 + 4 = 14 + 1 ∧ (Lvm.contRows Lvm.P20).Nodup ∧
    ∀ i ∈ Lvm.contRows Lvm.P20, 1 ≤ i ∧ i < 2 ^ (11 + 4) := by
  have hs : Lvm.spongeBlocks Lvm.P20 - 1 < 2 ^ Lvm.P20.recRowsLog + 400 ∧
      2 ^ Lvm.P20.recRowsLog + 400 + 31 ≤ 2 ^ (11 + 4) ∧ Lvm.spongeBlocks Lvm.P20 ≤ 2 ^ (11 + 4) := by
    rw [show Lvm.P20.recRowsLog = 14 from rfl, Lvm.sizes_P20.2.2.2.2.2.2.2.2]
    decide
  refine ⟨rfl, by norm_num, rfl, ?_, ?_⟩
  · unfold Lvm.contRows
    rw [List.nodup_append]
    refine ⟨(List.nodup_range).map fun a b h ↦ by omega, (List.nodup_range).map fun a b h ↦ by omega,
      fun a ha b hb hab ↦ ?_⟩
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    omega
  · intro i hi
    unfold Lvm.contRows at hi
    simp only [List.mem_append, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> omega

/-! ## `MidSpec` and an equivalent `Good` -/

theorem midSpec_congr {mid : List UInt8 → VerifierProgram OpenClaims} {G G' : GoodRel}
    (hG : ∀ x qm qr, G x qm qr ↔ G' x qm qr) {εm Lm : ℝ≥0∞} (h : MidSpec mid G εm Lm) :
    MidSpec mid G' εm Lm := by
  have e : G = G' := funext fun x ↦ funext fun qm ↦ funext fun qr ↦ propext (hG x qm qr)
  exact e ▸ h

end Lvm.ASM
