-- New for lvm2 (WP T-W): the tape's wiring phase (BLUEPRINT2 §1.2 T3–T4) as doom specifications on
-- leanVM's DSL. The pieces are v1's: plain sumcheck rounds (`sumcheckSpec`, `LvmKeccakRounds`), the
-- lane sumcheck before a ring switch (`G2`/`sliceExt_y`, `LvmChainTableLinkMath`) made generic in the
-- block (`slotSpec`), and ring switching with a carried predicate (`ringColSpec`); the kernels are
-- T-K's (`LvmWireKernel`).
import LvmWireKernel
import LvmTapeRel
import LvmKeccakCaller

/-!
# The wiring phase (stage S2: the chain)

The tape's GKR (T-G) ends at the **input claim** on the virtual inputs (`InClaimTrue`):

  `C_in = Σ_{i<2^w} ι(i)·⟨ω, in(i)⟩`,  `ι = Lvm.WK.iota ρ μ`,  `⟨ω, a⟩ = Σ_{j<1600} ω_j·a_j`

(`ρ`, `μ`, `ω`, `C_in` the claim's `point`, `mu`, `weights`, `value`). With `chainIn`
(`LvmTapeRel`) it is an identity in the committed digests `D` (**`wire_identity_ch`**):

  `C_in = const + Σ_{x<2^w} K_ch(x)·G_D(x)`,
  `const = ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i)`,
  `K_ch(x) = ι(x + 1)·[x + 1 ≤ m]` (T-K's `msK ρ μ 0 m`), `G_D(x) = Σ_{p<256} ω_{8+p}·bit_p(D[x])`,

`m = n − 1`. `wireChProg` (V_S's wire phase at S2) is, read for read and sample for sample:

```
sc ← w plain rounds of degree 2 on C_in + const;  g ← 1 scalar (g_D);
require sc.final = K̃_ch(σ)·g_D;                       -- `msEval ρ μ σ 0 m`
slotProg D: 2 plain rounds of degree 2 on g_D;  64 slices at (σ, τ, sel(dsel));
            require final = Σ_z W̃_z(τ)·slice_z;  ringSwitch (6 samples)
```

* `slotProg`/**`slotSpec`** (T4, generic): a claim `v = Σ_{o<2^b} Σ_{z<64} W(o, z)·S_z(pt, o)` on the
  64 bit slices `S_z(pt, o)` of slot `o` of a block of `2^b` slots of `2^k` words (`slotSum`) is
  reduced by `b` rounds to 64 slice claims at `(pt, τ, sel(blk))`, then ring-switched to one claim
  on the column (`RingColTrue`). D is the block `dsel` of 4 slots of `2^w` words: lane `l` of row
  `x` is word `x + 2^w·(l + 4·dsel)` of `C_main` (`dOf`).
* **`wireChSpec`**: from doom of `InClaimTrue ∧ R` to doom of the ring claim on `C_main` and `R`.
  Groups: each wiring and slot round `L₀·2/|E|`; the ring switch `6·L₀/|E|` plus the follower's
  lead. Lead `0` (the phase starts with a read).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open Lvm.KSponge Lvm.WK Finset
open scoped ENNReal

/-! ## The input claim -/

/-- `⟨ω, a⟩`: the position weights `ω` paired with the 1600 bits of a state. -/
def omegaDot (ω : List E) (a : RecursionFast.Keccak.State) : E :=
  ∑ j ∈ range 1600, ω.getD j 0 * bitE (sbit a j)

/-- **The GKR's input claim** on the virtual inputs `inp i` of the rows `i < 2^lg`. -/
def InClaimTrue (lg : ℕ) (inp : ℕ → RecursionFast.Keccak.State) (claim : KeccakClaim) : Prop :=
  claim.value = ∑ i ∈ range (2 ^ lg), iota claim.point claim.mu i * omegaDot claim.weights (inp i)

/-- **T-G's GKR end is the input claim** (`tapeGkrSpec`'s post, one segment, `P + 1` pack
coordinates): T-G's `claimTrue_tapeStates`, unfolded. The glue uses `.mpr` (`claimTrue_of_inClaim`): doom of
`ClaimTrue` gives doom of `InClaimTrue`. -/
theorem inClaim_iff_tape {P : ℕ} (I : ℕ → RecursionFast.Keccak.State) (c : KeccakClaim) :
    ClaimTrue (tapeStates P I 24) P c ↔ InClaimTrue (P + 5) I c := by
  rw [claimTrue_tapeStates]
  rfl

/-- The direction the doom glue needs: a true input claim is a true GKR claim. -/
theorem claimTrue_of_inClaim {P : ℕ} (I : ℕ → RecursionFast.Keccak.State) (c : KeccakClaim)
    (h : InClaimTrue (P + 5) I c) : ClaimTrue (tapeStates P I 24) P c :=
  (inClaim_iff_tape I c).mpr h

/-- **T-G's post is the wiring phase's pre** (doom of the GKR claim gives doom of the input claim). -/
theorem doomed_inClaim_of_tape {β : Type} {C : List Ev → Set β} {P : ℕ}
    (Iq : β → ℕ → RecursionFast.Keccak.State) (c : KeccakClaim) (R : β → Prop) {hist : List Ev}
    (hd : Doomed C (fun q ↦ ClaimTrue (tapeStates P (Iq q) 24) P c ∧ R q) hist) :
    Doomed C (fun q ↦ InClaimTrue (P + 5) (Iq q) c ∧ R q) hist :=
  Doomed.mono hd fun q ⟨h, hR⟩ ↦ ⟨claimTrue_of_inClaim (Iq q) c h, hR⟩

/-! ## The wiring identity -/

/-- `⟨ω, Pad43(y)⟩` for the 256 digest bits `y`. -/
def padDot (ω : List E) (y : ℕ → Bool) : E := ∑ j ∈ range 1600, ω.getD j 0 * bitE (pad43Bit y j)

/-- `⟨ω, c43⟩`: the constant bits of `Pad43` (`0x43`, `0x01` at bit 264, `0x80` at bit 1087). -/
def c43Dot (ω : List E) : E := padDot ω (fun _ ↦ false)

/-- The digest part of a row: `G_D(x) = Σ_{p<256} ω_{8+p}·bit_p(D[x])`. -/
def gDT (ω : List E) (D : ℕ → ℕ → K) (x : ℕ) : E :=
  ∑ p ∈ range 256, ω.getD (8 + p) 0 * bitE (rowBits D x p)

/-- **The wiring target** `C_in + const` (characteristic two), with T-K's threshold evaluator:
`Σ_{i=1}^{m} ι(i) = thrEval ρ μ m − ι(0)`. -/
def wireTarget (s : RecursionFast.Digest) (n : ℕ) (claim : KeccakClaim) : E :=
  claim.value + iota claim.point claim.mu 0 * padDot claim.weights (digestBits s) +
    c43Dot claim.weights * (thrEval claim.point claim.mu (n - 1) + iota claim.point claim.mu 0)

theorem omegaDot_pad43 (ω : List E) (y : ℕ → Bool) : omegaDot ω (pad43St y) = padDot ω y := by
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [← stBit_eq_sbit _ hj', pad43St, stBit_ofBits _ hj']

theorem omegaDot_zero (ω : List E) : omegaDot ω zeroSt = 0 :=
  Finset.sum_eq_zero fun j hj ↦ by
    rw [← stBit_eq_sbit _ (Finset.mem_range.1 hj), stBit_zeroSt, bitE_false, mul_zero]

/-- `Pad43`'s pairing splits into the constant bits and the digest bits. -/
theorem padDot_split (ω : List E) (y : ℕ → Bool) :
    padDot ω y = c43Dot ω + ∑ p ∈ range 256, ω.getD (8 + p) 0 * bitE (y p) := by
  have hj : ∀ j, bitE (pad43Bit y j) = bitE (pad43Bit (fun _ ↦ false) j) +
      if 8 ≤ j ∧ j < 264 then bitE (y (j - 8)) else 0 := by
    intro j
    unfold pad43Bit
    split_ifs <;> first | omega | simp
  rw [c43Dot, padDot, padDot, Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_add],
    Finset.sum_add_distrib]
  refine congrArg (HAdd.hAdd _) ?_
  rw [show 1600 = 8 + (256 + 1336) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, ω.getD j 0 * (if 8 ≤ j ∧ j < 264 then bitE (y (j - 8)) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), mul_zero]
  have h3 : ∑ j ∈ range 1336, ω.getD (8 + (256 + j)) 0 *
      (if 8 ≤ 8 + (256 + j) ∧ 8 + (256 + j) < 264 then bitE (y (8 + (256 + j) - 8)) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (by omega), mul_zero]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [if_pos (by have := Finset.mem_range.1 hp; omega), Nat.add_sub_cancel_left]

/-- **The wiring identity (chain)**: the input claim's sum over the chain rows is the constant plus
the kernel-weighted digest parts. -/
theorem wire_identity_ch (ρ μ ω : List E) (s : RecursionFast.Digest) {n : ℕ} (D : ℕ → ℕ → K)
    {w : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w) :
    ∑ i ∈ range (2 ^ w), iota ρ μ i * omegaDot ω (chainIn s n D i) =
      iota ρ μ 0 * padDot ω (digestBits s) + c43Dot ω * ∑ i ∈ range (n - 1), iota ρ μ (i + 1) +
        ∑ x ∈ range (2 ^ w), msK ρ μ 0 (n - 1) x * gDT ω D x := by
  have hp := Nat.two_pow_pos w
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ w = M + 1 := ⟨2 ^ w - 1, by omega⟩
  -- each row `x + 1`: its input is `Pad43(D[x])` below `n`, zero above
  have hrow : ∀ x, iota ρ μ (x + 1) * omegaDot ω (chainIn s n D (x + 1)) =
      msK ρ μ 0 (n - 1) x * (c43Dot ω + gDT ω D x) := by
    intro x
    rw [chainIn, if_neg (by omega), msK, Nat.zero_add]
    split_ifs with h1 h2 h2
    · rw [omegaDot_pad43, padDot_split, Nat.add_sub_cancel, gDT]
    · omega
    · omega
    · rw [omegaDot_zero, mul_zero, zero_mul]
  have hlast : msK ρ μ 0 (n - 1) M * (c43Dot ω + gDT ω D M) = 0 := by
    rw [msK, if_neg (by omega), zero_mul]
  have hK : ∑ x ∈ range (2 ^ w), msK ρ μ 0 (n - 1) x = ∑ i ∈ range (n - 1), iota ρ μ (i + 1) := by
    rw [show 2 ^ w = (n - 1) + (2 ^ w - (n - 1)) by omega, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := range (2 ^ w - (n - 1))) fun x _ ↦ by rw [msK, if_neg (by omega)],
      add_zero]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [msK, if_pos (by have := Finset.mem_range.1 hi; omega), Nat.zero_add]
  rw [hM] at hK
  rw [hM, Finset.sum_range_succ', Finset.sum_congr rfl fun x _ ↦ hrow x]
  rw [show (∑ x ∈ range M, msK ρ μ 0 (n - 1) x * (c43Dot ω + gDT ω D x)) =
      ∑ x ∈ range (M + 1), msK ρ μ 0 (n - 1) x * (c43Dot ω + gDT ω D x) by
    rw [Finset.sum_range_succ, hlast, add_zero]]
  rw [← hK, chainIn, if_pos rfl, omegaDot_pad43, Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [mul_comm (c43Dot ω)]
  ring

/-! ## The wiring sumcheck -/

/-- The extension of a table over `2^k` rows at `pt`. -/
def extE (k : ℕ) (pt : List E) (f : ℕ → E) : E := ∑ x ∈ range (2 ^ k), eqAt pt x * f x

/-- The wiring sumcheck's family (chain): `Σ_x K̃_ch(x)·G̃_D(x)` over the rows not bound. -/
noncomputable def wireChF (w : ℕ) (ρ μ ω : List E) (m : ℕ) (D : ℕ → ℕ → K) (acc : List E) : E :=
  cubeSum (fun pt ↦ extE w pt (msK ρ μ 0 m) * extE w pt (gDT ω D)) w acc

theorem wireChF_plain {β : Type} (w : ℕ) (ρ μ ω : List E) (m : ℕ) (D : β → ℕ → ℕ → K) :
    PlainFamily (fun q acc ↦ wireChF w ρ μ ω m (D q) acc) 2 w :=
  cube_plainFamily _ w fun _ pre post ↦ polyLE_mle_mul _ _ _ _ pre post

theorem wireChF_nil (w : ℕ) (ρ μ ω : List E) (m : ℕ) (D : ℕ → ℕ → K) :
    wireChF w ρ μ ω m D [] = ∑ x ∈ range (2 ^ w), msK ρ μ 0 m x * gDT ω D x := by
  rw [wireChF, cubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [extE, extE, sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

/-- The family's end: `K̃_ch(σ)` is T-K's `msEval`. -/
theorem wireChF_end {w : ℕ} (ρ μ ω : List E) {m : ℕ} (D : ℕ → ℕ → K) {σ : List E}
    (hσ : σ.length = w) (h4 : 4 ≤ w) (hρ : w - 4 ≤ ρ.length) (hm : m < 2 ^ w) :
    wireChF w ρ μ ω m D σ = msEval ρ μ σ 0 m * extE w σ (gDT ω D) := by
  subst hσ
  rw [wireChF, cubeSum_full _ rfl, extE, sum_msK_zero ρ μ σ m h4 hρ hm]

/-! ## Slot reductions (T4) -/

/-- Slice `z` of slot `o` of block `blk` (`2^b` slots of `2^k` words) at the rows' point `pt`. -/
def slotSlice (k b blk : ℕ) (col : ℕ → K) (pt : List E) (o z : ℕ) : E :=
  ∑ x ∈ range (2 ^ k), eqAt pt x * bitE ((col (x + 2 ^ k * (o + 2 ^ b * blk))).toBitVec.getLsbD z)

/-- The slot weights `W(o, z)` paired with the block's slices. -/
def slotSum (k b blk : ℕ) (W : ℕ → ℕ → E) (col : ℕ → K) (pt : List E) : E :=
  ∑ o ∈ range (2 ^ b), ∑ z ∈ range 64, W o z * slotSlice k b blk col pt o z

/-- `W̃_z(τ) = Σ_o eq(τ, o)·W(o, z)`, the slot weights at the slot point. -/
def slotWE (b : ℕ) (W : ℕ → ℕ → E) (τ : List E) (z : ℕ) : E :=
  ∑ o ∈ range (2 ^ b), eqAt τ o * W o z

/-- What a slot reduction returns. -/
structure SlotOut where
  /-- The slot point `τ` and the last claim. -/
  sl : List E × E
  /-- The 64 slices at `(pt, τ, sel(blk))`. -/
  sv : List E
  /-- Their ring switch. -/
  ring : E × (List E → E)

/-- **A slot reduction** (T4): `b` plain rounds, 64 slices, the check, the ring switch. -/
def slotProg (b sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) : VerifierProgram SlotOut :=
  sumcheck v 3 (List.replicate b none) >>= fun sl ↦
  VerifierProgram.readScalars 64 >>= fun sv ↦
  VerifierProgram.require (sl.2 = ∑ z ∈ range 64, slotWE b W sl.1 z * sv.getD z 0) >>= fun _ ↦
  ringSwitch (pt ++ sl.1 ++ selectorPoint blk sb) sv >>= fun ring ↦
  VerifierProgram.ret ⟨sl, sv, ring⟩

/-- The slot rounds' family: `Σ_z W̃_z(τ)·S̃_z(pt, τ)` over the slot bits not bound. -/
noncomputable def slotF (k b blk : ℕ) (W : ℕ → ℕ → E) (col : ℕ → K) (pt : List E)
    (acc : List E) : E :=
  cubeSum (fun τ ↦ ∑ z ∈ range 64, slotWE b W τ z *
    ∑ o ∈ range (2 ^ b), eqAt τ o * slotSlice k b blk col pt o z) b acc

theorem slotF_plain {β : Type} (k b blk : ℕ) (W : ℕ → ℕ → E) (col : β → ℕ → K) (pt : List E) :
    PlainFamily (fun q acc ↦ slotF k b blk W (col q) pt acc) 2 b :=
  cube_plainFamily _ b fun _ pre post ↦ PolyLE.sum _ fun _ _ ↦ polyLE_mle_mul _ _ _ _ pre post

theorem slotF_nil (k b blk : ℕ) (W : ℕ → ℕ → E) (col : ℕ → K) (pt : List E) :
    slotF k b blk W col pt [] = slotSum k b blk W col pt := by
  rw [slotF, cubeSum_nil, slotSum]
  refine Finset.sum_congr rfl fun u hu ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [slotWE, sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

theorem slotF_end (k b blk : ℕ) (W : ℕ → ℕ → E) (col : ℕ → K) (pt : List E) {τ : List E}
    (hτ : τ.length = b) :
    slotF k b blk W col pt τ = ∑ z ∈ range 64, slotWE b W τ z *
      ∑ o ∈ range (2 ^ b), eqAt τ o * slotSlice k b blk col pt o z := by
  rw [slotF, cubeSum_full _ hτ]

/-- **The slices of a block**: the column's bit slices at `(pt, τ, sel(blk))` are the block's
slices at `pt` weighted by `eq(τ, ·)`. -/
theorem sliceExt_slot {k b sb blk h : ℕ} (hk : k + b + sb = h + 6) (hblk : blk < 2 ^ sb)
    (col : ℕ → K) {pt τ : List E} (hpt : pt.length = k) (hτ : τ.length = b) (z : ℕ) :
    sliceExt h col (pt ++ τ ++ selectorPoint blk sb) z =
      ∑ o ∈ range (2 ^ b), eqAt τ o * slotSlice k b blk col pt o z := by
  unfold sliceExt
  have hsel : selectorPoint blk sb = bitsE blk sb := by
    rw [selectorPoint_eq_boolPoint]
    clear hblk hk
    induction sb generalizing blk with
    | zero => rfl
    | succ n ih =>
      rw [boolPoint_succ, bitsE, ih, Nat.testBit_zero]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one blk with h0 | h1 <;> simp [*]
  have hsl : (τ ++ selectorPoint blk sb).length = b + sb := by
    simp [hτ, selectorPoint]
  have e1 := col_split (s := τ ++ selectorPoint blk sb) hpt
    (fun n ↦ bitE ((col n).toBitVec.getLsbD z))
  rw [hsl, ← List.append_assoc, show k + (b + sb) = h + 6 by omega] at e1
  rw [e1]
  have e2 := col_split (h := b) (a := τ) (s := selectorPoint blk sb) hτ
    (fun o ↦ ∑ x ∈ range (2 ^ k), eqAt pt x * bitE ((col (x + 2 ^ k * o)).toBitVec.getLsbD z))
  rw [show (selectorPoint blk sb).length = sb by simp [selectorPoint]] at e2
  rw [e2, hsel, sum_eqAt_bitsE hblk]
  rfl

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **A slot reduction** as a specification: from doom of `v = slotSum ∧ R` to doom of the ring
claim on the column and `R`. Each round `L₀·2/|E|`; the ring switch `6·L₀/|E|` plus `T`. -/
noncomputable def slotSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    {k b sb blk h : ℕ} (hk : k + b + sb = h + 6) (hblk : blk < 2 ^ sb) (W : ℕ → ℕ → E)
    (col : β → ℕ → K) (R : β → Prop) {pt : List E} (hpt : pt.length = k) (v : E)
    (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (slotProg b sb blk W pt v) (Doomed C (fun q ↦ v = slotSum k b blk W (col q) pt ∧ R q))
      (fun out hist ↦ out.sl.1.length = b ∧
        Doomed C (fun q ↦ RingColTrue h (col q) out.ring ∧ R q) hist) εmax 0 T :=
  ((sumcheckSpec (T := 0) hst hcard R (slotF_plain k b blk W col pt) (count := 3) (by norm_num)
      (by norm_num) zero_le h2 b [] v (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨hv.trans (slotF_nil k b blk W (col q) pt), hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sl ↦
  if hm : sl.1.length = b then
    ((doomReadN (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) hst
        (fun q ↦ sl.2 = slotF k b blk W (col q) pt ([] ++ sl.1) ∧ R q) hrT 63).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sv ↦
    if hy : sv.length = 64 then
      (Spec.require (Pre := fun hist ↦ sv.length = 63 + 1 ∧
          Doomed C (fun q ↦ sl.2 = slotF k b blk W (col q) pt ([] ++ sl.1) ∧ R q) hist)
        (Post := fun _ hist ↦ Doomed C (fun q ↦
          slicesTrue h (col q) (pt ++ sl.1 ++ selectorPoint blk sb) sv ∧ R q) hist)
        (fun _ hd hcond ↦ Doomed.mono hd.2 fun q (hq : slicesTrue h (col q)
            (pt ++ sl.1 ++ selectorPoint blk sb) sv ∧ R q) ↦ ⟨by
          have hsl := hq.1
          rw [List.nil_append, slotF_end _ _ _ _ _ _ hm, hcond]
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          rw [hsl.2.2 z (Finset.mem_range.1 hz)]
          exact congrArg (HMul.hMul _) (sliceExt_slot hk hblk (col q) hpt hm z), hq.2⟩)).bind' fun _ ↦
      (ringColSpec (T := T) hst hcard h col R (pt ++ sl.1 ++ selectorPoint blk sb) sv
          ⟨by simp [hpt, hm, selectorPoint]; omega, hy⟩).bind' fun ring ↦
        (Spec.ret (⟨sl, sv, ring⟩ : SlotOut)).mono (fun _ hd ↦ ⟨hm, hd⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hm hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The chain wiring phase -/

/-- `D`'s lanes in `C_main`: lane `l` of row `x` at word `x + 2^w·(l + 4·dsel)`. -/
def dOf (w dsel : ℕ) (col : ℕ → K) (x l : ℕ) : K := col (x + 2 ^ w * (l + 4 * dsel))

/-- `D`'s slot weights: `W(l, z) = ω_{8 + 64l + z}`. -/
def dW (ω : List E) (l z : ℕ) : E := ω.getD (8 + 64 * l + z) 0

/-- **`G̃_D` is `D`'s slot sum.** -/
theorem gD_slot (w dsel : ℕ) (ω : List E) (col : ℕ → K) (pt : List E) :
    extE w pt (gDT ω (dOf w dsel col)) = slotSum w 2 dsel (dW ω) col pt := by
  simp only [extE, gDT, slotSum, slotSlice, Finset.mul_sum]
  rw [Finset.sum_comm, show 256 = 4 * 64 from rfl, sum_range_mul, show (2 : ℕ) ^ 2 = 4 from rfl]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦
    Finset.sum_congr rfl fun x _ ↦ ?_
  have hz' := Finset.mem_range.1 hz
  simp only [rowBits, dOf, dW, show (64 * l + z) / 64 = l by omega,
    show (64 * l + z) % 64 = z by omega, show 8 + (64 * l + z) = 8 + 64 * l + z by omega]
  ring

/-- **The wiring sumcheck's claim is the input claim**: `C_in + const = Σ_x K_ch(x)·G_D(x)` gives
`InClaimTrue` on the virtual chain inputs. -/
theorem inClaim_of_target {w : ℕ} (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w)
    (claim : KeccakClaim) (hρ : claim.point.length + 4 = w) (D : ℕ → ℕ → K)
    (hv : wireTarget s n claim = wireChF w claim.point claim.mu claim.weights (n - 1) D []) :
    InClaimTrue w (chainIn s n D) claim := by
  rw [wireChF_nil] at hv
  have hS := sum_range_iota_succ claim.point claim.mu (n - 1) (by rw [hρ]; omega)
  rw [CharTwo.sub_eq_add] at hS
  rw [InClaimTrue, wire_identity_ch _ _ _ s D hn hN, hS]
  rw [wireTarget] at hv
  linear_combination hv - (iota claim.point claim.mu 0 * padDot claim.weights (digestBits s) +
    c43Dot claim.weights * (thrEval claim.point claim.mu (n - 1) + iota claim.point claim.mu 0)) *
      CharTwo.two_eq_zero (R := E)

/-- What the chain wiring phase returns. -/
structure WireChOut where
  /-- The wiring point `σ` and the final claim. -/
  sc : List E × E
  /-- `[g_D]`. -/
  g : List E
  /-- `D`'s slot reduction. -/
  d : SlotOut

/-- **The chain wiring phase** (S2: T3 with `T = K_ch·G_D`, T4's `D` row). -/
def wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : KeccakClaim) :
    VerifierProgram WireChOut :=
  sumcheck (wireTarget s n claim) 3 (List.replicate w none) >>= fun sc ↦
  VerifierProgram.readScalars 1 >>= fun g ↦
  VerifierProgram.require (sc.2 = msEval claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0) >>=
    fun _ ↦
  slotProg 2 sb dsel (dW claim.weights) sc.1 (g.getD 0 0) >>= fun d ↦
  VerifierProgram.ret ⟨sc, g, d⟩

/-- **The chain wiring phase** as a specification: from doom of the GKR's input claim on the
virtual chain inputs and `R` to doom of the ring claim on `D`'s block of `C_main` and `R`. -/
noncomputable def wireChSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    {w sb dsel h : ℕ} (hw : w + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb)
    (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w)
    (claim : KeccakClaim) (hρ : claim.point.length + 4 = w)
    (colM : β → ℕ → K) (R : β → Prop)
    (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (wireChProg w sb dsel s n claim)
      (Doomed C (fun q ↦ InClaimTrue w (chainIn s n (dOf w dsel (colM q))) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = w ∧ out.d.sl.1.length = 2 ∧
        Doomed C (fun q ↦ RingColTrue h (colM q) out.d.ring ∧ R q) hist) εmax 0 T :=
  have h4 : 4 ≤ w := by omega
  have hρ' : w - 4 ≤ claim.point.length := by omega
  ((sumcheckSpec (T := 0) hst hcard R (wireChF_plain w claim.point claim.mu claim.weights (n - 1)
      (fun q ↦ dOf w dsel (colM q))) (count := 3) (by norm_num) (by norm_num) zero_le h2 w []
      (wireTarget s n claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦
      ⟨inClaim_of_target s hn hN claim hρ (dOf w dsel (colM q)) hv, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc ↦
  if hs : sc.1.length = w then
    ((doomReadN (T := 0) hst (fun q ↦ sc.2 = wireChF w claim.point claim.mu claim.weights (n - 1)
        (dOf w dsel (colM q)) ([] ++ sc.1) ∧ R q) zero_le 0).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun g ↦
    (Spec.require (Pre := fun hist ↦ g.length = 0 + 1 ∧ Doomed C (fun q ↦ sc.2 =
        wireChF w claim.point claim.mu claim.weights (n - 1) (dOf w dsel (colM q)) ([] ++ sc.1) ∧
          R q) hist)
      (Post := fun _ hist ↦ Doomed C (fun q ↦
        g.getD 0 0 = slotSum w 2 dsel (dW claim.weights) (colM q) sc.1 ∧ R q) hist)
      (fun _ hd hcond ↦ Doomed.mono hd.2 fun q (hq : g.getD 0 0 =
          slotSum w 2 dsel (dW claim.weights) (colM q) sc.1 ∧ R q) ↦ ⟨by
        have hg := hq.1
        rw [List.nil_append, wireChF_end _ _ _ _ hs h4 hρ' (by omega), hcond, hg, gD_slot], hq.2⟩)).bind'
      fun _ ↦
    (slotSpec (T := T) hst hcard (k := w) (b := 2) hw hsel (dW claim.weights) colM R hs (g.getD 0 0)
        h2 hrT).bind' fun d ↦
    (Spec.ret (⟨sc, g, d⟩ : WireChOut)).mono (fun _ hd ↦ ⟨hs, hd.1, hd.2⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
