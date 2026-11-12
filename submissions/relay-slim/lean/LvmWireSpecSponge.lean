-- New for lvm2 (WP T-W): the tape's wiring phase with the sponge region (BLUEPRINT2 §1.2 T3–T4,
-- stage S3, optional per §11), with review R-BP2's fix B2 (`I_ks` split at `x_14`; only the upper half
-- weights `XM`). Built on the chain part (`LvmWireSpec`: `slotSpec`, `wire_identity_ch`) and T-K's
-- kernels (`msEval`, `ikEval`).
import LvmWireSpec

/-!
# The wiring phase with the sponge region (stage S3)

The tape has `2^(w+1)` rows (`tapeIn`, `LvmTapeRel`): the chain region below `2^w`, the sponge
region `2^w + j` (`j < 2^hs`, `hs = hr + 1`), void above. The wiring identity
(**`wire_identity`**) adds three sponge terms to the chain's:

  `T(x) = K_ch(x)·G_D(x) + K_ks(x)·G_Y(x) + I_lo(x)·G_M(x) + I_hi(x)·G_XM(x)`

with `K_ks(x) = [x + 1 < 2^hs]·cont_{x+1}·ι(2^w + x + 1)` (`kksT`), and **B2's split**
`I_lo(x) = [x < 2^hr]·ι(2^w + x)`, `I_hi(x) = [2^hr ≤ x < 2^hs]·ι(2^w + x)` (`iloT`, `ihiT`);
`G_Y` pairs all 1600 bits of `Y[x]`, `G_M` and `G_XM` the 1088 rate bits of `M[x]` and `XM[x]`. In the
sumcheck the sponge data are read periodically (`x mod 2^hs`, `x mod 2^hr`), so at the end `σ`
(`σ' = σ_{<hs}`, `e' = eq(σ_{≥hs}, 0)`):

  `final = K̃_ch(σ)·g_D + e'·(u_SP + Ĩ_lo(σ')·g_M)`,
  `u_SP = K̃_ks(σ')·G̃_Y(σ') + Ĩ_hi(σ')·G̃_XM(σ')`, `g_M = G̃_M(σ_{<hr})`.

The verifier's closed forms are T-K's: `K̃_ks` the sum over `cont`'s intervals of `MS` differences
(`kksE`), `Ĩ_lo`, `Ĩ_hi` one `ikEval` on `σ_{<hr}` times `eq(σ'_{hr}, 0)` or `eq(σ'_{hr}, 1)`
(`iloE`, `ihiE`). `XM`'s lower half is never read (B2). Three slot reductions follow (`slotSpec`):
`D` (2 rounds), the `SP` block (`Y`, `XM` in one 64-slot block of `2^hs` rows, 6 rounds) and `M` on
`C_rec` (32 columns of `2^hr` rows, 5 rounds).

R-BP2's B1 (T1 samples `r_{<20}`, absorbs the 50 free scalars, then samples `r_20`) is the caller's
(`LvmKeccakCaller*`); `TapeRel (b)` on lanes `4 … 24` relies on it.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open Lvm.KSponge Lvm.WK Finset
open scoped ENNReal

/-! ## The layout -/

/-- The tape's layout constants (FRZ's record at S3). -/
structure TapeLayout where
  /-- Chain rows `2^w`. -/
  w : ℕ
  /-- Sponge rows `2^hs`. -/
  hs : ℕ
  /-- `C_rec`'s rows `2^hr` (the message lanes below `2^hr` are `C_rec`'s `M`). -/
  hr : ℕ
  /-- `C_main` has `2^(hM + 6)` words. -/
  hM : ℕ
  /-- `C_rec` has `2^(hR + 6)` words. -/
  hR : ℕ
  /-- `D` in slots `4·dsel … 4·dsel + 3` of `2^w` words. -/
  dsel : ℕ
  /-- The `SP` block: slot `o` of row `j` at word `j + 2^hs·(o + 64·spsel)`. -/
  spsel : ℕ
  /-- `Y`'s 25 slots in the `SP` block. -/
  ySlot : ℕ
  /-- `XM`'s 17 slots in the `SP` block. -/
  xSlot : ℕ
  /-- `M`'s 17 columns among `C_rec`'s 32. -/
  mSlot : ℕ
  /-- `cont`'s intervals `[a, b]` of sponge rows. -/
  iv : List (ℕ × ℕ)

namespace TapeLayout

variable (L : TapeLayout)

/-- `D`'s selector bits in `C_main`. -/
def sbD : ℕ := L.hM + 6 - (L.w + 2)

/-- The `SP` block's selector bits in `C_main`. -/
def sbS : ℕ := L.hM - L.hs

/-- The continuation flag of a sponge row. -/
def cont (j : ℕ) : Bool := L.iv.any fun ab ↦ decide (ab.1 ≤ j ∧ j ≤ ab.2)

/-- The layout's side conditions. -/
structure Ok : Prop where
  hs_eq : L.hs = L.hr + 1
  hr4 : 4 ≤ L.hr
  hsw : L.hs ≤ L.w
  hD : L.w + 2 ≤ L.hM + 6
  hS : L.hs ≤ L.hM
  hRec : L.hr + 5 = L.hR + 6
  dsel : L.dsel < 2 ^ L.sbD
  spsel : L.spsel < 2 ^ L.sbS
  ys : L.ySlot + 25 ≤ 64
  xs : L.xSlot + 17 ≤ 64
  yx : L.ySlot + 25 ≤ L.xSlot ∨ L.xSlot + 17 ≤ L.ySlot
  ms : L.mSlot + 17 ≤ 32
  iv : ∀ ab ∈ L.iv, 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 ^ L.hs
  ivd : L.iv.Pairwise fun a b ↦ a.2 < b.1 ∨ b.2 < a.1

/-- `Y`'s lanes in the `SP` block. -/
def yOf (col : ℕ → K) (j l : ℕ) : K := col (j + 2 ^ L.hs * (L.ySlot + l + 2 ^ 6 * L.spsel))

/-- `XM`'s lanes in the `SP` block. -/
def xmOf (col : ℕ → K) (j l : ℕ) : K := col (j + 2 ^ L.hs * (L.xSlot + l + 2 ^ 6 * L.spsel))

/-- `M`'s lanes in `C_rec`. -/
def mOf (colR : ℕ → K) (j l : ℕ) : K := colR (j + 2 ^ L.hr * (L.mSlot + l + 2 ^ 5 * 0))

/-- The sponge rows' message lanes: `M` below `2^hr`, `XM` above (B2). -/
def msgAt (colM colR : ℕ → K) : ℕ → ℕ → K := msgOf L.hr (L.mOf colR) (L.xmOf colM)

/-- The tape's virtual inputs of a candidate. -/
def tapeInOf (s : RecursionFast.Digest) (n : ℕ) (colM colR : ℕ → K) :
    ℕ → RecursionFast.Keccak.State :=
  tapeIn L.w L.hs s n (dOf L.w L.dsel colM) (L.yOf colM) (L.msgAt colM colR) L.cont

end TapeLayout

/-! ## Tables and kernels -/

/-- `G_Y(x) = Σ_{q<1600} ω_q·bit_q(Y[x])`. -/
def gYT (ω : List E) (Y : ℕ → ℕ → K) (x : ℕ) : E :=
  ∑ q ∈ range 1600, ω.getD q 0 * bitE (rowBits Y x q)

/-- `G_M(x) = Σ_{q<1088} ω_q·bit_q(M[x])` (the rate). -/
def gMT (ω : List E) (M : ℕ → ℕ → K) (x : ℕ) : E :=
  ∑ q ∈ range 1088, ω.getD q 0 * bitE (rowBits M x q)

/-- `K_ks(x) = [x + 1 < 2^hs]·cont_{x+1}·ι(2^w + x + 1)`. -/
def kksT (L : TapeLayout) (ρ μ : List E) (x : ℕ) : E :=
  if x + 1 < 2 ^ L.hs ∧ L.cont (x + 1) then iota ρ μ (2 ^ L.w + x + 1) else 0

/-- B2's lower kernel `I_lo(x) = [x < 2^hr]·ι(2^w + x)` (weights `M`). -/
def iloT (L : TapeLayout) (ρ μ : List E) (x : ℕ) : E :=
  if x < 2 ^ L.hr then iota ρ μ (2 ^ L.w + x) else 0

/-- B2's upper kernel `I_hi(x) = [2^hr ≤ x < 2^hs]·ι(2^w + x)` (weights `XM`). -/
def ihiT (L : TapeLayout) (ρ μ : List E) (x : ℕ) : E :=
  if 2 ^ L.hr ≤ x ∧ x < 2 ^ L.hs then iota ρ μ (2 ^ L.w + x) else 0

/-- `K̃_ks(σ')`: `cont`'s intervals as differences of T-K's `MS`. -/
def kksE (L : TapeLayout) (ρ μ σ' : List E) : E :=
  (L.iv.map fun ab ↦ msEval ρ μ σ' (2 ^ L.w) ab.2 - msEval ρ μ σ' (2 ^ L.w) (ab.1 - 1)).sum

/-- `Ĩ_lo(σ')`. -/
def iloE (L : TapeLayout) (ρ μ σ' : List E) : E :=
  ikEval ρ μ (σ'.take L.hr) (2 ^ L.w) * eqAt (σ'.drop L.hr) 0

/-- `Ĩ_hi(σ')`. -/
def ihiE (L : TapeLayout) (ρ μ σ' : List E) : E :=
  ikEval ρ μ (σ'.take L.hr) (2 ^ L.w + 2 ^ L.hr) * eqAt (σ'.drop L.hr) 1

/-! ### Extensions over fewer variables -/

/-- A table's extension over `w` variables split at `k`: high `o`, low `x`. -/
theorem extE_split {w k : ℕ} {σ : List E} (hσ : σ.length = w) (hk : k ≤ w) (f : ℕ → E) :
    extE w σ f = ∑ o ∈ range (2 ^ (σ.drop k).length), eqAt (σ.drop k) o *
      ∑ x ∈ range (2 ^ k), eqAt (σ.take k) x * f (x + 2 ^ k * o) := by
  have hl : (σ.take k).length = k := by simp [hσ]; omega
  have e := col_split (s := σ.drop k) hl f
  rw [List.take_append_drop, show k + (σ.drop k).length = w by simp [hσ]; omega] at e
  exact e

/-- **A periodic table** (`f (x mod 2^k)`) has the extension of `f` over the low `k` variables. -/
theorem extE_mod {w k : ℕ} {σ : List E} (hσ : σ.length = w) (hk : k ≤ w) (f : ℕ → E) :
    extE w σ (fun x ↦ f (x % 2 ^ k)) = extE k (σ.take k) f := by
  rw [extE_split hσ hk]
  have e : ∀ o, ∑ x ∈ range (2 ^ k), eqAt (σ.take k) x * f ((x + 2 ^ k * o) % 2 ^ k) =
      extE k (σ.take k) f := fun o ↦ Finset.sum_congr rfl fun x hx ↦ by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
  simp only [e, ← Finset.sum_mul, sum_eqAt, one_mul]

/-- **A table supported below `2^k`**: its extension is `eq(σ_{≥k}, 0)` times the low part's. -/
theorem extE_low {w k : ℕ} {σ : List E} (hσ : σ.length = w) (hk : k ≤ w) (f : ℕ → E)
    (hf : ∀ x, 2 ^ k ≤ x → f x = 0) : extE w σ f = eqAt (σ.drop k) 0 * extE k (σ.take k) f := by
  rw [extE_split hσ hk, Finset.sum_eq_single 0]
  · simp [extE]
  · intro o _ ho
    rw [Finset.sum_eq_zero fun x _ ↦ by
      rw [hf _ (by have : 1 ≤ o := Nat.pos_of_ne_zero ho; nlinarith [Nat.two_pow_pos k]), mul_zero],
      mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.two_pow_pos _)) h

/-- **A table supported on the upper half** of `k + 1` variables. -/
theorem extE_high {k : ℕ} {σ : List E} (hσ : σ.length = k + 1) (f : ℕ → E)
    (hf : ∀ x < 2 ^ k, f x = 0) :
    extE (k + 1) σ f = eqAt (σ.drop k) 1 * extE k (σ.take k) (fun x ↦ f (x + 2 ^ k)) := by
  rw [extE_split (k := k) hσ (by omega), show (σ.drop k).length = 1 by simp [hσ],
    show 2 ^ 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : ∑ x ∈ range (2 ^ k), eqAt (σ.take k) x * f (x + 2 ^ k * 0) = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by rw [mul_zero, add_zero, hf x (Finset.mem_range.1 hx), mul_zero]
  rw [h0, mul_zero, zero_add, extE]
  simp only [mul_one]

/-- Disjoint intervals: the sum of their `MS` kernels is the `cont`-gated one. -/
theorem sum_msIntK_list (ρ μ : List E) (base x : ℕ) :
    ∀ iv : List (ℕ × ℕ), iv.Pairwise (fun a b ↦ a.2 < b.1 ∨ b.2 < a.1) →
      (iv.map fun ab ↦ msIntK ρ μ base ab.1 ab.2 x).sum =
        if iv.any (fun ab ↦ decide (ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2)) then iota ρ μ (base + x + 1)
        else 0
  | [], _ => by simp
  | ab :: rest, hp => by
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.sum_cons, sum_msIntK_list ρ μ base x rest hp.2, List.any_cons, msIntK]
    by_cases h1 : ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2
    · have hr : rest.any (fun ab ↦ decide (ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2)) = false := by
        rw [List.any_eq_false]
        intro c hc hc'
        have := hp.1 c hc
        simp only [decide_eq_true_eq] at hc'
        omega
      rw [if_pos h1, hr, if_neg (by simp), add_zero, decide_eq_true h1, Bool.true_or, if_pos rfl]
    · rw [if_neg h1, zero_add, decide_eq_false h1, Bool.false_or]

theorem kksE_eq {L : TapeLayout} (hL : L.Ok) (ρ μ : List E) {σ' : List E} (hσ : σ'.length = L.hs)
    (hρ : L.hs - 4 ≤ ρ.length) : kksE L ρ μ σ' = extE L.hs σ' (kksT L ρ μ) := by
  have h4 : 4 ≤ σ'.length := by rw [hσ, hL.hs_eq]; have := hL.hr4; omega
  have hdv : 2 ^ σ'.length ∣ 2 ^ L.w := Nat.pow_dvd_pow 2 (by rw [hσ]; exact hL.hsw)
  have hk : ∀ x, kksT L ρ μ x = (L.iv.map fun ab ↦ msIntK ρ μ (2 ^ L.w) ab.1 ab.2 x).sum := by
    intro x
    rw [sum_msIntK_list ρ μ _ x L.iv hL.ivd, kksT, TapeLayout.cont]
    by_cases hc : L.iv.any (fun ab ↦ decide (ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2)) = true
    · obtain ⟨ab, hab, hab'⟩ := List.any_eq_true.1 hc
      have := hL.iv ab hab
      simp only [decide_eq_true_eq] at hab'
      rw [if_pos ⟨by omega, hc⟩, if_pos hc]
    · rw [if_neg (fun h ↦ hc h.2), if_neg hc]
  rw [extE, Finset.sum_congr rfl fun x _ ↦ by rw [hk x], kksE, ← hσ]
  have hcomm : ∀ iv' : List (ℕ × ℕ), (∀ ab ∈ iv', 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 ^ L.hs) →
      ∑ x ∈ range (2 ^ σ'.length), eqAt σ' x *
          (iv'.map fun ab ↦ msIntK ρ μ (2 ^ L.w) ab.1 ab.2 x).sum =
        (iv'.map fun ab ↦ msEval ρ μ σ' (2 ^ L.w) ab.2 - msEval ρ μ σ' (2 ^ L.w) (ab.1 - 1)).sum := by
    intro iv' hiv
    induction iv' with
    | nil => simp
    | cons ab rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
      have hab := hiv ab (by simp)
      rw [ih (fun c hc ↦ hiv c (by simp [hc])),
        sum_msIntK ρ μ σ' _ _ _ h4 (by rw [hσ]; omega) hdv hab.1 hab.2.1 (by rw [hσ]; exact hab.2.2)]
  exact (hcomm L.iv hL.iv).symm

theorem iloE_eq {L : TapeLayout} (hL : L.Ok) (ρ μ : List E) {σ' : List E} (hσ : σ'.length = L.hs)
    (hρ : L.hr - 4 ≤ ρ.length) : iloE L ρ μ σ' = extE L.hs σ' (iloT L ρ μ) := by
  have hhr : L.hr ≤ L.hs := by rw [hL.hs_eq]; omega
  have hl : (σ'.take L.hr).length = L.hr := by simp [hσ]; omega
  rw [extE_low hσ hhr _ fun x hx ↦ by rw [iloT, if_neg (by omega)], iloE, mul_comm]
  congr 1
  rw [← sum_ikK ρ μ (σ'.take L.hr) (2 ^ L.w) (by rw [hl]; exact hL.hr4) (by rw [hl]; exact hρ)
    (Nat.pow_dvd_pow 2 (by rw [hl]; have := hL.hsw; omega)), extE, hl]
  exact Finset.sum_congr rfl fun x hx ↦ by rw [iloT, if_pos (Finset.mem_range.1 hx), ikK]

theorem ihiE_eq {L : TapeLayout} (hL : L.Ok) (ρ μ : List E) {σ' : List E} (hσ : σ'.length = L.hs)
    (hρ : L.hr - 4 ≤ ρ.length) : ihiE L ρ μ σ' = extE L.hs σ' (ihiT L ρ μ) := by
  have hl : (σ'.take L.hr).length = L.hr := by simp [hσ, hL.hs_eq]
  rw [hL.hs_eq] at hσ ⊢
  rw [extE_high hσ _ fun x hx ↦ by rw [ihiT, if_neg (by omega)], ihiE, mul_comm]
  congr 1
  have hw : L.hr ≤ L.w := by have := hL.hsw; have := hL.hs_eq; omega
  rw [← sum_ikK ρ μ (σ'.take L.hr) (2 ^ L.w + 2 ^ L.hr) (by rw [hl]; exact hL.hr4)
    (by rw [hl]; exact hρ) (by rw [hl]; exact dvd_add (Nat.pow_dvd_pow 2 hw) dvd_rfl), extE, hl]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  rw [ihiT, if_pos ⟨by omega, by rw [hL.hs_eq, pow_succ]; omega⟩, ikK, Nat.add_assoc, Nat.add_comm x]

/-! ## The wiring identity -/

theorem TapeLayout.cont_zero {L : TapeLayout} (hL : L.Ok) : L.cont 0 = false := by
  rw [TapeLayout.cont, List.any_eq_false]
  intro ab hab h
  have := hL.iv ab hab
  simp only [decide_eq_true_eq] at h
  omega

theorem toBitVec_addK (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- A sponge row's pairing: the predecessor's 1600 bits if it continues, and its 1088 message
bits. -/
theorem omegaDot_ks (hs : ℕ) (ω : List E) (Y Msg : ℕ → ℕ → K) (cont : ℕ → Bool) {j : ℕ}
    (hj : j < 2 ^ hs) :
    omegaDot ω (inState hs (ksVirt hs Y Msg cont) 0 j) =
      (if cont j then gYT ω Y (j - 1) else 0) + gMT ω Msg j := by
  have hq : ∀ q < 1600, bitE (sbit (inState hs (ksVirt hs Y Msg cont) 0 j) q) =
      (if cont j then bitE (rowBits Y (j - 1) q) else 0) +
        (if q < 1088 then bitE (rowBits Msg j q) else 0) := by
    intro q hq
    rw [← stBit_eq_sbit _ hq, stBit_inState hs _ j hq, ksVirt, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj, Nat.add_mul_div_left _ _ (Nat.two_pow_pos hs), Nat.div_eq_of_lt hj,
      zero_add, toBitVec_addK, BitVec.getLsbD_xor, bitE_xor]
    congr 1
    · split_ifs <;> simp [rowBits, BF64.toBitVec_zero]
    · by_cases h17 : q / 64 < 17
      · rw [if_pos h17, if_pos (by omega)]
        rfl
      · rw [if_neg h17, if_neg (by omega), BF64.toBitVec_zero, BitVec.getLsbD_zero, bitE_false]
  rw [omegaDot, Finset.sum_congr rfl fun q hq' ↦ by rw [hq q (Finset.mem_range.1 hq'), mul_add],
    Finset.sum_add_distrib]
  refine congr (congrArg HAdd.hAdd ?_) ?_
  · split_ifs
    · rfl
    · simp
  · rw [gMT, show 1600 = 1088 + 512 from rfl, Finset.sum_range_add,
      Finset.sum_eq_zero (s := range 512) fun q _ ↦ by rw [if_neg (by omega), mul_zero], add_zero]
    exact Finset.sum_congr rfl fun q hq' ↦ by rw [if_pos (Finset.mem_range.1 hq')]

/-- **The wiring identity (tape)**: the input claim's sum over the whole tape is the chain's
constant plus the kernel-weighted chain and sponge parts. -/
theorem wire_identity (L : TapeLayout) (hL : L.Ok) (ρ μ ω : List E) (s : RecursionFast.Digest)
    {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ L.w) (D Y M XM : ℕ → ℕ → K) :
    ∑ i ∈ range (2 ^ (L.w + 1)), iota ρ μ i *
        omegaDot ω (tapeIn L.w L.hs s n D Y (msgOf L.hr M XM) L.cont i) =
      iota ρ μ 0 * padDot ω (digestBits s) + c43Dot ω * ∑ i ∈ range (n - 1), iota ρ μ (i + 1) +
        ∑ x ∈ range (2 ^ L.w), (msK ρ μ 0 (n - 1) x * gDT ω D x + kksT L ρ μ x * gYT ω Y x +
          iloT L ρ μ x * gMT ω M x + ihiT L ρ μ x * gMT ω XM x) := by
  have hp := Nat.two_pow_pos L.w
  have hsw : 2 ^ L.hs ≤ 2 ^ L.w := Nat.pow_le_pow_right (by norm_num) hL.hsw
  have hrs : 2 ^ L.hr < 2 ^ L.hs := Nat.pow_lt_pow_right (by norm_num) (by rw [hL.hs_eq]; omega)
  rw [pow_succ, mul_two, Finset.sum_range_add]
  have hch : ∑ i ∈ range (2 ^ L.w), iota ρ μ i *
      omegaDot ω (tapeIn L.w L.hs s n D Y (msgOf L.hr M XM) L.cont i) =
      ∑ i ∈ range (2 ^ L.w), iota ρ μ i * omegaDot ω (chainIn s n D i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [tapeIn, if_pos (Finset.mem_range.1 hi)]
  -- a sponge row splits into its `Y` part (shifted by one) and its message part
  let Yp : ℕ → E := fun j ↦
    if j < 2 ^ L.hs ∧ L.cont j then iota ρ μ (2 ^ L.w + j) * gYT ω Y (j - 1) else 0
  let Mp : ℕ → E := fun j ↦
    if j < 2 ^ L.hs then iota ρ μ (2 ^ L.w + j) * gMT ω (msgOf L.hr M XM) j else 0
  have hrow : ∀ j, iota ρ μ (2 ^ L.w + j) *
      omegaDot ω (tapeIn L.w L.hs s n D Y (msgOf L.hr M XM) L.cont (2 ^ L.w + j)) = Yp j + Mp j := by
    intro j
    rw [tapeIn, if_neg (by omega), Nat.add_sub_cancel_left]
    by_cases hj : j < 2 ^ L.hs
    · rw [if_pos hj, omegaDot_ks _ _ _ _ _ hj]
      simp only [Yp, Mp, hj, true_and, if_true]
      split_ifs <;> ring
    · rw [if_neg hj, omegaDot_zero]
      simp [Yp, Mp, hj]
  obtain ⟨N, hN'⟩ : ∃ N, 2 ^ L.w = N + 1 := ⟨2 ^ L.w - 1, by omega⟩
  have hY : ∑ j ∈ range (2 ^ L.w), Yp j = ∑ x ∈ range (2 ^ L.w), kksT L ρ μ x * gYT ω Y x := by
    rw [hN', Finset.sum_range_succ', Finset.sum_range_succ]
    have h0 : Yp 0 = 0 := by simp [Yp, TapeLayout.cont_zero hL]
    have hN0 : kksT L ρ μ N * gYT ω Y N = 0 := by rw [kksT, if_neg (by omega), zero_mul]
    rw [h0, hN0]
    refine congrArg (· + 0) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [Yp, kksT, Nat.add_sub_cancel, ← Nat.add_assoc]
    split_ifs <;> simp
  have hM : ∑ j ∈ range (2 ^ L.w), Mp j = ∑ x ∈ range (2 ^ L.w),
      (iloT L ρ μ x * gMT ω M x + ihiT L ρ μ x * gMT ω XM x) := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hg : gMT ω (msgOf L.hr M XM) x = if x < 2 ^ L.hr then gMT ω M x else gMT ω XM x := by
      unfold gMT rowBits msgOf
      split_ifs <;> rfl
    simp only [Mp, iloT, ihiT, hg]
    split_ifs <;> first | omega | simp
  rw [hch, wire_identity_ch ρ μ ω s D hn hN, Finset.sum_congr rfl fun j _ ↦ hrow j,
    Finset.sum_add_distrib, hY, hM]
  simp only [Finset.sum_add_distrib]
  ring

/-! ## The wiring sumcheck -/

/-- The wiring sumcheck's family (tape); the sponge data are read periodically. -/
noncomputable def wireF (L : TapeLayout) (ρ μ ω : List E) (m : ℕ) (D Y M XM : ℕ → ℕ → K)
    (acc : List E) : E :=
  cubeSum (fun pt ↦ extE L.w pt (msK ρ μ 0 m) * extE L.w pt (gDT ω D) +
    extE L.w pt (kksT L ρ μ) * extE L.w pt (fun x ↦ gYT ω Y (x % 2 ^ L.hs)) +
    extE L.w pt (iloT L ρ μ) * extE L.w pt (fun x ↦ gMT ω M (x % 2 ^ L.hr)) +
    extE L.w pt (ihiT L ρ μ) * extE L.w pt (fun x ↦ gMT ω XM (x % 2 ^ L.hs))) L.w acc

theorem wireF_plain {β : Type} (L : TapeLayout) (ρ μ ω : List E) (m : ℕ)
    (D Y M XM : β → ℕ → ℕ → K) :
    PlainFamily (fun q acc ↦ wireF L ρ μ ω m (D q) (Y q) (M q) (XM q) acc) 2 L.w :=
  cube_plainFamily _ L.w fun _ pre post ↦
    PolyLE.add (PolyLE.add (PolyLE.add (polyLE_mle_mul _ _ _ _ pre post)
      (polyLE_mle_mul _ _ _ _ pre post)) (polyLE_mle_mul _ _ _ _ pre post))
      (polyLE_mle_mul _ _ _ _ pre post)

theorem wireF_nil (L : TapeLayout) (ρ μ ω : List E) (m : ℕ) (D Y M XM : ℕ → ℕ → K) :
    wireF L ρ μ ω m D Y M XM [] = ∑ x ∈ range (2 ^ L.w), (msK ρ μ 0 m x * gDT ω D x +
      kksT L ρ μ x * gYT ω Y x + iloT L ρ μ x * gMT ω M x + ihiT L ρ μ x * gMT ω XM x) := by
  rw [wireF, cubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  simp only [extE, sum_eqAt_bitsE hu']
  have hY : kksT L ρ μ u * gYT ω Y (u % 2 ^ L.hs) = kksT L ρ μ u * gYT ω Y u := by
    unfold kksT
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]
    · simp
  have hM : iloT L ρ μ u * gMT ω M (u % 2 ^ L.hr) = iloT L ρ μ u * gMT ω M u := by
    unfold iloT
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · simp
  have hX : ihiT L ρ μ u * gMT ω XM (u % 2 ^ L.hs) = ihiT L ρ μ u * gMT ω XM u := by
    unfold ihiT
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h.2]
    · simp
  rw [hY, hM, hX]

/-- **The family's end**, in the verifier's closed forms. -/
theorem wireF_end (L : TapeLayout) (hL : L.Ok) (ρ μ ω : List E) {m : ℕ} (D Y M XM : ℕ → ℕ → K)
    {σ : List E} (hσ : σ.length = L.w) (hρ : L.w - 4 ≤ ρ.length) (hm : m < 2 ^ L.w) :
    wireF L ρ μ ω m D Y M XM σ = msEval ρ μ σ 0 m * extE L.w σ (gDT ω D) +
      eqAt (σ.drop L.hs) 0 * ((kksE L ρ μ (σ.take L.hs) * extE L.hs (σ.take L.hs) (gYT ω Y) +
        ihiE L ρ μ (σ.take L.hs) * extE L.hs (σ.take L.hs) (gMT ω XM)) +
        iloE L ρ μ (σ.take L.hs) * extE L.hr (σ.take L.hr) (gMT ω M)) := by
  have hsw := hL.hsw
  have hrs : L.hr ≤ L.hs := by rw [hL.hs_eq]; omega
  have h4 : 4 ≤ σ.length := by rw [hσ]; have := hL.hr4; omega
  have hσ' : (σ.take L.hs).length = L.hs := by simp [hσ]; omega
  have hρs : L.hs - 4 ≤ ρ.length := by omega
  have hρr : L.hr - 4 ≤ ρ.length := by omega
  rw [wireF, cubeSum_full _ hσ]
  rw [show extE L.w σ (msK ρ μ 0 m) = msEval ρ μ σ 0 m by
      rw [extE, ← hσ]; exact sum_msK_zero ρ μ σ m h4 (by rw [hσ]; exact hρ) (by rw [hσ]; exact hm),
    extE_low hσ hsw (kksT L ρ μ) (fun x hx ↦ by rw [kksT, if_neg (by omega)]),
    extE_low hσ hsw (iloT L ρ μ) (fun x hx ↦ by
      rw [iloT, if_neg (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hrs; omega)]),
    extE_low hσ hsw (ihiT L ρ μ) (fun x hx ↦ by rw [ihiT, if_neg (by omega)]),
    extE_mod hσ hsw, extE_mod hσ (hrs.trans hsw), extE_mod hσ hsw,
    ← kksE_eq hL ρ μ hσ' hρs, ← iloE_eq hL ρ μ hσ' hρr, ← ihiE_eq hL ρ μ hσ' hρr]
  ring

/-! ## The slot reductions of the sponge data -/

/-- The `SP` block's slot weights: `K̃_ks(σ')·ω` on `Y`'s slots, `Ĩ_hi(σ')·ω` on `XM`'s (B2). -/
def spW (L : TapeLayout) (ω : List E) (kk ih : E) (o z : ℕ) : E :=
  if L.ySlot ≤ o ∧ o < L.ySlot + 25 then kk * ω.getD (64 * (o - L.ySlot) + z) 0
  else if L.xSlot ≤ o ∧ o < L.xSlot + 17 then ih * ω.getD (64 * (o - L.xSlot) + z) 0
  else 0

/-- `M`'s slot weights in `C_rec`. -/
def mW (L : TapeLayout) (ω : List E) (o z : ℕ) : E :=
  if L.mSlot ≤ o ∧ o < L.mSlot + 17 then ω.getD (64 * (o - L.mSlot) + z) 0 else 0

/-- A window of `c` slots from `a` among `N`. -/
theorem sum_window {N a c : ℕ} (h : a + c ≤ N) (F : ℕ → E) :
    ∑ o ∈ range N, (if a ≤ o ∧ o < a + c then F (o - a) else 0) = ∑ l ∈ range c, F l := by
  rw [show N = a + (c + (N - a - c)) by omega, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range a) fun o ho ↦ by
      rw [if_neg (by have := Finset.mem_range.1 ho; omega)],
    Finset.sum_eq_zero (s := range (N - a - c)) fun o _ ↦ by rw [if_neg (by omega)], zero_add,
    add_zero]
  exact Finset.sum_congr rfl fun l hl ↦ by
    rw [if_pos (by have := Finset.mem_range.1 hl; omega), Nat.add_sub_cancel_left]

/-- A rows' pairing over `c` lanes, lane by lane and bit by bit. -/
theorem extE_rows (k c : ℕ) (ω pt : List E) (F : ℕ → ℕ → K) :
    extE k pt (fun x ↦ ∑ q ∈ range (c * 64), ω.getD q 0 * bitE (rowBits F x q)) =
      ∑ l ∈ range c, ∑ z ∈ range 64, ω.getD (64 * l + z) 0 *
        ∑ x ∈ range (2 ^ k), eqAt pt x * bitE ((F x l).toBitVec.getLsbD z) := by
  simp only [extE, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_range_mul]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦
    Finset.sum_congr rfl fun x _ ↦ ?_
  have hz' := Finset.mem_range.1 hz
  simp only [rowBits, show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]
  ring

theorem sp_slot (L : TapeLayout) (hL : L.Ok) (ω : List E) (kk ih : E) (col : ℕ → K)
    (pt : List E) :
    kk * extE L.hs pt (gYT ω (L.yOf col)) + ih * extE L.hs pt (gMT ω (L.xmOf col)) =
      slotSum L.hs 6 L.spsel (spW L ω kk ih) col pt := by
  let sl : ℕ → ℕ → E := fun o z ↦ slotSlice L.hs 6 L.spsel col pt o z
  let FY : ℕ → E := fun l ↦ ∑ z ∈ range 64, kk * (ω.getD (64 * l + z) 0 * sl (L.ySlot + l) z)
  let FX : ℕ → E := fun l ↦ ∑ z ∈ range 64, ih * (ω.getD (64 * l + z) 0 * sl (L.xSlot + l) z)
  have ho : ∀ o, ∑ z ∈ range 64, spW L ω kk ih o z * sl o z =
      (if L.ySlot ≤ o ∧ o < L.ySlot + 25 then FY (o - L.ySlot) else 0) +
        (if L.xSlot ≤ o ∧ o < L.xSlot + 17 then FX (o - L.xSlot) else 0) := by
    intro o
    have hyx := hL.yx
    by_cases hy : L.ySlot ≤ o ∧ o < L.ySlot + 25
    · rw [if_pos hy, if_neg (by omega), add_zero]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [spW, if_pos hy, Nat.add_sub_cancel' hy.1]
      ring
    · rw [if_neg hy, zero_add]
      by_cases hx : L.xSlot ≤ o ∧ o < L.xSlot + 17
      · rw [if_pos hx]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [spW, if_neg hy, if_pos hx, Nat.add_sub_cancel' hx.1]
        ring
      · rw [if_neg hx]
        exact Finset.sum_eq_zero fun z _ ↦ by rw [spW, if_neg hy, if_neg hx, zero_mul]
  rw [slotSum, Finset.sum_congr rfl fun o _ ↦ ho o, Finset.sum_add_distrib,
    show (2 : ℕ) ^ 6 = 64 from rfl, sum_window hL.ys, sum_window hL.xs,
    show gYT ω (L.yOf col) = fun x ↦ ∑ q ∈ range (25 * 64), ω.getD q 0 *
      bitE (rowBits (L.yOf col) x q) from rfl,
    show gMT ω (L.xmOf col) = fun x ↦ ∑ q ∈ range (17 * 64), ω.getD q 0 *
      bitE (rowBits (L.xmOf col) x q) from rfl, extE_rows, extE_rows]
  simp only [FY, FX, sl, Finset.mul_sum]
  exact congr (congrArg HAdd.hAdd (Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z _ ↦
    by simp only [slotSlice, Finset.mul_sum]; rfl)) (Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun z _ ↦ by simp only [slotSlice, Finset.mul_sum]; rfl)

theorem m_slot (L : TapeLayout) (hL : L.Ok) (ω : List E) (colR : ℕ → K) (pt : List E) :
    extE L.hr pt (gMT ω (L.mOf colR)) = slotSum L.hr 5 0 (mW L ω) colR pt := by
  let FM : ℕ → E := fun l ↦ ∑ z ∈ range 64,
    ω.getD (64 * l + z) 0 * slotSlice L.hr 5 0 colR pt (L.mSlot + l) z
  have ho : ∀ o, ∑ z ∈ range 64, mW L ω o z * slotSlice L.hr 5 0 colR pt o z =
      (if L.mSlot ≤ o ∧ o < L.mSlot + 17 then FM (o - L.mSlot) else 0) := by
    intro o
    by_cases hm : L.mSlot ≤ o ∧ o < L.mSlot + 17
    · rw [if_pos hm]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [mW, if_pos hm, Nat.add_sub_cancel' hm.1]
    · rw [if_neg hm]
      exact Finset.sum_eq_zero fun z _ ↦ by rw [mW, if_neg hm, zero_mul]
  rw [slotSum, Finset.sum_congr rfl fun o _ ↦ ho o, show (2 : ℕ) ^ 5 = 32 from rfl,
    sum_window hL.ms, show gMT ω (L.mOf colR) = fun x ↦ ∑ q ∈ range (17 * 64), ω.getD q 0 *
      bitE (rowBits (L.mOf colR) x q) from rfl, extE_rows]
  rfl

/-! ## The phase -/

/-- What the wiring phase returns. -/
structure WireOut where
  /-- The wiring point `σ` and the final claim. -/
  sc : List E × E
  /-- `[g_D, u_SP, g_M]`. -/
  g : List E
  /-- `D`'s slot reduction. -/
  d : SlotOut
  /-- The `SP` block's. -/
  sp : SlotOut
  /-- `M`'s (on `C_rec`). -/
  m : SlotOut

/-- **The wiring phase** (S3: T3 with the sponge terms and B2's split, T4's three reductions). -/
def wireProg (L : TapeLayout) (s : RecursionFast.Digest) (n : ℕ) (claim : KeccakClaim) :
    VerifierProgram WireOut :=
  sumcheck (wireTarget s n claim) 3 (List.replicate L.w none) >>= fun sc ↦
  VerifierProgram.readScalars 3 >>= fun g ↦
  VerifierProgram.require (sc.2 = msEval claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eqAt (sc.1.drop L.hs) 0 * (g.getD 1 0 +
      iloE L claim.point claim.mu (sc.1.take L.hs) * g.getD 2 0)) >>= fun _ ↦
  slotProg 2 L.sbD L.dsel (dW claim.weights) sc.1 (g.getD 0 0) >>= fun d ↦
  slotProg 6 L.sbS L.spsel (spW L claim.weights (kksE L claim.point claim.mu (sc.1.take L.hs))
    (ihiE L claim.point claim.mu (sc.1.take L.hs))) (sc.1.take L.hs) (g.getD 1 0) >>= fun sp ↦
  slotProg 5 0 0 (mW L claim.weights) (sc.1.take L.hr) (g.getD 2 0) >>= fun m ↦
  VerifierProgram.ret ⟨sc, g, d, sp, m⟩

/-- **The wiring sumcheck's claim is the input claim** (tape). -/
theorem inClaim_of_wireTarget (L : TapeLayout) (hL : L.Ok) (s : RecursionFast.Digest) {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ L.w) (claim : KeccakClaim) (hρ : claim.point.length + 3 = L.w)
    (colM colR : ℕ → K)
    (hv : wireTarget s n claim = wireF L claim.point claim.mu claim.weights (n - 1)
      (dOf L.w L.dsel colM) (L.yOf colM) (L.mOf colR) (L.xmOf colM) []) :
    InClaimTrue (L.w + 1) (L.tapeInOf s n colM colR) claim := by
  rw [wireF_nil] at hv
  have hS := sum_range_iota_succ claim.point claim.mu (n - 1)
    (by rw [show claim.point.length + 4 = L.w + 1 by omega, pow_succ]; omega)
  rw [CharTwo.sub_eq_add] at hS
  rw [InClaimTrue, TapeLayout.tapeInOf, TapeLayout.msgAt,
    wire_identity L hL _ _ _ s hn hN, hS]
  rw [wireTarget] at hv
  linear_combination hv - (iota claim.point claim.mu 0 * padDot claim.weights (digestBits s) +
    c43Dot claim.weights * (thrEval claim.point claim.mu (n - 1) + iota claim.point claim.mu 0)) *
      CharTwo.two_eq_zero (R := E)

/-- The claims the wiring phase leaves: one ring claim on `D`'s block and one on the `SP` block of
`C_main`, one on `C_rec`. -/
def WireClaims (L : TapeLayout) (colM colR : ℕ → K) (out : WireOut) : Prop :=
  RingColTrue L.hM colM out.d.ring ∧ RingColTrue L.hM colM out.sp.ring ∧
    RingColTrue L.hR colR out.m.ring

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **The wiring phase** as a specification: from doom of the GKR's input claim on the tape's
virtual inputs and `R` to doom of the three ring claims and `R`. -/
noncomputable def wireSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (L : TapeLayout)
    (hL : L.Ok) (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ L.w)
    (claim : KeccakClaim) (hρ : claim.point.length + 3 = L.w) (colM colR : β → ℕ → K)
    (R : β → Prop) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hr0 : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (wireProg L s n claim)
      (Doomed C (fun q ↦ InClaimTrue (L.w + 1) (L.tapeInOf s n (colM q) (colR q)) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = L.w ∧
        Doomed C (fun q ↦ WireClaims L (colM q) (colR q) out ∧ R q) hist) εmax 0 T :=
  have hw4 : 4 ≤ L.w := by have := hL.hr4; have := hL.hs_eq; have := hL.hsw; omega
  have hρ' : L.w - 4 ≤ claim.point.length := by omega
  have hkD : L.w + 2 + L.sbD = L.hM + 6 := by have := hL.hD; unfold TapeLayout.sbD; omega
  have hkS : L.hs + 6 + L.sbS = L.hM + 6 := by have := hL.hS; unfold TapeLayout.sbS; omega
  have hkR : L.hr + 5 + 0 = L.hR + 6 := by have := hL.hRec; omega
  let ρ := claim.point
  let μ := claim.mu
  let ω := claim.weights
  let F : β → List E → E := fun q acc ↦ wireF L ρ μ ω (n - 1) (dOf L.w L.dsel (colM q))
    (L.yOf (colM q)) (L.mOf (colR q)) (L.xmOf (colM q)) acc
  ((sumcheckSpec (T := 0) hst hcard R (wireF_plain L ρ μ ω (n - 1) (fun q ↦ dOf L.w L.dsel (colM q))
      (fun q ↦ L.yOf (colM q)) (fun q ↦ L.mOf (colR q)) (fun q ↦ L.xmOf (colM q))) (count := 3)
      (by norm_num) (by norm_num) zero_le h2 L.w [] (wireTarget s n claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦
      ⟨inClaim_of_wireTarget L hL s hn hN claim hρ (colM q) (colR q) hv, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc ↦
  if hs : sc.1.length = L.w then
    have hσS : (sc.1.take L.hs).length = L.hs := by simp [hs]; exact hL.hsw
    have hσR : (sc.1.take L.hr).length = L.hr := by
      simp [hs]; have := hL.hsw; have := hL.hs_eq; omega
    let cSP : β → E → Prop := fun q v ↦ v = slotSum L.hs 6 L.spsel
      (spW L ω (kksE L ρ μ (sc.1.take L.hs)) (ihiE L ρ μ (sc.1.take L.hs))) (colM q) (sc.1.take L.hs)
    let cM : β → E → Prop := fun q v ↦ v = slotSum L.hr 5 0 (mW L ω) (colR q) (sc.1.take L.hr)
    ((doomReadN (T := 0) hst (fun q ↦ sc.2 = F q ([] ++ sc.1) ∧ R q) zero_le 2).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun g ↦
    (Spec.require (Pre := fun hist ↦ g.length = 2 + 1 ∧
        Doomed C (fun q ↦ sc.2 = F q ([] ++ sc.1) ∧ R q) hist)
      (Post := fun _ hist ↦ Doomed C (fun q ↦
        g.getD 0 0 = slotSum L.w 2 L.dsel (dW ω) (colM q) sc.1 ∧
          ((cSP q (g.getD 1 0) ∧ cM q (g.getD 2 0)) ∧ R q)) hist)
      (fun _ hd hcond ↦ Doomed.mono hd.2 fun q (hq : g.getD 0 0 = slotSum L.w 2 L.dsel (dW ω)
          (colM q) sc.1 ∧ ((cSP q (g.getD 1 0) ∧ cM q (g.getD 2 0)) ∧ R q)) ↦ ⟨by
        have h0 := hq.1
        have h1 : g.getD 1 0 = _ := hq.2.1.1
        have h2' : g.getD 2 0 = _ := hq.2.1.2
        simp only [F, ρ, μ, ω]
        rw [List.nil_append, wireF_end L hL _ _ _ _ _ _ _ hs hρ' (by omega), hcond, h0, h1, h2',
          ← gD_slot, ← sp_slot L hL, ← m_slot L hL], hq.2.2⟩)).bind' fun _ ↦
    (slotSpec (T := 0) hst hcard (k := L.w) (b := 2) hkD hL.dsel (dW ω) colM
        (fun q ↦ (cSP q (g.getD 1 0) ∧ cM q (g.getD 2 0)) ∧ R q) hs (g.getD 0 0) h2 hr0).bind'
      fun d ↦
    ((slotSpec (T := 0) hst hcard (k := L.hs) (b := 6) hkS hL.spsel
        (spW L ω (kksE L ρ μ (sc.1.take L.hs)) (ihiE L ρ μ (sc.1.take L.hs))) colM
        (fun q ↦ RingColTrue L.hM (colM q) d.ring ∧ cM q (g.getD 2 0) ∧ R q) hσS (g.getD 1 0)
        h2 hr0).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hsp, hr, hm, hR⟩ ↦ ⟨hr, ⟨hsp, hm⟩, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sp ↦
    ((slotSpec (T := T) hst hcard (k := L.hr) (b := 5) (sb := 0) (blk := 0) hkR (by norm_num)
        (mW L ω) colR (fun q ↦ RingColTrue L.hM (colM q) d.ring ∧
          RingColTrue L.hM (colM q) sp.ring ∧ R q) hσR (g.getD 2 0) h2 hrT).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hm, hd', hsp, hR⟩ ↦ ⟨hsp, hd', hm, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun m ↦
    (Spec.ret (⟨sc, g, d, sp, m⟩ : WireOut)).mono
      (fun _ hd ↦ ⟨hs, Doomed.mono hd.2 fun q ⟨⟨hd', hsp, hm⟩, hR⟩ ↦ ⟨hm, hd', hsp, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
