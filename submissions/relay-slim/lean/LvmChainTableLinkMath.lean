-- New for lvm (WP-8): the algebra of the CH link (BLUEPRINT §4.1): V_S's `M3.v0` link formulas over `E`,
-- the zero-test tables and the identities the link's specification (`LvmChainTableLink`) needs.
import LvmChainTable
import LvmShift
import LvmKeccakCaller

/-!
# The `CH` link: formulas and identities

The link `in_{x+1} = Pad43(Y_x)` (`x + 1 < 2^h`) is checked bitwise on lanes `0 … 7` by a zero test
at `(ρ, λ, ζ) ∈ E^h × E^3 × E^6` and a shift sumcheck, and on lanes `8 … 24` (constants) by a zero
test riding on the shift sumcheck's challenges. With `ω(l, p) = eq(λ, l)·eq(ζ, p)`:

* `padWeightE`, `padConstE`, `chShiftTargetE`, `chSc2TargetE`, `wtE`: V_S's `padWeight`,
  `padConst`, `chShiftTarget0`, `chSc2Target0`, `wt` (`LvmDecideV0`) over `E`, with `eqAt` for the
  verifier's `eq` tables;
* **`padSum_eq`**: `Σ_{l<8, p<64} ω(l,p)·Pad43(y)[64l + p] = padConst + Σ_{m<4, q<64} W(m,q)·y[64m + q]`;
* `linkDelta`, `constDelta`: the zero-test tables; **`linkBits_of_zero`**, **`const_of_zero`**: they
  vanish exactly on the relation; **`linkZero_iff`**: at full length the link table's extension is
  `target + F(0)`, the shift sumcheck's claim (`shiftSum`);
* the sumcheck families `Fsh` (shift, `h` rounds) and `G2` (the `Y` lane, 2 rounds) and their ends
  (`Fsh_end`, `G2_nil`, `G2_end`) in the slices at `(ρ', λ, 0, 0, 0)` and `(ρ', μ, sel(ys/4))`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Ring Finset

/-! ## V_S's link formulas over `E` -/

/-- `ρ`, `λ`, `ζ` from the link's `h + 9` challenges. -/
def chRho (h : ℕ) (chal : List E) : List E := chal.take h
/-- The lane challenges `λ` (3). -/
def chLam (h : ℕ) (chal : List E) : List E := (chal.drop h).take 3
/-- The bit challenges `ζ` (6). -/
def chZeta (h : ℕ) (chal : List E) : List E := chal.drop (h + 3)

/-- `ω(l, p) = eq(λ, l)·eq(ζ, p)`. -/
def omegaE (lam zeta : List E) (l p : ℕ) : E := eqAt lam l * eqAt zeta p

/-- The weight of bit `q` of `Y` lane `m` through `Pad43` (V_S's `padWeight`). -/
def padWeightE (lam zeta : List E) (m q : ℕ) : E :=
  if q ≤ 55 then omegaE lam zeta m (q + 8) else omegaE lam zeta (m + 1) (q - 56)

/-- The constant bits of `Pad43`'s lanes `0 … 7` (V_S's `padConst`): `0x43`, and `0x01` at bit 8
of lane 4. -/
def padConstE (lam zeta : List E) : E :=
  (∑ p ∈ range 8, if (0x43 : ℕ).testBit p then omegaE lam zeta 0 p else 0) + omegaE lam zeta 4 8

/-- The shift sumcheck's claim `C·(1 + eq(ρ, 1^h))` (V_S's `chShiftTarget0`). -/
def chShiftTargetE (h : ℕ) (chal : List E) : E :=
  padConstE (chLam h chal) (chZeta h chal) * (1 + prodE (chRho h chal))

/-- The two-round sumcheck's claim `f₁ + S(ρ, ρ')·Σ_p eq(ζ, p) inS_p` (V_S's `chSc2Target0`). -/
def chSc2TargetE (h : ℕ) (chal : List E) (shift : List E × E) (inS : List E) : E :=
  shift.2 + shiftEvalE (chRho h chal) shift.1 *
    ∑ p ∈ range 64, eqAt (chZeta h chal) p * inS.getD p 0

/-- `W̃(μ, q) = Σ_m eq(μ, m)·W(m, q)` (V_S's `wt`). -/
def wtE (lam zeta mu : List E) (q : ℕ) : E := ∑ m ∈ range 4, eqAt mu m * padWeightE lam zeta m q

/-- The point of the `in` slices: `(ρ', λ, 0, 0, 0)` (slots `0 … 7`). -/
def chInPt (h : ℕ) (chal : List E) (shift : List E × E) : List E :=
  shift.1 ++ chLam h chal ++ [0, 0, 0]

/-- The point of the `Y` slices: `(ρ', μ, sel(ys / 4))` (slots `ys … ys + 3`). -/
def chYPt (ys : ℕ) (shift sc2 : List E × E) : List E := shift.1 ++ sc2.1 ++ selectorPoint (ys / 4) 4

/-! ## The `Pad43` weights -/

theorem bitE_add_eq_zero {a b : Bool} (h : bitE a + bitE b = 0) : a = b := by
  cases a <;> cases b <;> simp_all [bitE]

theorem bitE_add_self (a : Bool) : bitE a + bitE a = 0 := CharTwo.add_self_eq_zero _

/-- **The `Pad43` weights**: the link's lanes `0 … 7` weighted by `ω` are the constant bits plus
the `Y` bits through `padWeightE`. -/
theorem padSum_eq (lam zeta : List E) (y : ℕ → Bool) :
    ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE (pad43Bit y (64 * l + p)) =
      padConstE lam zeta +
        ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (y (64 * m + q)) := by
  let F : ℕ → E := fun j ↦ omegaE lam zeta (j / 64) (j % 64) * bitE (pad43Bit y j)
  have hL : ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE (pad43Bit y (64 * l + p)) =
      ∑ j ∈ range (8 * 64), F j := by
    rw [sum_range_mul]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun p hp ↦ ?_
    have hp' := Finset.mem_range.1 hp
    simp only [F, show (64 * l + p) / 64 = l by omega, show (64 * l + p) % 64 = p by omega]
  rw [hL, show 8 * 64 = 8 + (4 * 64 + 248) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, F j =
      ∑ p ∈ range 8, if (0x43 : ℕ).testBit p then omegaE lam zeta 0 p else 0 := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp' := Finset.mem_range.1 hp
    simp only [F, pad43Bit, if_pos hp', show p / 64 = 0 by omega, show p % 64 = p by omega]
    cases (0x43 : ℕ).testBit p <;> simp [bitE]
  have h2 : ∑ j ∈ range (4 * 64), F (8 + j) =
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (y (64 * m + q)) := by
    rw [sum_range_mul]
    refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun q hq ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have hq' := Finset.mem_range.1 hq
    simp only [F, pad43Bit, if_neg (show ¬ 8 + (64 * m + q) < 8 by omega),
      if_pos (show 8 + (64 * m + q) < 264 by omega), show 8 + (64 * m + q) - 8 = 64 * m + q by omega,
      padWeightE]
    split_ifs with h55
    · rw [show (8 + (64 * m + q)) / 64 = m by omega, show (8 + (64 * m + q)) % 64 = q + 8 by omega]
    · rw [show (8 + (64 * m + q)) / 64 = m + 1 by omega,
        show (8 + (64 * m + q)) % 64 = q - 56 by omega]
  have h3 : ∑ j ∈ range 248, F (8 + (4 * 64 + j)) = omegaE lam zeta 4 8 := by
    rw [Finset.sum_range_succ']
    have hz : ∑ j ∈ range 247, F (8 + (4 * 64 + (j + 1))) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by
        have hj' := Finset.mem_range.1 hj
        simp only [F, pad43Bit, if_neg (show ¬ 8 + (4 * 64 + (j + 1)) < 8 by omega),
          if_neg (show ¬ 8 + (4 * 64 + (j + 1)) < 264 by omega)]
        have : ¬ (8 + (4 * 64 + (j + 1)) = 264 ∨ 8 + (4 * 64 + (j + 1)) = 1087) := by omega
        rw [decide_eq_false this, bitE_false, mul_zero]
    rw [hz, zero_add]
    simp [F, pad43Bit, bitE]
  rw [h1, h2, h3, padConstE]
  ring

/-! ## The zero-test tables -/

variable (h ys : ℕ) (col : ℕ → K)

/-- The link's mismatch at row `x`, lane `l < 8`, bit `p` (rows `x + 1 < 2^h`). -/
def linkD (x l p : ℕ) : E :=
  if x + 1 < 2 ^ h then
    bitE ((col (x + 1 + 2 ^ h * l)).toBitVec.getLsbD p) + bitE (pad43Bit (yBits h ys col x) (64 * l + p))
  else 0

/-- The link's zero-test table on `h + 9` bits: row low, then lane (3 bits), then bit (6). -/
def linkDelta (w : ℕ) : E := linkD h ys col (w % 2 ^ h) (w / 2 ^ h % 8) (w / 2 ^ h / 8)

/-- The constant lanes' zero-test table on `h + 5` bits: row low, then lane. -/
def constDelta (w : ℕ) : E :=
  if 8 ≤ w / 2 ^ h ∧ w / 2 ^ h < 25 then
    ofK (col (w % 2 ^ h + 2 ^ h * (w / 2 ^ h))) + ofK (K.ofLane (padConstLane (w / 2 ^ h)))
  else 0

theorem idx_div {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) / 2 ^ h = t := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos h), Nat.div_eq_of_lt hx, zero_add]

theorem idx_mod {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) % 2 ^ h = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- **A vanishing link table is the link** on lanes `0 … 7`. -/
theorem linkBits_of_zero (hz : ZeroOn (linkDelta h ys col) [] (h + 9)) : LinkBits h ys col := by
  rw [zeroOn_nil] at hz
  intro x hx l hl p hp
  have := hz (x + 2 ^ h * (l + 8 * p)) (by
    have : 2 ^ (h + 9) = 2 ^ h * 512 := by rw [pow_add]; rfl
    nlinarith)
  simp only [linkDelta, idx_div h (show x < 2 ^ h by omega), idx_mod h (show x < 2 ^ h by omega),
    show (l + 8 * p) % 8 = l by omega, show (l + 8 * p) / 8 = p by omega, linkD, if_pos hx] at this
  exact bitE_add_eq_zero this

theorem ofK_injective' : Function.Injective (ofK : K → E) := (algebraMap K E).injective

/-- **A vanishing constant table is the constant lanes.** -/
theorem const_of_zero (hz : ZeroOn (constDelta h col) [] (h + 5)) : ConstLanes h col := by
  rw [zeroOn_nil] at hz
  intro x hx t h8 h25
  have := hz (x + 2 ^ h * t) (by
    have : 2 ^ (h + 5) = 2 ^ h * 32 := by rw [pow_add]; rfl
    nlinarith)
  simp only [constDelta, idx_div h hx, idx_mod h hx, h8, h25, and_self, if_true] at this
  exact ofK_injective' (add_eq_zero_iff_E.1 this)

/-- The constant lanes' claims at `ρ'`: `in_t(ρ') = c_t` for `t = 8 … 24` (V_S's 17 word claims). -/
def ConstClaims (pt : List E) : Prop :=
  ∀ t, 8 ≤ t → t < 25 → stepMle h pt (fun x ↦ col (x + 2 ^ h * t)) = ofK (K.ofLane (padConstLane t))

/-- The constant claims make the constant table's extension vanish at `ρ'`. -/
theorem constZero_of_claims {pt : List E} (hpt : pt.length = h) (hc : ConstClaims h col pt) :
    ZeroOn (constDelta h col) pt (h + 5) := by
  intro t ht
  unfold foldT
  rw [hpt]
  have e : ∀ x ∈ range (2 ^ h), constDelta h col (x + 2 ^ h * t) =
      if 8 ≤ t ∧ t < 25 then ofK (col (x + 2 ^ h * t)) + ofK (K.ofLane (padConstLane t)) else 0 :=
    fun x hx ↦ by simp only [constDelta, idx_div h (Finset.mem_range.1 hx),
      idx_mod h (Finset.mem_range.1 hx)]
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [e x hx]]
  split_ifs with ht'
  · have h1 : ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (col (x + 2 ^ h * t)) =
        ofK (K.ofLane (padConstLane t)) := hc t ht'.1 ht'.2
    have h2 : ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (K.ofLane (padConstLane t)) =
        ofK (K.ofLane (padConstLane t)) := by
      rw [← Finset.sum_mul, ← hpt, sum_eqAt, one_mul]
    rw [Finset.sum_congr rfl fun x _ ↦ mul_add _ _ _, Finset.sum_add_distrib, h1, h2]
    exact CharTwo.add_self_eq_zero _
  · simp

/-! ## The shift sumcheck -/

variable (lam zeta : List E)

/-- `A(k) = Σ_{l<8, p<64} ω(l,p)·bit_p(in_k[l])`. -/
def linkA (k : ℕ) : E :=
  ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE ((col (k + 2 ^ h * l)).toBitVec.getLsbD p)

/-- `B(k) = Σ_{m<4, q<64} W(m,q)·bit_q(Y_k[m])`. -/
def linkB (k : ℕ) : E :=
  ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (yBits h ys col k (64 * m + q))

/-- The shift sumcheck's family: `Σ_k S(ρ, k)·A(k) + Eq'(ρ, k)·B(k)` over the rows not bound. -/
noncomputable def Fsh (rho : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ (∑ k ∈ range (2 ^ h), eqAt pt k * shiftK rho k) *
      (∑ k ∈ range (2 ^ h), eqAt pt k * linkA h col lam zeta k) +
    (∑ k ∈ range (2 ^ h), eqAt pt k * maskK rho k) *
      (∑ k ∈ range (2 ^ h), eqAt pt k * linkB h ys col lam zeta k)) h acc

theorem Fsh_plain {β : Type} (cq : β → ℕ → K) (rho : List E) :
    PlainFamily (fun q acc ↦ Fsh h ys (cq q) lam zeta rho acc) 2 h :=
  cube_plainFamily _ h fun _ pre post ↦ PolyLE.add (polyLE_mle_mul _ _ _ _ pre post)
    (polyLE_mle_mul _ _ _ _ pre post)

/-- The family before the rounds: the sum over the rows. -/
theorem Fsh_nil (rho : List E) :
    Fsh h ys col lam zeta rho [] = ∑ k ∈ range (2 ^ h),
      (shiftK rho k * linkA h col lam zeta k + maskK rho k * linkB h ys col lam zeta k) := by
  rw [Fsh, cubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

/-- Three nested sums in the other order. -/
theorem sum_comm3 {a b c : ℕ} (g : ℕ → ℕ → ℕ → E) :
    ∑ x ∈ range a, ∑ l ∈ range b, ∑ p ∈ range c, g x l p =
      ∑ p ∈ range c, ∑ l ∈ range b, ∑ x ∈ range a, g x l p := by
  rw [Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm]

/-- The link table's extension at `(ρ, λ, ζ)`, regrouped: row, then lane, then bit. -/
theorem linkDelta_sum {rho : List E} (hr : rho.length = h) (hl : lam.length = 3)
    (hz : zeta.length = 6) :
    ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      ∑ x ∈ range (2 ^ h), eqAt rho x *
        ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * linkD h ys col x l p := by
  have e1 : ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      ∑ o ∈ range (2 ^ (3 + zeta.length)), eqAt (lam ++ zeta) o *
        ∑ x ∈ range (2 ^ h), eqAt rho x * linkD h ys col x (o % 8) (o / 8) := by
    have := col_split (s := lam ++ zeta) hr (linkDelta h ys col)
    rw [show (lam ++ zeta).length = 9 by simp [hl, hz], ← List.append_assoc] at this
    rw [this, hz]
    refine Finset.sum_congr rfl fun o _ ↦ congrArg _ (Finset.sum_congr rfl fun x hx ↦ ?_)
    rw [linkDelta, idx_div h (Finset.mem_range.1 hx), idx_mod h (Finset.mem_range.1 hx)]
  have e2 := col_split (h := 3) (a := lam) (s := zeta) hl
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt rho x * linkD h ys col x (o % 8) (o / 8))
  rw [e1, e2, hz]
  simp only [Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun l hl' ↦
    Finset.sum_congr rfl fun p _ ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [show (l + 2 ^ 3 * p) % 8 = l by omega, show (l + 2 ^ 3 * p) / 8 = p by omega, omegaE]
  ring

/-- **The link table's extension is the shift sumcheck's claim plus its target.** -/
theorem linkDelta_eq {rho : List E} (hr : rho.length = h) (hl : lam.length = 3)
    (hz : zeta.length = 6) :
    ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      Fsh h ys col lam zeta rho [] + padConstE lam zeta * (1 + prodE rho) := by
  rw [linkDelta_sum h ys col lam zeta hr hl hz, Fsh_nil, ← sum_maskK_one, hr]
  have hrow : ∀ x ∈ range (2 ^ h), eqAt rho x *
      ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * linkD h ys col x l p =
      maskK rho x * (linkA h col lam zeta (x + 1) + linkB h ys col lam zeta x +
        padConstE lam zeta) := by
    intro x _
    unfold maskK
    rw [hr]
    split_ifs with hx
    · simp only [linkD, if_pos hx, mul_add, Finset.sum_add_distrib]
      rw [padSum_eq, linkA, linkB]
      simp only [yBits]
      ring
    · simp [linkD, hx]
  rw [Finset.sum_congr rfl hrow, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- the shifted `A` terms: row `x + 1` under `maskK` is row `k` under `shiftK`
  have hp := Nat.two_pow_pos h
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ h = M + 1 := ⟨2 ^ h - 1, by omega⟩
  have hA : ∑ x ∈ range (2 ^ h), maskK rho x * linkA h col lam zeta (x + 1) =
      ∑ k ∈ range (2 ^ h), shiftK rho k * linkA h col lam zeta k := by
    rw [hM, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [maskK, hr, hM, show ¬ (M + 1 < M + 1) by omega, ite_false, zero_mul, add_zero,
      shiftK, show ¬ (1 ≤ 0) by omega, Nat.le_add_left, ite_true, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [if_pos (by have := Finset.mem_range.1 hx; omega)]
  have : ∀ x ∈ range (2 ^ h), maskK rho x * (linkA h col lam zeta (x + 1) +
      linkB h ys col lam zeta x + padConstE lam zeta) =
      maskK rho x * linkA h col lam zeta (x + 1) + (maskK rho x * linkB h ys col lam zeta x +
        padConstE lam zeta * maskK rho x) := fun x _ ↦ by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hA, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The shift sumcheck's claim at `(ρ, λ, ζ)` is the zero test**: if the claim holds, the link
table's extension vanishes there. -/
theorem zero_of_shiftClaim {chal : List E} (hc : chal.length = h + 9)
    (H : chShiftTargetE h chal = Fsh h ys col (chLam h chal) (chZeta h chal) (chRho h chal) []) :
    ZeroOn (linkDelta h ys col) chal (h + 9) := by
  have hsplit : chal = chRho h chal ++ chLam h chal ++ chZeta h chal := by
    simp only [chRho, chLam, chZeta, List.append_assoc, List.take_append_drop,
      ← List.drop_drop]
  have hr : (chRho h chal).length = h := by simp [chRho, hc]
  have hl : (chLam h chal).length = 3 := by simp [chLam, hc]
  have hz : (chZeta h chal).length = 6 := by simp [chZeta, hc]
  rw [zeroOn_full _ hc]
  conv_lhs => rw [hsplit]
  rw [linkDelta_eq h ys col _ _ hr hl hz, ← H, chShiftTargetE]
  exact CharTwo.add_self_eq_zero _

/-! ## The ends of the two sumchecks -/

/-- Slice `q` of `Y` lane `m` at the rows' point `pt`. -/
def ysl (pt : List E) (m q : ℕ) : E :=
  ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * (ys + m))).toBitVec.getLsbD q)

theorem eqAt_000 (t : ℕ) (ht : t < 8) : eqAt [0, 0, 0] t = if t = 0 then 1 else 0 := by
  have := eqAt_bitsE_lt (m := 3) (z := 0) (w := t) (by norm_num) (by simpa using ht)
  simpa [bitsE] using this

/-- **The `in` slices at `(ρ', λ, 0, 0, 0)`**: the lanes `0 … 7` weighted by `eq(λ, ·)`. -/
theorem sliceExt_in {pt : List E} (hpt : pt.length = h) (hl : lam.length = 3) (p : ℕ) :
    sliceExt h col (pt ++ lam ++ [0, 0, 0]) p = ∑ l ∈ range 8, eqAt lam l *
      ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * l)).toBitVec.getLsbD p) := by
  unfold sliceExt
  have := col_split (s := lam ++ ([0, 0, 0] : List E)) hpt
    (fun n ↦ bitE ((col n).toBitVec.getLsbD p))
  rw [show (lam ++ ([0, 0, 0] : List E)).length = 6 by simp [hl], ← List.append_assoc] at this
  rw [this]
  have e2 := col_split (h := 3) (a := lam) (s := ([0, 0, 0] : List E)) hl
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * o)).toBitVec.getLsbD p))
  rw [show ([0, 0, 0] : List E).length = 3 from rfl] at e2
  rw [show (6 : ℕ) = 3 + 3 from rfl, e2, Finset.sum_eq_single 0]
  · simp [eqAt_000]
  · intro t ht h0
    rw [eqAt_000 t (by simpa using ht), if_neg h0, zero_mul]
  · simp

/-- **The `Y` slices at `(ρ', μ, sel(ys / 4))`**: the lanes `ys … ys + 3` weighted by `eq(μ, ·)`. -/
theorem sliceExt_y {pt mu : List E} (hpt : pt.length = h) (hmu : mu.length = 2)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (q : ℕ) :
    sliceExt h col (pt ++ mu ++ selectorPoint (ys / 4) 4) q =
      ∑ m ∈ range 4, eqAt mu m * ysl h ys col pt m q := by
  unfold sliceExt
  have hsel : (selectorPoint (ys / 4) 4) = bitsE (ys / 4) 4 := by
    rw [selectorPoint_eq_boolPoint]
    clear hys hys'
    generalize ys / 4 = z
    induction (4 : ℕ) generalizing z with
    | zero => rfl
    | succ n ih =>
      rw [boolPoint_succ, bitsE, ih, Nat.testBit_zero]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one z with h0 | h1 <;> simp [*]
  have := col_split (s := mu ++ selectorPoint (ys / 4) 4) hpt
    (fun n ↦ bitE ((col n).toBitVec.getLsbD q))
  rw [show (mu ++ selectorPoint (ys / 4) 4).length = 6 by simp [hmu, selectorPoint],
    ← List.append_assoc] at this
  rw [this]
  have e2 := col_split (h := 2) (a := mu) (s := selectorPoint (ys / 4) 4) hmu
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * o)).toBitVec.getLsbD q))
  rw [show (selectorPoint (ys / 4) 4).length = 4 by simp [selectorPoint]] at e2
  rw [show (6 : ℕ) = 2 + 4 from rfl, e2, hsel, sum_eqAt_bitsE hys']
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [ysl, show m + 2 ^ 2 * (ys / 4) = ys + m by omega]

/-- `B` at the rows' point: the `Y` slices weighted by `W`. -/
theorem linkB_mle (pt : List E) :
    ∑ k ∈ range (2 ^ h), eqAt pt k * linkB h ys col lam zeta k =
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  simp only [linkB, ysl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  · have := Finset.mem_range.1 hq
    simp only [yBits, show (64 * m + q) / 64 = m by omega, show (64 * m + q) % 64 = q by omega]
    ring

/-- `A` at the rows' point: the `in` slices weighted by `eq(ζ, ·)`. -/
theorem linkA_mle {pt : List E} (hpt : pt.length = h) (hl : lam.length = 3) :
    ∑ k ∈ range (2 ^ h), eqAt pt k * linkA h col lam zeta k =
      ∑ p ∈ range 64, eqAt zeta p * sliceExt h col (pt ++ lam ++ [0, 0, 0]) p := by
  simp only [sliceExt_in h col lam hpt hl, linkA, omegaE, Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun x _ ↦ by ring

/-- **The shift sumcheck's end** at `ρ'`. -/
theorem Fsh_end {rho pt : List E} (hr : rho.length = h) (hpt : pt.length = h)
    (hl : lam.length = 3) :
    Fsh h ys col lam zeta rho pt =
      shiftEvalE rho pt * ∑ p ∈ range 64, eqAt zeta p * sliceExt h col (pt ++ lam ++ [0, 0, 0]) p +
        eqMaskedE rho pt *
          ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  rw [Fsh, cubeSum_full _ hpt, ← hr, sum_shiftK rho pt (by rw [hr, hpt]),
    sum_maskK rho pt (by rw [hr, hpt]), hr, linkA_mle h col lam zeta hpt hl, linkB_mle]

/-- The `Y` lane sumcheck's family (2 rounds over the lane `m` of `Y`). -/
noncomputable def G2 (rho pt : List E) (acc : List E) : E :=
  cubeSum (fun mpt ↦ eqMaskedE rho pt * ∑ q ∈ range 64,
    (∑ m ∈ range 4, eqAt mpt m * padWeightE lam zeta m q) *
      (∑ m ∈ range 4, eqAt mpt m * ysl h ys col pt m q)) 2 acc

theorem G2_plain {β : Type} (cq : β → ℕ → K) (rho pt : List E) :
    PlainFamily (fun q acc ↦ G2 h ys (cq q) lam zeta rho pt acc) 2 2 :=
  cube_plainFamily _ 2 fun _ pre post ↦ PolyLE.const_mul (PolyLE.sum _ fun _ _ ↦
    polyLE_mle_mul _ _ _ _ pre post) _

theorem G2_nil (rho pt : List E) :
    G2 h ys col lam zeta rho pt [] = eqMaskedE rho pt *
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  rw [G2, cubeSum_nil, ← Finset.mul_sum]
  refine congrArg _ ?_
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hm' : m < 2 ^ 2 := Finset.mem_range.1 hm
  have e1 := sum_eqAt_bitsE hm' (fun m' ↦ padWeightE lam zeta m' q)
  have e2 := sum_eqAt_bitsE hm' (fun m' ↦ ysl h ys col pt m' q)
  rw [show (2 : ℕ) ^ 2 = 4 from rfl] at e1 e2
  rw [e1, e2]

theorem G2_end (rho pt : List E) {mu : List E} (hmu : mu.length = 2) :
    G2 h ys col lam zeta rho pt mu = eqMaskedE rho pt * ∑ q ∈ range 64,
      wtE lam zeta mu q * ∑ m ∈ range 4, eqAt mu m * ysl h ys col pt m q := by
  rw [G2, cubeSum_full _ hmu]
  rfl

end Lvm.KG
