-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBJetLedger.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBHeight
import LvmJBJetRecursion

/-!
# The ledger: linear size growth along the jet recursion

This file proves the load-bearing estimate of the finite-jet argument: the jet
coefficients, cleared by the denominator `ξ^(2t-1)`, have *sizes growing linearly
in `t`*.  Both relevant sizes — the `Z`-height and the `T`-degree of numerators in
`A = F[Z][T]` — are handled at once through an abstract `SizeSystem`.

## The ledger

For the cleared coefficients

  `c_{r,s}(t) = ξ^(ledger t s) · [Uˢ]((D^r_Y R)(Γ_t))`,

the clearing exponents form the *ledger*

  `ledger t s = 0` (`s = 0`), `2s - 1` (`1 ≤ s ≤ t`), `2s - 2` (`s > t`),

and the whole analysis rests on a single inequality (`ledger_slack`): under the
Hasse–Taylor update `Γ_t = Γ_{t-1} + α_t U^t`, every term has nonnegative ledger slack

  `ledger (t-1) s' + ρ·(2t-1) ≤ ledger t s`,   `s = s' + t·ρ`.

This replaces the multi-index combinatorics of the height calculation (BCIKS
Claim 5.10): the "at least two nonzero parts" phenomenon is absorbed into the ledger
table.

## The collapse

Choosing the size bound *proportional to the ledger*,

  `size(c_{r,s}(t)) ≤ (m₀ + mξ) · (ledger t s + 1)`,

makes the inductive step automatic: a term with ledger slack `σ` picks up size at most
`ρ`-fold the jet coefficient bound plus `σ · mξ`, and the ledger identity converts this
into exactly the target bound.  No further case analysis is needed beyond
`ledger_slack` itself.

## Main results

* `SizeSystem` — the abstract size interface; `heightSizeSystem`, `degreeSizeSystem`.
* `ledger_slack` — the slack inequality.
* `jet_ledger` — the invariant: integrality and linear size of all cleared
  coefficients.
* `jet_coeff_integral` — the corollary used downstream: `ξ^(2t-1) · α_t` is integral
  of size at most `(mR + d·mα + mξ) · (2t - 1)`.  Linear in `t`: this is the estimate
  that puts `2r + 1` for the chosen jet order — not `D_X` — into the §3 branch bound. Weighted factor selection
  then sums exact capacities, improving the final threshold from the original `η⁵`
  and the intermediate uniform-bucket `η⁴` to `η³`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Abstract size systems -/

/-- An abstract *size* on a commutative ring: `P g m` says "`g` has size at most `m`".
Sizes are stable under negation and addition, and add under multiplication.  Both the
`Z`-height (`IsHeightLE`) and the `T`-degree on `F[Z][T]` are instances. -/
structure SizeSystem (A : Type*) [CommRing A] where
  P : A → ℕ → Prop
  mono : ∀ {g m m'}, P g m → m ≤ m' → P g m'
  zero : ∀ m, P 0 m
  one : P 1 0
  neg : ∀ {g m}, P g m → P (-g) m
  add : ∀ {g h m}, P g m → P h m → P (g + h) m
  mul : ∀ {g h m m'}, P g m → P h m' → P (g * h) (m + m')

namespace SizeSystem

variable {A : Type*} [CommRing A] (SS : SizeSystem A)

theorem pow {g : A} {m : ℕ} (h : SS.P g m) (n : ℕ) : SS.P (g ^ n) (n * m) := by
  induction n with
  | zero => simpa using SS.one
  | succ n ih =>
      rw [pow_succ]
      exact SS.mono (SS.mul ih h) (le_of_eq (by ring))

theorem nsmul {g : A} {m : ℕ} (h : SS.P g m) (n : ℕ) : SS.P (n • g) m := by
  induction n with
  | zero => simpa using SS.zero m
  | succ n ih =>
      rw [succ_nsmul]
      exact SS.add ih h

theorem sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) {m : ℕ}
    (hf : ∀ i ∈ s, SS.P (f i) m) : SS.P (∑ i ∈ s, f i) m := by
  induction s using Finset.induction with
  | empty => simpa using SS.zero m
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact SS.add (hf x (Finset.mem_insert_self x s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end SizeSystem

/-- Negation preserves heights. -/
theorem IsHeightLE.neg {F : Type*} [CommRing F] {p : F[X][X]} {a : ℕ}
    (hp : IsHeightLE p a) : IsHeightLE (-p) a := by
  intro i
  rw [coeff_neg, natDegree_neg]
  exact hp i

/-- The `Z`-height as a size system on `F[Z][T]`. -/
def heightSizeSystem (F : Type*) [CommRing F] : SizeSystem (F[X][X]) where
  P := IsHeightLE
  mono := fun h hle => h.mono hle
  zero := fun _ => IsHeightLE.zero
  one := by
    intro i
    rcases eq_or_ne i 0 with rfl | h
    · simp
    · simp [coeff_one, h]
  neg := IsHeightLE.neg
  add := IsHeightLE.add
  mul := IsHeightLE.mul

/-- The degree (in the outer variable) as a size system on `R[X]`. -/
def degreeSizeSystem (R : Type*) [CommRing R] : SizeSystem (R[X]) where
  P := fun p m => p.natDegree ≤ m
  mono := fun h hle => h.trans hle
  zero := fun m => by simp
  one := by simp
  neg := fun h => by rwa [natDegree_neg]
  add := fun h₁ h₂ => le_trans (natDegree_add_le _ _) (max_le h₁ h₂)
  mul := fun h₁ h₂ => natDegree_mul_le_of_le h₁ h₂

/-! ### The ledger and its slack inequality -/

/-- The clearing exponent for the cleared coefficient `c_{r,s}(t)`. -/
def ledger (t s : ℕ) : ℕ :=
  if s = 0 then 0 else if s ≤ t then 2 * s - 1 else 2 * s - 2

@[simp] theorem ledger_zero_right (t : ℕ) : ledger t 0 = 0 := by simp [ledger]

theorem ledger_self_succ (t : ℕ) : ledger t (t + 1) = 2 * t := by
  simp only [ledger, if_neg (Nat.succ_ne_zero t), if_neg (by omega : ¬ t + 1 ≤ t)]
  omega

theorem ledger_succ_self (t : ℕ) : ledger (t + 1) (t + 1) = 2 * t + 1 := by
  simp only [ledger, if_neg (Nat.succ_ne_zero t), if_pos (le_refl (t + 1))]
  omega

/-- **The slack inequality.**  Under the Hasse–Taylor update at order `t + 1`, a term
landing in coefficient `s = s' + (t+1)·ρ` carries the denominator
`ledger t s' + ρ·(2t+1)`, which never exceeds the target `ledger (t+1) s`.

The case `ρ = 0, s' = t + 1` is the crossing where the ledger increments; the cases
`ρ ≥ 1` encode "only previously computed coefficients are available", which in the
multi-index formulation is the *two nonzero parts* argument. -/
theorem ledger_slack (t s' ρ : ℕ) :
    ledger t s' + ρ * (2 * t + 1) ≤ ledger (t + 1) (s' + (t + 1) * ρ) := by
  rcases ρ with _ | ρ'
  · -- ρ = 0 : monotonicity of the ledger in `t`.
    simp only [mul_zero, zero_mul, add_zero]
    unfold ledger
    split_ifs <;> first | contradiction | omega
  rcases ρ' with _ | ρ''
  · -- ρ = 1 : everything is linear.
    simp only [zero_add, mul_one, one_mul]
    unfold ledger
    split_ifs <;> first | contradiction | omega
  · -- ρ ≥ 2 : the landing coefficient is beyond `t + 1`; linearize the products.
    have hnorm : ρ'' + 1 + 1 = ρ'' + 2 := by omega
    rw [hnorm]
    have hkey : ledger t s' + 2 ≤ 2 * s' + (ρ'' + 2) := by
      unfold ledger
      split_ifs <;> omega
    have hs : t + 1 < s' + (t + 1) * (ρ'' + 2) := by
      have hexp : (t + 1) * (ρ'' + 2) = t * ρ'' + ρ'' + 2 * t + 2 := by ring
      rw [hexp]
      generalize t * ρ'' = q
      omega
    have hs0 : ¬ (s' + (t + 1) * (ρ'' + 2) = 0) := fun h => Nat.not_lt_zero _ (h ▸ hs)
    have hsgt : ¬ (s' + (t + 1) * (ρ'' + 2) ≤ t + 1) := not_le.mpr hs
    conv_rhs => rw [ledger]
    rw [if_neg hs0, if_neg hsgt]
    have hexp2 : 2 * (s' + (t + 1) * (ρ'' + 2)) =
        2 * s' + (ρ'' + 2) * (2 * t + 1) + (ρ'' + 2) := by ring
    rw [hexp2]
    generalize (ρ'' + 2) * (2 * t + 1) = w at *
    omega

/-! ### Setup: integral models -/

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)

/-- The uniform size bound for the `U = 0` slices `c_{r,0}`. -/
def sliceBound (mR d mα : ℕ) : ℕ := mR + d * mα

/-- The ledger size constant: `b = m₀ + mξ`. -/
def ledgerConst (mR d mα mξ : ℕ) : ℕ := sliceBound mR d mα + mξ

section Ledger

variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hd in
/-- The `Y`-degree of `R` is bounded by `d`. -/
theorem natDegree_R_le : R.natDegree ≤ d := by
  rw [hR]
  exact le_trans (natDegree_map_le) hd

include hR hα hd hmR hmα in
/-- **The base computation.**  Every coefficient of `(D^r R)(C α₀)` is integral of size
at most `m₀ = mR + d·mα`: substituting the constant `α₀` costs `mα` per `Y`-power.
This covers both the `t = 0` base of the induction and, via `coeff_zero_eval`, the
`s = 0` column for every `t`. -/
theorem base_integral (r s : ℕ) :
    ∃ g : A, algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧
      SS.P g (sliceBound mR d mα) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  -- Expand the evaluation over `range (d + 1)`.
  have hdeg : (hasseDeriv r R).natDegree < d + 1 := by
    have h1 := natDegree_hasseDeriv_le R r
    omega
  have hexp : (hasseDeriv r R).eval (C α₀) =
      ∑ j ∈ range (d + 1), (hasseDeriv r R).coeff j * (C α₀) ^ j :=
    eval_eq_sum_range' hdeg _
  refine ⟨∑ j ∈ range (d + 1),
      (j + r).choose r • ((R₀.coeff (j + r)).coeff s) * a₀ ^ j, ?_, ?_⟩
  · -- The map identity.
    rw [hexp, finsetSum_coeff, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : ((C α₀ : K[X]) ^ j) = C (α₀ ^ j) := by rw [← C_pow]
    rw [hC, coeff_mul_C, hasseDeriv_coeff]
    rw [← nsmul_eq_mul, coeff_smul]
    rw [map_mul, map_nsmul, map_pow, ← hα]
    have hcoeff : algebraMap A K ((R₀.coeff (j + r)).coeff s) =
        (R.coeff (j + r)).coeff s := by
      simp [hR, coeff_map]
    rw [hcoeff]
  · -- The size bound.
    refine SS.sum _ _ fun j hj => ?_
    have hj' : j ≤ d := by
      have := Finset.mem_range.mp hj
      omega
    refine SS.mono (SS.mul (SS.nsmul (hmR (j + r) s) _) (SS.pow hmα j)) ?_
    have : j * mα ≤ d * mα := Nat.mul_le_mul_right _ hj'
    simp only [sliceBound]
    omega

include hR hα hd hmR hmα in
/-- Derivative-sensitive version of `base_integral`.  Evaluating `D^r R` at the
constant `a₀` costs only `d-r` powers of `a₀`; coefficients beyond that range
vanish by the `Y`-degree bound. -/
theorem base_integral_refined (r s : ℕ) :
    ∃ g : A, algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧
      SS.P g (mR + (d - r) * mα) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  have hdeg : (hasseDeriv r R).natDegree < d + 1 := by
    have h₁ := natDegree_hasseDeriv_le R r
    omega
  have hexp : (hasseDeriv r R).eval (C α₀) =
      ∑ j ∈ range (d + 1), (hasseDeriv r R).coeff j * (C α₀) ^ j :=
    eval_eq_sum_range' hdeg _
  refine ⟨∑ j ∈ range (d + 1),
      (j + r).choose r • ((R₀.coeff (j + r)).coeff s) * a₀ ^ j, ?_, ?_⟩
  · rw [hexp, finsetSum_coeff, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : ((C α₀ : K[X]) ^ j) = C (α₀ ^ j) := by rw [← C_pow]
    rw [hC, coeff_mul_C, hasseDeriv_coeff]
    rw [← nsmul_eq_mul, coeff_smul]
    rw [map_mul, map_nsmul, map_pow, ← hα]
    have hcoeff : algebraMap A K ((R₀.coeff (j + r)).coeff s) =
        (R.coeff (j + r)).coeff s := by
      simp [hR, coeff_map]
    rw [hcoeff]
  · refine SS.sum _ _ fun j hj => ?_
    by_cases hjr : j + r ≤ d
    · refine SS.mono (SS.mul (SS.nsmul (hmR (j + r) s) _) (SS.pow hmα j)) ?_
      have hjsub : j ≤ d - r := by omega
      have hjmul : j * mα ≤ (d - r) * mα := Nat.mul_le_mul_right _ hjsub
      omega
    · have hcoeff0 : R₀.coeff (j + r) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (lt_of_not_ge hjr))
      rw [hcoeff0, coeff_zero, nsmul_zero, zero_mul]
      exact SS.zero _


include hR hd in
/-- Hasse derivatives beyond the degree vanish. -/
theorem hasseDeriv_hasseDeriv_eq_zero {ρ r : ℕ} (h : d < ρ) :
    hasseDeriv ρ (hasseDeriv r R) = 0 := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  have h2 := natDegree_hasseDeriv_le R r
  apply Polynomial.ext
  intro n
  rw [hasseDeriv_coeff, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

/-- Pulling a natural scalar out of an evaluation. -/
theorem eval_nsmul' (S : K[X][X]) (γ : K[X]) (n : ℕ) :
    (n • S).eval γ = n • (S.eval γ) := by
  rw [nsmul_eq_mul, eval_mul, eval_natCast, nsmul_eq_mul]

/-- The `(t+1)`-st jet coefficient in closed form. -/
theorem jet_coeff_succ_self (t : ℕ) :
    (jet R α₀ (t + 1)).coeff (t + 1) =
      -((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) := by
  rw [jet_succ, coeff_sub, coeff_mul_X_pow']
  have h0 : (jet R α₀ t).coeff (t + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_jet_le R α₀ t) (by omega))
  simp [h0]

/-- The Taylor form of one recursion step, for an arbitrary polynomial `S`. -/
theorem eval_jet_succ_general (S : K[X][X]) (t : ℕ) :
    S.eval (jet R α₀ (t + 1)) =
      ∑ ρ ∈ range (S.natDegree + 1),
        (hasseDeriv ρ S).eval (jet R α₀ t) *
          (C ((jet R α₀ (t + 1)).coeff (t + 1)) * X ^ (t + 1)) ^ ρ := by
  have hj : jet R α₀ (t + 1) =
      jet R α₀ t + C ((jet R α₀ (t + 1)).coeff (t + 1)) * X ^ (t + 1) := by
    conv_lhs => rw [jet_succ]
    rw [jet_coeff_succ_self, map_neg]
    ring
  conv_lhs => rw [hj]
  exact eval_add_eq_sum_hasseDeriv S _ _

include hR hd in
/-- **The update coefficient formula.**  One recursion step, at the level of a single
`U`-coefficient of a single Hasse derivative. -/
theorem coeff_eval_hasseDeriv_jet_succ (r s t : ℕ) :
    ((hasseDeriv r R).eval (jet R α₀ (t + 1))).coeff s =
      ∑ ρ ∈ range (d + 1),
        (ρ + r).choose ρ •
          (if (t + 1) * ρ ≤ s
           then ((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff (s - (t + 1) * ρ) *
                  ((jet R α₀ (t + 1)).coeff (t + 1)) ^ ρ
           else 0) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
  rw [eval_jet_succ_general R α₀ (hasseDeriv r R) t]
  -- Extend the summation range to `d + 1`.
  have hsub : range ((hasseDeriv r R).natDegree + 1) ⊆ range (d + 1) := by
    intro ρ hρ
    have h1 := natDegree_hasseDeriv_le R r
    have h2 := Finset.mem_range.mp hρ
    exact Finset.mem_range.mpr (by omega)
  have hzero : ∀ ρ ∈ range (d + 1), ρ ∉ range ((hasseDeriv r R).natDegree + 1) →
      (hasseDeriv ρ (hasseDeriv r R)).eval (jet R α₀ t) *
        (C cJ * X ^ (t + 1)) ^ ρ = 0 := by
    intro ρ _ hρnot
    have hgt : (hasseDeriv r R).natDegree < ρ := by
      apply Nat.lt_of_not_ge
      intro h
      exact hρnot (Finset.mem_range.mpr (by omega))
    have hz : hasseDeriv ρ (hasseDeriv r R) = 0 := by
      apply Polynomial.ext
      intro n
      rw [hasseDeriv_coeff, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
    rw [hz, eval_zero, zero_mul]
  rw [Finset.sum_subset hsub hzero, finsetSum_coeff]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  -- Rewrite the iterated Hasse derivative.
  have hcomp : hasseDeriv ρ (hasseDeriv r R) =
      (ρ + r).choose ρ • hasseDeriv (ρ + r) R := by
    have := LinearMap.congr_fun (hasseDeriv_comp (R := K[X]) ρ r) R
    simpa using this
  rw [hcomp, eval_nsmul', smul_mul_assoc, coeff_smul]
  congr 1
  -- Extract the coefficient of the product with the explicit `X`-power.
  have hpow : (C cJ * X ^ (t + 1)) ^ ρ = C (cJ ^ ρ) * X ^ ((t + 1) * ρ) := by
    rw [mul_pow, ← C_pow, ← pow_mul]
  rw [hpow, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

/-- The `s = 0` column is `t`-independent: it always equals the base value. -/
theorem coeff_zero_column (r t : ℕ) :
    ((hasseDeriv r R).eval (jet R α₀ t)).coeff 0 =
      ((hasseDeriv r R).eval (C α₀)).coeff 0 := by
  rw [coeff_zero_eval, coeff_zero_eval, jet_coeff_zero, coeff_C_zero]

include hR hα hd hmR hmα hmξ hξint hξ0 in
/-- **The ledger invariant.**

Every cleared coefficient `ξ^(ledger t s) · [Uˢ]((D^r R)(Γ_t))` is integral, with size at
most `(m₀ + mξ) · (ledger t s + 1)` — linear in the ledger, hence linear in `s`, and
in particular linear in `t` for the jet coefficients themselves. -/
theorem jet_ledger :
    ∀ t r s, ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ ledger t s * (((hasseDeriv r R).eval (jet R α₀ t)).coeff s) ∧
      SS.P g (ledgerConst mR d mα mξ * (ledger t s + 1)) := by
  set b := ledgerConst mR d mα mξ with hbdef
  have hm₀b : sliceBound mR d mα ≤ b := by
    rw [hbdef]; unfold ledgerConst; omega
  have hmξb : mξ ≤ b := by
    rw [hbdef]; unfold ledgerConst; omega
  intro t
  induction t with
  | zero =>
      intro r s
      obtain ⟨g, hg, hgs⟩ := base_integral SS R R₀ α₀ a₀ d mR mα hR hα hd hmR hmα r s
      refine ⟨ξ₀ ^ ledger 0 s * g, ?_, ?_⟩
      · rw [map_mul, map_pow, hξint, hg, jet_zero]
      · refine SS.mono (SS.mul (SS.pow hmξ _) hgs) ?_
        have h1 : ledger 0 s * mξ ≤ ledger 0 s * b := Nat.mul_le_mul_left _ hmξb
        have h2 : ledger 0 s * b + b = b * (ledger 0 s + 1) := by ring
        exact le_trans (add_le_add h1 hm₀b) (le_of_eq h2)
  | succ t ih =>
      intro r s
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · -- The `s = 0` column.
        obtain ⟨g, hg, hgs⟩ := base_integral SS R R₀ α₀ a₀ d mR mα hR hα hd hmR hmα r 0
        refine ⟨g, ?_, ?_⟩
        · rw [ledger_zero_right, pow_zero, one_mul,
            coeff_zero_column R α₀ r (t + 1), hg]
        · exact SS.mono hgs (by simp only [ledger_zero_right]; omega)
      · -- The update, `s ≥ 1`.
        choose G hGmap hGsize using ih
        set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
        -- The integral model of the new jet coefficient.
        have hG0 := hGmap 0 (t + 1)
        rw [ledger_self_succ, hasseDeriv_zero'] at hG0
        have hGhat : algebraMap A K (-(G 0 (t + 1))) = xi R α₀ ^ (2 * t + 1) * cJ := by
          rw [map_neg, hG0, hcJdef, jet_coeff_succ_self, pow_succ]
          field_simp
        have hGhatSize : SS.P (-(G 0 (t + 1))) (b * (2 * t + 1)) := by
          have := hGsize 0 (t + 1)
          rw [ledger_self_succ] at this
          exact SS.neg (SS.mono this (by omega))
        -- Assemble the integral sum.
        refine ⟨∑ ρ ∈ range (d + 1),
            if (t + 1) * ρ ≤ s
            then (ρ + r).choose ρ •
              (G (ρ + r) (s - (t + 1) * ρ) * (-(G 0 (t + 1))) ^ ρ *
                ξ₀ ^ (ledger (t + 1) s - ledger t (s - (t + 1) * ρ) - ρ * (2 * t + 1)))
            else 0, ?_, ?_⟩
        · -- The map identity.
          rw [coeff_eval_hasseDeriv_jet_succ R R₀ α₀ d hR hd r s t, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond, if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            -- Exactness of the ledger split.
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            have hexact : ledger t s' + ρ * (2 * t + 1) +
                (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1)) =
                ledger (t + 1) s := by
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            rw [map_nsmul, map_mul, map_mul, map_pow, map_pow]
            rw [hGmap (ρ + r) s', hGhat, hξint]
            rw [mul_smul_comm]
            congr 1
            rw [mul_pow]
            rw [← pow_mul]
            calc xi R α₀ ^ ledger t s' *
                  (((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') *
                  (xi R α₀ ^ ((2 * t + 1) * ρ) * cJ ^ ρ) *
                  xi R α₀ ^ (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))
                = xi R α₀ ^ (ledger t s' + ρ * (2 * t + 1) +
                    (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))) *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                  rw [pow_add, pow_add]
                  ring
              _ = xi R α₀ ^ ledger (t + 1) s *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                  rw [hexact]
          · rw [if_neg hcond, if_neg hcond]
            simp
        · -- The size bound.
          refine SS.sum _ _ fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            set σ := ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1) with hσdef
            have hexact : ledger t s' + ρ * (2 * t + 1) + σ = ledger (t + 1) s := by
              rw [hσdef]
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            refine SS.mono (SS.nsmul (SS.mul (SS.mul (hGsize (ρ + r) s')
              (SS.pow hGhatSize ρ)) (SS.pow hmξ σ)) _) ?_
            -- Arithmetic: the sizes recombine into `b * (ledger (t+1) s + 1)`.
            have h1 : σ * mξ ≤ σ * b := Nat.mul_le_mul_left _ hmξb
            have h2 : b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * b =
                b * (ledger t s' + ρ * (2 * t + 1) + σ + 1) := by ring
            have h3 : ledger t s' + ρ * (2 * t + 1) + σ + 1 = ledger (t + 1) s + 1 := by
              rw [hexact]
            calc b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * mξ
                ≤ b * (ledger t s' + 1) + ρ * (b * (2 * t + 1)) + σ * b := by omega
              _ = b * (ledger t s' + ρ * (2 * t + 1) + σ + 1) := h2
              _ = b * (ledger (t + 1) s + 1) := by rw [h3]
          · rw [if_neg hcond]
            exact SS.zero _

include hR hd hmξ hξint hξ0 in
/-- **Refined ledger with derivative-sensitive base sizes.**

If the constant-jet coefficient of `D^r R` has size `base r`, where `base` decreases
under further Hasse differentiation, then the cleared `(r,s)` coefficient has size

`base r + slope * ledger t s`.

This retains the degree drop from differentiating in `Y`.  For `T`-degree one takes
`base r = d - r`, `slope = d`; for `Z`-height one takes the constant function `dZ`.
The ordinary ledger above deliberately forgets this information and is consequently
three times looser in the branch capacity. -/
theorem jet_ledger_refined (base : ℕ → ℕ) (slope : ℕ)
    (hbase : ∀ r s, ∃ g : A,
      algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧ SS.P g (base r))
    (hbase_mono : ∀ r ρ, base (ρ + r) ≤ base r)
    (hbase0 : base 0 ≤ slope) (hmξslope : mξ ≤ slope) :
    ∀ t r s, ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ ledger t s * (((hasseDeriv r R).eval (jet R α₀ t)).coeff s) ∧
      SS.P g (base r + slope * ledger t s) := by
  intro t
  induction t with
  | zero =>
      intro r s
      obtain ⟨g, hg, hgs⟩ := hbase r s
      refine ⟨ξ₀ ^ ledger 0 s * g, ?_, ?_⟩
      · rw [map_mul, map_pow, hξint, hg, jet_zero]
      · refine SS.mono (SS.mul (SS.pow hmξ _) hgs) ?_
        have h₁ : ledger 0 s * mξ ≤ ledger 0 s * slope :=
          Nat.mul_le_mul_left _ hmξslope
        calc
          ledger 0 s * mξ + base r ≤ ledger 0 s * slope + base r :=
            Nat.add_le_add_right h₁ _
          _ = base r + slope * ledger 0 s := by ring
  | succ t ih =>
      intro r s
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · obtain ⟨g, hg, hgs⟩ := hbase r 0
        refine ⟨g, ?_, ?_⟩
        · rw [ledger_zero_right, pow_zero, one_mul,
            coeff_zero_column R α₀ r (t + 1), hg]
        · simpa using hgs
      · choose G hGmap hGsize using ih
        set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
        have hG0 := hGmap 0 (t + 1)
        rw [ledger_self_succ, hasseDeriv_zero'] at hG0
        have hGhat : algebraMap A K (-(G 0 (t + 1))) =
            xi R α₀ ^ (2 * t + 1) * cJ := by
          rw [map_neg, hG0, hcJdef, jet_coeff_succ_self, pow_succ]
          field_simp
        have hGhatSize : SS.P (-(G 0 (t + 1))) (slope * (2 * t + 1)) := by
          have h := hGsize 0 (t + 1)
          rw [ledger_self_succ] at h
          exact SS.neg (SS.mono h (by nlinarith))
        refine ⟨∑ ρ ∈ range (d + 1),
            if (t + 1) * ρ ≤ s
            then (ρ + r).choose ρ •
              (G (ρ + r) (s - (t + 1) * ρ) * (-(G 0 (t + 1))) ^ ρ *
                ξ₀ ^ (ledger (t + 1) s - ledger t (s - (t + 1) * ρ) -
                  ρ * (2 * t + 1)))
            else 0, ?_, ?_⟩
        · rw [coeff_eval_hasseDeriv_jet_succ R R₀ α₀ d hR hd r s t,
            Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond, if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            have hexact : ledger t s' + ρ * (2 * t + 1) +
                (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1)) =
                ledger (t + 1) s := by
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            rw [map_nsmul, map_mul, map_mul, map_pow, map_pow]
            rw [hGmap (ρ + r) s', hGhat, hξint]
            rw [mul_smul_comm]
            congr 1
            rw [mul_pow, ← pow_mul]
            calc xi R α₀ ^ ledger t s' *
                  (((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') *
                  (xi R α₀ ^ ((2 * t + 1) * ρ) * cJ ^ ρ) *
                  xi R α₀ ^ (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))
                = xi R α₀ ^ (ledger t s' + ρ * (2 * t + 1) +
                    (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))) *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                    rw [pow_add, pow_add]
                    ring
              _ = xi R α₀ ^ ledger (t + 1) s *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                    rw [hexact]
          · rw [if_neg hcond, if_neg hcond]
            simp
        · refine SS.sum _ _ fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            set σ := ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1) with hσdef
            have hexact : ledger t s' + ρ * (2 * t + 1) + σ =
                ledger (t + 1) s := by
              rw [hσdef]
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            refine SS.mono (SS.nsmul (SS.mul (SS.mul (hGsize (ρ + r) s')
              (SS.pow hGhatSize ρ)) (SS.pow hmξ σ)) _) ?_
            have hb := hbase_mono r ρ
            have hξ := Nat.mul_le_mul_left σ hmξslope
            calc
              (base (ρ + r) + slope * ledger t s') +
                    ρ * (slope * (2 * t + 1)) + σ * mξ
                  ≤ (base r + slope * ledger t s') +
                    ρ * (slope * (2 * t + 1)) + σ * slope := by omega
              _ = base r + slope *
                    (ledger t s' + ρ * (2 * t + 1) + σ) := by ring
              _ = base r + slope * ledger (t + 1) s := by rw [hexact]
          · rw [if_neg hcond]
            exact SS.zero _

include hR hd hmξ hξint hξ0 in
/-- The refined numerator bound for the `(t+1)`-st Newton coefficient. -/
theorem jet_coeff_integral_refined (base : ℕ → ℕ) (slope : ℕ)
    (hbase : ∀ r s, ∃ g : A,
      algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧ SS.P g (base r))
    (hbase_mono : ∀ r ρ, base (ρ + r) ≤ base r)
    (hbase0 : base 0 ≤ slope) (hmξslope : mξ ≤ slope) (t : ℕ) :
    ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ (2 * t + 1) * ((jet R α₀ (t + 1)).coeff (t + 1)) ∧
      SS.P g (slope * (2 * t + 1)) := by
  obtain ⟨g, hg, hgs⟩ := jet_ledger_refined SS R R₀ α₀ ξ₀ d mξ hR hd hmξ hξint hξ0
    base slope hbase hbase_mono hbase0 hmξslope t 0 (t + 1)
  rw [ledger_self_succ, hasseDeriv_zero'] at hg
  rw [ledger_self_succ] at hgs
  refine ⟨-g, ?_, ?_⟩
  · rw [map_neg, hg, jet_coeff_succ_self, pow_succ]
    field_simp
  · exact SS.neg (SS.mono hgs (by nlinarith [hbase0]))

include hR hα hd hmR hmα hmξ hξint hξ0 in
/-- **The linear size bound for the jet coefficients** — the load-bearing estimate.

The `(t+1)`-st jet coefficient, cleared by `ξ^(2t+1)`, is integral of size at most
`(mR + d·mα + mξ) · (2t + 1)`.  Linear in `t`: with heights this reads
`ht(γ_{t+1}) ≤ (D + mξ) · (2t + 1) = O(D_Z · t)`, which is what puts a term
linear in the chosen jet order — not `D_X` — into the §3 branch bound. -/
theorem jet_coeff_integral (t : ℕ) :
    ∃ g : A,
      algebraMap A K g = xi R α₀ ^ (2 * t + 1) * ((jet R α₀ (t + 1)).coeff (t + 1)) ∧
      SS.P g (ledgerConst mR d mα mξ * (2 * t + 1)) := by
  obtain ⟨g, hg, hgs⟩ :=
    jet_ledger SS R R₀ α₀ a₀ ξ₀ d mR mα mξ hR hα hd hmR hmα hmξ hξint hξ0 t 0 (t + 1)
  rw [ledger_self_succ, hasseDeriv_zero'] at hg
  rw [ledger_self_succ] at hgs
  refine ⟨-g, ?_, ?_⟩
  · rw [map_neg, hg, jet_coeff_succ_self, pow_succ]
    field_simp
  · exact SS.neg (SS.mono hgs (by omega))

/-- Jet coefficients are stable: `(Γ_T).coeff t` does not depend on `T` once `T ≥ t`. -/
theorem jet_coeff_stable (t : ℕ) : ∀ T, t ≤ T → (jet R α₀ T).coeff t = (jet R α₀ t).coeff t := by
  intro T
  induction T with
  | zero =>
      intro h
      have ht0 : t = 0 := by omega
      subst ht0
      rfl
  | succ T ihT =>
      intro h
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · rfl
      · rw [jet_succ, coeff_sub, coeff_mul_X_pow']
        rw [if_neg (by omega)]
        rw [sub_zero]
        exact ihT (by omega)

end Ledger

end JBAgreement
