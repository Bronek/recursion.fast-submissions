-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBClearedJet.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBIntegral

/-!
# The cleared jet, and the passage from generic to specialised

The jet `Γ_r` of §1 lives over the fraction field `K = Frac A`; the counting argument of
§3 needs a polynomial over `A` itself.  Multiplying through by `ξ^(2r+1)` — the largest
denominator the ledger ever produces — turns it into one:

  `γ̂ = ξ^(2r+1) · Γ_r ∈ A[U]`,

with coefficients of size `O(r)` by `jet_coeff_integral`.  That is `exists_clearedJet`.

The point of clearing is that `γ̂` and the *homogenised* evaluation `evalH` are algebraic
over `A`, so both survive an arbitrary specialisation `A → F`, whereas `Γ_k` does not.
The generic jet property `U^{r+1} ∣ R(Γ_r) - r₀` therefore becomes an identity in `A[U]`

  `U^{r+1} ∣ evalH R₀ d (ξ^(2r+1)) γ̂ - C (ξ^((2r+1)d) · H₀)`,

which is the last statement of `exists_clearedJet`, and which specialises for free.

`clearedJet_spec` then closes the loop: at a branch point — a pair `(z, t_z)` with
`H₀(z, t_z) = 0` and `ξ(z, t_z) ≠ 0` — the specialised cleared jet, divided by the now
invertible `ξ(z, t_z)^(2r+1)`, *is* the proximate `p_z`.  This is §1's conclusion, and
the proof is `eq_of_dvd_eval`: both are degree-`r` roots of the specialised branch modulo
`U^{r+1}` with the same constant term.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Existence of the cleared jet -/

/-- The size bound for the coefficients of the cleared jet: linear in `r`. -/
def clearedBound (mR d mα mξ r : ℕ) : ℕ :=
  (2 * r + 1) * (ledgerConst mR d mα mξ + mξ) + mα

section Cleared

variable {A : Type*} [CommRing A] [IsDomain A]

/-- **The cleared jet.**

For a branch `R₀` over `A` with simple-root value `ξ = xi R₀ a₀ ≠ 0`, there is a
polynomial `γ̂ ∈ A[U]` of degree at most `r` such that

* `γ̂(0) = ξ^(2r+1) · a₀` — the constant term is the (cleared) initial value;
* every coefficient has size at most `clearedBound …`, *linear in `r`*, and this
  simultaneously for a whole family of size systems (the `T`-degree and the `Z`-height
  are both needed, of the *same* `γ̂`; the integral model is unique because `A → Frac A`
  is injective, so the bounds can be collected);
* `U^{r+1}` divides `evalH R₀ d (ξ^(2r+1)) γ̂ - C (ξ^((2r+1)d) · H₀)`.

The third item is the jet property in cleared, specialisation-stable form.  All three are
read off from the generic jet over `Frac A` and transported back by injectivity of
`A → Frac A`; `K` never appears in the statement. -/
theorem exists_clearedJet {Idx : Type*} [Nonempty Idx]
    (SS : Idx → SizeSystem A) (R₀ : A[X][X]) (a₀ : A) (d r : ℕ) (mR mα mξ : Idx → ℕ)
    (hd : R₀.natDegree ≤ d)
    (hmR : ∀ o j i, (SS o).P ((R₀.coeff j).coeff i) (mR o))
    (hmα : ∀ o, (SS o).P a₀ (mα o)) (hmξ : ∀ o, (SS o).P (xi R₀ a₀) (mξ o))
    (hξ0 : xi R₀ a₀ ≠ 0) :
    ∃ γ : A[X], γ.natDegree ≤ r ∧
      γ.coeff 0 = xi R₀ a₀ ^ (2 * r + 1) * a₀ ∧
      (∀ o i, (SS o).P (γ.coeff i) (clearedBound (mR o) d (mα o) (mξ o) r)) ∧
      (X : A[X]) ^ (r + 1) ∣
        evalH R₀ d (xi R₀ a₀ ^ (2 * r + 1)) γ
          - C (xi R₀ a₀ ^ ((2 * r + 1) * d) * jetConst R₀ a₀) := by
  classical
  set K := FractionRing A
  set ψ : A →+* K := algebraMap A K with hψ
  have hinj : Function.Injective ψ := IsFractionRing.injective A K
  set ξ₀ : A := xi R₀ a₀ with hξ₀
  set R : K[X][X] := R₀.map (mapRingHom ψ) with hRdef
  set α₀ : K := ψ a₀ with hα₀
  have hξint : ψ ξ₀ = xi R α₀ := (xi_map ψ R₀ a₀).symm
  have hHint : ψ (jetConst R₀ a₀) = jetConst R α₀ := (jetConst_map ψ R₀ a₀).symm
  have hξK : xi R α₀ ≠ 0 := by
    rw [← hξint]
    exact fun h => hξ0 (hinj (by simpa using h))
  have hRd : R.natDegree ≤ d := le_trans natDegree_map_le hd
  set c : A := ξ₀ ^ (2 * r + 1) with hc
  -- Integral models for every coefficient of the cleared jet, with *all* the size
  -- bounds at once: the model is unique, since `ψ` is injective.
  have key : ∀ t : ℕ, ∃ g : A, ψ g = ψ c * (jet R α₀ r).coeff t ∧
      ∀ o, (SS o).P g (clearedBound (mR o) d (mα o) (mξ o) r) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨c * a₀, ?_, fun o => ?_⟩
      · rw [map_mul, jet_coeff_zero]
      · refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) (hmα o)) ?_
        rw [clearedBound]
        have : (2 * r + 1) * mξ o
            ≤ (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rcases Nat.lt_or_ge t' r with htk | htk
    · -- The model supplied by the ledger, cleared up to the uniform exponent `2r+1`.
      have base : ∀ o, ∃ g : A,
          ψ g = xi R α₀ ^ (2 * t' + 1) * ((jet R α₀ (t' + 1)).coeff (t' + 1)) ∧
            (SS o).P g (ledgerConst (mR o) d (mα o) (mξ o) * (2 * t' + 1)) := fun o =>
        jet_coeff_integral (SS o) R R₀ α₀ a₀ ξ₀ d (mR o) (mα o) (mξ o)
          hRdef hα₀ hd (hmR o) (hmα o) (hmξ o) hξint hξK t'
      obtain ⟨g₀, hg₀, _⟩ := base (Classical.arbitrary Idx)
      refine ⟨ξ₀ ^ (2 * r + 1 - (2 * t' + 1)) * g₀, ?_, fun o => ?_⟩
      · rw [map_mul, map_pow, hg₀, hξint, jet_coeff_stable R α₀ (t' + 1) r (by omega)]
        rw [hc, map_pow, hξint, ← mul_assoc, ← pow_add]
        congr 2
        omega
      · obtain ⟨g, hg, hgs⟩ := base o
        have hgg : g = g₀ := hinj (by rw [hg, hg₀])
        rw [hgg] at hgs
        refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) hgs) ?_
        rw [clearedBound]
        calc (2 * r + 1 - (2 * t' + 1)) * mξ o
              + ledgerConst (mR o) d (mα o) (mξ o) * (2 * t' + 1)
            ≤ (2 * r + 1) * mξ o + ledgerConst (mR o) d (mα o) (mξ o) * (2 * r + 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
                (Nat.mul_le_mul_left _ (by omega))
          _ = (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) := by ring
          _ ≤ (2 * r + 1) * (ledgerConst (mR o) d (mα o) (mξ o) + mξ o) + mα o :=
              Nat.le_add_right _ _
    · refine ⟨0, ?_, fun o => (SS o).zero _⟩
      rw [map_zero, coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_jet_le R α₀ r) (by omega)), mul_zero]
  choose G hGmap hGsize using key
  refine ⟨∑ t ∈ range (r + 1), monomial t (G t), ?_, ?_, ?_, ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun t ht =>
      le_trans (natDegree_monomial_le _) (by simpa using Nat.lt_succ_iff.mp (mem_range.mp ht))
  all_goals
    have hcoeff : ∀ i, (∑ t ∈ range (r + 1), monomial t (G t)).coeff i =
        if i < r + 1 then G i else 0 := by
      intro i
      rw [finsetSum_coeff]
      simp [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  · rw [hcoeff 0, if_pos (by omega)]
    have := hGmap 0
    rw [jet_coeff_zero] at this
    rw [hα₀] at this
    exact hinj (by rw [this, ← map_mul])
  · intro o i
    rw [hcoeff i]
    split_ifs with h
    · exact hGsize i o
    · exact (SS o).zero _
  · set γ : A[X] := ∑ t ∈ range (r + 1), monomial t (G t) with hγ
    have hmapγ : γ.map ψ = C (ψ c) * jet R α₀ r := by
      apply Polynomial.ext
      intro i
      rw [coeff_map, hcoeff i, coeff_C_mul]
      split_ifs with h
      · exact hGmap i
      · rw [map_zero, coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_jet_le R α₀ r) (by omega)), mul_zero]
    have hev : (evalH R₀ d c γ).map ψ = C (ψ c ^ d) * R.eval (jet R α₀ r) := by
      rw [← evalH_map ψ R₀ d c γ, hmapγ, ← hRdef, evalH_C_mul R hRd]
    have hcoeff0 : (evalH R₀ d c γ).coeff 0 = c ^ d * jetConst R₀ a₀ := by
      refine hinj ?_
      have := congrArg (fun p => Polynomial.coeff p 0) hev
      simp only [coeff_map, coeff_C_mul] at this
      rw [this, coeff_zero_eval_jet, ← hHint, ← map_pow, ← map_mul]
    have hcoeffs : ∀ s, 1 ≤ s → s ≤ r → (evalH R₀ d c γ).coeff s = 0 := by
      intro s hs1 hsk
      refine hinj ?_
      have := congrArg (fun p => Polynomial.coeff p s) hev
      simp only [coeff_map, coeff_C_mul] at this
      rw [this, coeff_eval_jet_eq_zero R α₀ hξK r s hs1 hsk, mul_zero, map_zero]
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, coeff_C]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hcoeff0, if_pos rfl, hc, ← pow_mul, sub_self]
    · rw [hcoeffs i hipos (by omega), if_neg (by omega), sub_zero]

end Cleared

/-! ### Specialisation: the cleared jet at a branch point is the proximate -/

section Spec

variable {A : Type*} [CommRing A] {F : Type*} [Field F]

/-- **The specialised jet is the proximate (§1, conclusion).**

Let `φ : A → F` be a specialisation, `γ` the cleared jet, and suppose

* `φ` kills the obstruction: `φ (jetConst R₀ a₀) = 0` — i.e. `(z, t_z)` is a branch point;
* `φ ξ ≠ 0` — the branch is unramified there (the good slice `x₀`);
* `π` is a polynomial of degree at most `r` lying on the specialised branch,
  `R₀^φ (π) = 0`, with `π(0) = φ a₀`.

Then `π` is determined: `C (φ ξ ^ (2r+1)) * π = γ^φ`.

This is what makes the counting of §3 about the *proximates*: a coefficient identity for
`γ` over `A` is, at every branch point, a statement about `p_z`. -/
theorem clearedJet_spec_exp (R₀ : A[X][X]) (a₀ : A) (d r E : ℕ) (hd : R₀.natDegree ≤ d)
    (γ : A[X]) (hγdeg : γ.natDegree ≤ r)
    (hγ0 : γ.coeff 0 = xi R₀ a₀ ^ E * a₀)
    (hγjet : (X : A[X]) ^ (r + 1) ∣
      evalH R₀ d (xi R₀ a₀ ^ E) γ
        - C (xi R₀ a₀ ^ (E * d) * jetConst R₀ a₀))
    (φ : A →+* F) (hφH : φ (jetConst R₀ a₀) = 0) (hφξ : φ (xi R₀ a₀) ≠ 0)
    (π : F[X]) (hπdeg : π.natDegree ≤ r) (hπ0 : π.coeff 0 = φ a₀)
    (hπroot : (R₀.map (mapRingHom φ)).eval π = 0) :
    C (φ (xi R₀ a₀) ^ E) * π = γ.map φ := by
  set Rf : F[X][X] := R₀.map (mapRingHom φ) with hRf
  set c : F := φ (xi R₀ a₀) ^ E with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hφξ
  set γ' : F[X] := γ.map φ with hγ'
  -- The specialised cleared jet, with the denominator divided out.
  set δ : F[X] := C c⁻¹ * γ' with hδ
  have hγ'δ : γ' = C c * δ := by
    rw [hδ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  -- The jet property specialises.
  have hspec : (X : F[X]) ^ (r + 1) ∣ evalH Rf d c γ' := by
    have hmap := Polynomial.map_dvd φ hγjet
    rw [Polynomial.map_sub, ← evalH_map φ R₀ d _ γ, map_C, map_mul, map_pow, hφH,
      mul_zero, map_zero, sub_zero, ← hRf] at hmap
    simpa [hc] using hmap
  -- Divide out `c ^ d`.
  have hRfd : Rf.natDegree ≤ d := le_trans natDegree_map_le hd
  have hδroot : (X : F[X]) ^ (r + 1) ∣ Rf.eval δ := by
    rw [hγ'δ, evalH_C_mul Rf hRfd] at hspec
    have hcop : IsCoprime ((X : F[X]) ^ (r + 1)) (C (c ^ d)) := by
      refine isCoprime_X_pow_of_coeff_zero_ne_zero ?_ _
      rw [coeff_C_zero]
      exact pow_ne_zero d hc0
    exact hcop.dvd_of_dvd_mul_left hspec
  -- `π` and `δ` agree.
  have hδdeg : δ.natDegree ≤ r :=
    le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_map_le hγdeg)
  have hδ0 : δ.coeff 0 = π.coeff 0 := by
    rw [hδ, coeff_C_mul, hγ', coeff_map, hγ0, map_mul, map_pow, ← hc, ← mul_assoc,
      inv_mul_cancel₀ hc0, one_mul, hπ0]
  have hπdvd : (X : F[X]) ^ (r + 1) ∣ Rf.eval π := by rw [hπroot]; exact dvd_zero _
  have hunit : ((hasseDeriv 1 Rf).eval π).coeff 0 ≠ 0 := by
    rw [coeff_zero_eval, hπ0, ← xi, hRf, xi_map φ R₀ a₀]
    exact hφξ
  have := eq_of_dvd_eval Rf hδdeg hπdeg hδ0 hδroot hπdvd hunit
  rw [hγ'δ, ← this, hδ]

/-- Backwards-compatible specialization theorem using the original clearing exponent. -/
theorem clearedJet_spec (R₀ : A[X][X]) (a₀ : A) (d r : ℕ) (hd : R₀.natDegree ≤ d)
    (γ : A[X]) (hγdeg : γ.natDegree ≤ r)
    (hγ0 : γ.coeff 0 = xi R₀ a₀ ^ (2 * r + 1) * a₀)
    (hγjet : (X : A[X]) ^ (r + 1) ∣
      evalH R₀ d (xi R₀ a₀ ^ (2 * r + 1)) γ
        - C (xi R₀ a₀ ^ ((2 * r + 1) * d) * jetConst R₀ a₀))
    (φ : A →+* F) (hφH : φ (jetConst R₀ a₀) = 0) (hφξ : φ (xi R₀ a₀) ≠ 0)
    (π : F[X]) (hπdeg : π.natDegree ≤ r) (hπ0 : π.coeff 0 = φ a₀)
    (hπroot : (R₀.map (mapRingHom φ)).eval π = 0) :
    C (φ (xi R₀ a₀) ^ (2 * r + 1)) * π = γ.map φ :=
  clearedJet_spec_exp R₀ a₀ d r (2 * r + 1) hd γ hγdeg hγ0 hγjet
    φ hφH hφξ π hπdeg hπ0 hπroot

end Spec

end JBAgreement
