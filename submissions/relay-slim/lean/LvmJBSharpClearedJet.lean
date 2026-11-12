-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBSharpClearedJet.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBClearedJet

/-!
# Sharp cleared Newton jets

This file instantiates the derivative-sensitive ledger and clears the `r`-jet with
the common exponent `2*r`.  If `slope` bounds both the derivative-sensitive base and
the simple-root coefficient, every coefficient of the cleared jet has size at most
`2*r*slope`.  This is the local estimate behind the sharp `4*r` skeleton capacity.
-/

namespace JBAgreement

open Polynomial Finset

section

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A cleared jet with the sharp derivative-sensitive size bound. -/
theorem exists_sharpClearedJet {Idx : Type*} [Nonempty Idx]
    (SS : Idx → SizeSystem A) (R₀ : A[X][X]) (a₀ : A) (d r : ℕ)
    (mR mα mξ slope : Idx → ℕ)
    (hd : R₀.natDegree ≤ d)
    (hmR : ∀ o j i, (SS o).P ((R₀.coeff j).coeff i) (mR o))
    (hmα : ∀ o, (SS o).P a₀ (mα o))
    (hmξ : ∀ o, (SS o).P (xi R₀ a₀) (mξ o))
    (hbase : ∀ o, mR o + d * mα o ≤ slope o)
    (hξSlope : ∀ o, mξ o ≤ slope o)
    (hconst : ∀ o, 2 * r * mξ o + mα o ≤ 2 * r * slope o)
    (hξ0 : xi R₀ a₀ ≠ 0) :
    ∃ γ : A[X], γ.natDegree ≤ r ∧
      γ.coeff 0 = xi R₀ a₀ ^ (2 * r) * a₀ ∧
      (∀ o i, (SS o).P (γ.coeff i) (2 * r * slope o)) ∧
      (X : A[X]) ^ (r + 1) ∣
        evalH R₀ d (xi R₀ a₀ ^ (2 * r)) γ
          - C (xi R₀ a₀ ^ ((2 * r) * d) * jetConst R₀ a₀) := by
  classical
  set K := FractionRing A
  set ψ : A →+* K := algebraMap A K with hψ
  have hinj : Function.Injective ψ := IsFractionRing.injective A K
  set ξ₀ : A := xi R₀ a₀ with hξ₀
  set R : K[X][X] := R₀.map (mapRingHom ψ) with hRdef
  set α₀ : K := ψ a₀ with hα₀
  have hξint : ψ ξ₀ = xi R α₀ := (xi_map ψ R₀ a₀).symm
  have hHint : ψ (jetConst R₀ a₀) = jetConst R α₀ :=
    (jetConst_map ψ R₀ a₀).symm
  have hξK : xi R α₀ ≠ 0 := by
    rw [← hξint]
    exact fun h => hξ0 (hinj (by simpa using h))
  have hRd : R.natDegree ≤ d := le_trans natDegree_map_le hd
  set c : A := ξ₀ ^ (2 * r) with hc
  have key : ∀ t : ℕ, ∃ g : A, ψ g = ψ c * (jet R α₀ r).coeff t ∧
      ∀ o, (SS o).P g (2 * r * slope o) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨c * a₀, ?_, fun o => ?_⟩
      · rw [map_mul, jet_coeff_zero]
      · refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) (hmα o)) ?_
        simpa [hc] using hconst o
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rcases Nat.lt_or_ge t' r with htk | htk
    · have model : ∀ o, ∃ g : A,
          ψ g = xi R α₀ ^ (2 * t' + 1) *
              ((jet R α₀ (t' + 1)).coeff (t' + 1)) ∧
            (SS o).P g (slope o * (2 * t' + 1)) := by
        intro o
        apply jet_coeff_integral_refined (SS o) R R₀ α₀ ξ₀ d (mξ o)
          hRdef hd (hmξ o) hξint hξK
          (fun r => mR o + (d - r) * mα o) (slope o)
        · intro r s
          exact base_integral_refined (SS o) R R₀ α₀ a₀ d (mR o) (mα o)
            hRdef hα₀ hd (hmR o) (hmα o) r s
        · intro r ρ
          have hsub : d - (ρ + r) ≤ d - r := by omega
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hsub) _
        · simpa using hbase o
        · exact hξSlope o
      obtain ⟨g₀, hg₀, _⟩ := model (Classical.arbitrary Idx)
      refine ⟨ξ₀ ^ (2 * r - (2 * t' + 1)) * g₀, ?_, fun o => ?_⟩
      · rw [map_mul, map_pow, hg₀, hξint,
          jet_coeff_stable R α₀ (t' + 1) r (by omega)]
        rw [hc, map_pow, hξint, ← mul_assoc, ← pow_add]
        congr 2
        omega
      · obtain ⟨g, hg, hgs⟩ := model o
        have hgg : g = g₀ := hinj (by rw [hg, hg₀])
        rw [hgg] at hgs
        refine (SS o).mono ((SS o).mul ((SS o).pow (hmξ o) _) hgs) ?_
        have hmul : (2 * r - (2 * t' + 1)) * mξ o ≤
            (2 * r - (2 * t' + 1)) * slope o :=
          Nat.mul_le_mul_left _ (hξSlope o)
        calc
          (2 * r - (2 * t' + 1)) * mξ o + slope o * (2 * t' + 1)
              ≤ (2 * r - (2 * t' + 1)) * slope o + slope o * (2 * t' + 1) :=
                Nat.add_le_add_right hmul _
          _ = 2 * r * slope o := by
            have hu : 2 * t' + 1 ≤ 2 * r := by omega
            calc
              (2 * r - (2 * t' + 1)) * slope o + slope o * (2 * t' + 1) =
                  ((2 * r - (2 * t' + 1)) + (2 * t' + 1)) * slope o := by ring
              _ = 2 * r * slope o := by rw [Nat.sub_add_cancel hu]
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
    have h := hGmap 0
    rw [jet_coeff_zero, hα₀] at h
    exact hinj (by rw [h, ← map_mul])
  · intro o i
    rw [hcoeff i]
    split_ifs
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
      have h := congrArg (fun p => Polynomial.coeff p 0) hev
      simp only [coeff_map, coeff_C_mul] at h
      rw [h, coeff_zero_eval_jet, ← hHint, ← map_pow, ← map_mul]
    have hcoeffs : ∀ s, 1 ≤ s → s ≤ r → (evalH R₀ d c γ).coeff s = 0 := by
      intro s hs₁ hsk
      refine hinj ?_
      have h := congrArg (fun p => Polynomial.coeff p s) hev
      simp only [coeff_map, coeff_C_mul] at h
      rw [h, coeff_eval_jet_eq_zero R α₀ hξK r s hs₁ hsk, mul_zero, map_zero]
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, coeff_C]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hcoeff0, if_pos rfl, hc, ← pow_mul, sub_self]
    · rw [hcoeffs i hipos (by omega), if_neg (by omega), sub_zero]

end

end JBAgreement
