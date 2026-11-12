-- WP-13b: the decoder's encoder is leanVM's, as WP-7 ports it (`LvmNovelBasis`: `novelAt`, `enc`,
-- `encK`, `bitsToNat`, `bitsEquiv`; `LvmWhirProg`: `encRes`), which are canonical; the equalities are new.
import LvmXDec
import LvmNovelBasis
import LvmWhirProg

/-!
# `Enc₀` and `cwRec` are leanVM's `enc` and `encK` at `κ = 13`, `R = 2`

* `ptK_eq_ofBits`, `ofK_eq`: lvm's `ptK`, `ofK` are leanVM's `K.ofBits`, `ofK`.
* `nbAt_eq_novelAt`: `X_v(x_q)` (FR's `novelX` at `ptK`) is leanVM's `novelAt v (K.ofBits q)`
  (`v < 2^64`): the same product of normalised subspace polynomials.
* **`enc0_eq_enc`**: `enc0 f₁ q = enc 13 2 g q` for `g u = f₁ ⟨u⟩` (`⟨u⟩ = bitsToNat u`, bit 0 first);
  **`enc0_eq_encRes`**: the IOP program's `encRes 13 2 residual q` (WP-7, the direct final check).
* **`cwRec_eq_encK`**: row `l` of `cwRec msg` is `encK 13 2` of the row's message.
-/

namespace Lvm.X

open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

theorem ptK_eq_ofBits (n : ℕ) : ptK n = LeanVM.Parameters.K.ofBits n := rfl

theorem ofK_eq (a : BF64) : ofK a = LeanVM.Parameters.ofK a := by
  rw [ofK, Ext.algebraMap_eq_ofBase]

theorem sub_eq_add_K (a b : BF64) : a - b = a + b := by
  rw [sub_eq_add_neg, CharTwo.neg_eq]

/-- `Ŵ_i(a)` here is leanVM's. -/
theorem normW_eval_eq (i : ℕ) (a : BF64) :
    (normW ptK i).eval a = LeanVM.Protocol.Whir.normVanishingAt i a := by
  rw [normW, eval_mul, eval_C, eval_subW, eval_subW, LeanVM.Protocol.Whir.normVanishingAt,
    LeanVM.Protocol.Whir.vanishingAt, LeanVM.Protocol.Whir.vanishingAt,
    LeanVM.Protocol.Whir.basisVec, mul_comm]
  simp only [sub_eq_add_K]
  rfl

/-- **`X_v(x_q)` is leanVM's `novelAt v (K.ofBits q)`** (`v < 2^64`). -/
theorem nbAt_eq_novelAt {v : ℕ} (hv : v < 2 ^ 64) (q : ℕ) :
    nbAt v q = LeanVM.Protocol.Whir.novelAt v (LeanVM.Parameters.K.ofBits q) := by
  rw [nbAt, novelX_eq_bitProd ptK hv, bitProd, bitSel, eval_prod, LeanVM.Protocol.Whir.novelAt]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact normW_eval_eq i _
  · simp

/-- A sum over cube points is a sum over `range (2^κ)`. -/
theorem sum_cube {M : Type*} [AddCommMonoid M] (κ : ℕ) (F : ℕ → M) :
    ∑ u : Fin κ → Bool, F (LeanVM.Protocol.Whir.bitsToNat u) = ∑ j ∈ range (2 ^ κ), F j := by
  rw [← Fin.sum_univ_eq_sum_range, ← (LeanVM.Protocol.Whir.bitsEquiv κ).sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [LeanVM.Protocol.Whir.bitsEquiv_val]

/-- **`Enc₀` is leanVM's `enc 13 2`** on the message `u ↦ f₁ ⟨u⟩`. -/
theorem enc0_eq_enc (f₁ : ℕ → Ext3) (q : Fin (2 ^ (13 + 2))) :
    enc0 f₁ q = LeanVM.Protocol.Whir.enc 13 2 (fun u => f₁ (LeanVM.Protocol.Whir.bitsToNat u)) q := by
  rw [LeanVM.Protocol.Whir.enc_apply, enc0,
    ← sum_cube 13 (fun v => f₁ v * ofK (nbAt v q))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((LeanVM.Protocol.Whir.bitsToNat_lt u).trans (by norm_num)), ofK_eq]

/-- **`Enc₀` is the IOP program's `encRes`** (WP-7's direct final check) on the residual list. -/
theorem enc0_eq_encRes (residual : List Ext3) {q : ℕ} (hq : q < 2 ^ 15) :
    enc0 (fun v => residual.getD v 0) q =
      LeanVM.Protocol.Verifier.encRes 13 2 residual q := by
  rw [LeanVM.Protocol.Verifier.encRes, dif_pos hq]
  exact enc0_eq_enc (fun v => residual.getD v 0) ⟨q, hq⟩

/-- **Row `l` of `cwRec msg` is leanVM's `encK 13 2`** of the row's message. -/
theorem cwRec_eq_encK (msg : ℕ → BF64) (l : ℕ) (q : Fin (2 ^ (13 + 2))) :
    cwRec msg l q =
      LeanVM.Protocol.Whir.encK 13 2 (fun u => msg (l * 2 ^ 13 + LeanVM.Protocol.Whir.bitsToNat u)) q := by
  rw [LeanVM.Protocol.Whir.encK, cwRec,
    ← sum_cube 13 (fun v => msg (l * 2 ^ 13 + v) * nbAt v q)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((LeanVM.Protocol.Whir.bitsToNat_lt u).trans (by norm_num))]

end Lvm.X
