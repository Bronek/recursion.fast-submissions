-- WP-13b: the bridge from the machine's coordinates to the pure decoder (new; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXLevel.lean@8bff272b `foldAt_f₀`/`encF_f₀`/`mem_consSet_iff`:
-- the fold and `Enc` over the extension are the base field's on each coordinate).
import LvmXAgree

/-!
# The decoder's `E` objects in `K` coordinates

The machine computes in `K = BF64`; an `E = Ext3` element is three coordinates (`mkE c₀ c₁ c₂`).

* `mkE_sum`, `mkE_mul_ofK`: sums and `E × K` products coordinate by coordinate.
* `foldAt_coords`: the fold's coordinates are `K` dot products of the column with the coordinates
  of the `eq(α, ·)` table.
* `enc0_coords`: `Enc₀(f₁)`'s coordinates are `Enc` over `K` of `f₁`'s coordinates (what the forward
  NTT computes, `Lvm.Nb.fwdRun_enc`).
* **`agreeM_eq_agreeL`**: on a memory holding the word, the `eq` table and `Enc₀(f₁)`'s
  coordinates, the machine's agreement list (`LvmXAgree.agreeM`) is the decoder's `agreeL`.
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64

theorem mkE_sum {ι : Type*} (s : Finset ι) (a b c : ι → BF64) :
    ∑ i ∈ s, mkE (a i) (b i) (c i) = mkE (∑ i ∈ s, a i) (∑ i ∈ s, b i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mkE_zero]
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, sum_insert hx, sum_insert hx, ih, mkE_add]

theorem mkE_mul_ofK (a b c k : BF64) : mkE a b c * ofK k = mkE (a * k) (b * k) (c * k) := by
  rw [ofK, ← mkE_base, mkE_smul]

/-- **The fold in coordinates.** -/
theorem foldAt_coords (α : ℕ → Ext3) (wd : ℕ → ℕ → BF64) (q : ℕ) (e : ℕ → ℕ → BF64)
    (he : ∀ l < 64, eqA α l = mkE (e 0 l) (e 1 l) (e 2 l)) :
    foldAt α wd q = mkE (∑ l ∈ range 64, e 0 l * rowW wd l q) (∑ l ∈ range 64, e 1 l * rowW wd l q)
      (∑ l ∈ range 64, e 2 l * rowW wd l q) := by
  rw [foldAt, ← mkE_sum]
  exact sum_congr rfl fun l hl => by rw [he l (mem_range.1 hl), mkE_mul_ofK]

/-- **`Enc₀` in coordinates.** -/
theorem enc0_coords (f₁ : ℕ → Ext3) (g : ℕ → ℕ → BF64)
    (hg : ∀ v < 2 ^ 13, f₁ v = mkE (g 0 v) (g 1 v) (g 2 v)) (q : ℕ) :
    enc0 f₁ q = mkE (encN ptK (fun x : Fin (2 ^ 13) => g 0 x) q)
      (encN ptK (fun x : Fin (2 ^ 13) => g 1 x) q) (encN ptK (fun x : Fin (2 ^ 13) => g 2 x) q) := by
  have e : ∀ c, encN ptK (fun x : Fin (2 ^ 13) => g c x) q = ∑ v ∈ range (2 ^ 13), g c v * nbAt v q :=
    fun c => by
      rw [encN, ← Fin.sum_univ_eq_sum_range (fun v => g c v * nbAt v q)]; rfl
  rw [e, e, e, ← mkE_sum, enc0]
  exact sum_congr rfl fun v hv => by rw [hg v (mem_range.1 hv), mkE_mul_ofK]

/-- The test at one position is the decoder's. -/
theorem agreeP_iff {M : Mem} {wB qB eB q : ℕ} (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hq : q < 2 ^ 15)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK M (wB + 64 * q + t) = wd q t)
    (hQ : ∀ l < 64, rdE M (qB + 3 * l) = eqA α l)
    (hE : ∀ q < 2 ^ 15, enc0 f₁ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 15 + q)) (rdK M (eB + 2 * 2 ^ 15 + q))) :
    AgreeP M wB qB eB q ↔ foldAt α wd q = enc0 f₁ q := by
  have hF : foldAt α wd q = mkE (foldPM M wB qB q 0 64) (foldPM M wB qB q 1 64)
      (foldPM M wB qB q 2 64) := by
    rw [foldAt_coords α wd q (fun c l => rdK M (qB + 3 * l + c))
      (fun l hl => by rw [← hQ l hl]; rfl)]
    have e : ∀ c, ∑ l ∈ range 64, rdK M (qB + 3 * l + c) * rowW wd l q = foldPM M wB qB q c 64 :=
      fun c => sum_congr rfl fun l hl => by
        rw [rowW, hW q hq (63 - l) (by have := mem_range.1 hl; omega)]
    rw [e 0, e 1, e 2]
  rw [hF, hE q hq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    show mkE _ _ _ = mkE _ _ _
    rw [← h0, ← h1, ← h2]; rfl
  · intro h
    obtain ⟨h0, h1, h2⟩ := mkE_inj h
    exact ⟨h0.symm, h1.symm, h2.symm⟩

/-- The machine's list below `n ≤ 2^15` is the decoder's filter. -/
theorem agreeM_eq_filter {M : Mem} {wB qB eB n : ℕ} (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hn : n ≤ 2 ^ 15)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK M (wB + 64 * q + t) = wd q t)
    (hQ : ∀ l < 64, rdE M (qB + 3 * l) = eqA α l)
    (hE : ∀ q < 2 ^ 15, enc0 f₁ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 15 + q)) (rdK M (eB + 2 * 2 ^ 15 + q))) :
    agreeM M wB qB eB n = (List.range n).filter fun q => decide (foldAt α wd q = enc0 f₁ q) := by
  unfold agreeM
  refine List.filter_congr fun q hq => ?_
  exact decide_eq_decide.2 (agreeP_iff wd α f₁ (by have := List.mem_range.1 hq; omega) hW hQ hE)

/-- **The machine's agreement list is the decoder's**: the word at `wB + 64q + t`, the `eq(α, ·)`
table at `qB + 3l` (`rdE`), and `Enc₀(f₁)[q]`'s coordinates at `eB + c·2^15 + q`. -/
theorem agreeM_eq_agreeL {M : Mem} {wB qB eB : ℕ} (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK M (wB + 64 * q + t) = wd q t)
    (hQ : ∀ l < 64, rdE M (qB + 3 * l) = eqA α l)
    (hE : ∀ q < 2 ^ 15, enc0 f₁ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 15 + q)) (rdK M (eB + 2 * 2 ^ 15 + q))) :
    agreeM M wB qB eB (2 ^ 15) = agreeL wd α f₁ :=
  agreeM_eq_filter wd α f₁ le_rfl hW hQ hE

end Lvm.X
