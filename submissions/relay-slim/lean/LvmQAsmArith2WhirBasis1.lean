-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 2: the ring-switching leaf
-- `ringWeight pt x cs` with the coefficients given as cells (QA2's `ringWeightG` with the 64
-- coefficients copied instead of computed from the challenges; its proof adapted from
-- `LvmQRingWeight.ringWeight_eq`).
import LvmQAsmArith2WhirBasis0

/-!
# Claim batching, part 2: the ring leaf

`ringLeaf vc pt cs xb z`: copies of the point cells `pt` (contiguous), QA2's factor tables
`fChunks` (`66·vc` rows) over the point and the coordinates `x_n` in the `E` cells `xb + n`
(`n < vc`, chunks `binDec 64 vc 0`: the binary digits of `vc`), copies of the 64 coefficient cells,
QA2's products `pChunks` (`64·vc` rows), the sum of the 64 products (65 rows).
`ringLeaf_spec`: the cell is `F`'s `ringWeight (vs M pt) ys (vs M cs)` for `ys = x.take vc`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing

variable {c : Ctx} {M : Mem}

/-- Copies of the cells at consecutive `E` cells from the pointer. -/
def copyN : List Cell → BM Unit
  | [] => pure ()
  | a :: cs => do
    let _ ← lin .E 0 0 a a
    copyN cs

theorem linE_adv (k k' : FK) (a b : Cell) (p : Ptr) : p.adv (lin .E k k' a b p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem copyN_adv : ∀ (cs : List Cell) (p : Ptr), p.adv (copyN cs p).2 = ⟨p.k, p.e + cs.length⟩
  | [], p => by simp [copyN, pure_apply]
  | a :: cs, p => by
    simp only [copyN]
    rw [bind_adv_eq rfl (linE_adv _ _ _ _ _), copyN_adv cs, List.length_cons]
    simp only [Ptr.mk.injEq, true_and]
    omega

theorem copyN_spec : ∀ (cs : List Cell) (p : Ptr), SegsHold c M p (copyN cs p).2 →
    ∀ k < cs.length, M.e (p.e + k) = (cs.getD k default).val M
  | [], _, _, k, hk => by simp at hk
  | a :: cs, p, h, k, hk => by
    simp only [copyN] at h
    rw [hold_bind_eq rfl (linE_adv _ _ _ _ _)] at h
    obtain ⟨h1, h2⟩ := h
    rcases k with _ | k
    · have e := lin_spec h1
      simp only [lin, rowRes, Ptr.at, Cell.val_E, ofK_zero, zero_mul, add_zero] at e
      simpa using e
    · have e := copyN_spec cs ⟨p.k, p.e + 1⟩ h2 k (by simpa using hk)
      simp only at e
      rw [show p.e + (k + 1) = p.e + 1 + k by ring, e]
      simp

/-- The binary digits of `n` from weight `2^k` (at most `fuel` of them), as exponents. -/
def binDec : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, n, k => if n = 0 then [] else (if n % 2 = 1 then [k] else []) ++ binDec f (n / 2) (k + 1)

/-- QA2's `ringWeightG` with the 64 coefficients copied from the cells `cs`. -/
def ringWeightC (bs : List Nat) (cs : List Cell) (r0 rp0 z : Nat) : BM Nat := do
  let Fs ← fChunks r0 rp0 0 bs
  copyN cs
  pChunks z bs Fs
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] 1 0 (eA (p.e - 64) [1]) (eA q.n [1])
  pure (q.n + 64)

/-- **The ring leaf**: `ringWeight pt x cs` over the first `vc` coordinates `x_n = M.e (xb + n)`. -/
def ringLeaf (vc : Nat) (pt cs : List Cell) (xb z : Nat) : BM Cell := do
  let p ← getPtr
  copyN pt
  let w ← ringWeightC (binDec 64 vc 0) cs p.e xb z
  pure (ec w)

theorem getD_map_val (l : List Cell) {n : Nat} (hn : n < l.length) :
    (vs M l).getD n 0 = (l.getD n default).val M := by
  simp [vs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem ringWeightC_spec {bs : List Nat} {cs : List Cell} {r0 rp0 z : Nat} {R R' : Nat → FE}
    (hcs : cs.length = 64) (hz : M.e z = 0)
    (hrv : ∀ n < sz bs, M.e (r0 + n) = R n) (hrpv : ∀ n < sz bs, M.e (rp0 + n) = R' n)
    {p : Ptr} (h : SegsHold c M p (ringWeightC bs cs r0 rp0 z p).2) :
    M.e (ringWeightC bs cs r0 rp0 z p).1 = ∑ i ∈ Finset.range 64,
      (cs.getD i default).val M * ∏ n ∈ Finset.range (sz bs), wf (R n) (R' n) i := by
  have hout : (ringWeightC bs cs r0 rp0 z p).1 = p.e + 130 * sz bs + 128 := by
    simp only [ringWeightC]
    rw [bind_fst_eq rfl (fChunks_adv _ _ _ _ _), bind_fst_eq rfl (copyN_adv _ _),
      bind_fst_eq rfl (pChunks_adv _ _ _ _), bind_fst_eq (getPtr_out _) (getPtr_adv _),
      bind_fst_eq (copy_out _ _) (copyE_adv _ _), bind_fst_eq rfl (linL_adv _ _ _ _ _ _), pure_apply]
    simp only [ec, Ptr.at, hcs]
    ring
  rw [hout]
  simp only [ringWeightC] at h
  rw [hold_bind_eq rfl (fChunks_adv _ _ _ _ _)] at h
  obtain ⟨hf, h⟩ := h
  rw [hold_bind_eq rfl (copyN_adv _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl (pChunks_adv _ _ _ _)] at h
  obtain ⟨hp, h⟩ := h
  rw [hcs] at hp
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq (copy_out _ _) (copyE_adv _ _)] at h
  obtain ⟨hq, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv' [6] 64 rfl _ _ _ _ _)] at h
  obtain ⟨hH, -⟩ := h
  have hF := fChunks_spec (R := R) (R' := R') bs 0 p (by simpa using hrv) (by simpa using hrpv) hf
  have hC := copyN_spec cs _ hc
  simp only [hcs] at hC
  have hP := pChunks_spec hz bs _ 0 ⟨p.k, p.e + 66 * sz bs + 64⟩
    (fun k => (cs.getD k default).val M) (by show 64 ≤ p.e + 66 * sz bs + 64; omega)
    (fun k hk => by
      rw [← hC k hk]
      show M.e (p.e + 66 * sz bs + 64 - 64 + k) = M.e (p.e + 66 * sz bs + k)
      rw [show p.e + 66 * sz bs + 64 - 64 + k = p.e + 66 * sz bs + k by omega]) hF hp
  simp only [Nat.zero_add] at hP
  have h0 := (copyE_spec hq).2
  simp only [ec, Ptr.at, hcs] at h0 hH
  have hacc : ∀ k < 64, M.e (p.e + 66 * sz bs + 64 + 64 * sz bs + 1 + k) =
      ∑ j ∈ Finset.range (k + 1), (cs.getD j default).val M * ∏ n ∈ Finset.range (sz bs), wf (R n) (R' n) j := by
    intro k hk
    induction k with
    | zero =>
      have e := linL_spec hH (jf := 0) (by simp)
      simp only [Mem.rd, Addr.at, unflat_one (show 0 < 2 ^ 6 by norm_num), Loop.dot, Nat.add_zero,
        Nat.mul_zero, h0, hz, mul_zero, ofK_zero, ofK_one, one_mul, add_zero] at e
      rw [e, zero_add, Finset.sum_range_one]
      exact hP 0 hk
    | succ k ih =>
      have e := linL_spec hH (jf := k + 1) (by simpa using hk)
      simp only [Mem.rd, Addr.at, unflat_one (show k + 1 < 2 ^ 6 by simpa using hk), Loop.dot,
        Nat.add_zero, ofK_zero, ofK_one, one_mul, Nat.one_mul, add_zero] at e
      rw [e, Finset.sum_range_succ, ← ih (by omega), ← hP (k + 1) hk, add_comm]
      congr 2
      omega
  rw [show p.e + 130 * sz bs + 128 = p.e + 66 * sz bs + 64 + 64 * sz bs + 1 + 63 by ring,
    hacc 63 (by norm_num)]

/-- **The ring leaf**: `F`'s `ringWeight (vs M pt) ys (vs M cs)` for `ys` the first `vc`
coordinates (`ys_n = M.e (xb + n)`). -/
theorem ringLeaf_spec {vc xb z : Nat} {pt cs : List Cell} (hz : M.e z = 0) (hpt : pt.length = vc)
    (hcs : cs.length = 64) (hbs : sz (binDec 64 vc 0) = vc) (ys : List FE) (hys : ys.length = vc)
    (hy : ∀ n < vc, ys.getD n 0 = M.e (xb + n)) :
    Hs c M (ringLeaf vc pt cs xb z) (fun r => r.val M = ringWeight (vs M pt) ys (vs M cs)) := by
  intro p h
  simp only [ringLeaf] at h ⊢
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (copyN_adv _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl rfl] at h
  obtain ⟨hw, -⟩ := h
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _), bind_fst_eq rfl (copyN_adv _ _), bind_apply]
  simp only [pure_apply, Cell.val_E]
  have hC := copyN_spec pt _ hc
  rw [ringWeightC_spec (R := fun n => (vs M pt).getD n 0) (R' := fun n => ys.getD n 0) hcs hz
    (fun n hn => by rw [hC n (by omega), getD_map_val pt (by omega)])
    (fun n hn => (hy n (by omega)).symm) hw]
  have hl : (vs M pt).length = ys.length := by simp [vs, hpt, hys]
  rw [ringWeight_sum _ _ _ hl, hbs]
  have hl2 : (vs M cs).length = 64 := by simp [vs, hcs]
  have hl3 : (vs M pt).length = vc := by simp [vs, hpt]
  rw [hl2, hl3]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [getD_map_val cs (by rw [hcs]; exact Finset.mem_range.mp hi)]

end Lvm.Har
