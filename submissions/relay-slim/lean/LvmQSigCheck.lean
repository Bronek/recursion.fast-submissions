import LvmQSigPre
import LvmWotsSel

/-!
# `Q_sig`: the WOTS checksum, multiplicatively

New for lvm (WP-12; FR `FRNodeRows4Wots`'s `sumRows` idea: the checksum as a product of powers of
a generator, no integer arithmetic). `gCheck_spec`: in every memory where `gCheck`'s rows and its
assertion hold (gate `1`), with Boolean digit bits, `x^{Σ_{i<128} (3 − dᵢ)} = x^{Σ_k 2^k c_k}`.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Wots

/-- A product over a range, pairs folded. -/
theorem prod_pairs (A : Nat → FK) : ∀ n,
    ((List.range (2 * n)).map A).prod = ((List.range n).map fun y => A (2 * y) * A (2 * y + 1)).prod
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.range_succ,
      List.map_append, List.map_append, List.map_append, List.prod_append, List.prod_append,
      List.prod_append, prod_pairs A n]
    simp [mul_assoc]

theorem bnat_le (b : FK) : bnat b ≤ 1 := by unfold bnat; split <;> omega

/-- **The checksum factor**: `(Z + (x+1)·b₀ + x)·(Z + (x²+1)·b₁ + x²) = x^{3 − d}`. -/
theorem factor_eq {b0 b1 : FK} (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) :
    (0 + (FK.x + 1) * b0 + FK.x) * (0 + (FK.x ^ 2 + 1) * b1 + FK.x ^ 2) + 0 =
      FK.x ^ (3 - (bnat b0 + 2 * bnat b1)) := by
  have h01 : ¬ ((0 : FK) = 1) := by decide
  have h2 : (2 : FK) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : FK) = 0 := by rw [show (4 : FK) = 2 * 2 by norm_num, h2, zero_mul]
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;>
    simp [bnat, h01] <;> ring_nf <;> simp [h2, h4]

/-- **A product-tree level**: output `y` is `a[2y]·a[2y+1]`. -/
theorem pt_spec {c : Ctx} {M : Mem} {d src st Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (ptTpl src st Zn) p).2) (hZ : M.k Zn = 0) {y : Nat}
    (hy : y < 2 ^ d) :
    M.k (p.k + y) = M.k (src + 2 * st * y) * M.k (src + st + 2 * st * y) := by
  have r := loopK_mad h (by simpa using hy) (t := 0) (by simp [ptTpl]) rfl rfl rfl rfl
  rw [cell_lin1 _ 0 _ (by simp [loop_apply, ptTpl])
      (fun r hr => by simp [loop_apply, ptTpl] at hr; subst hr; simp),
    ov_oS _ _ rfl hy, ov_oS _ _ rfl hy, ov_oA, hZ, add_zero] at r
  simpa [loop_apply, ptTpl] using r

/-- The ten checksum bits as Booleans. -/
def cbit (M : Mem) (I : SigIn) (k : Nat) : Bool := decide (M.k (I.bc + k) = 1)

/-- `Σ_{j<n} 2^{k+j} c_{k+j}`. -/
def cexp (c : Nat → Bool) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if c k then 2 ^ k else 0) + cexp c (k + 1) n

theorem bitsVal_cexp (c : Nat → Bool) : ∀ n k, bitsVal c (k + n) = bitsVal c k + cexp c k n
  | 0, k => by simp [cexp]
  | n + 1, k => by
    rw [show k + (n + 1) = (k + 1) + n by omega, bitsVal_cexp c n (k + 1), cexp, bitsVal]
    ring

/-- **The bit factors' product.** -/
theorem cbitsGo_spec {c : Ctx} {M : Mem} {I : SigIn} {Z : Cell} (hZt : Z.ty = .K)
    (hZ : M.k Z.n = 0) (hb : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) :
    ∀ n k (acc : Cell) (p : Ptr), acc.ty = .K → k + n ≤ 10 →
      SegsHold c M p (cbitsGo I Z k n acc p).2 →
      (cbitsGo I Z k n acc p).1.ty = .K ∧
        M.k (cbitsGo I Z k n acc p).1.n = M.k acc.n * FK.x ^ cexp (cbit M I) k n
  | 0, k, acc, p, ht, _, _ => by simp [cbitsGo, pure_apply, cexp, ht]
  | n + 1, k, acc, p, ht, hkn, h => by
    unfold cbitsGo at h ⊢
    refine seqH (Q := fun r : Cell => r.ty = .K ∧ M.k r.n = M.k acc.n * FK.x ^ cexp (cbit M I) k (n + 1))
      h fun hg p1 h => ?_
    obtain ⟨Zt, Zn⟩ := Z
    simp only at hZt; subst hZt
    have eg := linK_spec hg
    have tg : (lin .K (FK.x ^ 2 ^ k + 1) 1 ⟨.K, Zn⟩ (kc (I.bc + k)) p).1 = kc p.k := rfl
    rw [tg]
    refine seqH (Q := fun r : Cell => r.ty = .K ∧ M.k r.n = M.k acc.n * FK.x ^ cexp (cbit M I) k (n + 1))
      h fun ha p2 h => ?_
    obtain ⟨At, An⟩ := acc
    simp only at ht; subst ht
    have ea := mulAddK_spec ha
    have ta : (mad ⟨.K, An⟩ (kc p.k) ⟨.K, Zn⟩ p1).1 = kc p1.k := rfl
    rw [ta]
    obtain ⟨t1, e1⟩ := cbitsGo_spec rfl hZ hb n (k + 1) (kc p1.k) p2 rfl (by omega) h
    refine ⟨t1, ?_⟩
    rw [e1, ea, eg, hZ, add_zero]
    simp only [cexp, pow_add, cbit]
    have h2 : (2 : FK) = 0 := CharTwo.two_eq_zero
    rcases hb k (by omega) with e | e <;> simp [e, show ¬ ((0 : FK) = 1) from by decide] <;> ring_nf <;>
      simp [h2]

theorem cell_eta {c : Cell} (h : c.ty = .K) : c = kc c.n := by
  cases c; simp only at h; subst h; rfl

/-- A product-tree level's product. -/
theorem prod_level (A B : Nat → FK) (n : Nat) (h : ∀ y < n, B y = A (2 * y) * A (2 * y + 1)) :
    ((List.range n).map B).prod = ((List.range (2 * n)).map A).prod := by
  rw [prod_pairs]
  congr 1
  exact List.map_congr_left fun y hy => h y (List.mem_range.mp hy)

/-- The digits of the message chains, from the digit bit cells. -/
def mdig (M : Mem) (I : SigIn) (i : Nat) : Nat := bnat (M.k (I.bd + 2 * i)) + 2 * bnat (M.k (I.bd + 2 * i + 1))

/-- A product-tree level at `p` with stride 1 from `src`. -/
theorem pt_level {c : Ctx} {M : Mem} {d src Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (ptTpl src 1 Zn) p).2) (hZ : M.k Zn = 0) {e : Nat} (he : e = d + 1)
    (A : Nat → FK) (hA : ∀ i < 2 ^ e, M.k (src + i) = A i) :
    ((List.range (2 ^ d)).map fun y => M.k (p.k + y)).prod = ((List.range (2 ^ e)).map A).prod := by
  subst he
  rw [pow_succ, mul_comm]
  apply prod_level
  intro y hy
  rw [pt_spec h hZ hy, ← hA _ (by omega), ← hA _ (by omega)]
  congr 2 <;> ring

/-- **The checksum gadget**: `x^{Σ_{i<128} (3 − dᵢ)} = x^{Σ_k 2^k c_k}`. -/
theorem gCheck_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Z O : Cell} (hZt : Z.ty = .K)
    (hOt : O.ty = .K) (h : SegsHold c M p (gCheck I Z O p).2) (hA : SegsAssert M p (gCheck I Z O p).2)
    (hg : M.k I.flag = 1) (hZ : M.k Z.n = 0) (hO : M.k O.n = 1)
    (hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1)
    (hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) :
    FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = FK.x ^ bitsVal (cbit M I) 10 := by
  obtain ⟨Zt, Zn⟩ := Z
  simp only at hZt hZ; subst hZt
  obtain ⟨Ot, On⟩ := O
  simp only at hOt hO; subst hOt
  let T : Prop := FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = FK.x ^ bitsVal (cbit M I) 10
  unfold gCheck at h hA
  refine seqHA (Q := fun _ => T) h hA fun hcs _ p1 h hA => ?_
  -- the factors
  have hP : ∀ i < 128, M.k ((loop [7] (csfTpl I Zn) p).1.p.k + 2 + 3 * i) =
      FK.x ^ (3 - mdig M I i) := by
    intro i hi
    have hi' : i < 2 ^ [7].sum := by simpa using hi
    have r0 := loopK_lin hcs hi' (t := 0) (by simp [csfTpl]) rfl rfl rfl
    have r1 := loopK_lin hcs hi' (t := 1) (by simp [csfTpl]) rfl rfl rfl
    have r2 := loopK_mad hcs hi' (t := 2) (by simp [csfTpl]) rfl rfl rfl rfl
    have hc : ∀ t < 3, ((loop [7] (csfTpl I Zn) p).1.cell t i).n = p.k + t + 3 * i := fun t ht =>
      cell_lin1 _ t i (by simpa [loop_apply, csfTpl] using ht)
        (fun r hr => by simp [loop_apply, csfTpl] at hr; rcases hr with rfl | rfl | rfl <;> simp)
    rw [ov_oA, ov_oS _ _ rfl (by simpa using hi), hZ] at r0 r1
    rw [ov_cur _ _ hi' 0 rfl, ov_cur _ _ hi' 1 rfl, ov_oA, hZ, r0, r1] at r2
    rw [hc 2 (by omega)] at r2
    show M.k (p.k + 2 + 3 * i) = _
    have hb1 : M.k (I.bd + 2 * i + 1) = 0 ∨ M.k (I.bd + 2 * i + 1) = 1 := by
      rw [Nat.add_assoc]; exact hbd _ (by omega)
    rw [r2, show I.bd + 1 + 2 * i = I.bd + 2 * i + 1 by ring,
      factor_eq (hbd _ (by omega)) hb1]
    rfl
  generalize loop [7] (csfTpl I Zn) p = rcs at hP h hA ⊢
  -- the tree
  refine seqHA (Q := fun _ => T) h hA fun h6 _ p2 h hA => ?_
  have q6 : ((List.range (2 ^ 6)).map fun y => M.k ((loop [6] (ptTpl (rcs.1.p.k + 2) 3 Zn) p1).1.p.k + y)).prod
      = ((List.range 128).map fun i => FK.x ^ (3 - mdig M I i)).prod := by
    show ((List.range (2 ^ 6)).map fun y => M.k (p1.k + y)).prod = _
    rw [show (128 : Nat) = 2 * 2 ^ 6 by norm_num]
    apply prod_level
    intro y hy
    rw [pt_spec h6 hZ hy, ← hP _ (by omega), ← hP _ (by omega)]
    congr 2 <;> ring
  generalize loop [6] (ptTpl (rcs.1.p.k + 2) 3 Zn) p1 = r6 at q6 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h5 _ p3 h hA => ?_
  have q5 := pt_level h5 hZ (e := 6) rfl _ fun i _ => rfl
  rw [q6] at q5
  replace q5 : ((List.range (2 ^ 5)).map fun y =>
      M.k ((loop [5] (ptTpl r6.1.p.k 1 Zn) p2).1.p.k + y)).prod = _ := q5
  generalize loop [5] (ptTpl r6.1.p.k 1 Zn) p2 = r5 at q5 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h4 _ p4 h hA => ?_
  have q4 := pt_level h4 hZ (e := 5) rfl _ fun i _ => rfl
  rw [q5] at q4
  replace q4 : ((List.range (2 ^ 4)).map fun y =>
      M.k ((loop [4] (ptTpl r5.1.p.k 1 Zn) p3).1.p.k + y)).prod = _ := q4
  generalize loop [4] (ptTpl r5.1.p.k 1 Zn) p3 = r4 at q4 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h3 _ p5 h hA => ?_
  have q3 := pt_level h3 hZ (e := 4) rfl _ fun i _ => rfl
  rw [q4] at q3
  replace q3 : ((List.range (2 ^ 3)).map fun y =>
      M.k ((loop [3] (ptTpl r4.1.p.k 1 Zn) p4).1.p.k + y)).prod = _ := q3
  generalize loop [3] (ptTpl r4.1.p.k 1 Zn) p4 = r3 at q3 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h2 _ p6 h hA => ?_
  have q2 := pt_level h2 hZ (e := 3) rfl _ fun i _ => rfl
  rw [q3] at q2
  replace q2 : ((List.range (2 ^ 2)).map fun y =>
      M.k ((loop [2] (ptTpl r3.1.p.k 1 Zn) p5).1.p.k + y)).prod = _ := q2
  generalize loop [2] (ptTpl r3.1.p.k 1 Zn) p5 = r2 at q2 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h1 _ p7 h hA => ?_
  have q1 := pt_level h1 hZ (e := 2) rfl _ fun i _ => rfl
  rw [q2] at q1
  replace q1 : ((List.range (2 ^ 1)).map fun y =>
      M.k ((loop [1] (ptTpl r2.1.p.k 1 Zn) p6).1.p.k + y)).prod = _ := q1
  generalize loop [1] (ptTpl r2.1.p.k 1 Zn) p6 = r1 at q1 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h0 _ p8 h hA => ?_
  have q0 := pt_level h0 hZ (e := 1) rfl _ fun i _ => rfl
  rw [q1] at q0
  have c0 : (loop [0] (ptTpl r1.1.p.k 1 Zn) p7).1.cell 0 0 = kc p7.k := by
    simp [loop_apply, LoopOut.cell, ptTpl, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]
  rw [c0] at h hA
  generalize loop [0] (ptTpl r1.1.p.k 1 Zn) p7 = r0 at q0 h hA ⊢
  -- the bit side
  refine seqHA (Q := fun _ => T) h hA fun hq _ p9 h hA => ?_
  obtain ⟨tq, eq⟩ := cbitsGo_spec (Z := ⟨.K, Zn⟩) rfl hZ hbc 10 0 ⟨.K, On⟩ p8 rfl (by omega) hq
  have ecq : (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1 = kc (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1.n :=
    cell_eta tq
  have eq' : M.k (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1.n = FK.x ^ bitsVal (cbit M I) 10 := by
    show M.k (cbitsGo I ⟨.K, Zn⟩ 0 10 ⟨.K, On⟩ p8).1.n = _
    rw [eq, hO, one_mul, show bitsVal (cbit M I) 10 = bitsVal (cbit M I) (0 + 10) from rfl,
      bitsVal_cexp]
    simp [bitsVal]
  beta_reduce at h hA
  rw [ecq] at h hA
  rw [hold_bind] at h
  rw [assert_bind] at hA
  have heq := assertEqKK_spec h.1 hA.1 hg
  rw [eq'] at heq
  simp only [pow_zero, pow_one, List.range_one, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Nat.add_zero] at q0
  show FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = _
  rw [← heq, q0]
  have := prod_pow_sum ((List.range 128).map (mdig M I))
  simp only [List.map_map] at this
  exact this.symm

end Lvm.QSig
