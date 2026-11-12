-- New for lvm2 (T-Q): Q_arith_eq of the S2 wiring gadget's blocks (`LvmQWire`), part 1: the
-- closed forms the rows compute. The proofs follow v1's template gadget specs (`LvmQKeccakTB`,
-- `LvmQKeccakParts*`); the `F`-side bridges (T-V's `dWire`, T-K's `msEvalA_bitsE`) are part 2.
import LvmQWire
import LvmQEqKeccakTape

/-!
# The wiring gadget's closed forms (`LvmQEqWire`)

Every gadget of `preW`, `postW`, `slotW` has a spec stating the value its result source takes in any
row assignment that satisfies the template (`THold`), as an `FE` closed form:

* `thrStepC`, `thrTailC`, `ltC`, `thrC`: `gThrStep`, `gThrTail`, `gLtTab`, `gThr` (`thrEvalA`'s rows);
* `msStepC`, `msTailC`, `msC`: `gMsStepA`, `gMsTail`, `gMs` (`msEvalA`'s rows);
* `gOmega_spec`: `ω_j = laneForm B (eq(a, (j mod 64 + ·) mod 64)) (j / 64)`, and `lt_pos`: that is
  entry `j` of `keccakLinearTranspose (prodW (eq a) B)` (the claim's weights, `Rep.weights`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {xv : Src → FE} {V : Nat → FE}

/-! ## Peeling -/

theorem pr_bind {α β : Type} {n : Nat} (m : TB α) (f : α → TB β) (h : THold xv V n ((m >>= f) n).2) :
    THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 :=
  (thold_bind m f).mp h

theorem pr_fst {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) :
    ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 := by rw [tb_bind]

/-! ## `thrEvalA`'s rows -/

/-- One bit of the threshold automaton, as the rows compute it: `(q₁ + (r + b r) d, q₂ + (b + b r) d)`,
`d = q₁ + q₂`. -/
def thrStepC (r b : FE) (q : FE × FE) : FE × FE :=
  ((r + b * r) * (q.1 + q.2) + q.1, (b + b * r) * (q.1 + q.2) + q.2)

/-- `thrTailA` as the rows compute it. -/
def thrTailC : List FE → List FE → FE × FE
  | r :: ρ, b :: tb => thrStepC r b (thrTailC ρ tb)
  | _, _ => (1, 0)

theorem gThrStep_spec {z r b : Src} (hz : z.valF xv V = 0) {q : Src × Src} {n : Nat}
    (h : THold xv V n (gThrStep z r b q n).2) :
    ((gThrStep z r b q n).1.1.valF xv V, (gThrStep z r b q n).1.2.valF xv V) =
      thrStepC (r.valF xv V) (b.valF xv V) (q.1.valF xv V, q.2.valF xv V) := by
  unfold gThrStep at h ⊢
  obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h4, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h5, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h6, -⟩ := pr_bind _ _ h; rw [pr_fst]
  simp only [tb_pure]
  rw [gMul_spec h6, gAdd_spec h5, gMul_spec h4, gAdd_spec h3, gMul_spec h2, gAdd_spec h1, hz, add_zero]
  rfl

theorem gThrTail_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) :
    ∀ (ρ tb : List Src) (n : Nat), THold xv V n (gThrTail z one ρ tb n).2 →
      ((gThrTail z one ρ tb n).1.1.valF xv V, (gThrTail z one ρ tb n).1.2.valF xv V) =
        thrTailC (vals xv V ρ) (vals xv V tb)
  | r :: ρ, b :: tb, n, h => by
    simp only [gThrTail] at h ⊢
    obtain ⟨h1, h2⟩ := pr_bind _ _ h
    rw [pr_fst, gThrStep_spec hz h2, gThrTail_spec hz ho ρ tb n h1]
    rfl
  | [], _, n, _ => by simp only [gThrTail, tb_pure, ho, hz]; rfl
  | _ :: _, [], n, _ => by simp only [gThrTail, tb_pure, ho, hz]; rfl

/-- `Σ_{j<e} eq(tb4, j)` (T-K's `ltE`, over `FE`). -/
def ltC (tb4 : List FE) (e : Nat) : FE := ((List.range e).map (eqAt tb4)).sum

theorem gLtTab_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) (tb4 : List Src)
    (h4 : tb4.length = 4) {n : Nat} (h : THold xv V n (gLtTab z one tb4 n).2) :
    vals xv V (gLtTab z one tb4 n).1 = (List.range 17).map (ltC (vals xv V tb4)) := by
  unfold gLtTab at h ⊢
  obtain ⟨h1, h2⟩ := pr_bind _ _ h
  rw [pr_fst]
  have e1 := gk_eqTab_one hz ho tb4 n h1
  have hl : (gEqTab z [one] tb4 n).1.length = 16 := by
    have := congrArg List.length e1
    rw [List.length_map, eqKernel_length, List.length_map, h4] at this; simpa using this
  refine forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = ltC (vals xv V tb4) k) _ (fun k hk m hm => ?_) _ h2)
  have hk' := List.mem_range.mp hk
  have hE : eqKernel (vals xv V tb4) = (List.range 16).map (eqAt (vals xv V tb4)) := by
    have hl' : (eqKernel (vals xv V tb4)).length = 16 := by
      rw [eqKernel_length, List.length_map, h4]; rfl
    conv_lhs => rw [← gk_range_map_getD (eqKernel (vals xv V tb4)), hl']
    rfl
  rw [gSum_spec _ _ _ hm, hz, zero_add, List.map_take, show List.map (Src.valF xv V) (gEqTab z [one] tb4 n).1 = _ from e1, hE, gk_take_range_map _ (by omega : k ≤ 16)]
  rfl

/-- `thrEvalA ρ μ tb` as the rows compute it. -/
def thrC (ρ μ tb : List FE) : FE :=
  ((thrTailC ρ (tb.drop 4)).1 + (thrTailC ρ (tb.drop 4)).2) *
      ((List.range 16).map fun d => μ.getD d 0 * ltC (tb.take 4) d).sum +
    μ.sum * (thrTailC ρ (tb.drop 4)).1

theorem gThr_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) {ρ μ tb lt : List Src}
    (hμ : μ.length = 16) (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (tb.take 4)))) {n : Nat}
    (h : THold xv V n (gThr z one ρ μ tb lt n).2) :
    (gThr z one ρ μ tb lt n).1.valF xv V = thrC (vals xv V ρ) (vals xv V μ) (vals xv V tb) := by
  unfold gThr at h ⊢
  obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
  have e1 := gThrTail_spec hz ho ρ (tb.drop 4) n h1
  generalize gThrTail z one ρ (tb.drop 4) n = R at h e1 ⊢
  obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h4, h⟩ := pr_bind _ _ h; rw [pr_fst]
  obtain ⟨h5, h⟩ := pr_bind _ _ h; rw [pr_fst]
  rw [gMul_spec h, gMul_spec h5, gAdd_spec h4, gDot_spec _ _ _ h3, gSum_spec _ _ _ h2, hz]
  have eq1 := congrArg Prod.fst e1
  have eq2 := congrArg Prod.snd e1
  simp only at eq1 eq2
  have hl : lt.length = 17 := by
    have := congrArg List.length hlt; simpa using this
  have hL : ((List.range 16).map fun d => (μ.getD d default, lt.getD d default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) =
      (List.range 16).map fun d => (μ.map (Src.valF xv V)).getD d 0 *
        ltC ((tb.map (Src.valF xv V)).take 4) d := by
    rw [List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hd' := List.mem_range.mp hd
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), hlt, ← List.map_take]
    simp [List.getD_eq_getElem?_getD, hd', show d < 17 by omega]
  rw [eq1, eq2, hL]
  simp only [thrC, vals, List.map_drop, zero_add, add_zero]

/-! ## `eq(ρ, 0)` -/

theorem gEq0_spec {z : Src} (hz : z.valF xv V = 0) :
    ∀ (acc : Src) (ρ : List Src) (n : Nat), THold xv V n (gEq0 z acc ρ n).2 →
      (gEq0 z acc ρ n).1.valF xv V = acc.valF xv V * ((vals xv V ρ).map (1 + ·)).prod
  | acc, [], n, _ => by simp [gEq0, tb_pure]
  | acc, r :: rs, n, h => by
    simp only [gEq0] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h3⟩ := pr_bind _ _ h; rw [pr_fst]
    rw [gEq0_spec hz _ rs _ h3, gMul_spec h2, gOne_spec h1, hz]
    simp only [vals, List.map_cons, List.prod_cons, add_zero]
    ring

/-! ## The weights `ω` -/

/-- **Entry `j` of the transposed product weights** is a lane form at slice `j mod 64`. -/
theorem lt_pos (A : ℕ → FE) (B : List FE) {j : ℕ} (hj : j < 1600) :
    (keccakLinearTranspose (prodW A B)).getD j 0 = laneForm B (fun s => A ((j % 64 + s) % 64)) (j / 64) := by
  have h := lane_dot A (fun z => if z = j % 64 then 1 else 0) B (l := j / 64) (by omega)
  rw [sumE_range] at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true] at h
  rw [show 64 * (j / 64) + j % 64 = j by omega] at h
  rw [h]
  congr 1
  funext s
  unfold rotSum
  rw [sumE_range]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    show j % 64 < 64 from Nat.mod_lt _ (by omega), if_true]

theorem gOmega_spec {z : Src} (hz : z.valF xv V = 0) {B eZ : List Src} (hB : 25 ≤ B.length) {j : Nat}
    (hj : j < 1600) {n : Nat} (h : THold xv V n (gOmega z B eZ j n).2) :
    (gOmega z B eZ j n).1.valF xv V =
      laneForm (vals xv V B) (fun s => (eZ.getD ((j % 64 + s) % 64) default).valF xv V) (j / 64) :=
  gLaneForm_spec hz hB _ (by omega) n h

/-! ## `msEvalA`'s rows -/

/-- Four `FE` entries `(c, s) = 00, 01, 10, 11`. -/
abbrev Q4F := FE × FE × FE × FE

/-- `msStep a r t q` as the rows compute it. -/
def msStepTC (al be ga de : FE) (t : Bool) (q : Q4F) : Q4F :=
  if t then (al * q.1 + be * q.1, al * q.1 + be * q.2.1, ga * q.1 + de * q.2.2.1, ga * q.2.1 + de * q.2.2.1)
  else (al * q.1 + be * q.2.1, al * q.2.1 + be * q.2.1, ga * q.2.1 + de * q.2.2.1, ga * q.2.1 + de * q.2.2.2)

/-- `f₀ + b·(f₁ + f₀)` entrywise. -/
def mixC (b : FE) (f1 f0 : Q4F) : Q4F :=
  (b * (f1.1 + f0.1) + f0.1, b * (f1.2.1 + f0.2.1) + f0.2.1, b * (f1.2.2.1 + f0.2.2.1) + f0.2.2.1,
    b * (f1.2.2.2 + f0.2.2.2) + f0.2.2.2)

/-- `msStepA a r b q` as the rows compute it. -/
def msStepC (a r b : FE) (q : Q4F) : Q4F :=
  mixC b (msStepTC (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) true q)
    (msStepTC (1 + (a + r + a * r)) (a * r) (r + a * r) (a + a * r) false q)

/-- `msTailA` as the rows compute it. -/
def msTailC : List FE → List FE → List FE → Q4F
  | a :: σ, r :: ρ, b :: tb => msStepC a r b (msTailC σ ρ tb)
  | _, _, _ => (1, 0, 0, 0)

/-- `msEvalA ρ μ σ tb 1` as the rows compute it. -/
def msC (ρ μ σ tb : List FE) : FE :=
  ((msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).2.1 +
      (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).1) *
    ((List.range 15).map fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * ltC (tb.take 4) (d + 1)).sum +
  (eqAt (σ.take 4) 15 * μ.getD 0 0 * (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).2.2.1 +
    ((List.range 15).map fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0).sum *
      (msTailC (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)).1)

/-- The values of a `Q4` of sources. -/
def q4v (q : Q4) : Q4F := (q.1.valF xv V, q.2.1.valF xv V, q.2.2.1.valF xv V, q.2.2.2.valF xv V)

theorem gDot2_spec {z a b c d : Src} (hz : z.valF xv V = 0) {n : Nat}
    (h : THold xv V n (gDot z [(a, b), (c, d)] n).2) :
    (gDot z [(a, b), (c, d)] n).1.valF xv V = a.valF xv V * b.valF xv V + c.valF xv V * d.valF xv V := by
  rw [gDot_spec _ _ _ h, hz]; simp

theorem gMsStep_spec {z al be ga de : Src} (hz : z.valF xv V = 0) (t : Bool) (q : Q4) {n : Nat}
    (h : THold xv V n (gMsStep z al be ga de t q n).2) :
    q4v (xv := xv) (V := V) (gMsStep z al be ga de t q n).1 =
      msStepTC (al.valF xv V) (be.valF xv V) (ga.valF xv V) (de.valF xv V) t (q4v (xv := xv) (V := V) q) := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  cases t
  · simp only [gMsStep, Bool.false_eq_true, ite_false] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h4, -⟩ := pr_bind _ _ h; rw [pr_fst]
    simp only [tb_pure, q4v, msStepTC, Bool.false_eq_true, ite_false]
    rw [gDot2_spec hz h1, gDot2_spec hz h2, gDot2_spec hz h3, gDot2_spec hz h4]
  · simp only [gMsStep, ite_true] at h ⊢
    obtain ⟨h1, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h2, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h3, h⟩ := pr_bind _ _ h; rw [pr_fst]
    obtain ⟨h4, -⟩ := pr_bind _ _ h; rw [pr_fst]
    simp only [tb_pure, q4v, msStepTC, ite_true]
    rw [gDot2_spec hz h1, gDot2_spec hz h2, gDot2_spec hz h3, gDot2_spec hz h4]

theorem gMix_spec {b f1 f0 : Src} {n : Nat} (h : THold xv V n (gMix b f1 f0 n).2) :
    (gMix b f1 f0 n).1.valF xv V = b.valF xv V * (f1.valF xv V + f0.valF xv V) + f0.valF xv V := by
  unfold gMix at h ⊢
  obtain ⟨h1, h2⟩ := pr_bind _ _ h; rw [pr_fst, gMul_spec h2, gAdd_spec h1]

theorem gMsStepA_spec {z a r b : Src} (hz : z.valF xv V = 0) (q : Q4) {n : Nat}
    (h : THold xv V n (gMsStepA z a r b q n).2) :
    q4v (xv := xv) (V := V) (gMsStepA z a r b q n).1 =
      msStepC (a.valF xv V) (r.valF xv V) (b.valF xv V) (q4v (xv := xv) (V := V) q) := by
  unfold gMsStepA at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e1 := gMul_spec h1; rw [hz, add_zero] at e1
  generalize (gMul a r z n).1 = ar at h e1 ⊢; generalize n + (gMul a r z n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e2 := gAdd_spec h2
  generalize (gAdd a r n1).1 = sr at h e2 ⊢; generalize n1 + (gAdd a r n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e3 := gAdd_spec h3
  generalize (gAdd sr ar n2).1 = al0 at h e3 ⊢; generalize n2 + (gAdd sr ar n2).2.length = n3 at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e4 := gOne_spec h4
  generalize (gOne al0 n3).1 = al at h e4 ⊢; generalize n3 + (gOne al0 n3).2.length = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e5 := gAdd_spec h5
  generalize (gAdd r ar n4).1 = ga at h e5 ⊢; generalize n4 + (gAdd r ar n4).2.length = n5 at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e6 := gAdd_spec h6
  generalize (gAdd a ar n5).1 = de at h e6 ⊢; generalize n5 + (gAdd a ar n5).2.length = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e7 := gMsStep_spec hz true q h7
  generalize (gMsStep z al ar ga de true q n6).1 = f1 at h e7 ⊢
  generalize n6 + (gMsStep z al ar ga de true q n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e8 := gMsStep_spec hz false q h8
  generalize (gMsStep z al ar ga de false q n7).1 = f0 at h e8 ⊢
  generalize n7 + (gMsStep z al ar ga de false q n7).2.length = n8 at h ⊢
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e9 := gMix_spec h9
  generalize (gMix b f1.1 f0.1 n8).1 = m1 at h e9 ⊢; generalize n8 + (gMix b f1.1 f0.1 n8).2.length = n9 at h ⊢
  obtain ⟨h10, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e10 := gMix_spec h10
  generalize (gMix b f1.2.1 f0.2.1 n9).1 = m2 at h e10 ⊢
  generalize n9 + (gMix b f1.2.1 f0.2.1 n9).2.length = n10 at h ⊢
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e11 := gMix_spec h11
  generalize (gMix b f1.2.2.1 f0.2.2.1 n10).1 = m3 at h e11 ⊢
  generalize n10 + (gMix b f1.2.2.1 f0.2.2.1 n10).2.length = n11 at h ⊢
  obtain ⟨h12, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e12 := gMix_spec h12
  generalize (gMix b f1.2.2.2 f0.2.2.2 n11).1 = m4 at e12 ⊢
  have a1 := congrArg Prod.fst e7
  have a2 := congrArg (fun x => x.2.1) e7
  have a3 := congrArg (fun x => x.2.2.1) e7
  have a4 := congrArg (fun x => x.2.2.2) e7
  have b1 := congrArg Prod.fst e8
  have b2 := congrArg (fun x => x.2.1) e8
  have b3 := congrArg (fun x => x.2.2.1) e8
  have b4 := congrArg (fun x => x.2.2.2) e8
  simp only [q4v] at a1 a2 a3 a4 b1 b2 b3 b4
  simp only [tb_pure, q4v]
  rw [e9, e10, e11, e12, a1, a2, a3, a4, b1, b2, b3, b4, e4, e3, e2, e5, e6, e1]
  rfl

theorem gMsTail_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) :
    ∀ (σ ρ tb : List Src) (n : Nat), THold xv V n (gMsTail z one σ ρ tb n).2 →
      q4v (xv := xv) (V := V) (gMsTail z one σ ρ tb n).1 = msTailC (vals xv V σ) (vals xv V ρ) (vals xv V tb)
  | a :: σ, r :: ρ, b :: tb, n, h => by
    simp only [gMsTail] at h ⊢
    obtain ⟨h1, h2⟩ := pr_bind _ _ h
    rw [pr_fst, gMsStepA_spec hz _ h2, gMsTail_spec hz ho σ ρ tb n h1]
    rfl
  | [], _, _, n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl
  | _ :: _, [], _, n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl
  | _ :: _, _ :: _, [], n, _ => by simp only [gMsTail, tb_pure, q4v, ho, hz]; rfl

theorem gnoA_dot2 (z a b c d : Src) (n : Nat) : GNoA (gDot z [(a, b), (c, d)] n).2 := gnoA_gDot _ _ _

theorem gnoA_gMsStep (z al be ga de : Src) (t : Bool) (q : Q4) (n : Nat) : GNoA (gMsStep z al be ga de t q n).2 := by
  obtain ⟨q00, q01, q10, q11⟩ := q
  cases t <;> simp only [gMsStep, Bool.false_eq_true, ite_false, ite_true] <;>
    exact gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _)
      (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_dot2 _ _ _ _ _ _) (gnoA_pure _ _))))

theorem gnoA_gMix (b f1 f0 : Src) (n : Nat) : GNoA (gMix b f1 f0 n).2 :=
  gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_mul _ _ _ _)

theorem gnoA_gMsStepA (z a r b : Src) (q : Q4) (n : Nat) : GNoA (gMsStepA z a r b q n).2 := by
  unfold gMsStepA
  exact gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI]))
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_one _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI]))
    (gnoA_bind _ _ _ (gnoA_gMsStep _ _ _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMsStep _ _ _ _ _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_gMix _ _ _ _) (gnoA_pure _ _))))))))))))

theorem gnoA_gMsTail (z one : Src) : ∀ (σ ρ tb : List Src) (n : Nat), GNoA (gMsTail z one σ ρ tb n).2
  | a :: σ, r :: ρ, b :: tb, n => by
    simp only [gMsTail]
    exact gnoA_bind _ _ _ (gnoA_gMsTail z one σ ρ tb n) (gnoA_gMsStepA _ _ _ _ _ _)
  | [], _, _, n => gnoA_pure _ _
  | _ :: _, [], _, n => gnoA_pure _ _
  | _ :: _, _ :: _, [], n => gnoA_pure _ _

theorem gnoA_gMs (z one : Src) (ρ μ σ tb lt : List Src) (n : Nat) : GNoA (gMs z one ρ μ σ tb lt n).2 := by
  unfold gMs
  exact gnoA_bind _ _ _ (gnoA_gMsTail _ _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _) (gnoA_bind _ _ _ (gnoA_gSum _ _ _)
    (gnoA_bind _ _ _ (gnoA_gDot _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_mul _ _ _ _))))))))

theorem gMs_spec {z one : Src} (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) {ρ μ σ tb lt : List Src}
    (hσ : 4 ≤ σ.length) (hμ : μ.length = 16)
    (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (tb.take 4)))) {n : Nat}
    (h : THold xv V n (gMs z one ρ μ σ tb lt n).2) :
    (gMs z one ρ μ σ tb lt n).1.valF xv V = msC (vals xv V ρ) (vals xv V μ) (vals xv V σ) (vals xv V tb) := by
  unfold gMs at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e1 := gMsTail_spec hz ho (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n h1
  generalize (gMsTail z one (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n).1 = q at h e1 ⊢
  generalize n + (gMsTail z one (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e2 := gk_eqTab_one hz ho (σ.take 4) n1 h2
  have hl4 : (gEqTab z [one] (σ.take 4) n1).1.length = 16 := by
    have := congrArg List.length e2
    rw [List.length_map, eqKernel_length, List.length_map, List.length_take, min_eq_left hσ] at this
    simpa using this
  generalize (gEqTab z [one] (σ.take 4) n1).1 = e4 at h e2 hl4 ⊢
  generalize n1 + (gEqTab z [one] (σ.take 4) n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e3 : vals xv V (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1 = (List.range 16).map fun d =>
        eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 :=
    forall₂_map_eq (mapTB_spec_mem (P := fun d v => v = eqAt (vals xv V (σ.take 4)) d *
      (vals xv V μ).getD ((d + 1) % 16) 0) _ (fun d hd m hm => by
        have hd' := List.mem_range.mp hd
        rw [gMul_spec hm, hz, add_zero, getD_vals _ (by omega), getD_vals _ (by omega), e2]
        rfl) _ h3)
  have hA16 : (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1.length = 16 := by rw [mapTB_length]; rfl
  generalize (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).1 = A at h e3 hA16 ⊢
  generalize n2 + (mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z)
      (List.range 16) n2).2.length = n3 at h ⊢
  have hAd : ∀ d < 16, (A.getD d default).valF xv V =
      eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 := by
    intro d hd
    rw [getD_vals _ (by omega), e3]; simp [List.getD_eq_getElem?_getD, hd]
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e4' := gSum_spec _ _ _ h4
  generalize (gSum z (A.take 15) n3).1 = sA at h e4' ⊢; generalize n3 + (gSum z (A.take 15) n3).2.length = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e5 := gDot_spec _ _ _ h5
  generalize (gDot z ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)) n4).1 = L at h e5 ⊢
  generalize n4 + (gDot z ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)) n4).2.length = n5
    at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e6 := gMul_spec h6
  generalize (gMul sA q.1 z n5).1 = x1 at h e6 ⊢; generalize n5 + (gMul sA q.1 z n5).2.length = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e7 := gMul_spec h7
  generalize (gMul (A.getD 15 default) q.2.2.1 x1 n6).1 = x2 at h e7 ⊢
  generalize n6 + (gMul (A.getD 15 default) q.2.2.1 x1 n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e8 := gAdd_spec h8
  generalize (gAdd q.2.1 q.1 n7).1 = d at h e8 ⊢; generalize n7 + (gAdd q.2.1 q.1 n7).2.length = n8 at h ⊢
  rw [gMul_spec h, e8, e7, e6, e5, e4', hz, hAd 15 (by omega)]
  have q1 := congrArg Prod.fst e1
  have q2 := congrArg (fun x => x.2.1) e1
  have q3 := congrArg (fun x => x.2.2.1) e1
  simp only [q4v] at q1 q2 q3
  rw [q1, q2, q3]
  have hlt' : ∀ d < 15, (lt.getD (d + 1) default).valF xv V = ltC (vals xv V (tb.take 4)) (d + 1) := by
    intro d hd
    have hl : lt.length = 17 := by have := congrArg List.length hlt; simpa using this
    rw [getD_vals _ (by omega), hlt]; simp [List.getD_eq_getElem?_getD, show d + 1 < 17 by omega]
  have hS1 : ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) = (List.range 15).map fun d =>
        eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 * ltC (vals xv V (tb.take 4)) (d + 1) := by
    rw [List.map_map]
    exact List.map_congr_left fun d hd => by
      have hd' := List.mem_range.mp hd
      simp only [Function.comp_apply]; rw [hAd d (by omega), hlt' d hd']
  have hS2 : (A.take 15).map (Src.valF xv V) = (List.range 15).map fun d =>
      eqAt (vals xv V (σ.take 4)) d * (vals xv V μ).getD ((d + 1) % 16) 0 := by
    rw [List.map_take, show A.map (Src.valF xv V) = vals xv V A from rfl, e3, gk_take_range_map _ (by omega)]
  rw [hS1, hS2]
  simp only [msC, vals, List.map_drop, List.map_take, List.length_map, zero_add, add_zero]

/-! ## The blocks' assertions -/

theorem gnoA_gThrStep (z r b : Src) (q : Src × Src) (n : Nat) : GNoA (gThrStep z r b q n).2 := by
  unfold gThrStep
  exact gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_emit _ (by simp [addI, linI])) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_pure _ _))))))

/-- **The final check block** (`postW`): `g_D` is the stream scalar at lane `qg`; its assertion is
`b·(msC … · g_D + final) = 0`. -/
theorem postW_spec {P qg : Nat} {cv : Nat → Src} {mb σ lt : List Src} {z one final b : Src}
    (hz : z.valF xv V = 0) (ho : one.valF xv V = 1) (hσ : 4 ≤ σ.length)
    (hlt : vals xv V lt = (List.range 17).map (ltC (vals xv V (mb.take 4)))) {n : Nat}
    (h : THold xv V n (postW P qg cv mb σ lt z one final b n).2) :
    (postW P qg cv mb σ lt z one final b n).1.valF xv V = lv xv [] qg ∧
    (TAssert xv V (postW P qg cv mb σ lt z one final b n).2 ↔
      b.valF xv V * (msC ((List.range (P + 1)).map fun i => (cv (18 + i)).valF xv V)
        ((List.range 16).map fun i => (cv (1 + i)).valF xv V) (vals xv V σ) (vals xv V mb) * lv xv [] qg +
        final.valF xv V) = 0) := by
  have hfst : (postW P qg cv mb σ lt z one final b n).1 = (gLoad qg [] n).1 := by
    simp only [postW, tb_bind, tb_pure]
  refine ⟨by rw [hfst]; unfold postW at h; exact gLoad_lv (tb_peel _ _ h).1, ?_⟩
  unfold postW at h ⊢
  obtain ⟨h1, h, -⟩ := tb_peel _ _ h
  rw [tassert_bind_noA _ _ (gnoA_load _ _ _)]
  have eg := gLoad_lv h1
  generalize (gLoad qg [] n).1 = g at h eg ⊢; generalize n + (gLoad qg [] n).2.length = n1 at h ⊢
  obtain ⟨h2, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gMs _ _ _ _ _ _ _ _)]
  have em := gMs_spec hz ho hσ (by simp) hlt h2
  generalize (gMs z one _ _ σ mb lt n1).1 = ms at h em ⊢
  generalize n1 + (gMs z one _ _ σ mb lt n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]
  have ee := gMul_spec h3
  generalize (gMul ms g final n2).1 = ee' at h ee ⊢
  generalize n2 + (gMul ms g final n2).2.length = n3 at h ⊢
  rw [tassert_bind, gAssert_iff, ee, em, eg]
  simp only [vals, List.map_map, Function.comp_def]
  exact ⟨fun h => h.1, fun h => ⟨h, tassert_noA (gnoA_pure _ _)⟩⟩

/-- **The slot check block** (`slotW`): the 64 slices are the stream scalars at lanes `qs + 3z`, and
its assertion is `b·(Σ_z (Σ_{o<4} eq(τ, o)·ω_{wIx(64 o + z)})·slice_z + final) = 0`. -/
theorem slotW_spec {qs : Nat} {om τ : List Src} {z one final b : Src} (hz : z.valF xv V = 0)
    (ho : one.valF xv V = 1) (hτ : τ.length = 2) {n : Nat}
    (h : THold xv V n (slotW qs om τ z one final b n).2) :
    TAssert xv V (slotW qs om τ z one final b n).2 ↔
      b.valF xv V * (final.valF xv V + ((List.range 64).map fun zz =>
        ((List.range 4).map fun o => eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum *
          lv xv [] (qs + 3 * zz)).sum) = 0 := by
  unfold slotW at h ⊢
  obtain ⟨h1, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _)]
  have esl : vals xv V (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1 =
      (List.range 64).map fun k => lv xv [] (qs + 3 * k) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = lv xv [] (qs + 3 * k)) _ (fun k _ m hm => gLoad_lv hm) _ h1)
  have hsl : (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1.length = 64 := by rw [mapTB_length]; rfl
  generalize (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).1 = sl at h esl hsl ⊢
  generalize n + (mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) n).2.length = n1 at h ⊢
  obtain ⟨h2, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]
  have et := gk_eqTab_one hz ho τ n1 h2
  have hl4 : (gEqTab z [one] τ n1).1.length = 4 := by
    have := congrArg List.length et
    rw [List.length_map, eqKernel_length, List.length_map, hτ] at this; simpa using this
  generalize (gEqTab z [one] τ n1).1 = e4 at h et hl4 ⊢
  generalize n1 + (gEqTab z [one] τ n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_gDot _ _ _) _ _)]
  have eW : vals xv V (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1 =
      (List.range 64).map fun zz => ((List.range 4).map fun o =>
        eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum :=
    forall₂_map_eq (mapTB_spec_mem (P := fun zz v => v = ((List.range 4).map fun o =>
        eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum) _ (fun zz _ m hm => by
      rw [gDot_spec _ _ _ hm, hz, zero_add, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun o ho' => ?_)
      have ho'' := List.mem_range.mp ho'
      simp only [Function.comp_apply]
      rw [getD_vals _ (by omega), et]; rfl) _ h3)
  have hW : (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1.length = 64 := by
    rw [mapTB_length]; rfl
  generalize (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).1 = W at h eW hW ⊢
  generalize n2 + (mapTB (fun zz => gDot z ((List.range 4).map fun o =>
      (e4.getD o default, om.getD (wIx (64 * o + zz)) default))) (List.range 64) n2).2.length = n3 at h ⊢
  obtain ⟨h4, -, -⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gDot _ _ _), gAssert_iff, gDot_spec _ _ _ h4]
  rw [List.map_map]
  have hs : ((List.range 64).map ((fun cd => cd.1.valF xv V * cd.2.valF xv V) ∘ fun zz =>
      (W.getD zz default, sl.getD zz default))) = (List.range 64).map fun zz =>
        ((List.range 4).map fun o => eqAt (vals xv V τ) o * (om.getD (wIx (64 * o + zz)) default).valF xv V).sum *
          lv xv [] (qs + 3 * zz) := by
    refine List.map_congr_left fun zz hzz => ?_
    have hzz' := List.mem_range.mp hzz
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), eW, esl]
    simp [List.getD_eq_getElem?_getD, hzz']
  rw [hs]

/-! ## The target block -/

theorem fx_gSum : ∀ (acc : Src) (cs : List Src) (n : Nat), Fx acc → Fx (gSum acc cs n).1
  | _, [], _, h => h
  | acc, c :: cs, n, _ => by
    simp only [gSum, tb_bind]
    exact fx_gSum _ cs _ (fx_emit _ _)

/-- `ω_j` from the claim's lane weights `B` and slice point `a` (`laneForm` at slice `j mod 64`). -/
def wOm (A B : List FE) (j : Nat) : FE := laneForm B (fun s => (eqKernel A).getD ((j % 64 + s) % 64) 0) (j / 64)

/-- `⟨ω, c43⟩` on `wOm`. -/
def wC43 (A B : List FE) : FE := wOm A B 0 + wOm A B 1 + wOm A B 6 + wOm A B 264 + wOm A B 1087

/-- **The wiring target as the rows compute it**: `ι(0)·padDot + (c43·(thr + ι(0)) + value)` with
`padDot = c43 + Σ_{p<256} ω_{8+p}·s_p`, `ι(0) = Π(1 + ρ_k)·μ_0`, `thr = thrC ρ μ bits(m)`. -/
def wTgt (value : FE) (μ ρ A B mb sb : List FE) : FE :=
  (ρ.map (1 + ·)).prod * μ.getD 0 0 *
      (wC43 A B + ((List.range 256).map fun p => wOm A B (8 + p) * sb.getD p 0).sum) +
    (wC43 A B * (thrC ρ μ mb + (ρ.map (1 + ·)).prod * μ.getD 0 0) + value)

theorem wPos_length : wPos.length = 261 := by simp [wPos]

theorem wPos_ix_all : ∀ p < 257, wPos.getD (3 + p) 0 = 8 + p := by decide +kernel

theorem wPos_getD_ix {p : Nat} (hp : p ≤ 256) : wPos.getD (wIx p) 0 = 8 + p := wPos_ix_all p (by omega)

theorem wPos_lt_all : wPos.all (· < 1600) = true := by decide +kernel

theorem wPos_lt : ∀ j ∈ wPos, j < 1600 := by
  intro j hj; have := List.all_eq_true.mp wPos_lt_all j hj; simpa using this

theorem wPos_c43 : wPos.getD 0 0 = 0 ∧ wPos.getD 1 0 = 1 ∧ wPos.getD 2 0 = 6 ∧ wPos.getD 259 0 = 264 ∧
    wPos.getD 260 0 = 1087 := by decide +kernel

theorem wPos_map_getD (f : Nat → FE) {k : Nat} (hk : k < 261) : (wPos.map f).getD k 0 = f (wPos.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simp [wPos_length]; omega), List.getElem_map,
    List.getD_eq_getElem _ _ (by rw [wPos_length]; omega)]

/-- **The target block** (`preW`): zero, one, `ω` on `wPos`, the `lt` table of `m`'s low bits and the
target. -/
theorem preW_spec {P : Nat} {cv : Nat → Src} {mb sb : List Src} {b : Src} (hmb : 4 ≤ mb.length)
    (hsb : sb.length = 256) {n : Nat} (h : THold xv V n (preW P cv mb sb b n).2) :
    (preW P cv mb sb b n).1.z.valF xv V = 0 ∧ Fx (preW P cv mb sb b n).1.z ∧
    (preW P cv mb sb b n).1.one.valF xv V = 1 ∧ Fx (preW P cv mb sb b n).1.one ∧
    vals xv V (preW P cv mb sb b n).1.om = wPos.map (wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
      ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V)) ∧
    (∀ x ∈ (preW P cv mb sb b n).1.om, Fx x) ∧
    vals xv V (preW P cv mb sb b n).1.lt = (List.range 17).map (ltC (vals xv V (mb.take 4))) ∧
    (∀ x ∈ (preW P cv mb sb b n).1.lt, Fx x) ∧
    (preW P cv mb sb b n).1.target.valF xv V =
      wTgt ((cv 0).valF xv V) ((List.range 16).map fun i => (cv (1 + i)).valF xv V)
        ((List.range (P + 1)).map fun i => (cv (18 + i)).valF xv V)
        ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
        ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V) (vals xv V mb) (vals xv V sb) ∧
    Fx (preW P cv mb sb b n).1.target := by
  unfold preW at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ez := gZero_spec h1; have fz : Fx (gZero b n).1 := fx_emit _ _
  generalize (gZero b n).1 = z at h ez fz ⊢; generalize n + (gZero b n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eo := gOne_spec h2; have fo : Fx (gOne z n1).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n1).1 = one at h eo fo ⊢; generalize n1 + (gOne z n1).2.length = n2 at h ⊢
  -- `eq(a)`
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eZ := gk_eqTab_one ez eo ((List.range 6).map fun i => cv (44 + P + i)) n2 h3
  have hZ : (gEqTab z [one] ((List.range 6).map fun i => cv (44 + P + i)) n2).1.length = 64 := by
    have := congrArg List.length eZ
    rw [List.length_map, eqKernel_length, List.length_map] at this; simpa using this
  generalize (gEqTab z [one] ((List.range 6).map fun i => cv (44 + P + i)) n2).1 = eZs at h eZ hZ ⊢
  generalize n2 + (gEqTab z [one] _ n2).2.length = n3 at h ⊢
  simp only [vals, List.map_map, Function.comp_def] at eZ
  -- `ω`
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eom : vals xv V (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1 =
      wPos.map (wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
        ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V)) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun j v => v = wOm _ _ j) _ (fun j hj m hm => by
      rw [gOmega_spec ez (by simp) (wPos_lt j hj) hm, wOm]
      simp only [vals, List.map_map, Function.comp_def]
      congr 1
      funext s
      rw [getD_vals _ (by rw [hZ]; exact Nat.mod_lt _ (by omega))]
      simp only [vals]; rw [eZ]) _ h4)
  have fom : ∀ x ∈ (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1, Fx x :=
    fx_mapTB (fun _ _ => by
      unfold gOmega gLaneForm
      simp only [tb_bind]
      exact fx_gDot _ _ _ (fx_gDot _ _ _ (fx_emit _ _))) _ _
  have hom : (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1.length = 261 := by
    rw [mapTB_length, wPos_length]
  generalize (mapTB (gOmega z ((List.range 25).map fun l => cv (19 + P + l)) eZs) wPos n3).1 = om at h eom fom hom ⊢
  generalize n3 + (mapTB (gOmega z _ eZs) wPos n3).2.length = n4 at h ⊢
  have hOm : ∀ k < 261, (om.getD k default).valF xv V = (wPos.map (wOm ((List.range 6).map fun i =>
      (cv (44 + P + i)).valF xv V) ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V))).getD k 0 := by
    intro k hk; rw [getD_vals _ (by omega), eom]
  -- `ι(0)`
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e0 := gEq0_spec ez one ((List.range (P + 1)).map fun i => cv (18 + i)) n4 h5
  rw [eo, one_mul] at e0
  generalize (gEq0 z one ((List.range (P + 1)).map fun i => cv (18 + i)) n4).1 = q0 at h e0 ⊢
  generalize n4 + (gEq0 z one _ n4).2.length = n5 at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ei := gMul_spec h6; rw [ez, add_zero] at ei
  generalize (gMul q0 _ z n5).1 = io0 at h ei ⊢; generalize n5 + (gMul q0 _ z n5).2.length = n6 at h ⊢
  -- `lt`, `thr`
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have elt := gLtTab_spec ez eo (mb.take 4) (by rw [List.length_take]; omega) h7
  have flt : ∀ x ∈ (gLtTab z one (mb.take 4) n6).1, Fx x := by
    unfold gLtTab; simp only [tb_bind]
    exact fx_mapTB (fun _ _ => fx_gSum _ _ _ fz) _ _
  generalize (gLtTab z one (mb.take 4) n6).1 = lt at h elt flt ⊢
  generalize n6 + (gLtTab z one (mb.take 4) n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eth := gThr_spec ez eo (by simp) elt h8
  generalize (gThr z one _ _ mb lt n7).1 = thr at h eth ⊢
  generalize n7 + (gThr z one _ _ mb lt n7).2.length = n8 at h ⊢
  -- `c43`, `padDot`
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ec := gSum_spec _ _ _ h9
  generalize (gSum z _ n8).1 = c43 at h ec ⊢; generalize n8 + (gSum z _ n8).2.length = n9 at h ⊢
  obtain ⟨h10, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have epd := gDot_spec _ _ _ h10
  generalize (gDot c43 _ n9).1 = pd at h epd ⊢; generalize n9 + (gDot c43 _ n9).2.length = n10 at h ⊢
  -- the target
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e11 := gAdd_spec h11
  generalize (gAdd thr io0 n10).1 = ti at h e11 ⊢; generalize n10 + (gAdd thr io0 n10).2.length = n11 at h ⊢
  obtain ⟨h12, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e12 := gMul_spec h12
  generalize (gMul c43 ti _ n11).1 = t1 at h e12 ⊢; generalize n11 + (gMul c43 ti _ n11).2.length = n12 at h ⊢
  obtain ⟨h13, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have e13 := gMul_spec h13
  have ft : Fx (gMul io0 pd t1 n12).1 := fx_emit _ _
  generalize (gMul io0 pd t1 n12).1 = tgt at e13 ft ⊢
  simp only [tb_pure]
  refine ⟨ez, fz, eo, fo, eom, fom, elt, flt, ?_, ft⟩
  rw [e13, e12, e11, epd, ec, eth, ei, e0, ez]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  have hpd : ((List.range 256).map fun p => (om.getD (wIx p) default, sb.getD p default)).map
      (fun cd => cd.1.valF xv V * cd.2.valF xv V) = (List.range 256).map fun p =>
        wOm ((List.range 6).map fun i => (cv (44 + P + i)).valF xv V)
          ((List.range 25).map fun l => (cv (19 + P + l)).valF xv V) (8 + p) * (vals xv V sb).getD p 0 := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hp' := List.mem_range.mp hp
    simp only [Function.comp_apply]
    rw [hOm _ (by simp [wIx]; omega), getD_vals _ (by omega), wPos_map_getD _ (by simp [wIx]; omega),
      wPos_getD_ix (by omega)]
  rw [hpd, hOm 0 (by omega), hOm 1 (by omega), hOm 2 (by omega), hOm 259 (by omega), hOm 260 (by omega),
    wPos_map_getD _ (by omega), wPos_map_getD _ (by omega), wPos_map_getD _ (by omega),
    wPos_map_getD _ (by omega), wPos_map_getD _ (by omega), wPos_c43.1, wPos_c43.2.1, wPos_c43.2.2.1,
    wPos_c43.2.2.2.1, wPos_c43.2.2.2.2]
  simp only [wTgt, wC43, vals, List.map_map, Function.comp_def]
  rw [getD_vals _ (by simp), List.getD_eq_getElem?_getD]
  simp only [vals, List.getElem?_map, List.getElem?_range (show 0 < 16 by omega), Option.map_some,
    Option.getD_some, Nat.add_zero]
  have hμ0 : (List.map (fun x => Src.valF xv V (cv (1 + x))) (List.range 16)).getD 0 0 = Src.valF xv V (cv 1) := by
    simp
  rw [hμ0]
  ring

end Lvm.Q1
