-- New for lvm (WP-14a, H4): the pure parts of V_S's WHIR (LvmDecideWhir, over `FE`) are the verifier
-- language's (LvmVCore / LvmWhirProg, over `E`) through `FE.toExt3`: subspace roots, induced weights, the row
-- folds read in place from Σ against the rows the compiled verifier decodes, the enforced sum, the glue.
-- The row folds as sums are LvmQWhirBase's `foldRow0_eq`/`foldRowE_eq` (WP-11b QA2), `dot` as a sum WP-7's
-- `Whir.Sound.dot_eq_sum`.
import LvmVEqRel
import LvmVEqArith
import LvmWhirParams
import LvmQWhirBase

/-!
# V_S's WHIR arithmetic over `E`

* `map_subspaceRoots`, `toExt3_inducedWeight`: `subspaceRoots`/`inducedWeight` transported;
* `rowAt_eq`: the compiled verifier's row (`rowOf kOfBytes`) is the native words at `o + 8 j`;
* `toExt3_foldRow0`, `toExt3_foldRowE`: V_S's level-0 fold `Σ_k eq[k]·word[w−1−k]` is `dot` of the
  DSL's `row.reverse.map ofK` with `eqKernel`, the later-level fold is `dot` of `extRow row` (rows of
  `3·2^ℓ` words);
* `toExt3_dot_rows`: `dot queryWeights folds` is the DSL's `enforcedSum` shape;
* `GRel`, `WRel`: glued claims and WHIR states (the DSL state's `target` is not related: V_S does not
  track it, and the DSL reads it only in `tailRoundsT 0`, where V_S's `tailRounds 0` fails);
  `wrel_glue`: `glue` vs `glueT` on one pending claim.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK FE_eq_of_beq)

/-! ## Subspace roots and induced weights -/

theorem map_subspaceRootsAux : ∀ (n : ℕ) (last : FE) (layer : List FE),
    (Lvm.subspaceRootsAux n last layer).map FE.toExt3 =
      Verifier.subspaceRootsAux n (FE.toExt3 last) (layer.map FE.toExt3)
  | 0, _, _ => rfl
  | n + 1, last, layer => by
    have h : (layer.map FE.toExt3).map (fun v ↦ v ^ 2 + FE.toExt3 last * v) =
        (layer.map fun v ↦ FE.sq v + last * v).map FE.toExt3 := by
      simp only [List.map_map]
      exact List.map_congr_left fun v _ ↦ by
        simp only [Function.comp_apply, tE_add, tE_mul, toExt3_sq_eq_pow]
    simp only [Lvm.subspaceRootsAux, Verifier.subspaceRootsAux, h]
    generalize layer.map (fun v ↦ FE.sq v + last * v) = l
    cases l with
    | nil => rfl
    | cons r rest => simp only [List.map_cons, map_subspaceRootsAux n r rest]

theorem map_subspaceRoots (n : ℕ) :
    (Lvm.subspaceRoots n).map FE.toExt3 = Verifier.subspaceRoots n := by
  simp only [Lvm.subspaceRoots, Verifier.subspaceRoots, List.map_cons, tE_one, map_subspaceRootsAux,
    List.map_map]
  congr 2

theorem toExt3_inv0 (v : FE) :
    FE.toExt3 (if v == 0 then 0 else v⁻¹) = if FE.toExt3 v = 0 then 0 else (FE.toExt3 v)⁻¹ := by
  have hr : (if FE.toExt3 v = 0 then 0 else (FE.toExt3 v)⁻¹) = (FE.toExt3 v)⁻¹ := by
    split_ifs with h
    · rw [h, inv_zero]
    · rfl
  rw [hr]
  split_ifs with h
  · rw [FE_eq_of_beq h, tE_zero, inv_zero]
  · exact FE.toExt3_inv v

/-- The induced weight's inner product over the point. -/
theorem toExt3_iwInner (rts invs : List FE) : ∀ (pt : List (FE × ℕ)) (acc : FE × FE),
    Prod.map FE.toExt3 FE.toExt3 (pt.foldl (fun (acc : FE × FE) (x : FE × ℕ) ↦
      (acc.1 * (1 + x.1 * (1 + acc.2 * invs.getD x.2 0)), FE.sq acc.2 + rts.getD x.2 0 * acc.2)) acc) =
    (pt.map (Prod.map FE.toExt3 id)).foldl (fun (acc : E × E) (x : E × ℕ) ↦
      (acc.1 * (1 + x.1 * (1 + acc.2 * (invs.map FE.toExt3).getD x.2 0)),
        acc.2 ^ 2 + (rts.map FE.toExt3).getD x.2 0 * acc.2)) (Prod.map FE.toExt3 FE.toExt3 acc)
  | [], _ => rfl
  | x :: pt, acc => by
    rw [List.foldl_cons, toExt3_iwInner rts invs pt, List.map_cons, List.foldl_cons]
    congr 1
    simp only [Prod.map, getD_map_toExt3, tE_add, tE_mul, tE_one, toExt3_sq_eq_pow, id]

theorem toExt3_inducedWeight (m : ℕ) (qs : List ℕ) (ws pt : List FE) :
    FE.toExt3 (Lvm.inducedWeight m qs ws pt) =
      Verifier.inducedWeight m qs (ws.map FE.toExt3) (pt.map FE.toExt3) := by
  have hr := map_subspaceRoots m
  have hi : ((Lvm.subspaceRoots m).map fun v ↦ if v == 0 then 0 else v⁻¹).map FE.toExt3 =
      ((Lvm.subspaceRoots m).map FE.toExt3).map fun v ↦ if v = 0 then 0 else v⁻¹ := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun v _ ↦ toExt3_inv0 v
  unfold Lvm.inducedWeight Verifier.inducedWeight
  simp only []
  rw [← hr, ← hi, List.zip_map_left, zipIdx_map_toExt3]
  generalize Lvm.subspaceRoots m = rts
  generalize (rts.map fun v ↦ if v == 0 then 0 else v⁻¹) = invs
  generalize ws.zip qs = l
  suffices h : ∀ a : FE, FE.toExt3 (l.foldl (fun total (x : FE × ℕ) ↦ total +
      (pt.zipIdx.foldl (fun (acc : FE × FE) (y : FE × ℕ) ↦
        (acc.1 * (1 + y.1 * (1 + acc.2 * invs.getD y.2 0)), FE.sq acc.2 + rts.getD y.2 0 * acc.2))
        (x.1, Lvm.eOfNat x.2)).1) a) =
      (l.map (Prod.map FE.toExt3 id)).foldl (fun total (x : E × ℕ) ↦ total +
      ((pt.zipIdx.map (Prod.map FE.toExt3 id)).foldl (fun (acc : E × E) (y : E × ℕ) ↦
        (acc.1 * (1 + y.1 * (1 + acc.2 * (invs.map FE.toExt3).getD y.2 0)),
          acc.2 ^ 2 + (rts.map FE.toExt3).getD y.2 0 * acc.2))
        (x.1, Verifier.eOfNat x.2)).1) (FE.toExt3 a) by
    exact (h 0).trans (by rw [tE_zero])
  induction l with
  | nil => intro a; rfl
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, tE_add]
    congr 2
    have := congrArg Prod.fst (toExt3_iwInner rts invs pt.zipIdx (x.1, Lvm.eOfNat x.2))
    simp only [Prod.map] at this
    rw [this, toExt3_eOfNat]
    rfl

/-! ## Rows -/

theorem getD_map_rangeWP {α : Type} (f : ℕ → α) {w k : ℕ} (hk : k < w) (d : α) :
    ((List.range w).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

@[simp] theorem length_rowAt (sig : ByteArray) (o wd : ℕ) : (rowAt sig o wd).length = wd := by
  simp [rowAt]

/-- **The compiled verifier's row** of `wd` words at byte `o`: the native words at `o + 8 j`. -/
theorem rowAt_eq (sig : ByteArray) (o wd : ℕ) :
    rowAt sig o wd = (List.range wd).map fun j ↦ FK.toBF64 (kAt sig (o + 8 * j)) := by
  apply List.ext_getElem
  · simp [rowAt]
  · intro j h1 h2
    have h := rowOf_sb sig o wd j (by simpa using h2)
    change (rowAt sig o wd).getD j 0 = _ at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at h
    rw [h, List.getElem_map, List.getElem_range]

/-- A level-0 row as the DSL folds it: reversed, lifted to `E`. -/
theorem rev_rowAt (sig : ByteArray) (o w : ℕ) :
    (rowAt sig o w).reverse.map ofK =
      (List.range w).map fun k ↦ FE.toExt3 (FE.ofK (kAt sig (o + 8 * (w - 1 - k)))) := by
  rw [rowAt_eq]
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_map,
      List.length_range, tE_ofK]
    rfl

theorem extRow_eq : ∀ (w : ℕ) (l : List K), l.length = 3 * w →
    Verifier.extRow l =
      (List.range w).map fun k ↦ E.ofLimbs (l.getD (3 * k) 0) (l.getD (3 * k + 1) 0) (l.getD (3 * k + 2) 0)
  | 0, l, hl => by
    have : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst this; rfl
  | w + 1, l, hl => by
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hl
    · simp at hl; omega
    · simp at hl; omega
    · simp only [List.length_cons] at hl
      rw [Verifier.extRow, extRow_eq w l (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg _ (List.map_congr_left fun k _ ↦ ?_)
      simp only [Function.comp_apply, Nat.mul_succ]
      rfl

theorem getD_rowAt (sig : ByteArray) (o wd j : ℕ) (hj : j < wd) :
    (rowAt sig o wd).getD j 0 = FK.toBF64 (kAt sig (o + 8 * j)) := rowOf_sb sig o wd j hj

/-- A later row (`3·w` words) as the DSL folds it: `w` scalars. -/
theorem extRow_rowAt (sig : ByteArray) (o w : ℕ) :
    Verifier.extRow (rowAt sig o (3 * w)) = (List.range w).map fun k ↦ FE.toExt3 (feAt sig (o + 24 * k)) := by
  rw [extRow_eq w _ (length_rowAt sig o _)]
  refine List.map_congr_left fun k hk ↦ ?_
  rw [List.mem_range] at hk
  rw [getD_rowAt _ _ _ _ (by omega), getD_rowAt _ _ _ _ (by omega), getD_rowAt _ _ _ _ (by omega),
    show o + 8 * (3 * k) = o + 24 * k by ring, show o + 8 * (3 * k + 1) = o + 24 * k + 8 by ring,
    show o + 8 * (3 * k + 2) = o + 24 * k + 16 by ring]
  rfl

theorem toExt3_sum (s : Finset ℕ) (f : ℕ → FE) : FE.toExt3 (∑ k ∈ s, f k) = ∑ k ∈ s, FE.toExt3 (f k) :=
  map_sum FE.ringEquivExt3 f s

/-- **The level-0 fold**: V_S's `foldRow0` is the DSL's `dot (row.reverse.map ofK) (eqKernel folds)`. -/
theorem toExt3_foldRow0 (sig : ByteArray) (lf : List FE) (o w : ℕ) (hw : w = 2 ^ lf.length) :
    FE.toExt3 (foldRow0 sig (eqKernelA lf) o w) =
      Verifier.dot ((rowAt sig o w).reverse.map ofK) (Verifier.eqKernel (lf.map FE.toExt3)) := by
  rw [Loop.foldRow0_eq, Whir.Sound.dot_eq_sum _ _ (by
    simp [Whir.Sound.length_eqKernel, hw]), toExt3_sum]
  simp only [List.length_map, List.length_reverse, length_rowAt]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [rev_rowAt, getD_map_rangeWP _ hk, ← map_eqKernel, getD_map_toExt3, ← getD_eqKernelA, tE_mul]

/-- **A later-level fold**: V_S's `foldRowE` is the DSL's `dot (extRow row) (eqKernel folds)`. -/
theorem toExt3_foldRowE (sig : ByteArray) (lf : List FE) (o w : ℕ) (hw : w = 2 ^ lf.length) :
    FE.toExt3 (foldRowE sig (eqKernelA lf) o w) =
      Verifier.dot (Verifier.extRow (rowAt sig o (3 * w))) (Verifier.eqKernel (lf.map FE.toExt3)) := by
  rw [Loop.foldRowE_eq, extRow_rowAt, Whir.Sound.dot_eq_sum _ _ (by
    simp [Whir.Sound.length_eqKernel, hw]), toExt3_sum]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [getD_map_rangeWP _ hk, ← map_eqKernel, getD_map_toExt3, ← getD_eqKernelA, tE_mul]

/-- **The enforced sum**: `dot queryWeights folds` with each fold a `dot` of the DSL's row. -/
theorem toExt3_dot_rows (ws : List FE) (offs : List ℕ) (g : ℕ → FE) (h : ℕ → List E) (lf : List E)
    (hg : ∀ o, FE.toExt3 (g o) = Verifier.dot (h o) (Verifier.eqKernel lf)) :
    FE.toExt3 (Lvm.dot ws (offs.map g)) = Verifier.enforcedSum (offs.map h) lf (ws.map FE.toExt3) := by
  unfold Lvm.dot Verifier.enforcedSum
  simp only []
  generalize Verifier.eqKernel lf = lw at hg
  suffices H : ∀ (a : FE), FE.toExt3 ((List.zipWith (· * ·) ws (offs.map g)).foldl (· + ·) a) =
      (List.zip (ws.map FE.toExt3) (offs.map h)).foldl (fun total x ↦ total + x.1 * Verifier.dot x.2 lw)
        (FE.toExt3 a) from (H 0).trans (by rw [tE_zero])
  induction ws generalizing offs with
  | nil => intro a; rfl
  | cons w ws ih =>
    intro a
    cases offs with
    | nil => rfl
    | cons o offs =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, List.foldl_cons]
      rw [ih, tE_add, tE_mul, hg]

/-! ## Glued claims and states -/

/-- A native glued claim and a language glued claim. -/
structure GRel (g : Lvm.GluedClaim) (g' : Verifier.GluedClaim) : Prop where
  scalar : g'.scalar = FE.toExt3 g.scalar
  start : g'.foldStart = g.foldStart
  weight : ∀ xs : List FE, g'.weightAt (xs.map FE.toExt3) = FE.toExt3 (g.weightAt xs)

/-- A native WHIR state and a language one (the language's `target` is free). -/
structure WRel (s : Lvm.WhirState) (t : Verifier.WhirStateT) : Prop where
  quad : t.quad = s.runningQuad.map FE.toExt3
  folds : t.folds = s.folds.map FE.toExt3
  glued : List.Forall₂ GRel s.glued t.glued

/-- **`glue` vs `glueT`** on one pending claim (the language also adds its value to `target`). -/
theorem wrel_glue {s : Lvm.WhirState} {t : Verifier.WhirStateT} (h : WRel s t) {lam : FE} {lam' : E}
    (hl : lam' = FE.toExt3 lam) {intro : List FE} {intro' : List E} (hi : intro' = intro.map FE.toExt3)
    {w : List FE → FE} {w' : List E → E} (hw : ∀ xs, w' (xs.map FE.toExt3) = FE.toExt3 (w xs)) (v : E) :
    WRel (Lvm.glue lam s [(intro, w)]) (Verifier.glueT lam' t [(v, intro', w')]) := by
  subst hl hi
  refine ⟨?_, h.folds, ?_⟩
  · simp only [Lvm.glue, Verifier.glueT, List.foldl_cons, List.foldl_nil, h.quad]
    exact (map_zipWith_of (fun q i ↦ by rw [tE_add, tE_mul, tE_mul, tE_one]) _ _).symm
  · simp only [Lvm.glue, Verifier.glueT, List.foldl_cons, List.foldl_nil]
    refine List.rel_append h.glued (List.Forall₂.cons ⟨by rw [tE_mul, tE_one], ?_, hw⟩ List.Forall₂.nil)
    simp [h.folds]

/-- The terminal weight's glued sum. -/
theorem toExt3_gluedWeight (folds tf : List FE) {gs : List Lvm.GluedClaim} {gs' : List Verifier.GluedClaim}
    (h : List.Forall₂ GRel gs gs') (a : FE) :
    FE.toExt3 (gs.foldl (fun weight claim ↦
        weight + claim.scalar * claim.weightAt (folds.drop claim.foldStart ++ tf)) a) =
      gs'.foldl (fun weight claim ↦ weight + claim.scalar *
        claim.weightAt ((folds.map FE.toExt3).drop claim.foldStart ++ tf.map FE.toExt3)) (FE.toExt3 a) := by
  induction h generalizing a with
  | nil => rfl
  | cons hg _ ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, tE_add, tE_mul, hg.scalar, hg.start, ← List.map_drop,
      ← List.map_append, hg.weight]

/-- **The terminal check**: V_S's terminal value over `E` is the DSL's. -/
theorem toExt3_terminal {s : Lvm.WhirState} {t : Verifier.WhirStateT} (h : WRel s t) (eb : List FE → FE)
    (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) (laneFolds : ℕ)
    (tf res : List FE) :
    t.glued.foldl (fun weight claim ↦
        weight + claim.scalar * claim.weightAt (t.folds.drop claim.foldStart ++ tf.map FE.toExt3))
      (eb' ((t.folds ++ tf.map FE.toExt3).drop laneFolds ++ (t.folds ++ tf.map FE.toExt3).take laneFolds)) *
      Verifier.multilinearEval (res.map FE.toExt3) (tf.map FE.toExt3) =
    FE.toExt3 (s.glued.foldl (fun weight claim ↦
        weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tf))
      (eb ((s.folds ++ tf).drop laneFolds ++ (s.folds ++ tf).take laneFolds)) * Lvm.multilinearEval res tf) := by
  rw [tE_mul, toExt3_multilinearEval, toExt3_gluedWeight _ _ h.glued, ← heb, h.folds]
  simp only [List.map_append, List.map_drop, List.map_take]

end Lvm.VEq
