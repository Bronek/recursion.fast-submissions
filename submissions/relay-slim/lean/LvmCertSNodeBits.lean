-- WP-14c (NodeSound, O10). New for lvm: the hypotheses `SigTabsIn` and `SigCellsLt` of WP-12b's
-- `sigBitsOk` (LvmSigBits): Q_sig's six BITS tables in the auxiliary tables, and every cell they
-- name inside the program. The part decomposition follows WP-12's `qsig_parts` (LvmQSigParts), with
-- QL's builder bookkeeping (`bind_apply`, `Ptr.adv_append`, `mkLoop_tw`; `loop_adv` as in QA2's
-- LvmQWhirBase).
import LvmSigBits

/-!
# The BITS tables of `Q_sig` in the instance

* **`sigTabsIn_append`**: `SigTabsIn` holds for `aux = (sigSpecs I o bpl).map BSpec.tab ++ rest`
  (any other auxiliary tables after them, e.g. QL's position-field tables).
* **`sigCellsLt_of`**: `SigCellsLt Q I o bpl` from two layout facts: `SigRegLt C I` (the input
  regions of `I` the tables name, with their extents, below `C = Q.cells .K`) and `SigOutLt C o` (the
  chain and path cells of `Q_sig`'s output below `C`).
* **`sigOutLt_qsig`**: `SigOutLt C (qsig I p).1` whenever `Q_sig` placed at `p` ends at or below `C`
  (`(p.adv (qsig I p).2).k ≤ C`; true when `Q_sig`'s segments are a prefix of the program's at `p`):
  every cell a loop of `Q_sig` writes lies below the pointer after it.
-/

set_option autoImplicit false

namespace Lvm.NS

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.SigBits Lvm.BitsTab Lvm.M3

/-! ## The tables in the auxiliary list -/

/-- **The six tables first in `aux`.** -/
theorem sigTabsIn_append (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (rest : List Tab) :
    SigTabsIn I o bpl ((sigSpecs I o bpl).map BSpec.tab ++ rest) :=
  fun _ hS => List.mem_append_left _ (List.mem_map_of_mem hS)

/-! ## The cells the tables name -/

/-- **The input regions** the six tables name, with their extents, below `C`. -/
structure SigRegLt (C : Nat) (I : SigIn) : Prop where
  sg : I.sg + 533 ≤ C
  bi : I.bi + 18 ≤ C
  md : I.md + 4 ≤ C
  bd : I.bd + 256 ≤ C
  bc : I.bc + 10 ≤ C
  bx : I.bx + 3192 ≤ C
  be : I.be + 1064 ≤ C
  bp : I.bp + 256 ≤ C
  hd : I.hd + 18 ≤ C
  bh : I.bh + 8 ≤ C
  bcl : I.bcl + 8 ≤ C
  yls : I.yls + 4 ≤ C
  bls : I.bls + 8 ≤ C
  bn : I.bn + I.ln + 5 ≤ C

/-- **Q_sig's chain and path cells** below `C`. -/
structure SigOutLt (C : Nat) (o : SigOut) : Prop where
  chain : ∀ i < 133, ∀ t < 28, chainCell o i t < C
  path : ∀ t < 16, ∀ c < 12, (o.pa.cell c t).n < C

/-- **`SigCellsLt` from the layout.** -/
theorem sigCellsLt_of {Q : Program} {I : SigIn} {o : SigOut} (bpl : Nat → Nat → Bool × Nat)
    (hR : SigRegLt (Q.cells .K) I) (hO : SigOutLt (Q.cells .K) o) : SigCellsLt Q I o bpl := by
  intro S hS x hx
  simp only [sigSpecs, List.mem_cons, List.not_mem_nil, or_false] at hS
  have R := hR
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [sIdx] at hx ⊢
    refine ⟨fun _ => by have := R.sg; omega, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range,
      List.length_nil] at hj
    have := R.bi; omega
  · simp only [sMd] at hx ⊢
    refine ⟨fun _ => by have := R.md; omega, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    have := R.bd; omega
  · simp only [sCs] at hx ⊢
    refine ⟨fun h => absurd h (by decide), fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    have := R.bc; omega
  · simp only [s24] at hx ⊢
    refine ⟨fun _ => ?_, fun j hj => ?_⟩
    · unfold xin
      split
      · have := R.sg; omega
      · exact hO.chain _ (by omega) _ (by omega)
    · simp only [List.length_cons, List.length_nil] at hj
      have := R.bx; omega
  · simp only [s8] at hx ⊢
    refine ⟨fun _ => ?_, fun j hj => ?_⟩
    · split
      · exact hO.chain _ (by omega) _ (by omega)
      · split
        · exact hO.path _ (by omega) _ (by omega)
        · split
          · have := R.hd; omega
          · split
            · have := R.hd; omega
            · have := R.yls; omega
    · simp only [List.length_cons, List.length_nil] at hj
      split
      · have := R.be; omega
      · split
        · have := R.bp; omega
        · split
          · have := R.bh; omega
          · split
            · have := R.bcl; omega
            · have := R.bls; omega
  · simp only [sN] at hx ⊢
    refine ⟨fun _ => by have := R.hd; omega, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range,
      List.length_nil] at hj
    have := R.bn; omega

/-! ## Q_sig's cells lie below the pointer after it -/

/-- A gadget placed at `p` ends at or below `C`. -/
def Inside (C : Nat) {α : Type} (m : BM α) (p : Ptr) : Prop := (p.adv (m p).2).k ≤ C

theorem inside_bind {C : Nat} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Inside C (m >>= f) p) :
    Inside C m p ∧ Inside C (f (m p).1) (p.adv (m p).2) ∧
      ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := by
  unfold Inside at h ⊢
  rw [bind_apply, Ptr.adv_append] at h
  refine ⟨?_, h, rfl⟩
  have : (p.adv (m p).2).k ≤ ((p.adv (m p).2).adv (f (m p).1 (p.adv (m p).2)).2).k := by
    simp only [Ptr.adv]; omega
  omega

theorem inside_seqAll_get {C : Nat} :
    ∀ (ms : List (BM LoopOut)) (p : Ptr), Inside C (seqAll ms) p →
      ∀ u < ms.length, ∃ q, Inside C (ms.getD u (pure dLoop)) q ∧
        (seqAll ms p).1.getD u dLoop = ((ms.getD u (pure dLoop)) q).1
  | [], _, _, u, hu => absurd hu (by simp)
  | m :: ms, p, h, u, hu => by
    unfold Inside at h
    rw [seqAll_cons_apply, Ptr.adv_append, Ptr.adv_append] at h
    have h1 : (p.adv (m p).2).k ≤ C := by
      have : (p.adv (m p).2).k ≤
          (((p.adv (m p).2).adv (seqAll ms (p.adv (m p).2)).2).adv []).k := by
        simp only [Ptr.adv]; omega
      omega
    have h2 : Inside C (seqAll ms) (p.adv (m p).2) := by
      unfold Inside; simpa using h
    cases u with
    | zero => exact ⟨p, h1, by simp [seqAll_cons_apply]⟩
    | succ u =>
      obtain ⟨q, hq, e⟩ := inside_seqAll_get ms _ h2 u (by simpa using hu)
      refine ⟨q, by simpa using hq, ?_⟩
      simp only [seqAll_cons_apply, List.getD_cons_succ]
      exact e

theorem inside_forN_get {C n : Nat} {f : Nat → BM LoopOut} {p : Ptr} (h : Inside C (forN n f) p) :
    ∀ u < n, ∃ q, Inside C (f u) q ∧ (forN n f p).1.getD u dLoop = (f u q).1 := by
  intro u hu
  obtain ⟨q, hq, e⟩ := inside_seqAll_get _ p h u (by simpa using hu)
  have hg : ((List.range n).map f).getD u (pure dLoop) = f u := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  rw [hg] at hq e
  exact ⟨q, hq, e⟩

set_option maxRecDepth 100000 in
/-- **Where Q_sig's loops sit** (the pointer form of `qsig_parts`): each loop whose cells the
tables name ends at or below `C`. -/
theorem qsig_inside {C : Nat} {p : Ptr} {I : SigIn} (h : Inside C (qsig I) p) :
    let o := (qsig I p).1
    (∃ q, Inside C (loop [7] (chainM I o.pre.1.n o.pre.2.1.n)) q ∧
      (loop [7] (chainM I o.pre.1.n o.pre.2.1.n) q).1 = o.cm) ∧
    (∀ u < 5, ∃ q, Inside C (loop [] (chainC I o.pre.1.n o.pre.2.1.n u)) q ∧
      (loop [] (chainC I o.pre.1.n o.pre.2.1.n u) q).1 = o.cc.getD u dLoop) ∧
    (∃ q, Inside C (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) := by
  unfold qsig at h ⊢
  intro o
  obtain ⟨-, h, e1⟩ := inside_bind h
  obtain ⟨o2, h, e2⟩ := inside_bind h
  obtain ⟨o3, h, e3⟩ := inside_bind h
  obtain ⟨-, h, e4⟩ := inside_bind h
  obtain ⟨o5, -, e5⟩ := inside_bind h
  refine ⟨⟨_, o2, rfl⟩, fun u hu => ?_, ⟨_, o5, rfl⟩⟩
  obtain ⟨q, hq, e⟩ := inside_forN_get o3 u hu
  exact ⟨q, hq, e.symm⟩

/-- The pointer after a loop (QA2's `loop_adv`, LvmQWhirBase). -/
theorem loop_adv' (dims : List Nat) (tpl : List LRow) (p : Ptr) :
    p.adv (loop dims tpl p).2 = ⟨p.k + ltw .K tpl * 2 ^ dims.sum, p.e + ltw .E tpl * 2 ^ dims.sum⟩ := by
  have := mkLoop_tw p dims tpl
  simp only [loop_apply, Ptr.adv, segsW, List.map, Seg.w, this, Block.size, Block.lsize, List.sum_cons,
    List.sum_nil, add_zero]
  simp [mkLoop]

/-- A template row writing `K` comes before the end of the `K` rows. -/
theorem lrank_lt {tpl : List LRow} {t : Nat} (ht : t < tpl.length)
    (hw : LRow.w .K (tpl.getD t default) = 1) : lrank .K tpl t + 1 ≤ ltw .K tpl := by
  unfold lrank ltw
  conv_rhs => rw [← List.take_append_drop t tpl]
  rw [List.map_append, List.sum_append, List.drop_eq_getElem_cons ht, List.map_cons, List.sum_cons]
  rw [List.getD_eq_getElem _ _ ht] at hw
  omega

/-- **A loop's `K` cells lie below the pointer after it.** -/
theorem loop_cell_lt {C : Nat} {dims : List Nat} {tpl : List LRow} {q : Ptr}
    (h : Inside C (loop dims tpl) q) {t jf : Nat} (ht : t < tpl.length)
    (hty : (tpl.getD t default).ty = .K) (hw : LRow.w .K (tpl.getD t default) = 1)
    (hjf : jf < 2 ^ dims.sum) : ((loop dims tpl q).1.cell t jf).n < C := by
  unfold Inside at h
  rw [loop_adv'] at h
  simp only at h
  have hr := lrank_lt ht hw
  simp only [loop_apply, LoopOut.cell, hty, Ptr.at]
  have : ltw .K tpl * jf + ltw .K tpl ≤ ltw .K tpl * 2 ^ dims.sum := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hjf
  omega

/-- Every row of a chain template writes one `K` cell. -/
theorem chainTpl_rows (d0 d1 Z O : Opd) (ots o1 o2 o3 : Nat → Opd) :
    ∀ r ∈ chainTpl d0 d1 Z O ots o1 o2 o3, r.ty = .K ∧ LRow.w .K r = 1 := by
  intro r hr
  simp only [chainTpl, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((((((h | h | h | h) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) | ⟨_, -, h⟩) |
    ⟨_, -, h⟩ <;> subst h <;> exact ⟨rfl, rfl⟩

theorem chainTpl_length (d0 d1 Z O : Opd) (ots o1 o2 o3 : Nat → Opd) :
    (chainTpl d0 d1 Z O ots o1 o2 o3).length = 28 := by
  simp [chainTpl]

theorem pathTpl_rows (I : SigIn) : ∀ r ∈ pathTpl I, r.ty = .K ∧ LRow.w .K r = 1 := by
  intro r hr
  simp only [pathTpl, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with (⟨_, -, h⟩ | ⟨_, -, h⟩) | ⟨_, -, h⟩ <;> subst h <;> exact ⟨rfl, rfl⟩

theorem pathTpl_length (I : SigIn) : (pathTpl I).length = 12 := by simp [pathTpl]

theorem getD_mem {tpl : List LRow} {t : Nat} (ht : t < tpl.length) : tpl.getD t default ∈ tpl := by
  rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht

/-- **Q_sig's chain and path cells lie below the pointer after it.** -/
theorem sigOutLt_qsig {C : Nat} (I : SigIn) (p : Ptr) (hP : (p.adv (qsig I p).2).k ≤ C) :
    SigOutLt C (qsig I p).1 := by
  obtain ⟨⟨q2, h2, e2⟩, h3, ⟨q5, h5, e5⟩⟩ := qsig_inside (C := C) (p := p) (I := I) hP
  constructor
  · intro i hi t ht
    unfold chainCell
    split
    · rw [← e2]
      have ht' : t < (chainM I (qsig I p).1.pre.1.n (qsig I p).1.pre.2.1.n).length := by
        unfold chainM; rw [chainTpl_length]; exact ht
      have hr := chainTpl_rows _ _ _ _ _ _ _ _ _ (getD_mem ht')
      exact loop_cell_lt h2 ht' hr.1 hr.2 (by simp; omega)
    · obtain ⟨q, hq, e⟩ := h3 (i - 128) (by omega)
      rw [← e]
      have ht' : t < (chainC I (qsig I p).1.pre.1.n (qsig I p).1.pre.2.1.n (i - 128)).length := by
        unfold chainC; rw [chainTpl_length]; exact ht
      have hr := chainTpl_rows _ _ _ _ _ _ _ _ _ (getD_mem ht')
      exact loop_cell_lt hq ht' hr.1 hr.2 (by simp)
  · intro t ht c hc
    rw [← e5]
    have hc' : c < (pathTpl I).length := by rw [pathTpl_length]; exact hc
    have hr := pathTpl_rows I _ (getD_mem hc')
    exact loop_cell_lt h5 hc' hr.1 hr.2 (by simp; omega)

/-- **`SigCellsLt` for `Q_sig` placed at `p`**, ending at or below `Q`'s `K` cells. -/
theorem sigCellsLt_qsig {Q : Program} {I : SigIn} {p : Ptr} (bpl : Nat → Nat → Bool × Nat)
    (hR : SigRegLt (Q.cells .K) I) (hP : (p.adv (qsig I p).2).k ≤ Q.cells .K) :
    SigCellsLt Q I (qsig I p).1 bpl :=
  sigCellsLt_of bpl hR (sigOutLt_qsig I p hP)

end Lvm.NS
