-- New for lvm (WP-13a), after FR's `FRXOut` (`trSeg`, `pSeg` and `logWords_trSeg`, `proof_words`;
-- rf-k/submissions/flock-recursive/lean@kk/base): lvm's trace and proof as output segments.
import LvmXOut
import LvmXSeg

/-!
# The child's trace and proof as output segments

`trSegL` and `pSegL` (`LvmXSeg.Seg`) emit, over the stream's lanes, the trace's words and the
reassembled proof's words: per block a constant length word and a copy (`trSegL`), per block the
messages, rows and compared siblings (`pSegL`); an opening is a `rep` over its positions, a
`rep` over its path. **`segOut_trSegL`**: `segOut W κ 0 trSegL = trWords W`;
**`segOut_pSegL`**: `segOut W κ 0 pSegL = pWords W`. **`readTraceL_congr`**: the trace reads
lanes below `T` only.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## Walks -/

/-- A block's query lengths. -/
def lensB (b : Blk) : List ℕ := b.queries.map Prod.snd

/-- The lanes of a run of entries. -/
def lanesOf (l : List ℕ) : ℕ := (l.map fun len => 5 + len / 8).sum

/-- One opened position's lanes: the leaf entry and `path` node entries. -/
def opS (row path : ℕ) : ℕ := 5 + row / 8 + 13 * path

theorem walk_append : ∀ (u : ℕ) (l₁ l₂ : List ℕ),
    walk u (l₁ ++ l₂) = walk u l₁ ++ walk (u + lanesOf l₁) l₂
  | _, [], _ => by simp [lanesOf, walk]
  | u, len :: r, l₂ => by
    simp only [List.cons_append, walk, walk_append _ r l₂, lanesOf, List.map_cons, List.sum_cons]
    congr 3; omega

theorem walk_rep64 : ∀ (w path : ℕ),
    walk w (List.replicate path 64) = (List.range path).map fun h => (w + 13 * h, 64)
  | _, 0 => rfl
  | w, path + 1 => by
    rw [List.replicate_succ, walk, walk_rep64 _ path, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.mul_zero, Nat.add_zero]
    congr 1
    exact List.map_congr_left fun h _ => by simp only [Prod.mk.injEq, and_true]; omega

theorem lanesOf_pos (row path : ℕ) : lanesOf (row :: List.replicate path 64) = opS row path := by
  simp [lanesOf, opS, List.map_replicate, List.sum_replicate]; ring

theorem walk_reps (row path : ℕ) : ∀ (u t : ℕ),
    walk u (List.replicate t (row :: List.replicate path 64)).flatten =
      (List.range t).flatMap fun j => walk (u + opS row path * j) (row :: List.replicate path 64)
  | _, 0 => rfl
  | u, t + 1 => by
    rw [List.replicate_succ, List.flatten_cons, walk_append, lanesOf_pos, walk_reps row path _ t,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.mul_zero, Nat.add_zero]
    congr 1
    exact List.flatMap_congr fun j _ => by congr 1; rw [Nat.succ_eq_add_one]; ring

theorem lensB_opn (t row path : ℕ) :
    lensB (.opn t row path) = (List.replicate t (row :: List.replicate path 64)).flatten := by
  simp [lensB, Blk.queries, List.map_flatten, List.map_replicate]

theorem lanes_eq (b : Blk) : b.lanes = lanesOf (lensB b) := by
  cases b with
  | one c len => simp [Blk.lanes, lensB, Blk.queries, lanesOf] <;> omega
  | opn t row path =>
    rw [lensB_opn, Blk.lanes]
    induction t with
    | zero => simp [lanesOf]
    | succ t ih =>
      rw [List.replicate_succ, List.flatten_cons]
      simp only [lanesOf, List.map_append, List.sum_append] at ih ⊢
      rw [← ih]
      have := lanesOf_pos row path
      simp only [lanesOf] at this
      rw [this, opS]; ring

/-! ## The trace's segment -/

/-- A block's trace segment at lane `u`. -/
def blkTSeg (u : ℕ) : Blk → Seg
  | .one _ len => .cat (.wd (toWord len)) (.cp (u + 1) (len / 8 + 4))
  | .opn t row path => .rep t (opS row path)
      (.cat (.cat (.wd (toWord row)) (.cp (u + 1) (row / 8 + 4)))
        (.rep path 13 (.cat (.wd (toWord 64)) (.cp (u + 6 + row / 8) 12))))

/-- The blocks' trace segments from lane `u`. -/
def blkTSegs : ℕ → List Blk → Seg
  | _, [] => .nil
  | u, b :: bs => .cat (blkTSeg u b) (blkTSegs (u + b.lanes) bs)

/-- **The trace's segment**: the count, `q₀`'s entry, the blocks from lane 6. -/
def trSegL : Seg :=
  .cat (.wd (toWord (qS pX))) (.cat (.wd (toWord 7)) (.cat (.sh8 1) (.cat (.cp 2 4)
    (blkTSegs 6 (blocks pX)))))

theorem segOut_blkTSeg (W : ℕ → Word) (κ : Bool) (b u : ℕ) (blk : Blk) :
    segOut W κ b (blkTSeg u blk) = (walk (b + u) (lensB blk)).flatMap fun x => entW W x.1 x.2 := by
  cases blk with
  | one c len =>
    simp only [blkTSeg, segOut, lensB, Blk.queries, List.map_cons, List.map_nil, walk,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, entW, wsAt, List.singleton_append,
      List.cons.injEq, true_and]
    all_goals exact List.map_congr_left fun j _ => by congr 1 <;> omega
  | opn t row path =>
    rw [lensB_opn, walk_reps, List.flatMap_assoc]
    simp only [blkTSeg, segOut]
    refine List.flatMap_congr fun j _ => ?_
    rw [walk, walk_rep64, List.flatMap_cons, List.flatMap_map]
    generalize opS row path * j = A
    simp only [entW, wsAt, List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq,
      true_and, List.append_cancel_left_eq, show 64 / 8 + 4 = 12 from rfl]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun k _ => by congr 1 <;> omega)
      (List.flatMap_congr fun h _ => ?_)
    simp only [List.cons.injEq, true_and]
    exact List.map_congr_left fun k _ => by congr 1 <;> omega

theorem segOut_blkTSegs (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (u : ℕ) (bs : List Blk),
    segOut W κ b (blkTSegs u bs) =
      (walk (b + u) (bs.flatMap lensB)).flatMap fun x => entW W x.1 x.2
  | _, [] => rfl
  | u, blk :: bs => by
    rw [blkTSegs, segOut, segOut_blkTSeg, segOut_blkTSegs W κ b _ bs, List.flatMap_cons,
      walk_append, List.flatMap_append, lanes_eq, Nat.add_assoc]

theorem lensL_eq : lensL = (blocks pX).flatMap lensB := rfl

/-- **The trace's segment denotes the trace's words.** -/
theorem segOut_trSegL (W : ℕ → Word) (κ : Bool) : segOut W κ 0 trSegL = trWords W := by
  simp only [trSegL, segOut, segOut_blkTSegs, trWords, entL, lensL_eq, wsAt, Nat.zero_add,
    List.singleton_append, List.cons_append, List.nil_append]

/-! ## The proof's segment -/

/-- A block's proof segment at lane `u`. -/
def blkPSeg (u : ℕ) : Blk → Seg
  | .one .seed len => .cp (u + 5) ((len - 32) / 8)
  | .one .fs len => .cp (u + 5) ((len - 32) / 8)
  | .one _ _ => .nil
  | .opn t row path => .rep t (opS row path)
      (.cat (.cp (u + 1) (row / 8)) (.rep path 13 (.sibc (u + 5 + row / 8))))

/-- The blocks' proof segments from lane `u`. -/
def blkPSegs : ℕ → List Blk → Seg
  | _, [] => .nil
  | u, b :: bs => .cat (blkPSeg u b) (blkPSegs (u + b.lanes) bs)

/-- **The proof's segment**: `'S' ‖ 0⁷`, then the blocks' contributions. -/
def pSegL : Seg := .cat (.wd (toWord 0x53)) (blkPSegs 6 (blocks pX))

/-- A block the extractor can reassemble: a seed or FS query (not a node's or a leaf's length), or
an opening of 384- or 512-byte rows. -/
def blkOk : Blk → Bool
  | .one .seed len | .one .fs len => len != 64 && len != 384 && len != 512
  | .one _ _ => false
  | .opn _ row _ => row == 384 || row == 512

/-! The static facts of the segments per block: the kernel checks `okSeg` block by block
(`blocks_segs`) instead of evaluating the segments; the depths are bounded for every block list. -/

private theorem okSeg_blkTSeg (u : ℕ) (b : Blk) : okSeg (blkTSeg u b) = okSeg (blkTSeg 0 b) := by
  cases b <;> simp [blkTSeg, okSeg]

private theorem okSeg_blkPSeg (u : ℕ) (b : Blk) : okSeg (blkPSeg u b) = okSeg (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> simp [blkPSeg, okSeg]
  | opn t row path =>
    simp only [blkPSeg, okSeg]
    rw [decide_eq_true (by omega : 4 ≤ u + 5 + row / 8), decide_eq_true (by omega : 4 ≤ 5 + row / 8)]

private theorem okSeg_blkTSegs : ∀ (u : ℕ) (bs : List Blk),
    okSeg (blkTSegs u bs) = bs.all fun b => okSeg (blkTSeg 0 b)
  | _, [] => rfl
  | u, b :: bs => by rw [blkTSegs, okSeg, okSeg_blkTSeg, okSeg_blkTSegs _ bs, List.all_cons]

private theorem okSeg_blkPSegs : ∀ (u : ℕ) (bs : List Blk),
    okSeg (blkPSegs u bs) = bs.all fun b => okSeg (blkPSeg 0 b)
  | _, [] => rfl
  | u, b :: bs => by rw [blkPSegs, okSeg, okSeg_blkPSeg, okSeg_blkPSegs _ bs, List.all_cons]

private theorem depthSeg_blkTSegs : ∀ (u : ℕ) (bs : List Blk), depthSeg (blkTSegs u bs) ≤ 2
  | _, [] => by simp [blkTSegs, depthSeg]
  | u, b :: bs => by
    rw [blkTSegs, depthSeg]
    refine max_le ?_ (depthSeg_blkTSegs _ bs)
    cases b <;> simp [blkTSeg, depthSeg]

private theorem depthSeg_blkPSegs : ∀ (u : ℕ) (bs : List Blk), depthSeg (blkPSegs u bs) ≤ 2
  | _, [] => by simp [blkPSegs, depthSeg]
  | u, b :: bs => by
    rw [blkPSegs, depthSeg]
    refine max_le ?_ (depthSeg_blkPSegs _ bs)
    cases b with
    | one c len => cases c <;> simp [blkPSeg, depthSeg]
    | opn t row path => simp [blkPSeg, depthSeg]

private theorem blocks_segs : (blocks pX).all (fun b => blkOk b && okSeg (blkTSeg 0 b) &&
    okSeg (blkPSeg 0 b)) = true := by
  decide +kernel

theorem blocks_ok : (blocks pX).all blkOk = true :=
  List.all_eq_true.mpr fun b hb => by
    have := List.all_eq_true.mp blocks_segs b hb
    simp only [Bool.and_eq_true] at this
    exact this.1.1

theorem segOut_blkPSeg (W : ℕ → Word) (κ : Bool) (b u : ℕ) (blk : Blk) (hb : blkOk blk = true) :
    segOut W κ b (blkPSeg u blk) = (walk (b + u) (lensB blk)).flatMap fun x => pieceW W x.1 x.2 := by
  cases blk with
  | one c len =>
    have key : len ≠ 64 ∧ len ≠ 384 ∧ len ≠ 512 → segOut W κ b (.cp (u + 5) ((len - 32) / 8)) =
        (walk (b + u) [len]).flatMap fun x => pieceW W x.1 x.2 := fun ⟨h1, h2, h3⟩ => by
      have hr : ¬ (len = 384 ∨ len = 512) := by omega
      simp only [segOut, walk, List.flatMap_cons, List.flatMap_nil, List.append_nil, pieceW,
        if_neg h1, if_neg hr, wsAt]
      all_goals exact List.map_congr_left fun j _ => by congr 1 <;> omega
    cases c <;> simp only [blkOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    · exact absurd hb (by decide)
    · exact key ⟨hb.1.1, hb.1.2, hb.2⟩
    · exact key ⟨hb.1.1, hb.1.2, hb.2⟩
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
  | opn t row path =>
    simp only [blkOk, Bool.or_eq_true, beq_iff_eq] at hb
    have hr : row ≠ 64 := by omega
    rw [lensB_opn, walk_reps, List.flatMap_assoc]
    simp only [blkPSeg, segOut]
    refine List.flatMap_congr fun j _ => ?_
    rw [walk, walk_rep64, List.flatMap_cons, List.flatMap_map]
    generalize opS row path * j = A
    rw [pieceW, if_neg hr, if_pos hb]
    simp only [wsAt]
    congr 1
    · exact List.map_congr_left fun k _ => by congr 1 <;> omega
    · refine List.flatMap_congr fun h _ => ?_
      rw [pieceW, if_pos rfl, sibWs]
      simp only [wsAt]
      have e1 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 1 + k = b + u + A + 5 + row / 8 + 13 * h + 1 + k :=
        fun k => by omega
      have e2 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) - 4 + k = b + u + A + 5 + row / 8 + 13 * h - 4 + k :=
        fun k => by omega
      have e3 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 5 + k = b + u + A + 5 + row / 8 + 13 * h + 5 + k :=
        fun k => by omega
      simp only [e1, e2, e3]
      exact if_congr Iff.rfl rfl rfl

theorem segOut_blkPSegs (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (u : ℕ) (bs : List Blk),
    bs.all blkOk = true → segOut W κ b (blkPSegs u bs) =
      (walk (b + u) (bs.flatMap lensB)).flatMap fun x => pieceW W x.1 x.2
  | _, [], _ => rfl
  | u, blk :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [blkPSegs, segOut, segOut_blkPSeg W κ b u blk h.1, segOut_blkPSegs W κ b _ bs h.2,
      List.flatMap_cons, walk_append, List.flatMap_append, lanes_eq, Nat.add_assoc]

/-- **The proof's segment denotes the reassembled proof's words.** -/
theorem segOut_pSegL (W : ℕ → Word) (κ : Bool) : segOut W κ 0 pSegL = pWords W := by
  show [toWord 0x53] ++ segOut W κ 0 (blkPSegs 6 (blocks pX)) = _
  rw [segOut_blkPSegs W κ 0 6 _ blocks_ok, Nat.zero_add, pWords, entL, lensL_eq,
    List.singleton_append]

/-! ## The trace reads lanes below `T` only -/

theorem walk_lt : ∀ (u : ℕ) (l : List ℕ), ∀ x ∈ walk u l, u ≤ x.1 ∧ x.1 + 5 + x.2 / 8 ≤ u + lanesOf l
  | _, [], x, hx => by cases hx
  | u, len :: r, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [lanesOf, List.map_cons, List.sum_cons]; omega
    · have := walk_lt _ r x hx
      simp only [lanesOf, List.map_cons, List.sum_cons] at this ⊢; omega

private theorem lanesOf_flatMap : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMap bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

theorem lanes_T : 6 + lanesOf lensL = streamLanes pX := by
  rw [lensL_eq, lanesOf_flatMap]
  exact blocks_sizes.1

theorem entAt_congr {W W' : ℕ → Word} {u len : ℕ} (h : ∀ v < u + 5 + len / 8, W v = W' v) :
    entAt W u len = entAt W' u len := by
  have e1 : wsAt W (u + 1) (len / 8) = wsAt W' (u + 1) (len / 8) :=
    List.map_congr_left fun j hj => h _ (by simp at hj; omega)
  have e2 : wsAt W (u + 1 + len / 8) 4 = wsAt W' (u + 1 + len / 8) 4 :=
    List.map_congr_left fun j hj => h _ (by simp at hj; omega)
  simp only [entAt, e1, e2]

/-- **The trace reads lanes below `T` only.** -/
theorem readTraceL_congr {W W' : ℕ → Word} (h : ∀ v < streamLanes pX, W v = W' v) :
    readTraceL W = readTraceL W' := by
  have hT := lanes_T
  have h6 : ∀ v < 6, W v = W' v := fun v hv => h v (by omega)
  have hq : q0Ent W = q0Ent W' := by
    have e : wsAt W 2 4 = wsAt W' 2 4 := List.map_congr_left fun j hj => h6 _ (by simp at hj; omega)
    simp only [q0Ent, e, h6 1 (by norm_num)]
  unfold readTraceL
  rw [hq]
  refine congrArg _ (List.map_congr_left fun x hx => entAt_congr fun v hv => h v ?_)
  have := walk_lt 6 lensL x hx
  omega

/-! ## Static facts of the two segments -/

theorem segs_ok : okSeg trSegL = true ∧ depthSeg trSegL ≤ 2 ∧ okSeg pSegL = true ∧
    depthSeg pSegL ≤ 2 := by
  have h := List.all_eq_true.mp blocks_segs
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [trSegL, okSeg, okSeg_blkTSegs, Bool.and_eq_true, List.all_eq_true]
    exact ⟨trivial, trivial, trivial, by decide, fun b hb => (h b hb).1.2⟩
  · simp only [trSegL, depthSeg]
    simpa using depthSeg_blkTSegs 6 (blocks pX)
  · simp only [pSegL, okSeg, okSeg_blkPSegs, Bool.and_eq_true, List.all_eq_true]
    exact ⟨trivial, fun b hb => (h b hb).2⟩
  · simp only [pSegL, depthSeg]
    simpa using depthSeg_blkPSegs 6 (blocks pX)

end Lvm.X
