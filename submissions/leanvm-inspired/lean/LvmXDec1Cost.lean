-- lvm2 X-REC2 (helper DEC): the level-1 decoder's well-formedness, cost, a concrete layout and the
-- non-vacuity checks. Adapted from this entry's `LvmXDecCost.lean`.
import LvmXDec1IR2
import LvmXRead1Defs
import LvmXDecCost

/-!
# The level-1 decoder's cost and layout

* `wf_dec1IR`, `noLoopT_dec1IR`, `outs_dec1IR`, `dec1IR_o` (no output statement).
* **`cost_dec1IR_le`**: the level-1 decoder is below `2^31` steps; with the level-1 reads
  (`cost_read1IR_le`) the level adds below `2^32` to v1's `2^37.95`.
* **`dec1Lay_example`**: `w1B = 2^23`, `d1B = 2^23 + 2^21`, `f2B = 2^23 + 2^22`,
  `a1B = 2^19 + 24`, `oB = 2^19 + 64` (v1's `fB`): everything below `2^24` (`memX = 2^25` is
  untouched), disjoint from v1's `decLay_example` (`dB = 2^22` workspace `[2^22, 3·2^21)`, word
  `[2^20, 3·2^20)`, `α₀` `[2^19, 2^19 + 18)`) except the output, which is v1's `f₁` input.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem wf_dec1IR (dB wB aB fB oB : ℕ) : WF (dec1IR dB wB aB fB oB) := by
  have h1 := wf_wtabIR (tbB dB)
  have h2 := wf_eqtIR 4 aB (q1B dB)
  have h3 := fun c => wf_mcpIR (2 ^ 9) (fB + c) 3 (enc1B dB + c * 2 ^ 12)
  have h4 := fun c => wf_zeroIR (2 ^ 12 - 2 ^ 9) (enc1B dB + c * 2 ^ 12 + 2 ^ 9)
  have h5 := wf_fwdIR 12 (tbB dB)
  have h6 := wf_agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)
  have h7 := wf_baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)
  have h8 := wf_bflyIR 9 (tbB dB)
  have n8 := bflyIR_nw_hi 9 (tbB dB) (r := zC) (by decide)
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, WF, Writes,
    Prim.dst, h1, h2, h3, h4, h5, h6, h7, h8, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, rA0, zK, rOk, zT, zN, zC, cTmp, regs, ySr,
    yDs, yStr, yV, yC, yN, yL, yK, yC2, yN2]

theorem noLoopT_dec1IR (dB wB aB fB oB : ℕ) : NoLoopT (dec1IR dB wB aB fB oB) := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, NoLoopT, noLoopT_wtabIR, noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdIR,
    noLoopT_agree1IR, noLoopT_baryIR, noLoopT_bflyIR, and_self]

theorem outs_dec1IR (dB wB aB fB oB t : ℕ) : outs (dec1IR dB wB aB fB oB) t = 0 := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, outs, outs_wtabIR, outs_eqtIR, outs_mcpIR, outs_zeroIR, outs_fwdIR, outs_agree1IR,
    outs_baryIR, outs_bflyIR]
  norm_num

theorem hasOut_dec1IR (dB wB aB fB oB : ℕ) : hasOut (dec1IR dB wB aB fB oB) = false := rfl

/-- **`dec1IR` writes no output.** -/
theorem dec1IR_o (I : Array Word) (s : St) (dB wB aB fB oB : ℕ) :
    (semXIR I (dec1IR dB wB aB fB oB) s).o = s.o := sem_o I _ s (hasOut_dec1IR dB wB aB fB oB)

/-! ## Costs -/

theorem cost_enc1C (dB fB c t : ℕ) : cost (enc1C dB fB c) t = 9058676 := by
  simp only [enc1C, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 12 - 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_fwdIR 12 _ _ (by norm_num) (by norm_num), blkSteps, List.length_cons, List.length_nil]
  norm_num

theorem cost_bfly1All (dB t : ℕ) : cost (bfly1All dB) t = 40598508 := by
  simp only [bfly1All, bfly1Row, cost, cost_bflyIR 9 _ _ (by norm_num) (by norm_num), blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_tr1IR (ob oB t : ℕ) : cost (tr1IR ob oB) t = 334348 := by
  simp only [tr1IR, tr1Row, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 9 < 2 ^ 64 by norm_num), toNat_toWord (show 48 < 2 ^ 64 by norm_num)]
  norm_num

/-- **The level-1 decoder's cost**: `925,440,493` steps (`≈ 2^29.79`; interpolation
`848,495,641`, inverse NTTs `40,598,508`, `Enc₁` `27,176,030`, agreement `8,802,318`). -/
theorem cost_dec1IR (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t = 925440493 := by
  simp only [dec1IR, enc1IR, ok1IR, dec1Tail, cost, cost_wtabIR, cost_eqtIR 4 _ _ _ (by norm_num),
    cost_enc1C, cost_agree1IR, cost_baryIR (2 ^ 9) 48 _ _ _ _ _ _ _ (by norm_num) (by norm_num),
    cost_bfly1All, cost_tr1IR, blkSteps, List.length_cons, List.length_nil]
  norm_num

/-- **The level-1 decoder is below `2^31`** (in fact `2^29.79`). -/
theorem cost_dec1IR_le (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 31 := by
  rw [cost_dec1IR]; norm_num

/-- **The level-1 reads and decoder together are below `2^32`.** -/
theorem dec1_fixed_le (bX pL capW wB dB aB fB oB t : ℕ) :
    cost (read1IR bX pL capW wB) t + cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 32 := by
  have h1 := cost_read1IR_le bX pL capW wB t
  have h2 := cost_dec1IR_le dB wB aB fB oB t
  omega

/-- **A layout** below `2^24` (see the module header). -/
theorem dec1Lay_example (sz : ℕ) (hsz : 2 ^ 25 ≤ sz) :
    Dec1Lay (2 ^ 23 + 2 ^ 21) (2 ^ 23) (2 ^ 19 + 24) (2 ^ 23 + 2 ^ 22) (2 ^ 19 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs]) <;> omega

end Lvm.X
