-- WP-13b: the agreement phase of the `C_rec` decoder (BLUEPRINT §6.2 step 5).
-- adapted from rf-k/submissions/flock-recursive/lean/FRXAgree.lean@8bff272b (`appendIR`, `scanBody`,
-- `scanIR`, `scanBody_sem`, `scanIR_sem`, `scanL_succ`: the append, the per-position step and the scan
-- loop, with FR's flag test replaced by lvm's fold-and-compare); the fold (`macC`, `laneBody`,
-- `foldIR`) and the comparison (`testIR`) are new.
import LvmXDec
import LvmXLoop

/-!
# The agreement set on the machine: the fold, the comparison with `Enc₀(f₁)`, the list

* `agreeIR wB qB eB agB`: for every position `q < 2^15`, the fold's three coordinates
  `Σ_{l<64} eq_c(l)·wd(q, 63 − l)` (`foldC`), compared with the three coordinates of `Enc₀(f₁)[q]`
  at `eB + c·2^15 + q`; the position is appended to the list at `agB` when all three agree
  (`agreeIR_sem`: the count is `|agreeW|` and the list is `agreeW`).
* `agreeW_eq_agreeL`: with the table of `eq(α, ·)` and `Enc₀(f₁)`'s coordinates, `agreeW` is the
  pure decoder's `agreeL` (`mkE` is injective).

The table of `eq(α, l)`'s coordinates (`qB + 3l + c`) is `LvmXEqT`'s. Registers `188 … 205`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-! ## Registers -/

/-- The position `q`. -/ def gQ : ℕ := 188
/-- The word pointer. -/ def gPw : ℕ := 189
/-- The table pointer. -/ def gPe : ℕ := 190
/-- Accumulator, coordinate 0. -/ def gA0 : ℕ := 191
/-- Accumulator, coordinate 1. -/ def gA1 : ℕ := 192
/-- Accumulator, coordinate 2. -/ def gA2 : ℕ := 193
/-- A word of `wd`. -/ def gV : ℕ := 194
/-- A table coordinate. -/ def gE : ℕ := 195
/-- A product. -/ def gT : ℕ := 196
/-- An address. -/ def gX : ℕ := 197
/-- The agreement flag. -/ def gZ : ℕ := 198
/-- A second flag. -/ def gZ2 : ℕ := 199
/-- The count of listed positions. -/ def gCnt : ℕ := 200
/-- Constant scratch. -/ def gK : ℕ := 201
/-- The outer loop's counter. -/ def gC1 : ℕ := 202
/-- Its count. -/ def gN1 : ℕ := 203
/-- The inner loop's counter. -/ def gC2 : ℕ := 204
/-- Its count. -/ def gN2 : ℕ := 205

/-! ## The fold at a position -/

/-- One coordinate's multiply-accumulate: `gE := M[gPe]`, `a ^= gE · gV`, `gPe += 1`. -/
def macC (a : ℕ) : XIR :=
  .seq (.load gE gPe) (.blk (mulKC gT gE gV ++ [.op .xor a a gT, .op .add gPe gPe cOne]))

/-- One lane: `gV := M[gPw]`, `gPw −= 1`, the three coordinates. -/
def laneBody : XIR :=
  .seq (.load gV gPw) (.seq (.blk [.op .sub gPw gPw cOne]) (.seq (macC gA0) (.seq (macC gA1)
    (macC gA2))))

/-- **The fold at the position `gQ`**: `gA_c := Σ_{l<64} eq_c(l) · wd(q, 63 − l)`. -/
def foldIR (wB qB : ℕ) : XIR :=
  .seq (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64, .op .mul gPw gQ gK,
      .const gK (toWord (wB + 63)), .op .add gPw gPw gK, .const gPe (toWord qB), .const gN2 64])
    (.loopK gC2 gN2 64 laneBody)

/-! ## The comparison, the append, the scan -/

/-- **The comparison** with `Enc₀(f₁)[q]`'s coordinates at `eB + c·2^15 + q`:
`gZ := [all three equal]`. -/
def testIR (eB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord eB), .op .add gX gQ gK]) (.seq (.load gE gX)
    (.seq (.blk [.op .eq gZ gE gA0, .const gK (toWord (2 ^ 15)), .op .add gX gX gK])
      (.seq (.load gE gX) (.seq (.blk [.op .eq gZ2 gE gA1, .op .and gZ gZ gZ2, .op .add gX gX gK])
        (.seq (.load gE gX) (.blk [.op .eq gZ2 gE gA2, .op .and gZ gZ gZ2]))))))

/-- The listing step: `M[agB + cnt] := q`, `cnt += 1`. -/
def appendIR (agB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord agB), .op .add gX gCnt gK])
    (.seq (.store gX gQ) (.blk [.op .add gCnt gCnt cOne]))

/-- **One position**: the fold, the comparison, the append, `q += 1`. -/
def posBody (wB qB eB agB : ℕ) : XIR :=
  .seq (foldIR wB qB) (.seq (testIR eB) (.seq (.ite gZ (appendIR agB) (.blk []))
    (.blk [.op .add gQ gQ cOne])))

/-- **The agreement scan** over the positions `q < 2^15`. -/
def agreeIR (wB qB eB agB : ℕ) : XIR :=
  .seq (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))])
    (.loopK gC1 gN1 (toWord (2 ^ 15)) (posBody wB qB eB agB))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_agreeIR (wB qB eB agB : ℕ) : WF (agreeIR wB qB eB agB) := by
  simp +decide [agreeIR, posBody, foldIR, laneBody, macC, testIR, appendIR, mulKC, redC, WF,
    Writes, Prim.dst, gQ, gPw, gPe, gA0, gA1, gA2, gV, gE, gT, gX, gZ, gZ2, gCnt, gK, gC1, gN1,
    gC2, gN2, cTmp, regs]

theorem noLoopT_agreeIR (wB qB eB agB : ℕ) : NoLoopT (agreeIR wB qB eB agB) := by
  simp [agreeIR, posBody, foldIR, laneBody, macC, testIR, appendIR, NoLoopT]

theorem outs_agreeIR (wB qB eB agB t : ℕ) : outs (agreeIR wB qB eB agB) t = 0 := by
  simp [agreeIR, posBody, foldIR, laneBody, macC, testIR, appendIR, outs]

theorem cost_posBody (wB qB eB agB t : ℕ) : cost (posBody wB qB eB agB) t = 4290 := by
  simp only [posBody, foldIR, laneBody, macC, testIR, appendIR, cost, blkSteps, mulKC, redC,
    List.length_cons, List.length_nil, List.cons_append, List.nil_append]
  norm_num

/-- **The agreement scan's cost**: `2^15` positions of `4,290` steps (`≈ 2^27.1`). -/
theorem cost_agreeIR (wB qB eB agB t : ℕ) :
    cost (agreeIR wB qB eB agB) t = 140673038 := by
  simp only [agreeIR, cost, cost_posBody, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 15 < 2 ^ 64 by norm_num)]
  norm_num

/-! ## Word helpers -/

theorem wK_inj {x y : Word} : wK x = wK y ↔ x = y :=
  ⟨fun h => by simpa [wK] using congrArg BF64.toBitVec h, fun h => h ▸ rfl⟩

theorem sem_blk' (I : Array Word) (ps : List Prim) (s : St) :
    semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ := rfl

/-- A block keeps every cell it does not name as a destination. -/
theorem rd_blk_of_not_dst (I : Array Word) (ps : List Prim) (s : St) {r : ℕ}
    (h : ∀ p ∈ ps, p.dst ≠ r) : rd (semXIR I (.blk ps) s).M r = rd s.M r :=
  rd_runPrims_of_not_writes h s.M

/-! ## The fold: one coordinate, one lane, the lane loop -/

/-- **One coordinate's multiply-accumulate**: `a += M[pe] · gV` (in `K`), `gPe := pe + 1`. -/
theorem macC_sem (I : Array Word) (s : St) (hM : Inv s.M) {a pe : ℕ}
    (ha : a = gA0 ∨ a = gA1 ∨ a = gA2) (hpe : pe + 1 < 2 ^ 64) (hP : rd s.M gPe = toWord pe) :
    rdK (semXIR I (macC a) s).M a = rdK s.M a + rdK s.M pe * rdK s.M gV ∧
    rd (semXIR I (macC a) s).M gPe = toWord (pe + 1) ∧
    (∀ r, r ≠ a → r ≠ gPe → r ≠ gE → r ≠ gT → (r < 5 ∨ 9 ≤ r) →
      rd (semXIR I (macC a) s).M r = rd s.M r) ∧
    Inv (semXIR I (macC a) s).M := by
  have hs := hM.1
  have ha9 : 9 ≤ a ∧ a < regs ∧ a ≠ gPe ∧ a ≠ gE ∧ a ≠ gT ∧ a ≠ gV := by
    rcases ha with rfl | rfl | rfl <;> decide
  rw [macC, semXIR_seq]
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM (d := gE) (p := gPe) (by decide) (by decide) hP
    (by omega)
  generalize semXIR I (.load gE gPe) s = s1 at l1 l2 hM1
  rw [sem_blk', runPrims_append]
  have m1 := mulKC_spec hM1 (d := gT) (a := gE) (b := gV) (by decide) (by decide) (by decide)
    (by decide)
  have m2 : ∀ i, (i < 5 ∨ 9 ≤ i) → i ≠ gT → rd (runPrims (mulKC gT gE gV) s1.M) i = rd s1.M i :=
    fun i h1 h2 => mulKC_frame _ _ _ h1 h2 _
  have hM2 := mulKC_inv gT gE gV (by decide) hM1
  generalize runPrims (mulKC gT gE gV) s1.M = M2 at m1 m2 hM2
  have hs2 := hM2.1
  have h1 : rd M2 cOne = 1 := hM2.2 0 (by decide)
  simp only [regs] at hs hs2 ha9
  refine ⟨?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, ?_⟩
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rdK, rd_set_ne (Ne.symm ha9.2.2.1), rd_set_self (by omega), eval_xor, wK_xor]
    rw [show wK (rd M2 a) = rdK s.M a by
          rw [m2 a (.inr ha9.1) ha9.2.2.2.2.1, l2 a ha9.2.2.2.1]; rfl,
      show wK (rd M2 gT) = rdK s.M pe * rdK s.M gV by
          rw [show wK (rd M2 gT) = rdK M2 gT from rfl, m1]
          simp only [rdK]
          rw [l1, l2 gV (by decide)]]
  · simp only [runPrims, List.foldl, Prim.run]
    have hac : a ≠ cOne := by simp only [cOne]; omega
    rw [rd_set_self (by simp only [size_set, gPe]; omega), rd_set_ne ha9.2.2.1,
      m2 _ (by decide) (by decide), l2 _ (by decide), hP, rd_set_ne hac, h1,
      add_one_toWord]
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (Ne.symm r2), rd_set_ne (Ne.symm r1), m2 r r5 r4, l2 r r3]
  · simp only [runPrims, List.foldl, Prim.run]
    exact inv_of_frame hM2 (by simp) fun i hi => by
      rw [rd_set_ne (by simp only [gPe]; omega), rd_set_ne (by omega)]

/-- **One lane**: `gV := M[pw]`, the three accumulators `+= M[pe + c] · M[pw]`, `gPw := pw − 1`,
`gPe := pe + 3`. -/
theorem laneBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {pw pe : ℕ} (hpwR : regs ≤ pw)
    (hpw : pw < 2 ^ 64) (hpeR : regs ≤ pe) (hpe : pe + 3 < 2 ^ 64)
    (hW : rd s.M gPw = toWord pw) (hP : rd s.M gPe = toWord pe) :
    rdK (semXIR I laneBody s).M gA0 = rdK s.M gA0 + rdK s.M pe * rdK s.M pw ∧
    rdK (semXIR I laneBody s).M gA1 = rdK s.M gA1 + rdK s.M (pe + 1) * rdK s.M pw ∧
    rdK (semXIR I laneBody s).M gA2 = rdK s.M gA2 + rdK s.M (pe + 2) * rdK s.M pw ∧
    rd (semXIR I laneBody s).M gPw = toWord (pw - 1) ∧
    rd (semXIR I laneBody s).M gPe = toWord (pe + 3) ∧
    (∀ r, r ≠ gA0 → r ≠ gA1 → r ≠ gA2 → r ≠ gPe → r ≠ gPw → r ≠ gV → r ≠ gE → r ≠ gT →
      (r < 5 ∨ 9 ≤ r) → rd (semXIR I laneBody s).M r = rd s.M r) ∧
    Inv (semXIR I laneBody s).M := by
  have hs := hM.1
  simp only [regs] at hs hpwR hpeR
  rw [laneBody, semXIR_seq]
  obtain ⟨v1, v2, hM1⟩ := load_sem I s hM (d := gV) (p := gPw) (by decide) (by decide) hW hpw
  generalize semXIR I (.load gV gPw) s = s1 at v1 v2 hM1
  rw [semXIR_seq]
  have h1 : rd s1.M cOne = 1 := hM1.2 0 (by decide)
  have hs1 := hM1.1
  simp only [regs] at hs1
  have b1 : rd (semXIR I (.blk [.op .sub gPw gPw cOne]) s1).M gPw = toWord (pw - 1) := by
    rw [sem_blk']
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gPw]; omega), v2 _ (by decide), hW, h1,
      show (1 : Word) = toWord 1 from rfl, sub_toWord hpw (by omega)]
  have b2 : ∀ r, r ≠ gPw → rd (semXIR I (.blk [.op .sub gPw gPw cOne]) s1).M r = rd s1.M r :=
    fun r hr => by
      rw [sem_blk']; exact rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hr) _
  have hM2 := inv_sem I (P := .blk [.op .sub gPw gPw cOne]) (by simp +decide [WF, Prim.dst, gPw])
    hM1
  generalize semXIR I (.blk [.op .sub gPw gPw cOne]) s1 = s2 at b1 b2 hM2
  have e2 : ∀ r, r ≠ gPw → r ≠ gV → rd s2.M r = rd s.M r := fun r h1 h2 =>
    (b2 r h1).trans (v2 r h2)
  rw [semXIR_seq]
  obtain ⟨c1, c2, c3, hM3⟩ := macC_sem I s2 hM2 (a := gA0) (pe := pe) (.inl rfl) (by omega)
    (by rw [e2 _ (by decide) (by decide), hP])
  generalize semXIR I (macC gA0) s2 = s3 at c1 c2 c3 hM3
  rw [semXIR_seq]
  obtain ⟨d1, d2, d3, hM4⟩ := macC_sem I s3 hM3 (a := gA1) (pe := pe + 1) (.inr (.inl rfl))
    (by omega) c2
  generalize semXIR I (macC gA1) s3 = s4 at d1 d2 d3 hM4
  obtain ⟨f1, f2, f3, hM5⟩ := macC_sem I s4 hM4 (a := gA2) (pe := pe + 1 + 1)
    (.inr (.inr rfl)) (by omega) d2
  generalize semXIR I (macC gA2) s4 = s5 at f1 f2 f3 hM5
  -- the frames of the three coordinates
  have fr : ∀ r, r ≠ gA0 → r ≠ gA1 → r ≠ gA2 → r ≠ gPe → r ≠ gE → r ≠ gT → (r < 5 ∨ 9 ≤ r) →
      rd s5.M r = rd s2.M r := fun r a0 a1 a2 a3 a4 a5 a6 =>
    (f3 r a2 a3 a4 a5 a6).trans ((d3 r a1 a3 a4 a5 a6).trans (c3 r a0 a3 a4 a5 a6))
  have hV : rdK s4.M gV = rdK s.M pw := by
    simp only [rdK]
    rw [d3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      c3 _ (by decide) (by decide) (by decide) (by decide) (by decide), b2 _ (by decide), v1]
  have hV3 : rdK s3.M gV = rdK s.M pw := by
    simp only [rdK]
    rw [c3 _ (by decide) (by decide) (by decide) (by decide) (by decide), b2 _ (by decide), v1]
  have hV2 : rdK s2.M gV = rdK s.M pw := by simp only [rdK]; rw [b2 _ (by decide), v1]
  have hpeK : ∀ j, regs ≤ j → rdK s2.M j = rdK s.M j := fun j hj => by
    simp only [rdK]; rw [e2 j (by simp only [gPw, regs] at *; omega) (by simp only [gV, regs] at *; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r r0 r1 r2 r3 r4 r5 r6 r7 r8 => ?_, hM5⟩
  · rw [show rdK s5.M gA0 = rdK s3.M gA0 by
        simp only [rdK]; rw [f3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
          d3 _ (by decide) (by decide) (by decide) (by decide) (by decide)],
      c1, hV2, hpeK pe (by simp only [regs]; omega)]
    simp only [rdK]; rw [e2 _ (by decide) (by decide)]
  · rw [show rdK s5.M gA1 = rdK s4.M gA1 by
        simp only [rdK]; rw [f3 _ (by decide) (by decide) (by decide) (by decide) (by decide)],
      d1, hV3]
    have q1 : rdK s3.M (pe + 1) = rdK s.M (pe + 1) := by
      rw [← hpeK (pe + 1) (by simp only [regs]; omega)]
      simp only [rdK]
      rw [c3 _ (by simp only [gA0]; omega) (by simp only [gPe]; omega) (by simp only [gE]; omega)
        (by simp only [gT]; omega) (by omega)]
    have q2 : rdK s3.M gA1 = rdK s.M gA1 := by
      simp only [rdK]
      rw [c3 _ (by decide) (by decide) (by decide) (by decide) (by decide), e2 _ (by decide) (by decide)]
    rw [q1, q2]
  · rw [f1, hV]
    have q1 : rdK s4.M (pe + 1 + 1) = rdK s.M (pe + 2) := by
      rw [← hpeK (pe + 2) (by simp only [regs]; omega)]
      simp only [rdK]
      rw [d3 _ (by simp only [gA1]; omega) (by simp only [gPe]; omega) (by simp only [gE]; omega)
        (by simp only [gT]; omega) (by omega),
        c3 _ (by simp only [gA0]; omega) (by simp only [gPe]; omega) (by simp only [gE]; omega)
        (by simp only [gT]; omega) (by omega)]
    have q2 : rdK s4.M gA2 = rdK s.M gA2 := by
      simp only [rdK]
      rw [d3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        c3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        e2 _ (by decide) (by decide)]
    rw [q1, q2]
  · rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      b1]
  · rw [f2]
  · rw [fr r r0 r1 r2 r3 r6 r7 r8, e2 r r4 r5]

/-- The fold's coordinate `c` at position `q` over the lanes `l < j`: `Σ_{l<j} e_c(l)·wd(q, 63 − l)`
with the table at `qB + 3l + c` and the word at `wB + 64q + t`. -/
def foldPM (M : Mem) (wB qB q c j : ℕ) : BF64 :=
  ∑ l ∈ range j, rdK M (qB + 3 * l + c) * rdK M (wB + 64 * q + (63 - l))

/-- The registers and cells `foldIR` keeps. -/
def KeepF (r : ℕ) : Prop :=
  r ≠ gA0 ∧ r ≠ gA1 ∧ r ≠ gA2 ∧ r ≠ gPe ∧ r ≠ gPw ∧ r ≠ gV ∧ r ≠ gE ∧ r ≠ gT ∧ r ≠ gK ∧
    r ≠ gC2 ∧ r ≠ gN2 ∧ r ≠ cTmp ∧ (r < 5 ∨ 9 ≤ r)

theorem keepF_of_regs {r : ℕ} (h : regs ≤ r) : KeepF r := by
  simp only [KeepF, regs, gA0, gA1, gA2, gPe, gPw, gV, gE, gT, gK, gC2, gN2, cTmp] at *; omega

theorem rdK_zero : wK 0 = 0 := rfl

/-- **The fold at the position `q`** (`gQ = q`): the three accumulators hold `foldPM … 64`;
the heap and the registers outside the fold's are kept. -/
theorem foldIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB q : ℕ} (hwB : regs ≤ wB)
    (hq : q < 2 ^ 15) (hwB2 : wB + 2 ^ 21 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (hQ : rd s.M gQ = toWord q) :
    (∀ c < 3, rdK (semXIR I (foldIR wB qB) s).M (gA0 + c) = foldPM s.M wB qB q c 64) ∧
    (∀ r, KeepF r → rd (semXIR I (foldIR wB qB) s).M r = rd s.M r) ∧
    Inv (semXIR I (foldIR wB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB
  have hpw : wB + 64 * q + 63 < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64, .op .mul gPw gQ gK,
      .const gK (toWord (wB + 63)), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 64]) := by
    simp +decide [WF, Prim.dst, gA0, gA1, gA2, gK, gPw, gPe, gN2]
  have hM0 := inv_sem I w0 hM
  rw [foldIR, semXIR_seq]
  have r0 : rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gPw = toWord (wB + 64 * q + 63) ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gPe = toWord qB ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gN2 = toWord 64 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA0 = 0 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA1 = 0 ∧
      rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
        .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
        .const gPe (toWord qB), .const gN2 64]) s).M gA2 = 0 := by
    rw [sem_blk']
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gA0, gA1, gA2, gK, gPw, gPe, gN2]; omega))
      only [rd_set_self, rd_set_ne]
    · rw [hQ, show (64 : Word) = toWord 64 from rfl, mul_toWord, add_toWord]
      congr 1; ring
    · rfl
  have k0 : ∀ r, KeepF r → rd (semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0,
      .const gK 64, .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
      .const gPe (toWord qB), .const gN2 64]) s).M r = rd s.M r := fun r hr => by
    simp only [KeepF, gA0, gA1, gA2, gPe, gPw, gV, gE, gT, gK, gC2, gN2, cTmp] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, gA0, gA1, gA2, gPe, gPw, gK, gN2] <;> omega
  generalize semXIR I (.blk [.const gA0 0, .const gA1 0, .const gA2 0, .const gK 64,
    .op .mul gPw gQ gK, .const gK (toWord (wB + 63)), .op .add gPw gPw gK,
    .const gPe (toWord qB), .const gN2 64]) s = s0 at hM0 r0 k0
  obtain ⟨p0, e0, n0, a0, a1, a2⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧
    rd s'.M gPw = toWord (wB + 64 * q + 63 - j) ∧ rd s'.M gPe = toWord (qB + 3 * j) ∧
    rdK s'.M gA0 = foldPM s.M wB qB q 0 j ∧ rdK s'.M gA1 = foldPM s.M wB qB q 1 j ∧
    rdK s'.M gA2 = foldPM s.M wB qB q 2 j ∧ (∀ r, KeepF r → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC2 gN2 (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0, Nat.sub_zero]
    · rw [hE _ (by decide) (by decide), e0, Nat.mul_zero, Nat.add_zero]
    · rw [rdK, hE _ (by decide) (by decide), a0]; rfl
    · rw [rdK, hE _ (by decide) (by decide), a1]; rfl
    · rw [rdK, hE _ (by decide) (by decide), a2]; rfl
    · rw [hE _ hr.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2.1, k0 r hr]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS gC2 (semXIR I laneBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hK : ∀ x, regs ≤ x → rdK s'.M x = rdK s.M x := fun x hx => by
      simp only [rdK]; rw [i7 x (keepF_of_regs hx)]
    obtain ⟨l1, l2, l3, l4, l5, l6, hM'⟩ := laneBody_sem I s' i1 (pw := wB + 64 * q + 63 - j)
      (pe := qB + 3 * j) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
      (by omega) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I laneBody s')).M x =
        rd (semXIR I laneBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hpw : wB + 64 * q + 63 - j = wB + 64 * q + (63 - j) := by omega
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l4, show wB + 64 * q + 63 - j - 1 = wB + 64 * q + 63 - (j + 1) by omega]
    · rw [hd _ (by decide), l5, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA0 = rdK (semXIR I laneBody s').M gA0 by
        simp only [rdK]; rw [hd _ (by decide)], l1, i4, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw, Nat.add_zero]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA1 = rdK (semXIR I laneBody s').M gA1 by
        simp only [rdK]; rw [hd _ (by decide)], l2, i5, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw]
    · rw [show rdK (decS gC2 (semXIR I laneBody s')).M gA2 = rdK (semXIR I laneBody s').M gA2 by
        simp only [rdK]; rw [hd _ (by decide)], l3, i6, foldPM, foldPM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega), hpw]
    · have hr' := hr
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, -, r9, -, -, r12⟩ := hr'
      rw [hd _ r9, l6 r r0 r1 r2 r3 r4 r5 r6 r7 r12, i7 r hr]
  have hfin := loopK_run I laneBody P s0 hM0 (c := gC2) (n := gN2) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  obtain ⟨f1, -, -, f4, f5, f6, f7⟩ := hfin
  refine ⟨fun c hc => ?_, f7, f1⟩
  interval_cases c
  · exact f4
  · exact f5
  · exact f6

/-! ## The comparison and the append -/

theorem lo_testIR (eB : ℕ) : LoK (testIR eB) := by
  simp +decide [testIR, LoK, Prim.dst, gK, gX, gE, gZ, gZ2, regs]

/-- **The comparison**: `gZ` is `1` iff the three accumulators equal the three words of
`Enc₀(f₁)[q]`'s coordinates (`eB + c·2^15 + q`); only `gK, gX, gE, gZ, gZ2` change. -/
theorem testIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {eB q : ℕ} (heB : regs ≤ eB)
    (hq : q < 2 ^ 15) (heB2 : eB + 3 * 2 ^ 15 < 2 ^ 64) (hQ : rd s.M gQ = toWord q) :
    rd (semXIR I (testIR eB) s).M gZ =
      bW (decide (rd s.M (eB + q) = rd s.M gA0) && decide (rd s.M (eB + 2 ^ 15 + q) = rd s.M gA1) &&
        decide (rd s.M (eB + 2 * 2 ^ 15 + q) = rd s.M gA2)) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gE → r ≠ gZ → r ≠ gZ2 → rd (semXIR I (testIR eB) s).M r = rd s.M r) ∧
    Inv (semXIR I (testIR eB) s).M := by
  have hs := hM.1
  simp only [regs] at hs heB
  have hw : WF (testIR eB) := by simp +decide [testIR, WF, Prim.dst, gK, gX, gE, gZ, gZ2]
  refine ⟨?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I hw hM⟩
  · simp only [testIR, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, gA0, gA1, gA2]; omega)) only [rd_set_self, rd_set_ne]
    rw [hQ, add_toWord, toNat_toWord (by omega), add_toWord, toNat_toWord (by omega), add_toWord,
      toNat_toWord (by omega)]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, gA0, gA1, gA2]; omega)) only [rd_set_self, rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (testIR eB) s hw hM r hr ?_
      simp only [testIR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      omega
    · exact hframeK I (testIR eB) s (lo_testIR eB) r (by omega)

/-- **The append**: `M[agB + c] := gQ`, `gCnt := c + 1`; only `gK`, `gX`, `gCnt`, `cTmp` and the
cell change. -/
theorem appendIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {agB c : ℕ} (hagB : regs ≤ agB)
    (hc2 : agB + c < 2 ^ 64) (hcs : agB + c < s.M.size) (hc1 : c + 1 < 2 ^ 64)
    (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (appendIR agB) s).M (agB + c) = rd s.M gQ ∧
    rd (semXIR I (appendIR agB) s).M gCnt = toWord (c + 1) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gCnt → r ≠ cTmp → r ≠ agB + c →
      rd (semXIR I (appendIR agB) s).M r = rd s.M r) ∧
    Inv (semXIR I (appendIR agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hagB
  rw [appendIR, semXIR_seq]
  have a1 : rd (semXIR I (.blk [.const gK (toWord agB), .op .add gX gCnt gK]) s).M gX =
      toWord (agB + c) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, gK, gX, gCnt]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, add_toWord, Nat.add_comm]
  have b1 : ∀ r, r ≠ gK → r ≠ gX → rd (semXIR I (.blk [.const gK (toWord agB),
      .op .add gX gCnt gK]) s).M r = rd s.M r := fun r h1 h2 =>
    rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hM1 := inv_sem I (P := .blk [.const gK (toWord agB), .op .add gX gCnt gK])
    (by simp +decide [WF, Prim.dst, gK, gX]) hM
  have z1 := size_sem I (.blk [.const gK (toWord agB), .op .add gX gCnt gK]) s
  generalize semXIR I (.blk [.const gK (toWord agB), .op .add gX gCnt gK]) s = s1 at a1 b1 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := gX) (v := gQ) (x := agB + c) (by decide)
    (by decide) a1 (by simp only [regs]; omega) hc2 (by omega)
  have z2 := size_sem I (.store gX gQ) s1
  generalize semXIR I (.store gX gQ) s1 = s2 at c1 c2 hM2 z2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; omega
  refine ⟨?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, ?_⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, gCnt]; omega), c1,
      b1 _ (by decide) (by decide)]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gCnt]; omega), c2 _ (hagc _ (by decide)) (by decide),
      b1 _ (by decide) (by decide), hC, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
      add_one_toWord]
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm r3), c2 r r5 r4, b1 r r1 r2]
  · exact inv_sem I (P := .blk [.op .add gCnt gCnt cOne]) (by simp +decide [WF, Prim.dst, gCnt])
      hM2

/-- The fold and `Enc₀(f₁)`'s three coordinates agree at `q` (memory `M`, the machine's test). -/
abbrev AgreeP (M : Mem) (wB qB eB q : ℕ) : Prop :=
  wK (rd M (eB + q)) = foldPM M wB qB q 0 64 ∧ wK (rd M (eB + 2 ^ 15 + q)) = foldPM M wB qB q 1 64 ∧
    wK (rd M (eB + 2 * 2 ^ 15 + q)) = foldPM M wB qB q 2 64

/-- **The machine's agreement list** below `n`. -/
def agreeM (M : Mem) (wB qB eB n : ℕ) : List ℕ :=
  (List.range n).filter fun q => decide (AgreeP M wB qB eB q)

theorem keepF_gQ : KeepF gQ := by unfold KeepF; decide
theorem keepF_gCnt : KeepF gCnt := by unfold KeepF; decide

theorem bW_true_ne : bW true ≠ 0 := by decide
theorem bW_false_eq : bW false = 0 := rfl

/-- **One position**: `q` is listed at `agB + c` iff the fold agrees with `Enc₀(f₁)` at `q`;
`gQ := q + 1`; the heap outside the listed cell is kept. -/
theorem posBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB q c : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 15 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 15 < 2 ^ 64) (hags : agB + 2 ^ 15 ≤ s.M.size)
    (hq : q < 2 ^ 15) (hcq : c ≤ q) (hQ : rd s.M gQ = toWord q) (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (posBody wB qB eB agB) s).M gQ = toWord (q + 1) ∧
    (if AgreeP s.M wB qB eB q then
      rd (semXIR I (posBody wB qB eB agB) s).M gCnt = toWord (c + 1) ∧
        rd (semXIR I (posBody wB qB eB agB) s).M (agB + c) = toWord q ∧
        ∀ x, regs ≤ x → x ≠ agB + c → rd (semXIR I (posBody wB qB eB agB) s).M x = rd s.M x
    else
      rd (semXIR I (posBody wB qB eB agB) s).M gCnt = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (posBody wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (posBody wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  rw [posBody, semXIR_seq]
  obtain ⟨f1, f2, hM1⟩ := foldIR_sem I s hM (wB := wB) (qB := qB) (by simp only [regs]; omega) hq
    hwB2 (by simp only [regs]; omega) hqB2 hQ
  have z1 := size_sem I (foldIR wB qB) s
  generalize semXIR I (foldIR wB qB) s = s1 at f1 f2 hM1 z1
  have q1 : rd s1.M gQ = toWord q := (f2 gQ keepF_gQ).trans hQ
  have c1 : rd s1.M gCnt = toWord c := (f2 gCnt keepF_gCnt).trans hC
  have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => f2 x (keepF_of_regs hx)
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM2⟩ := testIR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq heB2 q1
  have z2 := size_sem I (testIR eB) s1
  generalize semXIR I (testIR eB) s1 = s2 at t1 t2 hM2 z2
  -- the flag is the test
  have f10 : wK (rd s1.M gA0) = foldPM s.M wB qB q 0 64 := f1 0 (by norm_num)
  have f11 : wK (rd s1.M gA1) = foldPM s.M wB qB q 1 64 := f1 1 (by norm_num)
  have f12 : wK (rd s1.M gA2) = foldPM s.M wB qB q 2 64 := f1 2 (by norm_num)
  have e : ∀ a b, regs ≤ a → wK (rd s1.M b) = foldPM s.M wB qB q (b - gA0) 64 →
      (rd s1.M a = rd s1.M b ↔ wK (rd s.M a) = foldPM s.M wB qB q (b - gA0) 64) := by
    intro a b ha hb
    rw [← wK_inj, h1 a ha, hb]
  have hZ : rd s2.M gZ = bW (decide (AgreeP s.M wB qB eB q)) := by
    rw [t1]
    congr 1
    simp only [AgreeP, Bool.decide_and]
    rw [decide_eq_decide.2 (e _ gA0 (by simp only [regs]; omega) f10),
      decide_eq_decide.2 (e _ gA1 (by simp only [regs]; omega) f11),
      decide_eq_decide.2 (e _ gA2 (by simp only [regs]; omega) f12), Bool.and_assoc]
    rfl
  have q2 : rd s2.M gQ = toWord q := (t2 gQ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans q1
  have c2 : rd s2.M gCnt = toWord c := (t2 gCnt (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans c1
  have h2 : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [t2 x (by simp only [gK]; omega) (by simp only [gX]; omega) (by simp only [gE]; omega)
      (by simp only [gZ]; omega) (by simp only [gZ2]; omega), h1 x (by simp only [regs]; omega)]
  -- `q += 1`
  have fin : ∀ s3 : St, Inv s3.M → rd s3.M gQ = toWord q →
      rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M gQ = toWord (q + 1) ∧
      (∀ x, x ≠ gQ → rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M x = rd s3.M x) ∧
      Inv (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M := fun s3 h3 hq3 => by
    have := h3.1; simp only [regs] at this
    refine ⟨?_, fun x hx => rd_blk_of_not_dst I _ s3 (by simp [Prim.dst]; exact Ne.symm hx),
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF, Prim.dst, gQ]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; omega), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : AgreeP s.M wB qB eB q
  · rw [decide_eq_true hb, if_neg bW_true_ne, if_pos hb]
    obtain ⟨a1, a2, a3, hM3⟩ := appendIR_sem I s2 hM2 (agB := agB) (c := c)
      (by simp only [regs]; omega) (by omega) (by omega) (by omega) c2
    generalize semXIR I (appendIR agB) s2 = s3 at a1 a2 a3 hM3
    have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; omega
    obtain ⟨g1, g2, hM4⟩ := fin s3 hM3 (by
      rw [a3 gQ (by decide) (by decide) (by decide) (by decide) (hagc _ (by decide)), q2])
    refine ⟨g1, ⟨?_, ?_, fun x hx hx2 => ?_⟩, hM4⟩
    · rw [g2 _ (by decide), a2]
    · rw [g2 _ (Ne.symm (hagc _ (by decide))), a1, q2]
    · simp only [regs] at hx
      rw [g2 x (by simp only [gQ]; omega), a3 x (by simp only [gK]; omega) (by simp only [gX]; omega)
        (by simp only [gCnt]; omega) (by simp only [cTmp]; omega) hx2, h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; omega), h2 x (by simp only [regs]; omega)]

theorem agreeM_succ (M : Mem) (wB qB eB n : ℕ) : agreeM M wB qB eB (n + 1) =
    agreeM M wB qB eB n ++ if AgreeP M wB qB eB n then [n] else [] := by
  rw [agreeM, agreeM, List.range_succ, List.filter_append]
  congr 1
  by_cases h : AgreeP M wB qB eB n
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, decide_eq_false h]; rfl

theorem length_agreeM_le (M : Mem) (wB qB eB n : ℕ) : (agreeM M wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

/-- The cells the test reads, outside the list's region. -/
def ReadsOut (wB qB eB agB : ℕ) : Prop :=
  (agB + 2 ^ 15 ≤ wB ∨ wB + 2 ^ 21 ≤ agB) ∧ (agB + 2 ^ 15 ≤ qB ∨ qB + 192 ≤ agB) ∧
    (agB + 2 ^ 15 ≤ eB ∨ eB + 3 * 2 ^ 15 ≤ agB)

theorem agreeP_congr {M M' : Mem} {wB qB eB agB q : ℕ} (hq : q < 2 ^ 15) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : ReadsOut wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) → rd M' x = rd M x) :
    AgreeP M' wB qB eB q ↔ AgreeP M wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : ∀ c < 3, foldPM M' wB qB q c 64 = foldPM M wB qB q c 64 := fun c hc =>
    Finset.sum_congr rfl fun l hl => by
      have hl' := mem_range.1 hl
      simp only [rdK]
      rw [h (qB + 3 * l + c) (by simp only [regs]; omega) (by omega),
        h (wB + 64 * q + (63 - l)) (by simp only [regs]; omega) (by omega)]
  simp only [AgreeP]
  rw [hF 0 (by norm_num), hF 1 (by norm_num), hF 2 (by norm_num),
    h (eB + q) (by simp only [regs]; omega) (by omega),
    h (eB + 2 ^ 15 + q) (by simp only [regs]; omega) (by omega),
    h (eB + 2 * 2 ^ 15 + q) (by simp only [regs]; omega) (by omega)]

/-- **The agreement scan**: the count is `|agreeM|` and `agB + t` holds the `t`-th agreeing
position (`agreeM s.M wB qB eB (2^15)`, the positions in increasing order); the heap outside
`[agB, agB + 2^15)` is kept. -/
theorem agreeIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 15 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 15 < 2 ^ 64) (hags : agB + 2 ^ 15 ≤ s.M.size)
    (hR : ReadsOut wB qB eB agB) :
    rd (semXIR I (agreeIR wB qB eB agB) s).M gCnt =
      toWord (agreeM s.M wB qB eB (2 ^ 15)).length ∧
    (∀ t < (agreeM s.M wB qB eB (2 ^ 15)).length,
      rd (semXIR I (agreeIR wB qB eB agB) s).M (agB + t) =
        toWord ((agreeM s.M wB qB eB (2 ^ 15)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) →
      rd (semXIR I (agreeIR wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agreeIR wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) := by
    simp +decide [WF, Prim.dst, gQ, gCnt, gN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gQ =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gN1 =
        toWord (2 ^ 15) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (2 ^ 15))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> omega
  rw [agreeIR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agreeM s.M wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp → rd (entryK gC1 gN1 (toWord (2 ^ 15)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (2 ^ 15)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agreeM]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agreeM]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 15 → P j s' →
      P (j + 1) (decS gC1 (semXIR I (posBody wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agreeM_le s.M wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := posBody_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by omega) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (posBody wB qB eB agB) s')).M x =
        rd (semXIR I (posBody wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (posBody wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : AgreeP s'.M wB qB eB j ↔ AgreeP s.M wB qB eB j :=
      agreeP_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agreeM_succ]
    by_cases hb : AgreeP s.M wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agreeM s.M wB qB eB j ++ [j]).length = (L j).length + 1 := by
        rw [List.length_append, List.length_singleton]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1, hlen1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; omega)]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; omega) (by omega), i5 t (by omega),
            List.getD_append _ _ _ _ (by simp only [hL] at *; omega)]
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g3 x hx (by omega), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 _ (by simp only [regs]; omega), i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 x hx, i6 x hx hx2]
  have := loopK_run I (posBody wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := 2 ^ 15)
    (by decide) (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩

theorem lo_macC (a : ℕ) (ha : a = gA0 ∨ a = gA1 ∨ a = gA2) : LoK (macC a) := by
  rcases ha with rfl | rfl | rfl <;>
  simp +decide [macC, LoK, mulKC, redC, Prim.dst, gE, gPe, gT, gA0, gA1, gA2, regs]

theorem lo_laneBody : LoK laneBody := by
  simp +decide [laneBody, macC, LoK, mulKC, redC, Prim.dst, gE, gPe, gT, gA0, gA1, gA2, gV, gPw,
    regs]

end Lvm.X
