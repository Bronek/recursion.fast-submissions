-- lvm2 X-REC2 (helper DEC): the agreement scan of `C_rec`'s level-1 decoder. Adapted from this entry's
-- `LvmXAgree.lean` (v1's `agreeIR`, itself from rf-k FRXAgree@8bff272b): the scan loop, the comparison
-- and the append are v1's with `2^12` positions; the fold multiplies `E` lanes (three leaf words, loaded by
-- `LvmXEqT.eqtLdE`) by `E` weights with `mulE` (new), where v1's multiplied `K` words by `E` weights.
import LvmXDec1
import LvmXEqT

/-!
# The level-1 agreement set on the machine

* `agree1IR wB qB eB agB`: for every position `q < 2^12`, the fold
  `Σ_{u<16} E[qB + 3u] · E[wB + 48q + 3u]` (`fold1IR`, `E` products), compared with the three
  coordinates of `Enc₁(f₂)[q]` at `eB + c·2^12 + q` (`test1IR`); the position is appended to the
  list at `agB` (v1's `appendIR`) when they agree (`agree1IR_sem`: the count is `|agree1M|` and
  the list is `agree1M`).
* **`agree1M_eq_agree1L`**: with the table of `eq(α, ·)` and `Enc₁(f₂)`'s coordinates, `agree1M`
  is the pure decoder's `agree1L`.

Registers: v1's scalars `188 … 205` (`gQ` … `gN2`), the `E` registers `34 … 45` (`h1A`
accumulator, `h1S` weight, `h1W` lane, `h1T` product); `mulE`'s scratch `5 … 24`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-! ## Registers -/

/-- The fold's accumulator (`E`, `34 … 36`). -/ def h1A : ℕ := 34
/-- A weight `eq(α, u)` (`E`, `37 … 39`). -/ def h1S : ℕ := 37
/-- A lane (`E`, `40 … 42`). -/ def h1W : ℕ := 40
/-- A product (`E`, `43 … 45`). -/ def h1T : ℕ := 43

/-! ## The programs -/

/-- **One lane `u`**: the weight at `M[gPe]`, the lane at `M[gPw]` (both `+= 3`), their product
added to the accumulator. -/
def lane1Body : XIR :=
  .seq (eqtLdE h1S gPe) (.seq (eqtLdE h1W gPw) (.seq (mulE h1T h1S h1W)
    (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)])))

/-- **The fold at the position `gQ`**: `h1A := Σ_{u<16} E[qB + 3u] · E[wB + 48q + 3u]`. -/
def fold1IR (wB qB : ℕ) : XIR :=
  .seq (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
      .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 16])
    (.loopK gC2 gN2 16 lane1Body)

/-- **The comparison** with `Enc₁(f₂)[q]`'s coordinates at `eB + c·2^12 + q`:
`gZ := [all three equal]`. -/
def test1IR (eB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord eB), .op .add gX gQ gK]) (.seq (.load gE gX)
    (.seq (.blk [.op .eq gZ gE h1A, .const gK (toWord (2 ^ 12)), .op .add gX gX gK])
      (.seq (.load gE gX) (.seq (.blk [.op .eq gZ2 gE (h1A + 1), .op .and gZ gZ gZ2,
        .op .add gX gX gK])
        (.seq (.load gE gX) (.blk [.op .eq gZ2 gE (h1A + 2), .op .and gZ gZ gZ2]))))))

/-- **One position**: the fold, the comparison, the append, `q += 1`. -/
def pos1Body (wB qB eB agB : ℕ) : XIR :=
  .seq (fold1IR wB qB) (.seq (test1IR eB) (.seq (.ite gZ (appendIR agB) (.blk []))
    (.blk [.op .add gQ gQ cOne])))

/-- **The level-1 agreement scan** over the positions `q < 2^12`. -/
def agree1IR (wB qB eB agB : ℕ) : XIR :=
  .seq (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))])
    (.loopK gC1 gN1 (toWord (2 ^ 12)) (pos1Body wB qB eB agB))

/-! ## The machine's agreement list -/

/-- The fold at position `q` over the lanes `u < j` on the heap `M`. -/
def fold1PM (M : Mem) (wB qB q j : ℕ) : Ext3 :=
  ∑ u ∈ range j, rdE M (qB + 3 * u) * rdE M (wB + 48 * q + 3 * u)

/-- The fold and `Enc₁(f₂)`'s coordinates agree at `q` (the machine's test). -/
abbrev Agree1P (M : Mem) (wB qB eB q : ℕ) : Prop :=
  mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q)) =
    fold1PM M wB qB q 16

/-- **The machine's agreement list** below `n`. -/
def agree1M (M : Mem) (wB qB eB n : ℕ) : List ℕ :=
  (List.range n).filter fun q => decide (Agree1P M wB qB eB q)

/-- The cells the test reads, outside the list's region. -/
def Reads1Out (wB qB eB agB : ℕ) : Prop :=
  (agB + 2 ^ 12 ≤ wB ∨ wB + 48 * 2 ^ 12 ≤ agB) ∧ (agB + 2 ^ 12 ≤ qB ∨ qB + 48 ≤ agB) ∧
    (agB + 2 ^ 12 ≤ eB ∨ eB + 3 * 2 ^ 12 ≤ agB)

/-! ## Well formed, no tape loop, no output, cost -/

-- adapted from LvmXAgree.lean (`wf_agreeIR`, `noLoopT_agreeIR`, `outs_agreeIR`, `cost_posBody`,
-- `cost_agreeIR`)
theorem wf_agree1IR (wB qB eB agB : ℕ) : WF (agree1IR wB qB eB agB) := by
  simp +decide [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, mulEC, redC, test1IR,
    appendIR, WF, Writes, Prim.dst, gQ, gPw, gPe, h1A, h1S, h1W, h1T, gE, gX, gZ, gZ2, gCnt, gK,
    gC1, gN1, gC2, gN2, cOne]

theorem noLoopT_agree1IR (wB qB eB agB : ℕ) : NoLoopT (agree1IR wB qB eB agB) := by
  simp [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, test1IR, appendIR, NoLoopT]

theorem outs_agree1IR (wB qB eB agB t : ℕ) : outs (agree1IR wB qB eB agB) t = 0 := by
  simp [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, test1IR, appendIR, outs]

theorem cost_pos1Body (wB qB eB agB t : ℕ) : cost (pos1Body wB qB eB agB) t = 2146 := by
  simp only [pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, test1IR, appendIR, cost, cost_mulE,
    blkSteps, List.length_cons, List.length_nil]
  norm_num

/-- **The scan's exact cost**: `2^12` positions of `2,146` steps (`≈ 2^23.07`). -/
theorem cost_agree1IR (wB qB eB agB t : ℕ) : cost (agree1IR wB qB eB agB) t = 8802318 := by
  simp only [agree1IR, cost, cost_pos1Body, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 12 < 2 ^ 64 by norm_num)]
  norm_num

/-- **The scan's cost** (`2^12` positions). -/
theorem cost_agree1IR_le (wB qB eB agB t : ℕ) : cost (agree1IR wB qB eB agB) t ≤ 2 ^ 24 := by
  rw [cost_agree1IR]; norm_num

/-! ## The fold: one lane, the lane loop -/

/-- `mulE h1T h1S h1W` writes `mulE`'s scratch and the product, nothing else. -/
theorem mulE1_frame {I : Array Word} {s : St} {i : ℕ} (hi : i < 5 ∨ 25 ≤ i)
    (hT : i < h1T ∨ h1T + 3 ≤ i) : rd (semXIR I (mulE h1T h1S h1W) s).M i = rd s.M i := by
  rw [mulE, sem_blk]
  refine rd_runPrims_of_not_writes (fun p hp => ?_) s.M
  have := mulEC_dst h1T h1S h1W p hp
  simp only [h1T] at this hT
  omega

/-- The accumulate block: `h1A += h1T` in `E` (three xors, characteristic 2). -/
theorem acc1_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdE (semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M h1A = rdE s.M h1A + rdE s.M h1T ∧
    (∀ i, (i < h1A ∨ h1A + 3 ≤ i) → rd (semXIR I (.blk [.op .xor h1A h1A h1T,
      .op .xor (h1A + 1) (h1A + 1) (h1T + 1), .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M i =
      rd s.M i) ∧
    Inv (semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_blk_of_not_dst I _ s ?_,
    inv_sem I (by simp +decide [WF]) hM⟩
  · simp only [rdE, rdK, sem_blk, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, h1A, h1T]; omega)) only
      [rd_set_self, rd_set_ne]
    simp only [eval_xor, wK_xor]
    rw [mkE_add]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, h1A] at hi ⊢ <;> omega

/-- **One lane**: the weight at `pe` and the lane at `pw` (`E`, three words each), their product
added to the accumulator; `gPe := pe + 3`, `gPw := pw + 3`. -/
theorem lane1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {pw pe : ℕ} (hpwR : regs ≤ pw)
    (hpw : pw + 3 < 2 ^ 64) (hpeR : regs ≤ pe) (hpe : pe + 3 < 2 ^ 64)
    (hW : rd s.M gPw = toWord pw) (hP : rd s.M gPe = toWord pe) :
    rdE (semXIR I lane1Body s).M h1A = rdE s.M h1A + rdE s.M pe * rdE s.M pw ∧
    rd (semXIR I lane1Body s).M gPw = toWord (pw + 3) ∧
    rd (semXIR I lane1Body s).M gPe = toWord (pe + 3) ∧
    (∀ i, (i < 5 ∨ 46 ≤ i) → i ≠ gPe → i ≠ gPw → rd (semXIR I lane1Body s).M i = rd s.M i) ∧
    Inv (semXIR I lane1Body s).M := by
  have hs := hM.1
  simp only [regs] at hs hpwR hpeR
  rw [lane1Body, semXIR_seq]
  obtain ⟨l1, l2, l3, hM1⟩ := eqtLdE_sem I s hM (d := h1S) (p := gPe) (x := pe) (by decide)
    (by decide) (by decide) (by decide) (by decide) hP (by simp only [regs]; omega) hpe
  generalize semXIR I (eqtLdE h1S gPe) s = s1 at l1 l2 l3 hM1
  rw [semXIR_seq]
  obtain ⟨m1, m2, m3, hM2⟩ := eqtLdE_sem I s1 hM1 (d := h1W) (p := gPw) (x := pw) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [l3 _ (by decide) (by decide), hW])
    (by simp only [regs]; omega) hpw
  generalize semXIR I (eqtLdE h1W gPw) s1 = s2 at m1 m2 m3 hM2
  rw [semXIR_seq]
  have p3 : rdE (semXIR I (mulE h1T h1S h1W) s2).M h1T = rdE s2.M h1S * rdE s2.M h1W :=
    mulE_sem hM2 (by decide) (by decide) (by decide) (by decide)
  have f3 : ∀ i, (i < 5 ∨ 25 ≤ i) → (i < h1T ∨ h1T + 3 ≤ i) →
      rd (semXIR I (mulE h1T h1S h1W) s2).M i = rd s2.M i := fun i h1 h2 => mulE1_frame h1 h2
  have hM3 := inv_sem I (wf_mulE h1T h1S h1W (by decide)) hM2
  generalize semXIR I (mulE h1T h1S h1W) s2 = s3 at p3 f3 hM3
  obtain ⟨a1, a2, hM4⟩ := acc1_sem I s3 hM3
  generalize semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
    .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s3 = s4 at a1 a2 hM4
  have kA : rdE s3.M h1A = rdE s.M h1A := eqt_rdE_eq
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
  have kS : rdE s2.M h1S = rdE s.M pe := by
    rw [← l1]
    exact eqt_rdE_eq (m3 _ (by decide) (by decide)) (m3 _ (by decide) (by decide))
      (m3 _ (by decide) (by decide))
  have kW : rdE s1.M pw = rdE s.M pw := eqt_rdE_eq
    (l3 _ (by simp only [h1S]; omega) (by simp only [gPe]; omega))
    (l3 _ (by simp only [h1S]; omega) (by simp only [gPe]; omega))
    (l3 _ (by simp only [h1S]; omega) (by simp only [gPe]; omega))
  refine ⟨?_, ?_, ?_, fun i i1 i2 i3 => ?_, hM4⟩
  · rw [a1, kA, p3, kS, m1, kW]
  · rw [a2 _ (by decide), f3 _ (by decide) (by decide), m2]
  · rw [a2 _ (by decide), f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l2]
  · simp only [h1A, h1T, h1W, h1S] at *
    rw [a2 i (by omega), f3 i (by omega) (by omega), m3 i (by omega) i3, l3 i (by omega) i2]

/-- The registers and cells `fold1IR` keeps. -/
def Keep1F (r : ℕ) : Prop :=
  (r < 5 ∨ 46 ≤ r) ∧ r ≠ gPe ∧ r ≠ gPw ∧ r ≠ gK ∧ r ≠ gC2 ∧ r ≠ gN2 ∧ r ≠ cTmp

theorem keep1F_of_regs {r : ℕ} (h : regs ≤ r) : Keep1F r := by
  simp only [Keep1F, regs, gPe, gPw, gK, gC2, gN2, cTmp] at *; omega

/-- **The fold at the position `q`** (`gQ = q`): the accumulator holds `fold1PM … 16`; the heap
and the registers outside the fold's are kept. -/
theorem fold1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB q : ℕ} (hwB : regs ≤ wB)
    (hq : q < 2 ^ 12) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (hQ : rd s.M gQ = toWord q) :
    rdE (semXIR I (fold1IR wB qB) s).M h1A = fold1PM s.M wB qB q 16 ∧
    (∀ r, Keep1F r → rd (semXIR I (fold1IR wB qB) s).M r = rd s.M r) ∧
    Inv (semXIR I (fold1IR wB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB
  have w0 : WF (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
      .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 16]) := by
    simp +decide [WF, Prim.dst, h1A, gK, gPw, gPe, gN2]
  have hM0 := inv_sem I w0 hM
  rw [fold1IR, semXIR_seq]
  have r0 : rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPw = toWord (wB + 48 * q + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPe = toWord (qB + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gN2 = toWord 16 ∧
      rdE (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M h1A = 0 := by
    rw [sem_blk']
    simp only [rdE, rdK, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, h1A, gK, gPw, gPe, gN2]; omega))
      only [rd_set_self, rd_set_ne]
    · rw [hQ, show (48 : Word) = toWord 48 from rfl, mul_toWord, add_toWord]
      congr 1; ring
    · rfl
    · rfl
    · rw [eqt_wK_zero, mkE_zero]
  have k0 : ∀ r, Keep1F r → rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0,
      .const (h1A + 2) 0, .const gK 48, .op .mul gPw gQ gK, .const gK (toWord wB),
      .op .add gPw gPw gK, .const gPe (toWord qB), .const gN2 16]) s).M r = rd s.M r :=
    fun r hr => by
    simp only [Keep1F, gPe, gPw, gK, gC2, gN2, cTmp] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, h1A, gPe, gPw, gK, gN2] <;> omega
  generalize semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
    .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
    .const gN2 16]) s = s0 at hM0 r0 k0
  obtain ⟨p0, e0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧
    rd s'.M gPw = toWord (wB + 48 * q + 3 * j) ∧ rd s'.M gPe = toWord (qB + 3 * j) ∧
    rdE s'.M h1A = fold1PM s.M wB qB q j ∧ (∀ r, Keep1F r → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord 16) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC2 gN2 (toWord 16) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, ?_, fun r hr => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0]
    · rw [hE _ (by decide) (by decide), e0]
    · rw [eqt_rdE_eq (hE _ (by decide) (by decide)) (hE _ (by decide) (by decide))
        (hE _ (by decide) (by decide)), a0, fold1PM, Finset.sum_range_zero]
    · rw [hE _ hr.2.2.2.2.1 hr.2.2.2.2.2.2, k0 r hr]
  have hstep : ∀ j s', j < 16 → P j s' → P (j + 1) (decS gC2 (semXIR I lane1Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hK : ∀ x, regs ≤ x → rdE s'.M x = rdE s.M x := fun x hx => eqt_rdE_eq
      (i5 x (keep1F_of_regs hx)) (i5 _ (keep1F_of_regs (by omega)))
      (i5 _ (keep1F_of_regs (by omega)))
    obtain ⟨l1, l2, l3, l4, hM'⟩ := lane1Body_sem I s' i1 (pw := wB + 48 * q + 3 * j)
      (pe := qB + 3 * j) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
      (by omega) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I lane1Body s')).M x =
        rd (semXIR I lane1Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l2, show wB + 48 * q + 3 * j + 3 = wB + 48 * q + 3 * (j + 1) by ring]
    · rw [hd _ (by decide), l3, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [eqt_rdE_decS _ (.inr (by decide)), l1, i4, fold1PM, fold1PM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; omega), hK _ (by simp only [regs]; omega)]
    · have hr' := hr
      obtain ⟨r0, r1, r2, -, r4, -, -⟩ := hr'
      rw [hd _ r4, l4 r r0 r1 r2, i5 r hr]
  have hfin := loopK_run I lane1Body P s0 hM0 (c := gC2) (n := gN2) (K := 16) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, hfin.2.2.2.2, hfin.1⟩

/-! ## The comparison -/

-- adapted from LvmXAgree.lean (`lo_testIR`, `testIR_sem`)
theorem lo_test1IR (eB : ℕ) : LoK (test1IR eB) := by
  simp +decide [test1IR, LoK, Prim.dst, gK, gX, gE, gZ, gZ2, regs]

/-- **The comparison**: `gZ` is `1` iff the accumulator's three words equal the three words of
`Enc₁(f₂)[q]`'s coordinates (`eB + c·2^12 + q`); only `gK, gX, gE, gZ, gZ2` change. -/
theorem test1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {eB q : ℕ} (heB : regs ≤ eB)
    (hq : q < 2 ^ 12) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64) (hQ : rd s.M gQ = toWord q) :
    rd (semXIR I (test1IR eB) s).M gZ =
      bW (decide (rd s.M (eB + q) = rd s.M h1A) &&
        decide (rd s.M (eB + 2 ^ 12 + q) = rd s.M (h1A + 1)) &&
        decide (rd s.M (eB + 2 * 2 ^ 12 + q) = rd s.M (h1A + 2))) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gE → r ≠ gZ → r ≠ gZ2 →
      rd (semXIR I (test1IR eB) s).M r = rd s.M r) ∧
    Inv (semXIR I (test1IR eB) s).M := by
  have hs := hM.1
  simp only [regs] at hs heB
  have hw : WF (test1IR eB) := by simp +decide [test1IR, WF, Prim.dst, gK, gX, gE, gZ, gZ2]
  refine ⟨?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I hw hM⟩
  · simp only [test1IR, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_self, rd_set_ne]
    rw [hQ, add_toWord, toNat_toWord (by omega), add_toWord, toNat_toWord (by omega), add_toWord,
      toNat_toWord (by omega)]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (test1IR eB) s hw hM r hr ?_
      simp only [test1IR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      omega
    · exact hframeK I (test1IR eB) s (lo_test1IR eB) r (by omega)

/-! ## One position and the scan -/

theorem keep1F_gQ : Keep1F gQ := by unfold Keep1F; decide
theorem keep1F_gCnt : Keep1F gCnt := by unfold Keep1F; decide

theorem mkE_eq_iff {a₀ a₁ a₂ b₀ b₁ b₂ : BF64} :
    mkE a₀ a₁ a₂ = mkE b₀ b₁ b₂ ↔ a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ :=
  ⟨mkE_inj, fun ⟨h0, h1, h2⟩ => by rw [h0, h1, h2]⟩

-- adapted from LvmXAgree.lean (`posBody_sem`)
/-- **One position**: `q` is listed at `agB + c` iff the fold agrees with `Enc₁(f₂)` at `q`;
`gQ := q + 1`; the heap outside the listed cell is kept. -/
theorem pos1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB q c : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB)
    (hqB2 : qB + 48 < 2 ^ 64) (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 12 < 2 ^ 64) (hags : agB + 2 ^ 12 ≤ s.M.size)
    (hq : q < 2 ^ 12) (hcq : c ≤ q) (hQ : rd s.M gQ = toWord q) (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (pos1Body wB qB eB agB) s).M gQ = toWord (q + 1) ∧
    (if Agree1P s.M wB qB eB q then
      rd (semXIR I (pos1Body wB qB eB agB) s).M gCnt = toWord (c + 1) ∧
        rd (semXIR I (pos1Body wB qB eB agB) s).M (agB + c) = toWord q ∧
        ∀ x, regs ≤ x → x ≠ agB + c → rd (semXIR I (pos1Body wB qB eB agB) s).M x = rd s.M x
    else
      rd (semXIR I (pos1Body wB qB eB agB) s).M gCnt = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (pos1Body wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (pos1Body wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  rw [pos1Body, semXIR_seq]
  obtain ⟨f1, f2, hM1⟩ := fold1IR_sem I s hM (wB := wB) (qB := qB) (by simp only [regs]; omega)
    hq hwB2 (by simp only [regs]; omega) hqB2 hQ
  have z1 := size_sem I (fold1IR wB qB) s
  generalize semXIR I (fold1IR wB qB) s = s1 at f1 f2 hM1 z1
  have q1 : rd s1.M gQ = toWord q := (f2 gQ keep1F_gQ).trans hQ
  have c1 : rd s1.M gCnt = toWord c := (f2 gCnt keep1F_gCnt).trans hC
  have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => f2 x (keep1F_of_regs hx)
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM2⟩ := test1IR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq heB2 q1
  have z2 := size_sem I (test1IR eB) s1
  generalize semXIR I (test1IR eB) s1 = s2 at t1 t2 hM2 z2
  -- the flag is the test
  have e : ∀ a b, regs ≤ a → (rd s1.M a = rd s1.M b ↔ rdK s.M a = rdK s1.M b) := fun a b ha => by
    rw [rdK, rdK, wK_inj, h1 a ha]
  have hiff : Agree1P s.M wB qB eB q ↔ (rd s1.M (eB + q) = rd s1.M h1A ∧
      rd s1.M (eB + 2 ^ 12 + q) = rd s1.M (h1A + 1) ∧
      rd s1.M (eB + 2 * 2 ^ 12 + q) = rd s1.M (h1A + 2)) := by
    simp only [Agree1P]
    rw [← f1, rdE, mkE_eq_iff, e _ _ (by simp only [regs]; omega),
      e _ _ (by simp only [regs]; omega), e _ _ (by simp only [regs]; omega)]
  have hZ : rd s2.M gZ = bW (decide (Agree1P s.M wB qB eB q)) := by
    rw [t1]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact hiff.symm
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
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; omega), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : Agree1P s.M wB qB eB q
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
      rw [g2 x (by simp only [gQ]; omega), a3 x (by simp only [gK]; omega)
        (by simp only [gX]; omega) (by simp only [gCnt]; omega) (by simp only [cTmp]; omega) hx2,
        h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; omega), h2 x (by simp only [regs]; omega)]

-- adapted from LvmXAgree.lean (`agreeM_succ`, `length_agreeM_le`, `agreeP_congr`)
theorem agree1M_succ (M : Mem) (wB qB eB n : ℕ) : agree1M M wB qB eB (n + 1) =
    agree1M M wB qB eB n ++ if Agree1P M wB qB eB n then [n] else [] := by
  rw [agree1M, agree1M, List.range_succ, List.filter_append]
  congr 1
  by_cases h : Agree1P M wB qB eB n
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, decide_eq_false h]; rfl

theorem length_agree1M_le (M : Mem) (wB qB eB n : ℕ) : (agree1M M wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

theorem agree1P_congr {M M' : Mem} {wB qB eB agB q : ℕ} (hq : q < 2 ^ 12) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : Reads1Out wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) → rd M' x = rd M x) :
    Agree1P M' wB qB eB q ↔ Agree1P M wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : fold1PM M' wB qB q 16 = fold1PM M wB qB q 16 :=
    Finset.sum_congr rfl fun u hu => by
      have hu' := mem_range.1 hu
      have hq' : q + 1 ≤ 2 ^ 12 := hq
      have hq48 : 48 * q + 48 ≤ 48 * 2 ^ 12 := by omega
      rw [eqt_rdE_eq (h (qB + 3 * u) (by simp only [regs]; omega) (by omega))
          (h (qB + 3 * u + 1) (by simp only [regs]; omega) (by omega))
          (h (qB + 3 * u + 2) (by simp only [regs]; omega) (by omega)),
        eqt_rdE_eq (h (wB + 48 * q + 3 * u) (by simp only [regs]; omega) (by omega))
          (h (wB + 48 * q + 3 * u + 1) (by simp only [regs]; omega) (by omega))
          (h (wB + 48 * q + 3 * u + 2) (by simp only [regs]; omega) (by omega))]
  simp only [Agree1P, hF, rdK]
  rw [h (eB + q) (by simp only [regs]; omega) (by omega),
    h (eB + 2 ^ 12 + q) (by simp only [regs]; omega) (by omega),
    h (eB + 2 * 2 ^ 12 + q) (by simp only [regs]; omega) (by omega)]

/-! ## Semantics -/

-- adapted from LvmXAgree.lean (`agreeIR_sem`)
/-- **The level-1 agreement scan**: the count is `|agree1M|` and `agB + t` holds the `t`-th
agreeing position (`agree1M s.M wB qB eB (2^12)`, increasing); the heap outside
`[agB, agB + 2^12)` is kept. -/
theorem agree1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 12 < 2 ^ 64) (hags : agB + 2 ^ 12 ≤ s.M.size)
    (hR : Reads1Out wB qB eB agB) :
    rd (semXIR I (agree1IR wB qB eB agB) s).M gCnt =
      toWord (agree1M s.M wB qB eB (2 ^ 12)).length ∧
    (∀ t < (agree1M s.M wB qB eB (2 ^ 12)).length,
      rd (semXIR I (agree1IR wB qB eB agB) s).M (agB + t) =
        toWord ((agree1M s.M wB qB eB (2 ^ 12)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) →
      rd (semXIR I (agree1IR wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agree1IR wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) := by
    simp +decide [WF]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M
        gQ = toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M gN1 =
        toWord (2 ^ 12) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (2 ^ 12))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> omega
  rw [agree1IR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agree1M s.M wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp →
      rd (entryK gC1 gN1 (toWord (2 ^ 12)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (2 ^ 12)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agree1M]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agree1M]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; omega) (by simp only [cTmp]; omega),
        k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 12 → P j s' →
      P (j + 1) (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agree1M_le s.M wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := pos1Body_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by omega) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')).M x =
        rd (semXIR I (pos1Body wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : Agree1P s'.M wB qB eB j ↔ Agree1P s.M wB qB eB j :=
      agree1P_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agree1M_succ]
    by_cases hb : Agree1P s.M wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agree1M s.M wB qB eB j ++ [j]).length = (L j).length + 1 := by
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
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 _ (by simp only [regs]; omega),
          i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; omega), g2 x hx, i6 x hx hx2]
  have := loopK_run I (pos1Body wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := 2 ^ 12)
    (by decide) (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩

-- adapted from LvmXDecBr.lean (`agreeP_iff`, `agreeM_eq_filter`)
/-- The test at one position is the decoder's. -/
theorem agree1P_iff {M : Mem} {wB qB eB q : ℕ} (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hq : q < 2 ^ 12)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < 2 ^ 12, enc1 f₂ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q))) :
    Agree1P M wB qB eB q ↔ fold1At α wd q = enc1 f₂ q := by
  have hF : fold1At α wd q = fold1PM M wB qB q 16 := by
    rw [fold1At, fold1PM]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_range.1 hu
    rw [hQ u hu', row1, rdE, ← hW q hq (3 * u) (by omega), ← hW q hq (3 * u + 1) (by omega),
      ← hW q hq (3 * u + 2) (by omega)]
    rfl
  simp only [Agree1P]
  rw [← hF, ← hE q hq]
  exact eq_comm

/-- **The machine's list is the decoder's**: the word at `wB + 48q + t`, the `eq(α, ·)` table at
`qB + 3u` (`rdE`), and `Enc₁(f₂)[q]`'s coordinates at `eB + c·2^12 + q`. -/
theorem agree1M_eq_agree1L {M : Mem} {wB qB eB : ℕ} (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < 2 ^ 12, enc1 f₂ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q))) :
    agree1M M wB qB eB (2 ^ 12) = agree1L wd α f₂ := by
  unfold agree1M agree1L
  refine List.filter_congr fun q hq => ?_
  exact decide_eq_decide.2 (agree1P_iff wd α f₂ (List.mem_range.1 hq) hW hQ hE)

end Lvm.X
