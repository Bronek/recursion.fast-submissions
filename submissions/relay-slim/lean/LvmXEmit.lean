-- New for lvm (WP-13a): small output emitters (a constant word, a copy of tape words) and the copy of
-- the decoded stream to a contiguous buffer. FR's counterparts are `FRXLeaf.leafIR`/`outAt`
-- (rf-k/submissions/flock-recursive/lean@kk/base); the loop lemma is `LvmXSeg.loopK_emit`.
import LvmXNode
import LvmXDecCost

/-!
# Emitters and the stream copy

* `emitIR w`: output the constant `w` (`emitIR_sem`).
* `tcpIR a n`: output tape words `a … a + n − 1` (`tcpIR_sem`).
* `copyIR mB`: `sgB + u := M[mB + crecIdx u]` for `u < 17·2^14`, the stream's lanes in a contiguous
  buffer (`copyIR_sem`).

Registers `120 … 129`. None of these writes a heap cell but `copyIR` (the buffer only).
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The word emitted. -/ def eW : ℕ := 120
/-- The tape position / the lane. -/ def eP : ℕ := 121
/-- The loop count. -/ def eN : ℕ := 122
/-- The loop counter. -/ def eC : ℕ := 123
/-- The row `⌊u/17⌋`. -/ def eQ : ℕ := 124
/-- The column `u mod 17`. -/ def eR : ℕ := 125
/-- An address. -/ def eA : ℕ := 126
/-- Constant scratch. -/ def eK : ℕ := 128

/-- The stream buffer's base. -/
def sgB : ℕ := 16842752
/-- The stream buffer's lanes: `17 · 2^14`. -/
def nCp : ℕ := 278528

theorem sgB_eq : sgB = 2 ^ 24 + 2 ^ 16 := rfl
theorem nCp_eq : nCp = 17 * 2 ^ 14 := rfl

/-! ## A constant -/

/-- Output the constant `w`. -/
def emitIR (w : Word) : XIR := .seq (.blk [.const eW w]) (.out eW)

theorem wf_emitIR (w : Word) : WF (emitIR w) := by
  simp +decide [emitIR, WF, Prim.dst, eW]

theorem emitIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : Word) :
    (semXIR I (emitIR w) s).o.toList = s.o.toList ++ [w] ∧
    (∀ y, y ≠ eW → rd (semXIR I (emitIR w) s).M y = rd s.M y) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun y hy => ?_⟩
  · simp only [emitIR, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
    rw [rd_set_self (by simp only [eW]; omega)]
  · simp only [emitIR, semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne (Ne.symm hy)

/-! ## A copy of tape words -/

/-- One word: `out I[eP]`, `eP += 1`. -/
def tcpBody : XIR := .seq (.input eW eP) (.seq (.out eW) (.blk [.op .add eP eP cOne]))

/-- **Output tape words `a … a + n − 1`.** -/
def tcpIR (a n : ℕ) : XIR :=
  .seq (.blk [.const eP (toWord a), .const eN (toWord n)]) (.loopK eC eN (toWord n) tcpBody)

theorem wf_tcpIR (a n : ℕ) : WF (tcpIR a n) := by
  simp +decide [tcpIR, tcpBody, WF, Writes, Prim.dst, eW, eP, eN, eC, cTmp, regs]

theorem tcpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : rd s.M eP = toWord p)
    (hp2 : p < 2 ^ 64) :
    (semXIR I tcpBody s).o.toList = s.o.toList ++ [I.getD p 0] ∧
    rd (semXIR I tcpBody s).M eP = toWord (p + 1) ∧
    (∀ y, y ≠ eW → y ≠ eP → rd (semXIR I tcpBody s).M y = rd s.M y) ∧
    (semXIR I tcpBody s).M.size = s.M.size := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [tcpBody, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
  refine ⟨?_, ?_, fun y h1 h2 => ?_, by simp⟩
  · rw [rd_set_self (by simp only [eW]; omega), hp, toNat_toWord hp2]
  · simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hp, h1]
    exact add_one_toWord p
  · rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]

/-- **The tape copy**: `n` tape words from `a` are output; only `eW, eP, eN, eC, cTmp` change. -/
theorem tcpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a n : ℕ} (h : a + n < 2 ^ 64) :
    (semXIR I (tcpIR a n) s).o.toList = s.o.toList ++ (List.range n).map (fun j => I.getD (a + j) 0) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eN → y ≠ eC → y ≠ cTmp → rd (semXIR I (tcpIR a n) s).M y = rd s.M y) ∧
    Inv (semXIR I (tcpIR a n) s).M ∧ (semXIR I (tcpIR a n) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf := wf_tcpIR a n
  have hM1 : Inv (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M := inv_sem I hwf.1 hM
  have p1 : rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M eP = toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have n1 : rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M eN = toWord n := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eN →
      rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M y = rd s.M y :=
    fun y a b => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b) _
  have z1 := size_sem I (.blk [.const eP (toWord a), .const eN (toWord n)]) s
  have o1 : (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).o = s.o := rfl
  rw [tcpIR, semXIR_seq]
  generalize semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s = s1 at hM1 p1 n1 f1 z1 o1
  -- the loop
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ rd t.M eP = toWord (a + j) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eN → y ≠ eC → y ≠ cTmp → rd t.M y = rd s.M y) ∧ t.M.size = s.M.size
  have h0 : Q 0 ⟨entryK eC eN (toWord n) s1.M, s1.o⟩ := by
    refine ⟨inv_of_frame hM1 (size_entryK ..) fun i hi => entryK_frame _ (by simp only [eC]; omega)
        (by simp only [cTmp]; omega), ?_, fun y a b c d e => ?_, by rw [size_entryK, z1]⟩
    · rw [entryK_frame _ (by decide) (by decide), p1, Nat.add_zero]
    · rw [entryK_frame _ (Ne.symm d) (Ne.symm e), f1 y b c]
  have hf : ∀ j t, j < n → Q j t → (semXIR I tcpBody t).o.toList = t.o.toList ++ [I.getD (a + j) 0] ∧
      Q (j + 1) (decS eC (semXIR I tcpBody t)) := by
    intro j t hj ⟨q1, q2, q3, q4⟩
    obtain ⟨b1, b2, b3, b4⟩ := tcpBody_sem I t q1 q2 (by omega)
    refine ⟨b1, inv_of_frame (inv_sem I hwf.2.2.2.2 q1) (size_decS ..) fun i hi =>
      rd_decS (by simp only [eC]; omega) _, by rw [rd_decS (by decide), b2, Nat.add_assoc],
      fun y a b c d e => by rw [rd_decS (Ne.symm d), b3 y a b, q3 y a b c d e], by rw [size_decS, b4, q4]⟩
  obtain ⟨l1, l2⟩ := loopK_emit I (b := tcpBody) Q (fun j => [I.getD (a + j) 0]) s1 hM1 (by decide)
    (by decide) (by decide) (by omega) n1 h0 hf
  refine ⟨?_, l2.2.2.1, l2.1, l2.2.2.2⟩
  rw [l1, o1, flatMap_single]

/-! ## The stream copy -/

/-- The address arithmetic of lane `eP`: `eA := mB + (eP mod 17)·2^14 + ⌊eP/17⌋`. -/
def cpAddrPs (mB : ℕ) : List Prim :=
  [.const eK 17, .op .divu eQ eP eK, .op .remu eR eP eK, .const eK (toWord (2 ^ 14)),
   .op .mul eA eR eK, .op .add eA eA eQ, .const eK (toWord mB), .op .add eA eA eK]

/-- One lane: `sgB + eP := M[mB + crecIdx eP]`, `eP += 1`. -/
def copyBody (mB : ℕ) : XIR :=
  .seq (.blk (cpAddrPs mB)) (.seq (.load eW eA) (.seq (.blk [.const eK (toWord sgB),
    .op .add eA eP eK]) (.seq (.store eA eW) (.blk [.op .add eP eP cOne]))))

/-- **The stream copy.** -/
def copyIR (mB : ℕ) : XIR :=
  .seq (.blk [.const eP 0, .const eN (toWord nCp)]) (.loopK eC eN (toWord nCp) (copyBody mB))

theorem wf_copyIR (mB : ℕ) : WF (copyIR mB) := by
  simp +decide [copyIR, copyBody, cpAddrPs, WF, Writes, Prim.dst, eW, eP, eN, eC, eQ, eR, eA, eK,
    cTmp, regs]

theorem crecIdx_lt {u : ℕ} (hu : u < nCp) : crecIdx u < 2 ^ 19 := by
  simp only [crecIdx, nCp] at hu ⊢; omega

theorem semXIR_blk_M (I : Array Word) (ps : List Prim) (s : St) :
    (semXIR I (.blk ps) s).M = runPrims ps s.M := rfl

theorem cpAddr_frame (mB : ℕ) (M : Mem) {y : ℕ} (a : y ≠ eQ) (b : y ≠ eR) (c : y ≠ eA)
    (d : y ≠ eK) : rd (runPrims (cpAddrPs mB) M) y = rd M y := by
  have hw : ∀ p ∈ cpAddrPs mB, p.dst ≠ y := fun p hp => by
    simp only [cpAddrPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c | exact Ne.symm d
  exact rd_runPrims_of_not_writes hw _

theorem cpAddr_val (M : Mem) (hs : 256 ≤ M.size) {mB u : ℕ} (hu : u < nCp)
    (hmB : mB < 2 ^ 40) (hp : rd M eP = toWord u) :
    rd (runPrims (cpAddrPs mB) M) eA = toWord (mB + crecIdx u) := by
  simp only [nCp] at hu
  simp only [cpAddrPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  rw [hp, show (17 : Word) = toWord 17 from rfl, divu_toWord (a := u) (b := 17) (by omega) (by norm_num),
    remu_toWord (a := u) (b := 17) (by omega) (by norm_num), mulW_toWord, add_toWord, add_toWord,
    show mB + crecIdx u = u % 17 * 2 ^ 14 + u / 17 + mB by unfold crecIdx; omega]

theorem copyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {mB u : ℕ} (hu : u < nCp)
    (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (hp : rd s.M eP = toWord u) :
    rd (semXIR I (copyBody mB) s).M (sgB + u) = rd s.M (mB + crecIdx u) ∧
    rd (semXIR I (copyBody mB) s).M eP = toWord (u + 1) ∧
    (∀ y, regs ≤ y → y ≠ sgB + u → rd (semXIR I (copyBody mB) s).M y = rd s.M y) ∧
    Inv (semXIR I (copyBody mB) s).M ∧ (semXIR I (copyBody mB) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hmB
  have hu' := hu
  simp only [sgB, nCp] at hu' hmB2 hsz
  have hci := crecIdx_lt hu
  have hwf : WF (.blk (cpAddrPs mB)) := by
    intro q hq; simp only [cpAddrPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.dst, eQ, eR, eA, eK]
  -- the address
  have a1 : rd (semXIR I (.blk (cpAddrPs mB)) s).M eA = toWord (mB + crecIdx u) := by
    rw [semXIR_blk_M]; exact cpAddr_val s.M hs hu (mB := mB) (by omega) hp
  have f1 : ∀ y, y ≠ eQ → y ≠ eR → y ≠ eA → y ≠ eK →
      rd (semXIR I (.blk (cpAddrPs mB)) s).M y = rd s.M y := fun y a b c d => by
    rw [semXIR_blk_M]; exact cpAddr_frame mB s.M a b c d
  have hM1 := inv_sem I hwf hM
  have z1 := size_sem I (.blk (cpAddrPs mB)) s
  rw [copyBody, semXIR_seq]
  generalize semXIR I (.blk (cpAddrPs mB)) s = s1 at a1 f1 hM1 z1
  -- the load
  obtain ⟨l1, l2, hM2⟩ := load_sem I s1 hM1 (d := eW) (p := eA) (x := mB + crecIdx u) (by decide)
    (by decide) a1 (by omega)
  have z2 := size_sem I (.load eW eA) s1
  rw [semXIR_seq]
  generalize semXIR I (.load eW eA) s1 = s2 at l1 l2 hM2 z2
  -- the store address
  have hwf3 : WF (.blk [.const eK (toWord sgB), .op .add eA eP eK]) := by
    simp +decide [WF, Prim.dst, eK, eA]
  have a3 : rd (semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2).M eA =
      toWord (sgB + u) := by
    have hs2 := hM2.1
    simp only [regs] at hs2
    rw [semXIR_blk_M]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [l2 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide), hp, add_toWord,
      Nat.add_comm]
  have f3 : ∀ y, y ≠ eK → y ≠ eA →
      rd (semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2).M y = rd s2.M y :=
    fun y a b => rd_blk_of_not_dst I _ s2 (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b)
  have hM3 := inv_sem I hwf3 hM2
  have z3 := size_sem I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2 = s3 at a3 f3 hM3 z3
  -- the store
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := eA) (v := eW) (x := sgB + u) (by decide)
    (by decide) a3 (by simp only [regs, sgB]; omega) (by simp only [sgB]; omega)
    (by rw [z3, z2, z1]; simp only [sgB]; omega)
  have z4 := size_sem I (.store eA eW) s3
  rw [semXIR_seq]
  generalize semXIR I (.store eA eW) s3 = s4 at c1 c2 hM4 z4
  -- `eP += 1`
  have hwf5 : WF (.blk [.op .add eP eP cOne]) := by simp +decide [WF, Prim.dst, eP]
  have hs4 := hM4.1
  simp only [regs] at hs4
  have hreg : ∀ y, y < 256 → y ≠ sgB + u := fun y hy => by simp only [sgB]; omega
  refine ⟨?_, ?_, fun y hy hne => ?_, inv_sem I hwf5 hM4, by rw [size_sem, z4, z3, z2, z1]⟩
  · rw [rd_blk_of_not_dst I _ s4 (by simp [Prim.dst, eP, sgB]; omega), c1,
      f3 _ (by decide) (by decide), l1, f1 _ (by simp only [eQ, sgB] at *; omega)
        (by simp only [eR]; omega) (by simp only [eA]; omega) (by simp only [eK]; omega)]
  · rw [semXIR_blk_M]
    simp only [runPrims, List.foldl, Prim.run]
    have h1 : rd s4.M cOne = 1 := hM4.2 0 (by decide)
    rw [rd_set_self (by simp only [eP]; omega), h1, c2 _ (hreg _ (by decide)) (by decide),
      f3 _ (by decide) (by decide), l2 _ (by decide), f1 _ (by decide) (by decide) (by decide)
        (by decide), hp]
    exact add_one_toWord u
  · simp only [regs] at hy
    rw [rd_blk_of_not_dst I _ s4 (by simp [Prim.dst, eP]; omega), c2 _ hne (by simp only [cTmp]; omega),
      f3 _ (by simp only [eK]; omega) (by simp only [eA]; omega), l2 _ (by simp only [eW]; omega),
      f1 _ (by simp only [eQ]; omega) (by simp only [eR]; omega) (by simp only [eA]; omega)
        (by simp only [eK]; omega)]

/-- **The stream copy**: `sgB + u` holds the message word `crecIdx u` for every `u < 17·2^14`;
the heap outside the buffer is kept; no output. -/
theorem copyIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB)
    (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size) :
    (∀ u < nCp, rd (semXIR I (copyIR mB) s).M (sgB + u) = rd s.M (mB + crecIdx u)) ∧
    (∀ y, regs ≤ y → (y < sgB ∨ sgB + nCp ≤ y) → rd (semXIR I (copyIR mB) s).M y = rd s.M y) ∧
    Inv (semXIR I (copyIR mB) s).M ∧ (semXIR I (copyIR mB) s).M.size = s.M.size ∧
    (semXIR I (copyIR mB) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf := wf_copyIR mB
  have hO : (semXIR I (copyIR mB) s).o = s.o := sem_o I _ s rfl
  rw [copyIR, semXIR_seq] at hO ⊢
  have hM1 := inv_sem I hwf.1 hM
  have p1 : rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M eP = toWord 0 := by
    rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]; rfl
  have n1 : rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M eN = toWord nCp := by
    rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eN → rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M y = rd s.M y :=
    fun y a b => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b)
  have z1 := size_sem I (.blk [.const eP 0, .const eN (toWord nCp)]) s
  generalize semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s = s1 at hM1 p1 n1 f1 z1 hO
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M eP = toWord j ∧
    (∀ u < j, rd t.M (sgB + u) = rd s.M (mB + crecIdx u)) ∧
    (∀ y, regs ≤ y → (y < sgB ∨ sgB + j ≤ y) → rd t.M y = rd s.M y)
  have h0 : Q 0 ⟨entryK eC eN (toWord nCp) s1.M, s1.o⟩ := by
    refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], by rw [entryK_frame _ (by decide)
      (by decide), p1], fun u hu => absurd hu (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    simp only [regs] at hy
    rw [entryK_frame _ (by simp only [eC]; omega) (by simp only [cTmp]; omega),
      f1 _ (by simp only [eP]; omega) (by simp only [eN]; omega)]
  have hstep : ∀ j t, j < nCp → Q j t → Q (j + 1) (decS eC (semXIR I (copyBody mB) t)) := by
    intro j t hj ⟨q1, q2, q3, q4, q5⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := copyBody_sem I t q1 hj hmB hmB2 (by rw [q2]; exact hsz) q3
    have hrd : ∀ y, regs ≤ y → rd (decS eC (semXIR I (copyBody mB) t)).M y =
        rd (semXIR I (copyBody mB) t).M y := fun y hy => rd_decS (by simp only [regs, eC] at *; omega) _
    have hcl : crecIdx j < 2 ^ 19 := crecIdx_lt hj
    refine ⟨inv_decS b4 (by decide), by rw [size_decS, b5, q2], by rw [rd_decS (by decide), b2], fun u hu => ?_,
      fun y hy hy' => ?_⟩
    · rw [hrd _ (by simp only [regs, sgB]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | rfl
      · rw [b3 _ (by simp only [regs, sgB]; omega) (by omega), q4 u h]
      · rw [b1, q5 _ (by simp only [regs] at hmB ⊢; omega) (.inl (by simp only [sgB] at hmB2 ⊢; omega))]
    · rw [hrd _ hy, b3 _ hy (by omega), q5 _ hy (by omega)]
  have := loopK_run I (copyBody mB) Q ⟨s1.M, s1.o⟩ hM1 (by decide) (by decide) (by decide) n1
    (by simp only [nCp]; norm_num) h0 hstep
  obtain ⟨r1, r2, -, r4, r5⟩ := this
  refine ⟨r4, fun y hy hy' => r5 y hy hy', r1, r2, hO⟩

/-! ## A copy of tape words to the heap -/

/-- One word: `M[eA] := I[eP]`, `eP += 1`, `eA += 1`. -/
def thcpBody : XIR :=
  .seq (.input eW eP) (.seq (.store eA eW) (.blk [.op .add eP eP cOne, .op .add eA eA cOne]))

/-- **Tape words `a … a + n − 1` to the heap at `dst`.** -/
def thcpIR (a dst n : ℕ) : XIR :=
  .seq (.blk [.const eP (toWord a), .const eA (toWord dst), .const eN (toWord n)])
    (.loopK eC eN (toWord n) thcpBody)

theorem wf_thcpIR (a dst n : ℕ) : WF (thcpIR a dst n) := by
  simp +decide [thcpIR, thcpBody, WF, Writes, Prim.dst, eW, eP, eN, eC, eA, cTmp, regs]

theorem thcpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p x : ℕ} (hp : rd s.M eP = toWord p)
    (hx : rd s.M eA = toWord x) (hp2 : p + 1 < 2 ^ 64) (hxr : regs ≤ x) (hx2 : x + 1 < 2 ^ 64)
    (hxs : x < s.M.size) :
    rd (semXIR I thcpBody s).M x = I.getD p 0 ∧ rd (semXIR I thcpBody s).M eP = toWord (p + 1) ∧
    rd (semXIR I thcpBody s).M eA = toWord (x + 1) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eA → y ≠ cTmp → y ≠ x → rd (semXIR I thcpBody s).M y = rd s.M y) ∧
    Inv (semXIR I thcpBody s).M ∧ (semXIR I thcpBody s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hxr
  rw [thcpBody, semXIR_seq]
  have i1 : rd (semXIR I (.input eW eP) s).M eW = I.getD p 0 := by
    show rd (s.M.setIfInBounds eW (I.getD (rd s.M eP).toNat 0)) eW = _
    rw [rd_set_self (by simp only [eW]; omega), hp, toNat_toWord (by omega)]
  have g1 : ∀ y, y ≠ eW → rd (semXIR I (.input eW eP) s).M y = rd s.M y := fun y hy =>
    rd_set_ne (Ne.symm hy)
  have hM1 := inv_sem I (P := .input eW eP) (show 4 ≤ eW by decide) hM
  have z1 := size_sem I (.input eW eP) s
  generalize semXIR I (.input eW eP) s = s1 at i1 g1 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := eA) (v := eW) (x := x) (by decide) (by decide)
    (by rw [g1 _ (by decide), hx]) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (.store eA eW) s1
  generalize semXIR I (.store eA eW) s1 = s2 at c1 c2 hM2 z2
  have hx' : ∀ r, r < 256 → r ≠ x := fun r hr => by omega
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun y a b c d e => ?_, inv_sem I (by simp +decide [WF, Prim.dst, eP, eA]) hM2,
    by rw [size_sem, z2, z1]⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, eP, eA]; omega), c1, i1]
  · rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [eP]; omega), h1,
      c2 _ (hx' _ (by decide)) (by decide), g1 _ (by decide), hp]
    exact add_one_toWord p
  · rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, eA]; omega), rd_set_ne (show eP ≠ eA by decide),
      rd_set_ne (show eP ≠ cOne by decide), h1, c2 _ (hx' _ (by decide)) (by decide), g1 _ (by decide), hx]
    exact add_one_toWord x
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm b, Ne.symm c⟩), c2 _ e d, g1 _ a]

/-- **The tape-to-heap copy.** -/
theorem thcpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a dst n : ℕ} (ha : a + n < 2 ^ 63)
    (hd : regs ≤ dst) (hd2 : dst + n < 2 ^ 63) (hds : dst + n ≤ s.M.size) :
    (∀ j < n, rd (semXIR I (thcpIR a dst n) s).M (dst + j) = I.getD (a + j) 0) ∧
    (∀ y, regs ≤ y → (y < dst ∨ dst + n ≤ y) → rd (semXIR I (thcpIR a dst n) s).M y = rd s.M y) ∧
    Inv (semXIR I (thcpIR a dst n) s).M ∧ (semXIR I (thcpIR a dst n) s).M.size = s.M.size ∧
    (semXIR I (thcpIR a dst n) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs hd
  have hwf := wf_thcpIR a dst n
  have hO : (semXIR I (thcpIR a dst n) s).o = s.o := sem_o I _ s rfl
  rw [thcpIR, semXIR_seq] at hO ⊢
  set B := (Prim.const eP (toWord a)) :: (Prim.const eA (toWord dst)) :: [Prim.const eN (toWord n)]
  have hM1 := inv_sem I hwf.1 hM
  have v : rd (semXIR I (.blk B) s).M eP = toWord a ∧ rd (semXIR I (.blk B) s).M eA = toWord dst ∧
      rd (semXIR I (.blk B) s).M eN = toWord n := by
    rw [semXIR_blk_M]; simp only [B, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;> simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eA → y ≠ eN → rd (semXIR I (.blk B) s).M y = rd s.M y :=
    fun y x1 x2 x3 => rd_blk_of_not_dst I _ s (by
      simp only [B, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · exact Ne.symm x1
      · exact Ne.symm x2
      · exact Ne.symm x3)
  have z1 := size_sem I (.blk B) s
  obtain ⟨v1, v2, v3⟩ := v
  generalize semXIR I (.blk B) s = s1 at hM1 v1 v2 v3 f1 z1 hO
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M eP = toWord (a + j) ∧
    rd t.M eA = toWord (dst + j) ∧ (∀ i < j, rd t.M (dst + i) = I.getD (a + i) 0) ∧
    (∀ y, regs ≤ y → (y < dst ∨ dst + j ≤ y) → rd t.M y = rd s.M y)
  have h0 : Q 0 ⟨entryK eC eN (toWord n) s1.M, s1.o⟩ := by
    refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], by rw [entryK_frame _ (by decide)
      (by decide), v1, Nat.add_zero], by rw [entryK_frame _ (by decide) (by decide), v2, Nat.add_zero],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    simp only [regs] at hy
    rw [entryK_frame _ (by simp only [eC]; omega) (by simp only [cTmp]; omega),
      f1 _ (by simp only [eP]; omega) (by simp only [eA]; omega) (by simp only [eN]; omega)]
  have hstep : ∀ j t, j < n → Q j t → Q (j + 1) (decS eC (semXIR I thcpBody t)) := by
    intro j t hj ⟨q1, q2, q3, q4, q5, q6⟩
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := thcpBody_sem I t q1 q3 q4 (by omega) (by simp only [regs]; omega)
      (by omega) (by rw [q2]; omega)
    have hrd : ∀ y, y ≠ eC → rd (decS eC (semXIR I thcpBody t)).M y = rd (semXIR I thcpBody t).M y :=
      fun y hy => rd_decS (Ne.symm hy) _
    refine ⟨inv_decS b5 (by decide), by rw [size_decS, b6, q2], by rw [hrd _ (by decide), b2, Nat.add_assoc],
      by rw [hrd _ (by decide), b3, Nat.add_assoc], fun i hi => ?_, fun y hy hy' => ?_⟩
    · rw [hrd _ (by simp only [eC]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [b4 _ (by simp only [eW]; omega) (by simp only [eP]; omega) (by simp only [eA]; omega)
          (by simp only [cTmp]; omega) (by omega), q5 i h]
      · exact b1
    · simp only [regs] at hy
      rw [hrd _ (by simp only [eC]; omega), b4 _ (by simp only [eW]; omega) (by simp only [eP]; omega)
        (by simp only [eA]; omega) (by simp only [cTmp]; omega) (by omega), q6 _ (by simp only [regs]; omega)
        (by omega)]
  obtain ⟨r1, r2, -, -, r5, r6⟩ := loopK_run I thcpBody Q ⟨s1.M, s1.o⟩ hM1 (by decide) (by decide)
    (by decide) v3 (by omega) h0 hstep
  exact ⟨r5, r6, r1, r2, hO⟩

theorem cost_thcpIR (a dst n t : ℕ) (hn : n < 2 ^ 64) : cost (thcpIR a dst n) t = 14 + n * 13 := by
  simp only [thcpIR, thcpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

end Lvm.X
