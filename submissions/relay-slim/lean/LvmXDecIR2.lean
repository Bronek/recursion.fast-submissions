-- WP-13b: the decoder's phases composed (new; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b, one level here).
import LvmXDecIR

/-!
# The decoder after the `eq` table: semantics of the phases and of `decMain`

* `encC_sem`, `encIR_sem`: `Enc₀(f₁)`'s three coordinates at `encB + c·2^15 + q`.
* `bflyAll_sem`: the 64 rows at `oB` become their novel-basis coefficients.
* `decTail_sem`: on a list of `≥ 2^13` agreeing positions at `agB`, the message at `mB`.
* **`decMain_sem`**: `encIR ; agreeIR ; okIR ; (decTail if ok)`: the flag at `okB` is
  `[2^13 ≤ |agreeL|]`, and on success the `2^19` words at `mB` are `decodeRec`'s.

`DecLay dB wB aB fB sz`: the workspace `[dB, dB + 2^21)` inside the memory, the inputs (word at
`wB`, `2^21` words; `α` at `aB`, 18; `f₁` at `fB`, `3·2^13`) outside it, every address below `2^60`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- The decoder's memory layout. -/
structure DecLay (dB wB aB fB sz : ℕ) : Prop where
  r : regs ≤ dB
  t : dB + 2 ^ 21 < 2 ^ 60
  z : dB + 2 ^ 21 ≤ sz
  rW : regs ≤ wB
  tW : wB + 2 ^ 21 < 2 ^ 60
  dW : wB + 2 ^ 21 ≤ dB ∨ dB + 2 ^ 21 ≤ wB
  rA : regs ≤ aB
  tA : aB + 18 < 2 ^ 60
  dA : aB + 18 ≤ dB ∨ dB + 2 ^ 21 ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ 13 < 2 ^ 60
  dF : fB + 3 * 2 ^ 13 ≤ dB ∨ dB + 2 ^ 21 ≤ fB

/-- The table hypothesis of the NTTs. -/
def TabOk (M : Mem) (tb : ℕ) : Prop :=
  ∀ v < nLog, ∀ i < nLog, rdK M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0

theorem tabOk_congr {M M' : Mem} {tb : ℕ} (h : TabOk M tb)
    (hf : ∀ x, tb ≤ x → x < tb + 225 → rd M' x = rd M x) : TabOk M' tb := fun v hv i hi => by
  have : 15 * v + i < 225 := by simp only [nLog] at hv hi; omega
  simp only [rdK]; rw [hf _ (by omega) (by omega)]; exact h v hv i hi

/-! ## `Enc₀(f₁)` -/

/-- **One coordinate of `Enc₀(f₁)`.** -/
theorem encC_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB c : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hc : c < 3) (hT : TabOk s.M (tbB dB)) :
    (∀ j < 2 ^ 15, rdK (semXIR I (encC dB fB c) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB + c * 2 ^ 15 ∨ encB dB + c * 2 ^ 15 + 2 ^ 15 ≤ x) →
      rd (semXIR I (encC dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (encC dB fB c) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  set A := encB dB + c * 2 ^ 15 with hA
  have hAd : dB + 2 ^ 16 ≤ A ∧ A + 2 ^ 15 ≤ dB + 2 ^ 18 := by
    simp only [hA, encB]; constructor <;> omega
  rw [encC, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ 13) (src := fB + c) (str := 3) (dst := A)
    (by norm_num) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ 13) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ 13) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ 15 - 2 ^ 13) (dst := A + 2 ^ 13)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1
  generalize semXIR I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; omega)]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; omega)
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  -- the heap of `s3`
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ 15 ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOk s3.M (tbB dB) := tabOk_congr hT fun x h1 h2 => h3 x (by simp only [regs, tbB] at *; omega)
    (by simp only [tbB] at *; omega)
  have hY : ∀ i < 2 ^ 15, rdK s3.M (A + i) =
      if h : i < 2 ^ 13 then (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ 13
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ 13 + (i - 2 ^ 13) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdIR_enc I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (m := 13) (by decide) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3
    (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdIR_sem I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (Y := fun i => rdK s3.M (A + i))
    (by decide) (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc₀(f₁)`'s three coordinates** at `encB + c·2^15 + j`. -/
theorem encIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) :
    (∀ c < 3, ∀ j < 2 ^ 15, rdK (semXIR I (encIR dB fB) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ x) →
      rd (semXIR I (encIR dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (encIR dB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rF
  rw [encIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := encC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (encC dB fB 0) s
  generalize semXIR I (encC dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 2 ^ 15 ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := encC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (encC dB fB 1) s1
  generalize semXIR I (encC dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := encC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ 13 → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, encB] at *; omega
  have e1 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have e2 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact e1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega),
        b2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      rw [show wK (rd s2.M (encB dB + 1 * 2 ^ 15 + j)) = rdK s2.M (encB dB + 1 * 2 ^ 15 + j) from rfl,
        b1 j hj]
      congr 1; funext x; exact e1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact e2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

theorem bflyIR_nw_hi (ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (bflyIR ℓ tb) r := by
  intro hw
  simp only [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

/-- **The inverse NTT of the 64 rows** at `oB`. -/
theorem bflyAll_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < 64, ∀ i < 2 ^ 13, rdK s.M (oB dB + t * 2 ^ 13 + i) = Y t i) :
    (∀ t < 64, ∀ i < 2 ^ 13, rdK (semXIR I (bflyAll dB) s).M (oB dB + t * 2 ^ 13 + i) =
      coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + 2 ^ 19 ≤ x) → rd (semXIR I (bflyAll dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyAll dB) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r hs
  rw [bflyAll, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN 64]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN 64]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zN = toWord 64 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN 64]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ 13, rdK s'.M (oB dB + t * 2 ^ 13 + i) = coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x) → rd s'.M x = rd s.M x)
  have hoB : oB dB = dB + 2 ^ 19 := rfl
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS zC (semXIR I (bflyRow dB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bflyRow, semXIR_seq]
    set A := oB dB + j * 2 ^ 13 with hA
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
        .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)),
        .op .mul rA0 zT zK, .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hAv : A = dB + 2 ^ 19 + j * 2 ^ 13 := by simp only [hA, oB]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x hx1' hx2' => by
      simp only [tbB] at hx1' hx2'
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ 13, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hAv,
        show dB + 2 ^ 19 + j * 2 ^ 13 + i = oB dB + j * 2 ^ 13 + i by rw [hoB],
        i5 _ (by simp only [regs, hoB] at *; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    have hjb : j * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 19 := by omega
    obtain ⟨-, b2, hM2⟩ := bflyIR_sem I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have b1 := bflyIR_coeffs I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyIR 13 (tbB dB)) s1).M zT = toWord j := by
      rw [frame I _ s1 (by simp +decide [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR,
        alphaBody, arithIR, addK, mulK, mulKC, redC, WF, Writes, Prim.dst, rLv, rTr, rN3, rC3, rQ,
        rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW,
        fH, fT, fN, cTmp, regs]) hM1 zT (by decide) (bflyIR_nw_hi 13 _ (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyIR 13 (tbB dB)) s1
    generalize semXIR I (bflyIR 13 (tbB dB)) s1 = s2 at b1 b2 hM2 q2 z2
    have hd : ∀ x, x ≠ zC → rd (decS zC (semXIR I (.blk [.op .add zT zT cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have c2 : ∀ x, x ≠ zT → rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x = rd s2.M x :=
      fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm hx)
    have hM3 := inv_sem I (P := .blk [.op .add zT zT cOne]) (by simp +decide [WF, Prim.dst, zT]) hM2
    have hx3 : ∀ x, regs ≤ x → x ≠ zC ∧ x ≠ zT := fun x hx => by
      simp only [regs, zC, zT] at *; omega
    refine ⟨inv_decS hM3 (by decide), by rw [size_decS, size_sem, z2, z1, i2], ?_,
      fun t ht i hi => ?_, fun x hx hx2 => ?_⟩
    · have hs2 := hM2.1
      simp only [regs] at hs2
      rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [zT]; omega), q2, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
        add_one_toWord]
    · have hxr : regs ≤ oB dB + t * 2 ^ 13 + i := by simp only [regs, oB] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ 13 + 2 ^ 13 ≤ j * 2 ^ 13 := by nlinarith
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ 13 = j * 2 ^ 13 + 2 ^ 13 := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right (oB dB) (j * 2 ^ 13)))
        · rw [← Nat.add_assoc] at h; exact Or.inr h
      have hx5 : x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _) h)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bflyRow dB) P s0 hM0 (c := zC) (n := zN) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx
    (by rw [show 64 * 2 ^ 13 = 2 ^ 19 by norm_num]; exact hx2), hfin.1⟩

end Lvm.X
