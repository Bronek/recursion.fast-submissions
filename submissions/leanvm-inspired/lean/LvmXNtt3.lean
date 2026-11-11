-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly,
-- part "The basis table": rdF_add_one, wRow_zero_getD … wtabIR_sem).
-- New for lvm (WP-13b); namespace `FR.X` → `Lvm.X`. Re-targeted from FR's two-word `F` and
-- domain `D` to lvm's one-word `K = BF64` and domain `ptK` (row `0` is the word `2^i`; element
-- stride 2 → 1, row stride 40 → 15, 20 rows of 20 → 15 of 15).
import LvmXNtt2

/-!
# The basis table on the machine

**`wtabIR_sem`**: `wtabIR tb` writes the rows `wRow ptK 15 v`, `v < 15`, at `tb + 15 v + i`
(`wtabIR_normW`: entry `(v, i)` is `Ŵ_v(ptK 2^i)`, `Lvm.Nb.wRow_spec`) and keeps the heap outside
`[tb, tb + 225)`. Row `0` is `ptK (2^i)` (`row0IR_sem`); row `j + 1` is
`R i (R i + 1) (b (b + 1))⁻¹` with `b = R (j + 1)` (`rowIR_sem`, LCH's recursion `wRow`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

theorem wK_add_one (a : Word) : wK (a ^^^ 1) = wK a + 1 := wK_xor a 1

theorem wRow_zero_getD {i : ℕ} (hi : i < 15) : (wRow ptK nLog 0).getD i 0 = ptK (2 ^ i) := by
  simp [wRow, hi, List.getD_eq_getElem?_getD, ptK_zero, show ptK 1 = 1 from rfl]

theorem wRow_succ_getD (v : ℕ) {i : ℕ} (hi : i < 15) : (wRow ptK nLog (v + 1)).getD i 0 =
    (wRow ptK nLog v).getD i 0 * ((wRow ptK nLog v).getD i 0 + 1) *
      ((wRow ptK nLog v).getD (v + 1) 0 * ((wRow ptK nLog v).getD (v + 1) 0 + 1))⁻¹ := by
  rw [wRow]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, wRow_length]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0]
  rfl

/-- One entry of row `0`: `ptK (2^i)` at `tb + i`. -/
theorem row0Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb i : ℕ} (hi : i < 15)
    (htb : regs ≤ tb) (htb2 : tb + 15 < 2 ^ 64) (hsz : tb + 15 ≤ s.M.size)
    (hI : rd s.M uI = toWord i) (hTa : rd s.M rTa = toWord (tb + i)) :
    rdK (semXIR I row0Body s).M (tb + i) = ptK (2 ^ i) ∧
    (∀ x, regs ≤ x → x ≠ tb + i → rd (semXIR I row0Body s).M x = rd s.M x) ∧
    rd (semXIR I row0Body s).M uI = toWord (i + 1) ∧
    rd (semXIR I row0Body s).M rTa = toWord (tb + (i + 1)) ∧
    rd (semXIR I row0Body s).M rTr = rd s.M rTr := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w1 : WF (.blk [.op .shl fG cOne uI]) := by simp +decide only [WF, Prim.dst, fG]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shl fG cOne uI]) s (by simp +decide only [Lo, Prim.dst, regs, fG])
  have r1 : rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M fG = toWord (2 ^ i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTa = toWord (tb + i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M uI = toWord i ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTr = rd s.M rTr := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fG]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hI, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by omega)
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.one_mul]
    · exact hTa
    · exact hI
  rw [row0Body, semXIR_seq]
  have z1 := size_sem I (.blk [.op .shl fG cOne uI]) s
  generalize semXIR I (.blk [.op .shl fG cOne uI]) s = s1 at hM1 hH1 r1 z1
  obtain ⟨g1, a1, i1, t1⟩ := r1
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := rTa) (v := fG) (x := tb + i) (by decide)
    (by decide) a1 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rTa fG) s1 = s2 at c1 c2 hM2
  have hT4 : cTmp = 4 := rfl
  have hr2 : ∀ r, r < 256 → r ≠ cTmp → rd s2.M r = rd s1.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have hb : ∀ x, x ≠ rTa → x ≠ uI → rd (semXIR I (.blk [.op .add rTa rTa cOne,
      .op .add uI uI cOne]) s2).M x = rd s2.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hs2 := hM2.1
  simp only [regs] at hs2
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; omega) (by simp only [uI]; omega)), rdK_eq c1, rdK, g1]
    rfl
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; omega) (by simp only [uI]; omega), c2 _ x1 (by omega),
      hH1 x (by simp only [regs]; omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), i1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), a1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
    rfl
  · rw [hb _ (by decide) (by decide), hr2 _ (by decide) (by decide), t1]

theorem wf_row0Body : WF row0Body := by
  simp +decide only [row0Body, WF, Prim.dst, fG, rTa, uI, cTmp, and_true]

/-- **Row `0`** at `rTr = tb`: `ptK (2^i)` at `tb + i`, `i < 15`. -/
theorem row0IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 15 < 2 ^ 64) (hsz : tb + 15 ≤ s.M.size) (hTr : rd s.M rTr = toWord tb) :
    (∀ i < 15, rdK (semXIR I row0IR s).M (tb + i) = ptK (2 ^ i)) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 15 ≤ x) → rd (semXIR I row0IR s).M x = rd s.M x) ∧
    rd (semXIR I row0IR s).M rTr = toWord tb ∧ Inv (semXIR I row0IR s).M ∧
    (semXIR I row0IR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w0 : WF (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) := by
    simp +decide only [WF, Prim.dst, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
  have hH0 := hframe I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
    (by simp +decide only [Lo, Prim.dst, regs, uI, rTa, rN2])
  have r0 : rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M uI =
        toWord 0 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rTa =
        toWord (tb + 0) ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rN2 = 15 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rTr =
        toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hTr
  rw [row0IR, semXIR_seq]
  generalize semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨i0, a0, n0, t0⟩ := r0
  rw [loopK_eq I row0Body s0 hM0 (by decide) (by decide) (by decide) n0]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 15 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 15) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M uI = toWord j ∧ rd s'.M rTa = toWord (tb + j) ∧ rd s'.M rTr = toWord tb ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + j ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < j, rdK s'.M (tb + i) = ptK (2 ^ i)
  have step : ∀ j s', j < 15 → P j s' → P (j + 1) (decS rC2 (semXIR I row0Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := row0Body_sem I s' i1 hj (by simp only [regs]; omega) htb2
      (by omega) i3 i4
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I row0Body s')).M x =
        rd (semXIR I row0Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS (inv_sem I wf_row0Body i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [hd _ (by decide), e4], by rw [hd _ (by decide), e5, i5],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
    · rw [rdK_eq (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = j
      · subst h; exact e1
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i7 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 15 s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
  have := iterL_ind (f := semXIR I row0Body) (c := rC2) (m := 15) P step 15 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6, f7⟩ := this
  exact ⟨f7, fun x hx hx2 => f6 x hx (by omega), f5, f1, f2⟩

/-- `a + 1` on the machine: `fW := fU + 1`. -/
theorem plusOne_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdK (semXIR I (.blk [.op .xor fW fU cOne]) s).M fW = rdK s.M fU + 1 ∧
    ∀ x, x ≠ fW → rd (semXIR I (.blk [.op .xor fW fU cOne]) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun x h1 => rd_runPrims_of_not_writes (by
    simp [Prim.dst]; exact Ne.symm h1) _⟩
  simp only [semXIR, runPrims, List.foldl, Prim.run, rdK]
  simp (disch := first | decide | (simp only [size_set, fW]; omega)) only [rd_set_self, rd_set_ne]
  rw [show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor]
  exact wK_add_one _

theorem wf_plusOne : WF (.blk [.op .xor fW fU cOne]) := by
  simp +decide only [WF, Prim.dst, fW]

/-- **One entry of row `j + 1`**: `a (a + 1) c` at `ta + 15 + k`, `a` the entry at `ta + k`,
`c` in `fAl`. -/
theorem rowBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta k : ℕ} (hk : k < 15)
    (hta : regs ≤ ta) (hta2 : ta + 30 < 2 ^ 64) (hsz : ta + 30 ≤ s.M.size)
    (hTa : rd s.M rTa = toWord (ta + k)) :
    rdK (semXIR I rowBody s).M (ta + 15 + k) =
      rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl ∧
    (∀ x, regs ≤ x → x ≠ ta + 15 + k → rd (semXIR I rowBody s).M x = rd s.M x) ∧
    rd (semXIR I rowBody s).M rTa = toWord (ta + (k + 1)) ∧
    rdK (semXIR I rowBody s).M fAl = rdK s.M fAl ∧
    rd (semXIR I rowBody s).M rTr = rd s.M rTr ∧ rd (semXIR I rowBody s).M rLv = rd s.M rLv := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- load `a`
  obtain ⟨u1, u3, hM1⟩ := load_sem I s hM (d := fU) (p := rTa) (by decide) (by decide) hTa
    (by omega)
  have y1 := size_sem I (.load fU rTa) s
  rw [rowBody, semXIR_seq]
  generalize semXIR I (.load fU rTa) s = s1 at u1 u3 hM1 y1
  -- `a + 1`
  obtain ⟨v1, v2⟩ := plusOne_sem I s1 hM1
  have hM2 := inv_sem I wf_plusOne hM1
  have y2 := size_sem I (.blk [.op .xor fW fU cOne]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s1 = s2 at v1 v2 hM2 y2
  -- the products
  have m3 := mulK_sem (I := I) (s := s2) hM2 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s2).M i = rd s2.M i :=
    fun i h0 h1 => mulK_frame I s2 h0 h1
  have hM3 := inv_sem I (wf_mulK fH fU fW (by decide)) hM2
  have y3 := size_sem I (mulK fH fU fW) s2
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s2 = s3 at m3 f3 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fN) (a := fH) (b := fAl) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fN → rd (semXIR I (mulK fN fH fAl) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fN fH fAl (by decide)) hM3
  have y4 := size_sem I (mulK fN fH fAl) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fN fH fAl) s3 = s4 at m4 f4 hM4 y4
  -- facts on `s4`
  have k4 : ∀ x, 256 ≤ x → rd s4.M x = rd s.M x := fun x hx => by
    rw [f4 x (by omega) (by simp only [fN]; omega), f3 x (by omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega), u3 x (by simp only [fU]; omega)]
  have r4 : ∀ r, (r = rTa ∨ r = rTr ∨ r = rLv ∨ r = fAl) → rd s4.M r = rd s.M r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
      rw [f4 _ (by decide) (by decide), f3 _ (by decide) (by decide), v2 _ (by decide),
        u3 _ (by decide)]
  have n4 : rdK s4.M fN = rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl := by
    have al2 : rdK s2.M fAl = rdK s.M fAl :=
      rdK_eq ((v2 _ (by decide)).trans (u3 _ (by decide)))
    have al3 : rdK s3.M fAl = rdK s.M fAl := (rdK_eq (f3 _ (by decide) (by decide))).trans al2
    have fu2 : rdK s2.M fU = rdK s.M (ta + k) := (rdK_eq (v2 _ (by decide))).trans (rdK_eq u1)
    rw [m4, m3, v1, al3, fu2, rdK_eq u1]
  -- the address
  have hs4 := hM4.1
  simp only [regs] at hs4
  have a5 : rd (semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4).M rAH =
      toWord (ta + 15 + k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rAH]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r4 _ (.inl rfl), hTa, show (15 : Word) = toWord 15 from rfl, add_toWord]
    congr 1; omega
  have b5 : ∀ x, x ≠ uT1 → x ≠ rAH → rd (semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1])
      s4).M x = rd s4.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM5 := inv_sem I (P := .blk [.const uT1 15, .op .add rAH rTa uT1])
    (by simp +decide only [WF, Prim.dst, uT1, rAH]) hM4
  have z5 := size_sem I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4 = s5 at a5 b5 hM5 z5
  -- the store
  obtain ⟨c1, c2, hM6⟩ := store_sem I s5 hM5 (p := rAH) (v := fN) (x := ta + 15 + k)
    (by decide) (by decide) a5 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fN) s5 = s6 at c1 c2 hM6
  have hr6 : ∀ r, r < 256 → r ≠ cTmp → rd s6.M r = rd s5.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have hb : ∀ x, x ≠ rTa → rd (semXIR I (.blk [.op .add rTa rTa cOne]) s6).M x = rd s6.M x :=
    fun x h1 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h1) _
  have hs6 := hM6.1
  simp only [regs] at hs6
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; omega)), rdK_eq c1,
      rdK_eq (b5 _ (by decide) (by decide)), n4]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; omega), c2 _ x1 (by omega), b5 _ (by simp only [uT1]; omega)
      (by simp only [rAH]; omega), k4 x hx]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr6 _ (by decide) (by decide), b5 _ (by decide) (by decide), r4 _ (.inl rfl), hTa,
      hr6 _ (by decide) (by decide), show rd s5.M cOne = 1 from hM5.2 0 (by decide),
      add_one_toWord]
    rfl
  · exact rdK_eq ((hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inr rfl)))))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inl rfl)))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inl rfl))))))

set_option maxRecDepth 8000 in
/-- **Row `j + 1`** from row `j` (`R`, at `ta = rTr`; `rLv = j`, `j + 1 < 15`):
`R i (R i + 1) (b (b + 1))⁻¹` at `ta + 15 + i`, `b = R (j + 1)`. -/
theorem rowIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta j : ℕ} {R : ℕ → BF64}
    (hj : j + 1 < 15) (hta : regs ≤ ta) (hta2 : ta + 30 < 2 ^ 64) (hsz : ta + 30 ≤ s.M.size)
    (hLv : rd s.M rLv = toWord j) (hTr : rd s.M rTr = toWord ta)
    (hR : ∀ i < 15, rdK s.M (ta + i) = R i) :
    (∀ i < 15, rdK (semXIR I rowIR s).M (ta + 15 + i) =
      R i * (R i + 1) * (R (j + 1) * (R (j + 1) + 1))⁻¹) ∧
    (∀ x, regs ≤ x → (x < ta + 15 ∨ ta + 30 ≤ x) → rd (semXIR I rowIR s).M x = rd s.M x) ∧
    rd (semXIR I rowIR s).M rLv = toWord (j + 1) ∧ rd (semXIR I rowIR s).M rTr = toWord (ta + 15) ∧
    Inv (semXIR I rowIR s).M ∧ (semXIR I rowIR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- `rTa := ta + (j + 1)`
  have r1 : rd (semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s).M rTa =
      toWord (ta + (j + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hLv, hTr, show rd s.M cOne = 1 from hM.2 0 (by decide), add_one_toWord, add_toWord]
  have b1 : ∀ x, x ≠ uT1 → x ≠ rTa → rd (semXIR I (.blk [.op .add uT1 rLv cOne,
      .op .add rTa rTr uT1]) s).M x = rd s.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM1 := inv_sem I (P := .blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1])
    (by simp +decide only [WF, Prim.dst, uT1, rTa]) hM
  have y1 := size_sem I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s
  rw [rowIR, semXIR_seq]
  generalize semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s = s1 at r1 b1 hM1 y1
  -- `b`
  obtain ⟨u1, u3, hM2⟩ := load_sem I s1 hM1 (d := fU) (p := rTa) (by decide) (by decide) r1
    (by omega)
  have y2 := size_sem I (.load fU rTa) s1
  rw [semXIR_seq]
  generalize semXIR I (.load fU rTa) s1 = s2 at u1 u3 hM2 y2
  have hb2 : rdK s2.M fU = R (j + 1) := by
    rw [rdK_eq u1, ← hR (j + 1) hj]
    exact rdK_eq (b1 _ (by simp only [uT1]; omega) (by simp only [rTa]; omega))
  obtain ⟨v1, v2⟩ := plusOne_sem I s2 hM2
  have hM3 := inv_sem I wf_plusOne hM2
  have y3 := size_sem I (.blk [.op .xor fW fU cOne]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s2 = s3 at v1 v2 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fH fU fW (by decide)) hM3
  have y4 := size_sem I (mulK fH fU fW) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s3 = s4 at m4 f4 hM4 y4
  have i5 := invK_sem (I := I) (s := s4) hM4 (d := fAl) (a := fH) (by decide) (by decide)
  have f5 : ∀ i, 12 ≤ i → i ≠ fAl → rd (semXIR I (invK fAl fH) s4).M i = rd s4.M i :=
    fun i h0 h1 => by rw [invK, sem_blk]; exact invKC_frame _ _ (.inr h0) h1 _
  have hM5 := inv_sem I (wf_invK fAl fH (by decide)) hM4
  have y5 := size_sem I (invK fAl fH) s4
  rw [semXIR_seq]
  generalize semXIR I (invK fAl fH) s4 = s5 at i5 f5 hM5 y5
  have c5 : rdK s5.M fAl = (R (j + 1) * (R (j + 1) + 1))⁻¹ := by
    rw [i5, m4, v1, rdK_eq (v2 _ (by decide)), hb2]
  have k5 : ∀ x, 256 ≤ x → rd s5.M x = rd s.M x := fun x hx => by
    rw [f5 x (by omega) (by simp only [fAl]; omega), f4 x (by omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega), u3 x (by simp only [fU]; omega),
      b1 x (by simp only [uT1]; omega) (by simp only [rTa]; omega)]
  have r5 : ∀ r, (r = rTr ∨ r = rLv) → rd s5.M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl <;>
    rw [f5 _ (by decide) (by decide), f4 _ (by decide) (by decide), v2 _ (by decide),
      u3 _ (by decide), b1 _ (by decide) (by decide)]
  -- the entries
  have hs5 := hM5.1
  simp only [regs] at hs5
  have r6 : rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5).M rTa = toWord (ta + 0) ∧
      rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5).M rN2 = 15 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r5 _ (.inl rfl), hTr, or_self_eval]; rfl
  have b6 : ∀ x, x ≠ rTa → x ≠ rN2 → rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15])
      s5).M x = rd s5.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM6 := inv_sem I (P := .blk [.op .or rTa rTr rTr, .const rN2 15])
    (by simp +decide only [WF, Prim.dst, rTa, rN2]) hM5
  have y6 := size_sem I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5 = s6 at r6 b6 hM6 y6
  obtain ⟨a6, n6⟩ := r6
  rw [semXIR_seq, loopK_eq I rowBody s6 hM6 (by decide) (by decide) (by decide) n6]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 15 s6.M) i = rd s6.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 15) hM6 (by decide)
  let c := (R (j + 1) * (R (j + 1) + 1))⁻¹
  let P : ℕ → St → Prop := fun k s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rTa = toWord (ta + k) ∧ rdK s'.M fAl = c ∧ rd s'.M rTr = toWord ta ∧
    rd s'.M rLv = toWord j ∧
    (∀ x, regs ≤ x → (x < ta + 15 ∨ ta + 15 + k ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < k, rdK s'.M (ta + 15 + i) = R i * (R i + 1) * c
  have step : ∀ k s', k < 15 → P k s' → P (k + 1) (decS rC2 (semXIR I rowBody s')) := by
    rintro k s' hk ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowBody_sem I s' i1 hk (by simp only [regs]; omega) hta2
      (by omega) i3
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I rowBody s')).M x =
        rd (semXIR I rowBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hRk : rdK s'.M (ta + k) = R k := by
      rw [← hR k hk]
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    refine ⟨inv_decS (inv_sem I wf_rowBody i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [rdK_decS _ (by decide), e4, i4],
      by rw [hd _ (by decide), e5, i5], by rw [hd _ (by decide), e6, i6],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i7 x (by simp only [regs]; omega) (by omega)]
    · rw [rdK_eq (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = k
      · subst h; rw [e1, hRk, i4]
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i8 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 15 s6.M, s6.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, y6, y5, y4, y3, y2, y1], ?_, ?_, ?_, ?_,
      fun x hx _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), a6]
    · dsimp only
      rw [rdK_eq ((hE _ (by decide) (by decide)).trans (b6 _ (by decide) (by decide))), c5]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inl rfl), hTr]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inr rfl), hLv]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC2]; omega) (by omega), b6 _ (by simp only [rTa]; omega)
        (by simp only [rN2]; omega), k5 x hx]
  have := iterL_ind (f := semXIR I rowBody) (c := rC2) (m := 15) P step 15 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  rw [show (15 : Word).toNat = 15 from rfl]
  generalize iterL (semXIR I rowBody) rC2 15 ⟨entryK rC2 rN2 15 s6.M, s6.o⟩ = s7 at this ⊢
  obtain ⟨g1, g2, -, -, g5, g6, g7, g8⟩ := this
  have hs7 := g1.1
  simp only [regs] at hs7
  have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
      .const uT1 15, .op .add rTr rTr uT1]) s7).M x = rd s7.M x := fun x h1 h2 h3 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
  have wfin : WF (.blk [.op .add rLv rLv cOne, .const uT1 15, .op .add rTr rTr uT1]) := by
    simp +decide only [WF, Prim.dst, rLv, uT1, rTr]
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, ?_, ?_, inv_sem I wfin g1, ?_⟩
  rotate_left 4
  · rw [size_sem, g2]
  · rw [rdK_eq (hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega)
      (by simp only [rTr]; omega)), g8 i hi]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega) (by simp only [rTr]; omega),
      g7 x (by simp only [regs]; omega) (by omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g6, show rd s7.M cOne = 1 from g1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g5, show (15 : Word) = toWord 15 from rfl, add_toWord]

/-- **The basis table** (`wtabIR tb`): the rows `wRow ptK 15 v`, `v < 15`, at `tb + 15 v + i`;
the heap outside `[tb, tb + 225)` is kept. -/
theorem wtabIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 225 < 2 ^ 64) (hsz : tb + 225 ≤ s.M.size) :
    (∀ v < nLog, ∀ i < nLog, rdK (semXIR I (wtabIR tb) s).M (tb + 15 * v + i) =
      (wRow ptK nLog v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 225 ≤ x) → rd (semXIR I (wtabIR tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (wtabIR tb) s).M ∧ (semXIR I (wtabIR tb) s).M.size = s.M.size := by
  have hs := hM.1
  have hN : nLog = 15 := rfl
  simp only [regs] at hs htb
  have hT4 : cTmp = 4 := rfl
  have w0 : WF (.blk [.const rTr (toWord tb)]) := by simp +decide only [WF, Prim.dst, rTr,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rTr (toWord tb)]) s
  have hH0 := hframe I (.blk [.const rTr (toWord tb)]) s (by simp +decide only [Lo, Prim.dst, regs,
    rTr, List.mem_cons, List.mem_nil_iff, forall_eq, or_false])
  have t0 : rd (semXIR I (.blk [.const rTr (toWord tb)]) s).M rTr = toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTr]; omega)
  rw [wtabIR, semXIR_seq]
  generalize semXIR I (.blk [.const rTr (toWord tb)]) s = s0 at hM0 z0 hH0 t0
  obtain ⟨o1, o2, o3, hM1, z1⟩ := row0IR_sem I s0 hM0 (by simp only [regs]; omega) (by omega)
    (by omega) t0
  rw [semXIR_seq]
  generalize semXIR I row0IR s0 = s1 at o1 o2 o3 hM1 z1
  have r2 : rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M rN3 = 14 := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rN3]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have b2 : ∀ x, x ≠ rLv → x ≠ rN3 → rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M x =
      rd s1.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM2 := inv_sem I (P := .blk [.const rLv 0, .const rN3 14]) (by simp +decide only [WF,
    Prim.dst, rLv, rN3]) hM1
  have z2 := size_sem I (.blk [.const rLv 0, .const rN3 14]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rN3 14]) s1 = s2 at r2 b2 hM2 z2
  obtain ⟨l2, n2⟩ := r2
  rw [loopK_eq I rowIR s2 hM2 (by decide) (by decide) (by decide) n2,
    show (14 : Word).toNat = 14 from rfl]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 14 s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := 14) hM2 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + 15 * j) ∧
    (∀ v ≤ j, ∀ i < 15, rdK s'.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 15 * (j + 1) ≤ x) → rd s'.M x = rd s.M x)
  have step : ∀ j s', j < 14 → P j s' → P (j + 1) (decS rC3 (semXIR I rowIR s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowIR_sem I s' i1 (ta := tb + 15 * j)
      (R := fun i => (wRow ptK nLog j).getD i 0) (by omega) (by simp only [regs]; omega)
      (by omega) (by omega) i3 i4 (fun i hi => i5 j le_rfl i hi)
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I rowIR s')).M x =
        rd (semXIR I rowIR s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS e5 (by decide), by rw [size_decS, e6, i2], by rw [hd _ (by decide), e3],
      by rw [hd _ (by decide), e4, show tb + 15 * j + 15 = tb + 15 * (j + 1) by ring],
      fun v hv i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [rdK_eq (hd _ (by simp only [rC3]; omega))]
      by_cases h : v = j + 1
      · subst h
        rw [show tb + 15 * (j + 1) + i = tb + 15 * j + 15 + i by ring, e1 i hi,
          wRow_succ_getD j hi]
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i5 v (by omega) i hi]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
  have hP0 : P 0 ⟨entryK rC3 rN3 14 s2.M, s2.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z2, z1, z0], ?_, ?_, fun v hv i hi => ?_,
      fun x hx hx2 => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l2]
    · dsimp only
      rw [hE _ (by decide) (by decide), b2 _ (by decide) (by decide), o3]; rfl
    · obtain rfl : v = 0 := by omega
      dsimp only
      rw [rdK_eq ((hE _ (by simp only [rC3]; omega) (by omega)).trans
          (b2 _ (by simp only [rLv]; omega) (by simp only [rN3]; omega))),
        Nat.mul_zero, Nat.add_zero, o1 i hi, wRow_zero_getD hi]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC3]; omega) (by omega), b2 _ (by simp only [rLv]; omega)
        (by simp only [rN3]; omega), o2 x (by simp only [regs]; omega) (by omega),
        hH0 x (by simp only [regs]; omega)]
  have := iterL_ind (f := semXIR I rowIR) (c := rC3) (m := 14) P step 14 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6⟩ := this
  exact ⟨fun v hv i hi => f5 v (by omega) i (by omega), fun x hx hx2 => f6 x hx (by omega), f1, f2⟩

/-- **The table holds `Ŵ_v(ptK 2^i)`** (`Lvm.Nb.wRow_spec`). -/
theorem wtabIR_normW (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 225 < 2 ^ 64) (hsz : tb + 225 ≤ s.M.size) :
    ∀ v < nLog, ∀ i < nLog, rdK (semXIR I (wtabIR tb) s).M (tb + 15 * v + i) =
      (Lvm.Nb.normW ptK v).eval (ptK (2 ^ i)) := fun v hv i hi => by
  rw [(wtabIR_sem I s hM htb htb2 hsz).1 v hv i hi, wRow_spec ptK_xor ptK_injOn15 v hv i hi]

end Lvm.X
