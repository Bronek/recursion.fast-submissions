-- adapted from rf-k/submissions/flock-recursive/lean/FRXBary.lean@8bff272b (`aBody_sem`, `aLoop_sem`,
-- `cBody_sem`, `cLoop_sem`) for lvm (WP-13b): FR's two-word `F` re-targeted to `K = BF64`; a
-- coordinate's offset is `c` (FR: `2c` in `bCo`), the output cell `ob + k·c + s` (FR: `ob + 2kc + 2s`).
import LvmXInterp2

/-!
# The barycentric interpolation on the machine (2): one coordinate, the coordinate loop

`aLoop_sem`: `acc = Σ_{t<k} y_c(J_t) E[t]`; `cBody_sem`: `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)`;
**`cLoop_sem`**: every coordinate `c < C` of one target `s`.
-/

namespace Lvm.X

open RecursionFast Finset

attribute [local irreducible] entryK storeM

/-! ## Arithmetic of the cells -/

theorem lt_mulB {k c j : ℕ} (h : c < j) : k * c + k ≤ k * j := by
  have := Nat.mul_le_mul_left k (show c + 1 ≤ j by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- Output cell `(c, s)` lies in the output rows. -/
theorem out_ltB {k c C s : ℕ} (hc : c < C) (hs : s < k) : k * c + s < k * C := by
  have := lt_mulB (k := k) hc; omega

/-- Distinct targets have distinct output cells. -/
theorem cellB_ne {k c c' s s' : ℕ} (hs : s < k) (hs' : s' < k) (hne : s ≠ s') :
    k * c + s ≠ k * c' + s' := by
  intro h
  have h3 : c = c' := by
    have := congrArg (· / k) h
    rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs,
      Nat.div_eq_of_lt hs', add_zero, add_zero] at this
  subst h3; omega

/-- A column cell lies in the column store. -/
theorem ycell_lt {cs j c : ℕ} (hj : j < 2 ^ 15) (hc : c < cs) : cs * j + c < cs * 2 ^ 15 := by
  have := lt_mulB (k := cs) hj; omega

/-! ## One coordinate's accumulation -/

theorem lo_aBody (jb eb cb cs : ℕ) : Lo (aBody jb eb cb cs) := by
  simp [aBody, Lo, addrPs, addr1Ps, Prim.dst, regs, bK, bA, bJ, bT, fY, fX, fAc, bCi, fPr]
  exact lo_mulK (by decide)

theorem wf_aBody (jb eb cb cs : ℕ) : WF (aBody jb eb cb cs) := by
  simp [aBody, addrPs, addr1Ps, WF, Prim.dst, wfK_mul, bA, bK, bJ, fY, fX, fPr, fAc, bT, bCi]

/-- **One term of `acc`**: `acc += y(J_t) · E[t]`, `y(j)` at `cb + cs·j + c`. -/
theorem aBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb eb cb cs t c x : ℕ} {acc : BF64}
    (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hjb2 : jb + t < 2 ^ 64)
    (heb2 : eb + t < 2 ^ 64) (hcb2 : cb + cs * x + c < 2 ^ 64)
    (hBt : rd s.M bT = toWord t) (hCi : rd s.M bCi = toWord c) (hAc : rdK s.M fAc = acc)
    (hJ : rd s.M (jb + t) = toWord x) :
    rdK (semXIR I (aBody jb eb cb cs) s).M fAc =
      acc + rdK s.M (cb + cs * x + c) * rdK s.M (eb + t) ∧
    rd (semXIR I (aBody jb eb cb cs) s).M bT = toWord (t + 1) ∧
    Inv (semXIR I (aBody jb eb cb cs) s).M := by
  simp only [regs] at hjb heb hcb
  rw [aBody]
  simp only [semXIR_seq, sem_blk_append]
  -- `bA := jb + t`, `bJ := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := bJ) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; omega) (by simp only [bK]; omega), hJ] at l2
  generalize semXIR I (.load bJ bA) s1 = s2 at l2 f2 hM2
  have k2 : ∀ r, r ≠ bJ → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `bJ := cb + cs·x`, `bJ += c`
  obtain ⟨c3, f3, hM3⟩ := addr_sem I s2 hM2 (d := bJ) (i := bJ) (b := cb) (m := cs) (x := x)
    (by decide) (by decide) (by decide) (by decide) l2
  generalize semXIR I (.blk (addrPs bJ bJ cb cs)) s2 = s3 at c3 f3 hM3
  obtain ⟨c4, f4, hM4⟩ := bAdd_sem I s3 hM3 (d := bJ) (r := bCi) (x := cb + cs * x) (y := c)
    (by decide) (by decide) c3
    ((f3 _ (by decide) (by decide)).trans ((k2 _ (by decide) (by decide) (by decide)).trans hCi))
  generalize semXIR I (.blk [.op .add bJ bJ bCi]) s3 = s4 at c4 f4 hM4
  have k4 : ∀ r, r ≠ bJ → r ≠ bA → r ≠ bK → rd s4.M r = rd s.M r := fun r a b c =>
    (f4 r a).trans ((f3 r a c).trans (k2 r a b c))
  -- `fY := y(J_t)`
  obtain ⟨l5, f5, hM5⟩ := load_sem I s4 hM4 (d := fY) (p := bJ) (x := cb + cs * x + c)
    (by decide) (by decide) c4 hcb2
  have hy : rdK (semXIR I (.load fY bJ) s4).M fY = rdK s.M (cb + cs * x + c) :=
    rdK_congrB (l5.trans (k4 _ (by simp only [bJ]; omega) (by simp only [bA]; omega)
      (by simp only [bK]; omega)))
  generalize semXIR I (.load fY bJ) s4 = s5 at l5 f5 hM5 hy
  have k5 : ∀ r, r ≠ fY → r ≠ bJ → r ≠ bA → r ≠ bK → rd s5.M r = rd s.M r := fun r a b c d =>
    (f5 r a).trans (k4 r b c d)
  -- `fX := E[t]`
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := eb) (by decide)
    (by decide) (by decide) (by decide)
    ((k5 _ (by decide) (by decide) (by decide) (by decide)).trans hBt)
  generalize semXIR I (.blk (addr1Ps bA bT eb)) s5 = s6 at a6 f6 hM6
  obtain ⟨l7, f7, hM7⟩ := load_sem I s6 hM6 (d := fX) (p := bA) (x := eb + t) (by decide)
    (by decide) a6 heb2
  have he : rdK (semXIR I (.load fX bA) s6).M fX = rdK s.M (eb + t) :=
    rdK_congrB (l7.trans ((f6 _ (by simp only [bA]; omega) (by simp only [bK]; omega)).trans
      (k5 _ (by simp only [fY]; omega) (by simp only [bJ]; omega) (by simp only [bA]; omega)
        (by simp only [bK]; omega))))
  generalize semXIR I (.load fX bA) s6 = s7 at l7 f7 hM7 he
  have k7 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s7.M r = rd s5.M r := fun r a b c =>
    (f7 r a).trans (f6 r b c)
  -- `fPr := y · E`
  have m8 := mulK_sem (I := I) (s := s7) hM7 (d := fPr) (a := fY) (b := fX) (by decide)
    (by decide) (by decide) (by decide)
  rw [rdK_congrB (k7 fY (by decide) (by decide) (by decide)), hy, he] at m8
  have hM8 := inv_sem I (wf_mulK fPr fY fX (by decide)) hM7
  have k8 : ∀ r, 9 ≤ r → r ≠ fPr → r ≠ fX → r ≠ bA → r ≠ bK →
      rd (semXIR I (mulK fPr fY fX) s7).M r = rd s5.M r := fun r h0 a b c d =>
    (frK_mul h0 a).trans (k7 r b c d)
  generalize semXIR I (mulK fPr fY fX) s7 = s8 at m8 hM8 k8
  -- `fAc += fPr`, `t += 1`
  have hs8 := hM8.1
  have h1 : rd s8.M cOne = 1 := hM8.2 0 (by decide)
  have ac8 : rd s8.M fAc = rd s.M fAc := (k8 fAc (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans (k5 _ (by decide) (by decide) (by decide) (by decide))
  have t8 : rd s8.M bT = toWord t := (k8 bT (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans ((k5 _ (by decide) (by decide) (by decide) (by decide)).trans hBt)
  refine ⟨?_, ?_, inv_sem I (P := .blk [.op .xor fAc fAc fPr, .op .add bT bT cOne])
    (by simp [WF, Prim.dst, fAc, bT]) hM8⟩
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    rw [rdK]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs8))
      only [rd_set_self, rd_set_ne]
    rw [eval_xor, wK_xor, ac8]
    show rdK s.M fAc + rdK s8.M fPr = _
    rw [hAc, m8]
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs8))
      only [rd_set_self, rd_set_ne]
    rw [t8, h1, add_one_toWord]

/-- **The accumulation loop**: `acc = Σ_{t<k} y(J_t) · E[t]`. -/
theorem aLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb eb cb cs c : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + c < 2 ^ 64)
    (hN : rd s.M bN3 = toWord k) (hBt : rd s.M bT = toWord 0) (hCi : rd s.M bCi = toWord c)
    (hAc : rdK s.M fAc = 0) (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdK (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M fAc =
      ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) ∧
    Inv (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M ∧
    (∀ y, regs ≤ y → rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M y =
      rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M r = rd s.M r) := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧
    rdK st.M fAc = ∑ t ∈ range j, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) ∧
    rd st.M bT = toWord j ∧ (∀ y, regs ≤ y → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC3 → i ≠ cTmp → rd (entryK bC3 bN3 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  refine (loopK_run I (c := bC3) (n := bN3) (K := k) (aBody jb eb cb cs) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_entryK hM (by decide), ?_, ?_, fun y hy => ?_,
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_) |> fun h => ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [rdK_congrB (ef _ (by decide) (by decide)), hAc, sum_range_zero]
  · rw [ef _ (by decide) (by decide), hBt]
  · simp only [regs] at hy
    exact ef y (by simp only [bC3]; omega) (by simp only [cTmp]; omega)
  · rintro j st hj ⟨hM', hA, hT', hH, hR⟩
    have hJ' : rd st.M (jb + j) = toWord (x j) := by
      rw [hH _ (by simp only [regs] at hjb ⊢; omega), hJ j hj]
    have hCi' : rd st.M bCi = toWord c := by
      rw [hR _ (by decide) (by decide) (by decide) (by
        simp [aBody, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bCi, fPr, fAc, bA, bK, bJ, fY,
          fX, bT]), hCi]
    obtain ⟨b1, b2, hM2⟩ := aBody_sem I st hM' (t := j) (c := c) (x := x j) hjb heb hcb (by omega)
      (by omega) (hcb2 j hj) hT' hCi' hA hJ'
    have hH2 : ∀ y, regs ≤ y → rd (semXIR I (aBody jb eb cb cs) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_aBody jb eb cb cs) y hy
    refine ⟨inv_decS hM2 (by decide), ?_, by rw [rd_decS (by decide), b2], fun y hy => ?_,
      fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by decide) _), b1, sum_range_succ,
        rdK_congrB (hH (cb + cs * x j + c) (by simp only [regs] at hcb ⊢; omega)),
        rdK_congrB (hH (eb + j) (by simp only [regs] at heb ⊢; omega))]
    · rw [rd_decS (by simp only [bC3, regs] at hy ⊢; omega), hH2 y hy, hH y hy]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_aBody jb eb cb cs) hM' r hr h3,
        hR r hr h1 h2 h3]

/-! ## One coordinate -/

/-- **One coordinate `c`**: `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · Σ_t y_c(J_t) E[t])` at
`ob + k·c + s`; `c += 1`. -/
theorem cBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k jb eb cb cs ob c s0 : ℕ} {x : ℕ → ℕ} {lp : BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hob : regs ≤ ob)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + c < 2 ^ 64) (hcs2 : cb + cs * s0 + c < 2 ^ 64)
    (hob2 : ob + k * c + s0 < 2 ^ 64) (hsz : ob + k * c + s0 < s.M.size)
    (hCi : rd s.M bCi = toWord c) (hS : rd s.M bS = toWord s0)
    (hLp : rdK s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdK (semXIR I (cBody k jb eb cb cs ob) s).M (ob + k * c + s0) =
      (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
        lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)) ∧
    rd (semXIR I (cBody k jb eb cb cs ob) s).M bCi = toWord (c + 1) ∧
    (∀ y, regs ≤ y → y ≠ ob + k * c + s0 →
      rd (semXIR I (cBody k jb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (cBody k jb eb cb cs ob) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb heb hcb hob
  rw [cBody]
  simp only [semXIR_seq, sem_blk_append]
  -- `acc := 0`, `t := 0`, `bN3 := k`
  have q1 : rdK (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M fAc = 0 ∧
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M bT =
        toWord 0 ∧
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M bN3 =
        toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne] <;> rfl
  have f1 : ∀ i, i ≠ fAc → i ≠ bT → i ≠ bN3 →
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M i = rd s.M i :=
    fun i a b c => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM1 := inv_sem I (P := .blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) (s := s)
    (by simp [WF, Prim.dst, fAc, bT, bN3]) hM
  have z1 := size_sem I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s
  generalize semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s = s1
    at q1 f1 hM1 z1
  have hH1 : ∀ y, 256 ≤ y → rd s1.M y = rd s.M y := fun y hy =>
    f1 y (by simp only [fAc]; omega) (by simp only [bT]; omega) (by simp only [bN3]; omega)
  -- the accumulation
  obtain ⟨A1, hM2, A3, A4⟩ := aLoop_sem I s1 hM1 (k := k) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (c := c) (x := x) hk (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by simp only [regs]; omega) hjb2 heb2 hcb2 q1.2.2 q1.2.1
    ((f1 _ (by decide) (by decide) (by decide)).trans hCi) q1.1
    (fun t ht => by rw [hH1 _ (by omega), hJ t ht])
  have nw : ∀ r, r ∈ [bZ, bS, bCi, fLp] → ¬ Writes (aBody jb eb cb cs) r := by
    simp [aBody, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bZ, bS, bCi, fLp, fPr, fAc, bA, bK,
      bJ, fY, fX, bT]
  have R2 : ∀ r, r ∈ [bZ, bS, bCi, fLp] →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1).M r = rd s.M r :=
    fun r hr => by
      have : r < regs ∧ r ≠ bC3 ∧ r ≠ cTmp ∧ r ≠ fAc ∧ r ≠ bT ∧ r ≠ bN3 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, c', d, e, f⟩ := this
      rw [A4 r a b c' (nw r hr), f1 r d e f]
  replace A1 : rdK (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1).M fAc =
      ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) := by
    rw [A1]
    exact Finset.sum_congr rfl fun t _ => by
      rw [rdK_congrB (hH1 (cb + cs * x t + c) (by omega)), rdK_congrB (hH1 (eb + t) (by omega))]
  have z2 := size_sem I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1
  generalize semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1 = s2
    at A1 hM2 A3 A4 R2 z2
  have H2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy =>
    (A3 y hy).trans (hH1 y (by simp only [regs] at hy; omega))
  -- the value: `y_c(s)` or `ℓ · acc`
  have st3 : rdK (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M fAc =
        (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
          lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)) ∧
      (∀ r, r ∈ [bS, bCi] →
        rd (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M r = rd s.M r) ∧
      (∀ y, regs ≤ y → rd (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M y =
        rd s.M y) ∧
      Inv (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M := by
    have wy : WF (yIR cb cs) := by simp [yIR, addrPs, WF, Prim.dst, bA, bK, fAc]
    have ly : Lo (yIR cb cs) := by simp [yIR, addrPs, Lo, Prim.dst, bA, bK, fAc, regs]
    have nwy : ∀ r, r ∈ [bS, bCi] → ¬ Writes (yIR cb cs) r := by
      simp [yIR, addrPs, Writes, Prim.dst, bA, bK, fAc, bS, bCi]
    have nwm : ∀ r, r ∈ [bS, bCi] → ¬ Writes (mulK fAc fLp fAc) r := by
      simp [bnw_mulK, fAc, bS, bCi]
    have mem3 : ∀ r, r ∈ [bS, bCi] → r < regs ∧ r ∈ [bZ, bS, bCi, fLp] := by
      simp [bS, bCi, regs]
    rw [semXIR_ite, R2 bZ (by simp), hZ]
    by_cases hl : lp = 0
    · rw [decide_eq_true hl, if_neg bW_ne_zero, if_pos hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 ly y hy).trans (H2 y hy),
        inv_sem I wy hM2⟩
      · rw [yIR, semXIR_seq, sem_blk_append]
        obtain ⟨c1, f1', hMa⟩ := addr_sem I s2 hM2 (d := bA) (i := bS) (b := cb) (m := cs)
          (x := s0) (by decide) (by decide) (by decide) (by decide) ((R2 bS (by simp)).trans hS)
        obtain ⟨c2, f2', hMb⟩ := bAdd_sem I _ hMa (d := bA) (r := bCi) (x := cb + cs * s0)
          (y := c) (by decide) (by decide) c1
          ((f1' _ (by decide) (by decide)).trans ((R2 bCi (by simp)).trans hCi))
        obtain ⟨l1, -, -⟩ := load_sem I _ hMb (d := fAc) (p := bA) (x := cb + cs * s0 + c)
          (by decide) (by decide) c2 hcs2
        rw [rdK_congrB (l1.trans ((f2' _ (by simp only [bA]; omega)).trans
          ((f1' _ (by simp only [bA]; omega) (by simp only [bK]; omega)).trans
            (H2 _ (by simp only [regs]; omega)))))]
      · rw [frame I _ s2 wy hM2 r (mem3 r hr).1 (nwy r hr), R2 r (mem3 r hr).2]
    · rw [decide_eq_false hl, bW_false, if_pos rfl, if_neg hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 (lo_mulK (by decide)) y hy).trans
        (H2 y hy), inv_sem I (wf_mulK _ _ _ (by decide)) hM2⟩
      · rw [mulK_sem hM2 (by decide) (by decide) (by decide) (by decide), A1,
          rdK_congrB (R2 fLp (by simp)), hLp]
      · rw [frame I _ s2 (wf_mulK _ _ _ (by decide)) hM2 r (mem3 r hr).1 (nwm r hr),
          R2 r (mem3 r hr).2]
  obtain ⟨v3, r3, h3, hM3⟩ := st3
  have z3 := size_sem I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2
  generalize semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2 = s3 at v3 r3 h3 hM3 z3
  -- the address `ob + k·c + s`
  obtain ⟨o1, g1, hM4⟩ := addr_sem I s3 hM3 (d := bA) (i := bCi) (b := ob) (m := k) (x := c)
    (by decide) (by decide) (by decide) (by decide) ((r3 bCi (by simp)).trans hCi)
  have z4 := size_sem I (.blk (addrPs bA bCi ob k)) s3
  generalize semXIR I (.blk (addrPs bA bCi ob k)) s3 = s4 at o1 g1 hM4 z4
  obtain ⟨o2, g2, hM5⟩ := bAdd_sem I s4 hM4 (d := bA) (r := bS) (x := ob + k * c) (y := s0)
    (by decide) (by decide) o1 ((g1 _ (by decide) (by decide)).trans ((r3 bS (by simp)).trans hS))
  have z5 := size_sem I (.blk [.op .add bA bA bS]) s4
  generalize semXIR I (.blk [.op .add bA bA bS]) s4 = s5 at o2 g2 hM5 z5
  -- the store
  have hz : ob + k * c + s0 < s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hsz
  obtain ⟨w1, w2, hM6⟩ := store_sem I s5 hM5 (p := bA) (v := fAc) (x := ob + k * c + s0)
    (by decide) (by decide) o2 (by simp only [regs]; omega) hob2 hz
  have K6 : ∀ r, r < 256 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (.store bA fAc) s5).M r = rd s3.M r := fun r hr a b c' => by
    rw [w2 r (by omega) a, g2 r b, g1 r b c']
  generalize semXIR I (.store bA fAc) s5 = s6 at w1 w2 hM6 K6
  -- `c += 1`
  obtain ⟨i7, f7, hM7⟩ := bInc_sem I s6 hM6 (r := bCi) (x := c) (by decide) (by decide)
    ((K6 _ (by decide) (by decide) (by decide) (by decide)).trans ((r3 bCi (by simp)).trans hCi))
  refine ⟨?_, i7, fun y hy hy1 => ?_, hM7⟩
  · rw [rdK_congrB ((f7 (ob + k * c + s0) (by simp only [bCi]; omega)).trans w1),
      rdK_congrB ((g2 fAc (by decide)).trans (g1 fAc (by decide) (by decide))), v3]
  · simp only [regs] at hy
    rw [f7 _ (by simp only [bCi]; omega), w2 y hy1 (by simp only [cTmp]; omega),
      g2 _ (by simp only [bA]; omega), g1 _ (by simp only [bA]; omega) (by simp only [bK]; omega),
      h3 y (by simp only [regs]; omega)]

/-! ## The coordinates of one target -/

theorem wf_cBody (k jb eb cb cs ob : ℕ) : WF (cBody k jb eb cb cs ob) := by
  simp [cBody, aBody, yIR, addrPs, addr1Ps, WF, Writes, Prim.dst, wfK_mul, bnw_mulK, bA, bK, bJ,
    fY, fX, fPr, fAc, fLp, bT, bN3, bC3, bCi, bS, cTmp, regs]

/-- **The coordinates of one target**: `out[c][s] = (ℓ = 0 ? y_c(s) : ℓ Σ_t y_c(J_t) E[t])` for
`c < C`. -/
theorem cLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb eb cb cs ob s0 : ℕ} {x : ℕ → ℕ} {lp : BF64}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hob : regs ≤ ob) (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + c < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + c < 2 ^ 64) (hs0 : s0 < k)
    (hob2 : ob + k * C < 2 ^ 64) (hsz : ob + k * C ≤ s.M.size)
    (hOJ : ob + k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + k * C ≤ eb ∨ eb + k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      ob + k * C ≤ cb + cs * j + c ∨ cb + cs * j + c < ob)
    (hN : rd s.M bN2 = toWord C) (hCi : rd s.M bCi = toWord 0)
    (hS : rd s.M bS = toWord s0) (hLp : rdK s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdK (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M
        (ob + k * c + s0) =
      (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
        lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t))) ∧
    (∀ y, regs ≤ y → (∀ c < C, y ≠ ob + k * c + s0) →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M := by
  simp only [regs] at hjb heb hcb hob
  let V : ℕ → BF64 := fun c => if lp = 0 then rdK s.M (cb + cs * s0 + c) else
    lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bCi = toWord j ∧
    (∀ c < j, rdK st.M (ob + k * c + s0) = V c) ∧
    (∀ y, regs ≤ y → (∀ c < j, y ≠ ob + k * c + s0) → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord C) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := C) (cBody k jb eb cb cs ob) Q s hM (by decide)
    (by decide) (by decide) hN hC ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hCi],
      fun c hc => absurd hc (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hCi', hV, hH, hR⟩
    have nwc : ∀ r, r ∈ [bS, fLp, bZ] → ¬ Writes (cBody k jb eb cb cs ob) r := by
      simp [cBody, aBody, yIR, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bA, bK, bJ, fY, fX,
        fPr, fAc, bT, bN3, bC3, bCi, cTmp, bS, fLp, bZ]
    have R : ∀ r, r ∈ [bS, fLp, bZ] → rd st.M r = rd s.M r := fun r hr => by
      have : r < regs ∧ r ≠ bC2 ∧ r ≠ cTmp := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide
      exact hR r this.1 this.2.1 this.2.2 (nwc r hr)
    have hHy : ∀ y, regs ≤ y → (y < ob ∨ ob + k * C ≤ y) → rd st.M y = rd s.M y :=
      fun y hy hy2 => hH y hy fun c hc => by
        have := out_ltB (k := k) (show c < C by omega) hs0
        omega
    have hk2 := out_ltB (k := k) hj hs0
    obtain ⟨b1, b2, b3, hM2⟩ := cBody_sem I st hM' (c := j) (s0 := s0) (x := x) (lp := lp) hk
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) hjb2 heb2 (fun t ht => hcb2 t ht j hj) (hcs2 j hj) (by omega)
      (by rw [hz]; omega) hCi' ((R bS (by simp)).trans hS)
      (by rw [rdK_congrB (R fLp (by simp)), hLp]) ((R bZ (by simp)).trans hZ)
      (fun t ht => by
        rw [hHy _ (by simp only [regs]; omega) (by rcases hOJ with h | h <;> omega), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun c hc => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by simp only [bC2]; omega) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have hlt := lt_mulB (k := k) hc
        rw [rdK_congrB (b3 _ (by simp only [regs]; omega) (by omega)), hV c hc]
      · rw [b1]
        have hy' : ∀ j', j' ∈ (List.range k).map x ∨ j' = s0 →
            rdK st.M (cb + cs * j' + c) = rdK s.M (cb + cs * j' + c) := fun j' hj' =>
          rdK_congrB (hHy _ (by simp only [regs]; omega)
            (by rcases hOY c hj j' hj' with h | h <;> omega))
        simp only [V]
        split_ifs
        · exact hy' s0 (.inr rfl)
        · refine congrArg (lp * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 ht', rfl⟩)),
            rdK_congrB (hHy _ (by simp only [regs]; omega) (by rcases hOE with h | h <;> omega))]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega), b3 y hy (hy2 j (by omega)),
        hH y hy fun c hc => hy2 c (by omega)]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_cBody k jb eb cb cs ob) hM' r hr h3,
        hR r hr h1 h2 h3]

end Lvm.X
