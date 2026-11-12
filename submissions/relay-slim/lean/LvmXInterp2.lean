-- adapted from rf-k/submissions/flock-recursive/lean/FRXBary.lean@8bff272b (helpers, `wInner_sem` …
-- `wtIR_sem`, `eBody_sem`, `eLoop_sem`) for lvm (WP-13b): FR's two-word `F` re-targeted to `K = BF64`;
-- FR's `djIR` (the table `D(J_t)`) is dropped: `J_t`'s word is its domain point (`ptK`).
import LvmXInterp

/-!
# The barycentric interpolation on the machine (1): the table `W` and one target's `E` row

Bottom-up: the address blocks, the increment, `wInner_sem` (one factor of a weight),
**`wtIR_sem`** (`W[t] = (Π_{m ≠ t} (G t + G m))⁻¹` at `wb + t`, `G m` the element at `jb + m`),
`eBody_sem` and **`eLoop_sem`** (`E[t] = W[t] (ds + G t)⁻¹` at `eb + t`, `ℓ = Π_t (ds + G t)`).
-/

namespace Lvm.X

open RecursionFast Finset

attribute [local irreducible] entryK storeM

/-! ## Helpers -/

theorem rdK_congrB {M M' : Mem} {a a' : ℕ} (h : rd M a = rd M' a') : rdK M a = rdK M' a' := by
  rw [rdK, rdK, h]

theorem wK_eq_zero (w : Word) : wK w = 0 ↔ w = 0 := by
  constructor
  · intro h; exact congrArg BF64.toBitVec h
  · rintro rfl; rfl

theorem sem_blk_append (I : Array Word) (ps qs : List Prim) (s : St) :
    semXIR I (.blk (ps ++ qs)) s = semXIR I (.blk qs) (semXIR I (.blk ps) s) := by
  simp only [semXIR, runPrims_append]

/-- **The address block** `d := b + m · M[i]`. -/
theorem addr_sem (I : Array Word) (s : St) (hM : Inv s.M) {d i b m x : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (hdK : d ≠ bK) (hi : i ≠ bK) (hx : rd s.M i = toWord x) :
    rd (semXIR I (.blk (addrPs d i b m)) s).M d = toWord (b + m * x) ∧
    (∀ j, j ≠ d → j ≠ bK → rd (semXIR I (.blk (addrPs d i b m)) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk (addrPs d i b m)) s).M := by
  have hs := hM.1
  have hK : bK < s.M.size := by simp only [regs] at hs; simp only [bK]; omega
  have hd' : d < s.M.size := by simp only [regs] at hs hd; omega
  rw [sem_blk]
  refine ⟨?_, fun j h1 h2 => rd_runPrims_of_not_writes (by
    simp only [addrPs, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _,
    inv_runPrims (by
      simp only [addrPs, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, bK] <;> omega) hM⟩
  simp only [addrPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | exact hdK | exact hdK.symm | exact hi.symm | exact hK | exact hd' |
    (simp only [size_set]; first | exact hd' | exact hK)) only [rd_set_self, rd_set_ne, hx]
  rw [mul_toWord, add_toWord, Nat.add_comm, Nat.mul_comm]

/-- **The address block** `d := b + M[i]` (stride 1). -/
theorem addr1_sem (I : Array Word) (s : St) (hM : Inv s.M) {d i b x : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (_hdK : d ≠ bK) (hi : i ≠ bK) (hx : rd s.M i = toWord x) :
    rd (semXIR I (.blk (addr1Ps d i b)) s).M d = toWord (b + x) ∧
    (∀ j, j ≠ d → j ≠ bK → rd (semXIR I (.blk (addr1Ps d i b)) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk (addr1Ps d i b)) s).M := by
  have hs := hM.1
  have hK : bK < s.M.size := by simp only [regs] at hs; simp only [bK]; omega
  have hd' : d < s.M.size := by simp only [regs] at hs hd; omega
  rw [sem_blk]
  refine ⟨?_, fun j h1 h2 => rd_runPrims_of_not_writes (by
    simp only [addr1Ps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _,
    inv_runPrims (by
      simp only [addr1Ps, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, bK] <;> omega) hM⟩
  simp only [addr1Ps, runPrims, List.foldl, Prim.run]
  simp (disch := first | exact hi.symm | exact hK | exact hd' |
    (simp only [size_set]; first | exact hd' | exact hK)) only [rd_set_self, rd_set_ne, hx]
  rw [add_toWord, Nat.add_comm]

/-- `r += 1`. -/
theorem bInc_sem (I : Array Word) (s : St) (hM : Inv s.M) {r x : ℕ} (hr : r < regs)
    (hr4 : 4 ≤ r) (hx : rd s.M r = toWord x) :
    rd (semXIR I (.blk [.op .add r r cOne]) s).M r = toWord (x + 1) ∧
    (∀ i, i ≠ r → rd (semXIR I (.blk [.op .add r r cOne]) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk [.op .add r r cOne]) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  rw [sem_blk]
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _,
    inv_runPrims (by simp [Prim.dst]; exact hr4) hM⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hr; omega), hx, h1, add_one_toWord]

/-- `d += M[r]`. -/
theorem bAdd_sem (I : Array Word) (s : St) (hM : Inv s.M) {d r x y : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (hx : rd s.M d = toWord x) (hy : rd s.M r = toWord y) :
    rd (semXIR I (.blk [.op .add d d r]) s).M d = toWord (x + y) ∧
    (∀ j, j ≠ d → rd (semXIR I (.blk [.op .add d d r]) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk [.op .add d d r]) s).M := by
  have hs := hM.1
  rw [sem_blk]
  refine ⟨?_, fun j hj => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hj) _,
    inv_runPrims (by simp [Prim.dst]; exact hd4) hM⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hd; omega), hx, hy, add_toWord]

theorem frK_mul {I : Array Word} {s : St} {d a b r : ℕ} (h0 : 9 ≤ r) (h1 : r ≠ d) :
    rd (semXIR I (mulK d a b) s).M r = rd s.M r := by
  rw [mulK, sem_blk]; exact mulKC_frame _ _ _ (.inr h0) h1 _

theorem frK_inv {I : Array Word} {s : St} {d a r : ℕ} (h0 : 12 ≤ r) (h1 : r ≠ d) :
    rd (semXIR I (invK d a) s).M r = rd s.M r := by
  rw [invK, sem_blk]; exact invKC_frame _ _ (.inr h0) h1 _

theorem lo_mulK {d a b : ℕ} (h : d < regs) : Lo (mulK d a b) := fun p hp => by
  have := mulKC_dst d a b p hp; simp only [regs] at h ⊢; omega

theorem lo_invK {d a : ℕ} (h : d < regs) : Lo (invK d a) := fun p hp => by
  have := invKC_dst d a p hp; simp only [regs] at h ⊢; omega

theorem loK_mul_iff {d a b : ℕ} (h : d < regs) : Lo (mulK d a b) ↔ True := iff_true_intro (lo_mulK h)
theorem loK_inv_iff {d a : ℕ} (h : d < regs) : Lo (invK d a) ↔ True := iff_true_intro (lo_invK h)

/-! ## The table `W` -/

theorem lo_wInner (jb : ℕ) : Lo (wInner jb) := by
  simp [wInner, addr1Ps, Lo, Prim.dst, bA, bK, fX, fDd, bZ, bM, fPr, regs]
  exact lo_mulK (by decide)

theorem wf_wInner (jb : ℕ) : WF (wInner jb) := by
  simp [wInner, addr1Ps, WF, Prim.dst, wfK_mul, bA, bK, fX, fDd, bZ, bM, fPr]

/-- **One factor** of `W[t]`: `fPr *= (m = t ? 1 : J_t + J_m)`. -/
theorem wInner_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb m t : ℕ} {dt : BF64}
    (hjb : regs ≤ jb) (hm : m < 2 ^ 64) (ht : t < 2 ^ 64) (hjb2 : jb + m < 2 ^ 64)
    (hBm : rd s.M bM = toWord m) (hBt : rd s.M bT = toWord t) (hDs : rdK s.M fDs = dt) :
    rdK (semXIR I (wInner jb) s).M fPr =
      rdK s.M fPr * (if m = t then 1 else dt + rdK s.M (jb + m)) ∧
    rd (semXIR I (wInner jb) s).M bM = toWord (m + 1) ∧
    rd (semXIR I (wInner jb) s).M bT = toWord t ∧ rdK (semXIR I (wInner jb) s).M fDs = dt ∧
    Inv (semXIR I (wInner jb) s).M := by
  simp only [regs] at hjb
  rw [wInner]
  simp only [semXIR_seq]
  -- `bA := jb + m`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bM) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBm
  generalize semXIR I (.blk (addr1Ps bA bM jb)) s = s1 at a1 f1 hM1
  -- `fX := J_m`
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fX) (p := bA) (x := jb + m) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; omega) (by simp only [bK]; omega)] at l2
  generalize semXIR I (.load fX bA) s1 = s2 at l2 f2 hM2
  have g2 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `fDd := fDs + fX`, `bZ := [m = t]`
  have hs2 := hM2.1
  have v3 : rdK (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M fDd =
        dt + rdK s.M (jb + m) ∧
      rd (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M bZ =
        bW (decide (m = t)) := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩
    · rw [rdK]
      simp (disch := first | decide |
        ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
        only [rd_set_self, rd_set_ne]
      rw [eval_xor, wK_xor, g2 fDs (by decide) (by decide) (by decide), l2]
      show rdK s.M fDs + rdK s.M (jb + m) = dt + rdK s.M (jb + m)
      rw [hDs]
    · simp (disch := first | decide |
        ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
        only [rd_set_self, rd_set_ne]
      rw [g2 bM (by decide) (by decide) (by decide), g2 bT (by decide) (by decide) (by decide),
        hBm, hBt, eqW_toWord hm ht]
  have f3 : ∀ r, r ≠ fDd → r ≠ bZ →
      rd (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M r = rd s2.M r :=
    fun r a b => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM3 := inv_sem I (P := .blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) (s := s2)
    (by simp [WF, Prim.dst, fDd, bZ]) hM2
  generalize semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2 = s3 at v3 f3 hM3
  -- the conditional product
  have ePr : rdK s3.M fPr = rdK s.M fPr :=
    rdK_congrB ((f3 _ (by decide) (by decide)).trans (g2 _ (by decide) (by decide) (by decide)))
  have p4 : rdK (semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3).M fPr =
      rdK s.M fPr * (if m = t then 1 else dt + rdK s.M (jb + m)) := by
    rw [semXIR_ite, v3.2]
    by_cases hmt : m = t
    · rw [decide_eq_true hmt, if_neg bW_ne_zero, if_pos hmt, mul_one]; exact ePr
    · rw [decide_eq_false hmt, bW_false, if_pos rfl, if_neg hmt,
        mulK_sem hM3 (by decide) (by decide) (by decide) (by decide), ePr, v3.1]
  have f4 : ∀ r, 9 ≤ r → r ≠ fPr →
      rd (semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3).M r = rd s3.M r := fun r h0 h1 => by
    rw [semXIR_ite]
    split_ifs
    · exact frK_mul h0 h1
    · rfl
  have hM4 := inv_sem I (P := .ite bZ (.blk []) (mulK fPr fPr fDd)) (s := s3)
    ⟨by simp [WF], wf_mulK _ _ _ (by decide)⟩ hM3
  generalize semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3 = s4 at p4 f4 hM4
  have G4 : ∀ r, 9 ≤ r → r ≠ fPr → r ≠ fDd → r ≠ bZ → r ≠ fX → r ≠ bA → r ≠ bK →
      rd s4.M r = rd s.M r := fun r h0 a b c d e f =>
    (f4 r h0 a).trans ((f3 r b c).trans (g2 r d e f))
  -- `m += 1`
  obtain ⟨i5, f5, hM5⟩ := bInc_sem I s4 hM4 (r := bM) (x := m) (by decide) (by decide)
    ((G4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hBm)
  refine ⟨?_, i5, ?_, ?_, hM5⟩
  · rw [rdK_congrB (f5 fPr (by decide)), p4]
  · rw [f5 _ (by decide), G4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hBt]
  · rw [rdK_congrB ((f5 fDs (by decide)).trans (G4 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))), hDs]

/-- **One entry of `W`**: `W[t] := (Π_{m < k} (m = t ? 1 : G t + G m))⁻¹`, `G m` the element at
`jb + m`. -/
theorem wtBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb t : ℕ} {G : ℕ → BF64}
    (hk : k < 2 ^ 64) (ht : t < k) (hjb : regs ≤ jb) (hwb : regs ≤ wb)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (hsz : wb + k ≤ s.M.size)
    (hG : ∀ m < k, rdK s.M (jb + m) = G m) (hBt : rd s.M bT = toWord t) :
    rdK (semXIR I (wtBody k jb wb) s).M (wb + t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ ∧
    rd (semXIR I (wtBody k jb wb) s).M bT = toWord (t + 1) ∧
    (∀ y, regs ≤ y → y ≠ wb + t → rd (semXIR I (wtBody k jb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtBody k jb wb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb hwb
  rw [wtBody]
  simp only [semXIR_seq]
  -- `fDs := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  have z1 := size_sem I (.blk (addr1Ps bA bT jb)) s
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1 z1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fDs) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 (by omega)
  have z2 := size_sem I (.load fDs bA) s1
  have gt : rdK (semXIR I (.load fDs bA) s1).M fDs = G t := by
    rw [rdK_congrB (l2.trans (f1 _ (by simp only [bA]; omega) (by simp only [bK]; omega))),
      hG t ht]
  generalize semXIR I (.load fDs bA) s1 = s2 at l2 f2 hM2 z2 gt
  have g2 : ∀ r, r ≠ fDs → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- the product's constants
  have hs2 := hM2.1
  have q3 : rdK (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M fPr = 1 ∧
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M bM =
        toWord 0 ∧
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M bN2 =
        toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
      only [rd_set_self, rd_set_ne] <;> rfl
  have f3 : ∀ r, r ≠ fPr → r ≠ bM → r ≠ bN2 →
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M r =
        rd s2.M r := fun r a b c => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM3 := inv_sem I (P := .blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) (s := s2)
    (by simp [WF, Prim.dst, fPr, bM, bN2]) hM2
  have z3 := size_sem I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2
  generalize semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2 = s3
    at q3 f3 hM3 z3
  have g3 : ∀ r, r ≠ fPr → r ≠ bM → r ≠ bN2 → r ≠ fDs → r ≠ bA → r ≠ bK →
      rd s3.M r = rd s.M r := fun r a b c d e f => (f3 r a b c).trans (g2 r d e f)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rdK st.M fPr = (∏ m ∈ range j, if m = t then 1 else G t + G m) ∧ rd st.M bM = toWord j ∧
    rd st.M bT = toWord t ∧ rdK st.M fDs = G t ∧ ∀ y, regs ≤ y → rd st.M y = rd s.M y
  have hQ := loopK_run I (c := bC2) (n := bN2) (K := k) (wInner jb) Q s3 hM3
    (by decide) (by decide) (by decide) q3.2.2 hk ?_ ?_
  rotate_left
  · have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) s3.M) i = rd s3.M i :=
      fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
    refine ⟨inv_entryK hM3 (by decide), by rw [size_entryK, z3, z2, z1], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdK_congrB (ef _ (by decide) (by decide)), q3.1, prod_range_zero]
    · rw [ef _ (by decide) (by decide), q3.2.1]
    · rw [ef _ (by decide) (by decide), g3 _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hBt]
    · rw [rdK_congrB ((ef _ (by decide) (by decide)).trans
        (f3 _ (by decide) (by decide) (by decide))), gt]
    · simp only [regs] at hy
      rw [ef _ (by simp only [bC2]; omega) (by simp only [cTmp]; omega),
        g3 _ (by simp only [fPr]; omega) (by simp only [bM]; omega) (by simp only [bN2]; omega)
          (by simp only [fDs]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega)]
  · rintro j st hj ⟨hM', hz, hP, hm, hb, hd, hH⟩
    obtain ⟨w1, w2, w3, w4, hM''⟩ := wInner_sem I st hM' (jb := jb) (m := j) (t := t) (dt := G t)
      (by simp only [regs]; omega) (by omega) (by omega) (by omega) hm hb hd
    have hrs : ∀ y, regs ≤ y → rd (semXIR I (wInner jb) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_wInner jb) y hy
    refine ⟨inv_decS hM'' (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdK_congrB (rd_decS (by decide) _), w1, hP, prod_range_succ,
        rdK_congrB (hH (jb + j) (by simp only [regs]; omega)), hG j hj]
    · rw [rd_decS (by decide), w2]
    · rw [rd_decS (by decide), w3]
    · rw [rdK_congrB (rd_decS (by decide) _), w4]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega), hrs y hy, hH y hy]
  obtain ⟨Q1, Qz, Q2, -, Q4, -, Q6⟩ := hQ
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (wInner jb)) s3 = s4 at Q1 Qz Q2 Q4 Q6
  -- the inverse
  have v5 := invK_sem (I := I) (s := s4) Q1 (d := fIv) (a := fPr) (by decide) (by decide)
  rw [Q2] at v5
  have hM5 := inv_sem I (wf_invK fIv fPr (by decide)) Q1
  have z5 := size_sem I (invK fIv fPr) s4
  have k5 : ∀ r, 12 ≤ r → r ≠ fIv → rd (semXIR I (invK fIv fPr) s4).M r = rd s4.M r :=
    fun r h0 h1 => frK_inv h0 h1
  generalize semXIR I (invK fIv fPr) s4 = s5 at v5 hM5 k5 z5
  -- `bA := wb + t`
  have t5 : rd s5.M bT = toWord t := (k5 _ (by decide) (by decide)).trans Q4
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := wb) (by decide)
    (by decide) (by decide) (by decide) t5
  have z6 := size_sem I (.blk (addr1Ps bA bT wb)) s5
  have v6 : rdK (semXIR I (.blk (addr1Ps bA bT wb)) s5).M fIv =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ := by
    rw [rdK_congrB (f6 _ (by decide) (by decide)), v5]
  generalize semXIR I (.blk (addr1Ps bA bT wb)) s5 = s6 at a6 f6 hM6 z6 v6
  -- `W[t] := fIv`
  have hz : wb + t < s6.M.size := by rw [z6, z5, Qz]; omega
  obtain ⟨g1, g2', hM7⟩ := store_sem I s6 hM6 (p := bA) (v := fIv) (x := wb + t) (by decide)
    (by decide) a6 (by simp only [regs]; omega) (by omega) hz
  have t7 : rd (semXIR I (.store bA fIv) s6).M bT = toWord t := by
    rw [g2' _ (by simp only [bT]; omega) (by decide), f6 _ (by decide) (by decide), t5]
  generalize semXIR I (.store bA fIv) s6 = s7 at g1 g2' hM7 t7
  obtain ⟨i8, f8, hM8⟩ := bInc_sem I s7 hM7 (r := bT) (x := t) (by decide) (by decide) t7
  refine ⟨?_, i8, fun y hy h1' => ?_, hM8⟩
  · rw [rdK_congrB ((f8 (wb + t) (by simp only [bT]; omega)).trans g1), v6]
  · simp only [regs] at hy
    rw [f8 _ (by simp only [bT]; omega), g2' y h1' (by simp only [cTmp]; omega),
      f6 _ (by simp only [bA]; omega) (by simp only [bK]; omega),
      k5 _ (by omega) (by simp only [fIv]; omega), Q6 y (by simp only [regs]; omega)]

/-- **The table `W`**: `W[t] = (Π_{m<k} (m = t ? 1 : G t + G m))⁻¹` at `wb + t`, `G m` the
element at `jb + m`; nothing else on the heap changes. -/
theorem wtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb : ℕ} {G : ℕ → BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hwb : regs ≤ wb) (hjb2 : jb + k < 2 ^ 64)
    (hwb2 : wb + k < 2 ^ 64) (hsz : wb + k ≤ s.M.size)
    (hdW : jb + k ≤ wb ∨ wb + k ≤ jb) (hG : ∀ m < k, rdK s.M (jb + m) = G m) :
    (∀ t < k, rdK (semXIR I (wtIR k jb wb) s).M (wb + t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) →
      rd (semXIR I (wtIR k jb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtIR k jb wb) s).M := by
  have hs := hM.1
  rw [wtIR, semXIR_seq]
  have p1 : rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M bT = toWord 0 ∧
      rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M bN1 = toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne] <;> rfl
  have p3 : ∀ i, i ≠ bT → i ≠ bN1 →
      rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M i = rd s.M i :=
    fun i h1 h2 => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM1 := inv_sem I (P := .blk [.const bT 0, .const bN1 (toWord k)]) (s := s)
    (by simp [WF, Prim.dst, bT, bN1]) hM
  have z1 := size_sem I (.blk [.const bT 0, .const bN1 (toWord k)]) s
  generalize semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s = s1 at p1 p3 hM1 z1
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    (∀ t < j, rdK st.M (wb + t) = (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + j ≤ y) → rd st.M y = rd s.M y)
  have hfin := loopK_run I (c := bC1) (n := bN1) (K := k) (wtBody k jb wb) P s1 hM1
    (by decide) (by decide) (by decide) p1.2 hk ?_ ?_
  · exact ⟨hfin.2.2.2.1, fun y hy hy2 => hfin.2.2.2.2 y hy hy2, hfin.1⟩
  · refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], ?_,
      fun t ht => absurd ht (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    · rw [entryK_frame _ (by decide) (by decide), p1.1]
    · simp only [regs] at hy
      rw [entryK_frame _ (by simp only [bC1]; omega) (by simp only [cTmp]; omega),
        p3 _ (by simp only [bT]; omega) (by simp only [bN1]; omega)]
  · rintro j st hj ⟨hM', hz, hT', hW, hH⟩
    have hG' : ∀ m < k, rdK st.M (jb + m) = G m := fun m hm => by
      rw [rdK_congrB (hH (jb + m) (by simp only [regs] at hjb ⊢; omega) (by omega)), hG m hm]
    obtain ⟨b1, b2, b3, hM2⟩ := wtBody_sem I st hM' hk hj hjb hwb hjb2 hwb2 (by omega) hG' hT'
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz], ?_, fun t ht => ?_,
      fun y hy hy2 => ?_⟩
    · rw [rd_decS (by decide), b2]
    · rw [rdK_congrB (rd_decS (by simp only [bC1, regs] at hwb ⊢; omega) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdK_congrB (b3 _ (by simp only [regs] at hwb ⊢; omega) (by omega)), hW t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega), b3 y hy (by omega),
        hH y hy (by omega)]

/-! ## One target's `E` row -/

theorem wf_eBody (jb wb eb : ℕ) : WF (eBody jb wb eb) := by
  simp [eBody, addr1Ps, WF, Prim.dst, wfK_mul, wfK_inv, bA, bK, fX, fDd, fLp, fIv, fEt, bT, cTmp]

/-- **One entry of the `E` row**: `E[t] := W[t] · (ds + J_t)⁻¹`, `ℓ *= ds + J_t`. -/
theorem eBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb wb eb t : ℕ} {ds lp g w : BF64}
    (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hjb2 : jb + t < 2 ^ 64)
    (hwb2 : wb + t < 2 ^ 64) (heb2 : eb + t < 2 ^ 64)
    (hsz : eb + t < s.M.size) (hBt : rd s.M bT = toWord t) (hDs : rdK s.M fDs = ds)
    (hLp : rdK s.M fLp = lp) (hG : rdK s.M (jb + t) = g) (hW : rdK s.M (wb + t) = w) :
    rdK (semXIR I (eBody jb wb eb) s).M (eb + t) = w * (ds + g)⁻¹ ∧
    rdK (semXIR I (eBody jb wb eb) s).M fLp = lp * (ds + g) ∧
    rd (semXIR I (eBody jb wb eb) s).M bT = toWord (t + 1) ∧
    rdK (semXIR I (eBody jb wb eb) s).M fDs = ds ∧
    (∀ y, regs ≤ y → y ≠ eb + t → rd (semXIR I (eBody jb wb eb) s).M y = rd s.M y) ∧
    Inv (semXIR I (eBody jb wb eb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb hwb heb
  rw [eBody]
  simp only [semXIR_seq]
  -- `fX := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  have z1 := size_sem I (.blk (addr1Ps bA bT jb)) s
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1 z1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fX) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; omega) (by simp only [bK]; omega)] at l2
  have z2 := size_sem I (.load fX bA) s1
  generalize semXIR I (.load fX bA) s1 = s2 at l2 f2 hM2 z2
  have g2 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `fDd := ds + J_t`
  have hs2 := hM2.1
  have d3 : rdK (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M fDd = ds + g := by
    rw [sem_blk, rdK, rd_xor_run (lt_of_lt_of_le (by decide) hs2), wK_xor,
      g2 fDs (by decide) (by decide) (by decide), l2]
    show rdK s.M fDs + rdK s.M (jb + t) = ds + g
    rw [hDs, hG]
  have f3 : ∀ r, r ≠ fDd → rd (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M r = rd s2.M r :=
    fun r h => xorC_frame _ _ _ h _
  have hM3 : Inv (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M := xorC_inv _ _ _ (by decide) hM2
  have z3 := size_sem I (.blk [.op .xor fDd fDs fX]) s2
  generalize semXIR I (.blk [.op .xor fDd fDs fX]) s2 = s3 at d3 f3 hM3 z3
  -- `ℓ *= fDd`
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fLp) (a := fLp) (b := fDd) (by decide)
    (by decide) (by decide) (by decide)
  rw [d3, rdK_congrB ((f3 _ (by decide)).trans (g2 _ (by decide) (by decide) (by decide))),
    hLp] at m4
  have hM4 := inv_sem I (wf_mulK fLp fLp fDd (by decide)) hM3
  have z4 := size_sem I (mulK fLp fLp fDd) s3
  have f4 : ∀ r, 9 ≤ r → r ≠ fLp → rd (semXIR I (mulK fLp fLp fDd) s3).M r = rd s3.M r :=
    fun r h0 h1 => frK_mul h0 h1
  have dd4 : rdK (semXIR I (mulK fLp fLp fDd) s3).M fDd = ds + g := by
    rw [rdK_congrB (f4 _ (by decide) (by decide)), d3]
  generalize semXIR I (mulK fLp fLp fDd) s3 = s4 at m4 hM4 z4 f4 dd4
  -- `fIv := fDd⁻¹`
  have v5 := invK_sem (I := I) (s := s4) hM4 (d := fIv) (a := fDd) (by decide) (by decide)
  rw [dd4] at v5
  have hM5 := inv_sem I (wf_invK fIv fDd (by decide)) hM4
  have z5 := size_sem I (invK fIv fDd) s4
  have f5 : ∀ r, 12 ≤ r → r ≠ fIv → rd (semXIR I (invK fIv fDd) s4).M r = rd s4.M r :=
    fun r h0 h1 => frK_inv h0 h1
  generalize semXIR I (invK fIv fDd) s4 = s5 at v5 hM5 z5 f5
  -- the registers so far, against `s`
  have K5 : ∀ r, 12 ≤ r → r ≠ fIv → r ≠ fLp → r ≠ fDd → r ≠ fX → r ≠ bA → r ≠ bK →
      rd s5.M r = rd s.M r := fun r h0 a b c d e f =>
    (f5 r h0 a).trans ((f4 r (by omega) b).trans ((f3 r c).trans (g2 r d e f)))
  have Lp5 : rdK s5.M fLp = lp * (ds + g) := by
    rw [rdK_congrB (f5 _ (by decide) (by decide)), m4]
  have t5 : rd s5.M bT = toWord t := (K5 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hBt
  have hH5 : ∀ y, 256 ≤ y → rd s5.M y = rd s.M y := fun y hy =>
    K5 y (by omega) (by simp only [fIv]; omega) (by simp only [fLp]; omega)
      (by simp only [fDd]; omega) (by simp only [fX]; omega) (by simp only [bA]; omega)
      (by simp only [bK]; omega)
  -- `fX := W[t]`
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := wb) (by decide)
    (by decide) (by decide) (by decide) t5
  have z6 := size_sem I (.blk (addr1Ps bA bT wb)) s5
  generalize semXIR I (.blk (addr1Ps bA bT wb)) s5 = s6 at a6 f6 hM6 z6
  obtain ⟨l7, f7, hM7⟩ := load_sem I s6 hM6 (d := fX) (p := bA) (x := wb + t) (by decide)
    (by decide) a6 hwb2
  have w7 : rdK (semXIR I (.load fX bA) s6).M fX = w := by
    rw [rdK_congrB (l7.trans ((f6 _ (by simp only [bA]; omega) (by simp only [bK]; omega)).trans
      (hH5 _ (by omega)))), hW]
  have z7 := size_sem I (.load fX bA) s6
  generalize semXIR I (.load fX bA) s6 = s7 at l7 f7 hM7 z7 w7
  have k7 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s7.M r = rd s5.M r := fun r a b c =>
    (f7 r a).trans (f6 r b c)
  -- `fEt := W[t] · fIv`
  have m8 := mulK_sem (I := I) (s := s7) hM7 (d := fEt) (a := fX) (b := fIv) (by decide)
    (by decide) (by decide) (by decide)
  rw [w7, rdK_congrB (k7 _ (by decide) (by decide) (by decide)), v5] at m8
  have hM8 := inv_sem I (wf_mulK fEt fX fIv (by decide)) hM7
  have z8 := size_sem I (mulK fEt fX fIv) s7
  have k8 : ∀ r, 9 ≤ r → r ≠ fEt → r ≠ fX → r ≠ bA → r ≠ bK →
      rd (semXIR I (mulK fEt fX fIv) s7).M r = rd s5.M r := fun r h0 a b c d =>
    (frK_mul h0 a).trans (k7 r b c d)
  generalize semXIR I (mulK fEt fX fIv) s7 = s8 at m8 hM8 z8 k8
  -- `E[t] := fEt`
  have t8 : rd s8.M bT = toWord t := (k8 _ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans t5
  obtain ⟨a9, f9, hM9⟩ := addr1_sem I s8 hM8 (d := bA) (i := bT) (b := eb) (by decide)
    (by decide) (by decide) (by decide) t8
  have z9 := size_sem I (.blk (addr1Ps bA bT eb)) s8
  have E9 : rdK (semXIR I (.blk (addr1Ps bA bT eb)) s8).M fEt = w * (ds + g)⁻¹ := by
    rw [rdK_congrB (f9 _ (by decide) (by decide)), m8]
  generalize semXIR I (.blk (addr1Ps bA bT eb)) s8 = s9 at a9 f9 hM9 z9 E9
  have hz : eb + t < s9.M.size := by rw [z9, z8, z7, z6, z5, z4, z3, z2, z1]; exact hsz
  obtain ⟨g1, g2', hM10⟩ := store_sem I s9 hM9 (p := bA) (v := fEt) (x := eb + t) (by decide)
    (by decide) a9 (by simp only [regs]; omega) heb2 hz
  have K10 : ∀ r, r < 256 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (.store bA fEt) s9).M r = rd s8.M r := fun r hr a b c => by
    rw [g2' r (by omega) a, f9 r b c]
  generalize semXIR I (.store bA fEt) s9 = s10 at g1 g2' hM10 K10
  have t10 : rd s10.M bT = toWord t := (K10 _ (by decide) (by decide) (by decide)
    (by decide)).trans t8
  obtain ⟨i11, f11, hM11⟩ := bInc_sem I s10 hM10 (r := bT) (x := t) (by decide) (by decide) t10
  have back : ∀ r, 12 ≤ r → r < 256 → r ≠ bT → r ≠ cTmp → r ≠ bA → r ≠ bK → r ≠ fEt →
      r ≠ fX → rd (semXIR I (.blk [.op .add bT bT cOne]) s10).M r = rd s5.M r :=
    fun r h0 hr a b c d e f => (f11 r a).trans ((K10 r hr b c d).trans (k8 r (by omega) e f c d))
  refine ⟨?_, ?_, i11, ?_, fun y hy h1' => ?_, hM11⟩
  · rw [rdK_congrB ((f11 (eb + t) (by simp only [bT]; omega)).trans g1), E9]
  · rw [rdK_congrB (back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)), Lp5]
  · rw [rdK_congrB ((back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (K5 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))), hDs]
  · simp only [regs] at hy
    rw [f11 _ (by simp only [bT]; omega), g2' y h1' (by simp only [cTmp]; omega),
      f9 _ (by simp only [bA]; omega) (by simp only [bK]; omega),
      k8 _ (by omega) (by simp only [fEt]; omega) (by simp only [fX]; omega)
        (by simp only [bA]; omega) (by simp only [bK]; omega), hH5 y hy]

/-- **The `E` row**: `E[t] = W[t] (ds + J_t)⁻¹` for `t < k`, `ℓ = Π_t (ds + J_t)`. -/
theorem eLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb eb : ℕ} {ds : BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hsz : eb + k ≤ s.M.size) (hjE : jb + k ≤ eb ∨ eb + k ≤ jb)
    (hwE : wb + k ≤ eb ∨ eb + k ≤ wb)
    (hN : rd s.M bN2 = toWord k) (hBt : rd s.M bT = toWord 0) (hDs : rdK s.M fDs = ds)
    (hLp : rdK s.M fLp = 1) :
    (∀ t < k, rdK (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M (eb + t) =
      rdK s.M (wb + t) * (ds + rdK s.M (jb + t))⁻¹) ∧
    rdK (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M fLp =
      ∏ t ∈ range k, (ds + rdK s.M (jb + t)) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody jb wb eb) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    rdK st.M fDs = ds ∧ rdK st.M fLp = ∏ t ∈ range j, (ds + rdK s.M (jb + t)) ∧
    (∀ t < j, rdK st.M (eb + t) = rdK s.M (wb + t) * (ds + rdK s.M (jb + t))⁻¹) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + j ≤ y) → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody jb wb eb) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := k) (eBody jb wb eb) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hBt],
      by rw [rdK_congrB (ef _ (by decide) (by decide)), hDs],
      by rw [rdK_congrB (ef _ (by decide) (by decide)), hLp, prod_range_zero],
      fun t ht => absurd ht (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, fun y hy hy2 => h.2.2.2.2.2.2.1 y hy hy2,
      h.2.2.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hT', hD, hL, hE, hH, hR⟩
    simp only [regs] at hjb hwb heb
    have hG : rdK st.M (jb + j) = rdK s.M (jb + j) :=
      rdK_congrB (hH _ (by simp only [regs]; omega) (by omega))
    have hW : rdK st.M (wb + j) = rdK s.M (wb + j) :=
      rdK_congrB (hH _ (by simp only [regs]; omega) (by omega))
    obtain ⟨b1, b2, b3, b4, b5, hM2⟩ := eBody_sem I st hM' (t := j) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by omega) hT' hD hL hG hW
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b3],
      by rw [rdK_congrB (rd_decS (by decide) _), b4],
      by rw [rdK_congrB (rd_decS (by decide) _), b2, prod_range_succ], fun t ht => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by simp only [bC2]; omega) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdK_congrB (b5 _ (by simp only [regs]; omega) (by omega)), hE t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega), b5 y hy (by omega),
        hH y hy (by omega)]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_eBody jb wb eb) hM' r hr h3, hR r hr h1 h2 h3]

end Lvm.X
