-- adapted from rf-k/submissions/flock-recursive/lean/FRXRead.lean@8bff272b (sections "One
-- position", "The read at a parametric index base", `read_spec`): `posBody_sem`, `posLoop4`,
-- `readIR4_sem` + `readIR4_frame`, `read_spec`.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 3: one
-- position, the position loop and **`readIR_sem`**.
import LvmXRead

/-!
# The column reads' semantics (`readIR_sem`)

On a domain tape of a SNARK proof, after the log index (`idxIR4 bX pL`, sorted by
`idxIR4_sorted`), with `C_rec`'s cap (128 nodes) on the tape at `capW`, `readIR bX pL capW wB`
leaves in cell `wB + 64 p + t` (`p < 2^15`, `t < 64`) leaf word `t` of the row the log holds
under the cap at position `p`: as a `K` element, `(readRow L cap p).getD t 0` (zeros for an
erasure). It keeps every heap cell outside `[wB, wB + 2^21)`, in particular the index at `bX`.

* `cr_pos_sem`: one position; `cr_posLoop`: positions `j … j + m − 1`;
* `readIR_sem4`: on any sorted index (`Sorted4`), words as `crLeafW`;
* **`readIR_sem`**: after `idxIR4`, words as `K` elements, the frame, the index and `Inv`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

section Read2

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the leaf words of position `p` at `a … a + 63`; `crP := p + 1`,
`crWA := a + 64`; every other heap cell kept. -/
theorem cr_pos_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < 2 ^ 15) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size) :
    (∀ t < 64, rd (semXIR (crTape c π L) (crPos bX pL capW) s).M (a + t) =
      crLeafW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) →
      rd (semXIR (crTape c π L) (crPos bX pL capW) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (crPos bX pL capW) s).M ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crWA = toWord (a + 64) ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 256 < cap.length := by rw [hcl]; omega
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, WF, Prim.dst,
    crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, Lo, Prim.dst,
    regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_lo_ld4⟩
  have q1 := cr_capLd_sem I s hM (by rw [hcl]; omega) hcap (by omega) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [crCapPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3, crP,
        crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (crCapPs capW)) crLd4) s
  rw [crPos, semXIR_seq]
  generalize semXIR I (.seq (.blk (crCapPs capW)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord 8)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crNH = toWord 8 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalk L (cap[p / 256]'hpc) p 8 s2.M := by
    refine .inl ⟨o2.1, cap[p / 256]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; omega) (by simp only [crNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord 8) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord 8) s2.M) crHc = toWord 8 :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord 8) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord 8) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 8 < 2 ^ 64 by norm_num)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; omega
  have hWE : crWalk L (cap[p / 256]'hpc) p 8 (entryK crHc crNH (toWord 8) s2.M) := by
    unfold crWalk at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord 8) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord 8) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoop hbX hbX2 hpL hD hX (by omega) 8
    ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ (by norm_num) hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord 8) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord 8) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord 8) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord 8) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_sem hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := cr_copy_sem I s4 hM4 hql ha ha2 (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I crCopy s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k1 t ht, c2, xLeafBytes_eq hp hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their leaf words' cells. -/
theorem cr_posLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ 2 ^ 15 → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + 64 * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < 64,
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M (wB + 64 * q + t) =
          crLeafW (xLeafBytes L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + 64 * j ∨ wB + 64 * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : 64 * (j + 1) = 64 * j + 64 := Nat.mul_succ 64 j
    obtain ⟨b1, b2, b3, b4, b5⟩ := cr_pos_sem hbX hbX2 hpL hD hX s hM hXs hcl hcw hcap (p := j)
      (a := wB + 64 * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (crPos bX pL capW) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (crPos bX pL capW) s)).M r =
        rd (semXIR I (crPos bX pL capW) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (crPos bX pL capW) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := cr_posLoop hD hX hcl hcw hcap hwB hwB2 m (j + 1) _ (by omega) hM' hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : 64 * (j + 1 + m) = 64 * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by omega) (.inl (by omega)), dk _ (hy _ (by omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), b2 _ hy1 (by omega)]

/-- **The column reads' semantics on a sorted index**: `readIR bX pL capW wB` stores at
`wB + 64 p + t` leaf word `t` of the reading at position `p < 2^15` (`crLeafW`, zeros for an
erasure) and keeps every heap cell outside `[wB, wB + 2^21)`. -/
theorem readIR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M (wB + 64 * p + t) =
        crLeafW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (readIR bX pL capW wB) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 15))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crWA = toWord (wB + 64 * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crNp = toWord (2 ^ 15) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | (rw [Nat.mul_zero, Nat.add_zero])
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
  rw [readIR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crCp = toWord (2 ^ 15) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (2 ^ 15)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (2 ^ 15)) (crPos bX pL capW)) s0 =
      iterL (semXIR I (crPos bX pL capW)) crCp (2 ^ 15)
        ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 2 ^ 15 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : 64 * (0 + 2 ^ 15) = 2 ^ 21 := by norm_num
  obtain ⟨d1, d2, d3⟩ := cr_posLoop hbX hbX2 hpL hD hX hcl hcw hcap hwB hwB2 (2 ^ 15) 0
    ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by omega) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = _
  rw [hHE y hy1]

end Read2

/-- **`readIR_sem`** (BLUEPRINT §6.2 step 4). On a domain tape of a SNARK proof whose log starts
at tape word `pL`, take a state `s₂` (memory of at least `bX` words) whose `X[0..|L|)` is the
one `idxIR4 bX pL` left from `s`, with `C_rec`'s cap (128 nodes) on the tape at `capW`. After
`readIR bX pL capW wB`, cell `wB + 64 p + t` holds, as a `K` element, word `t` of the row the
log holds under the cap at position `p` (`readRow`, WP-5's first-preimage reading; zeros for an
erasure), for every `p < 2^15`, `t < 64`; every heap cell outside `[wB, wB + 2^21)` is kept,
in particular the index; `Inv` holds. -/
theorem readIR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
        (readRow L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (bX + a) =
        rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := readIR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; omega)
    (.inr (by omega)), w3⟩
  rw [rdK, w1 p hp t ht', crLeafW_readRow L cap p ht']

/-- **The word the decoder consumes** after the read: `readWd L cap p t` at `wB + 64 p + t`. -/
theorem readIR_readWd {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) {p t : ℕ} (hp : p < 2 ^ 15) (ht' : t < 64) :
    rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
      readWd L cap p t :=
  (readIR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ hcl hcw hcap hwB hwB2).1 p hp
    t ht'

end Lvm.X
