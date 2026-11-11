-- WP-13b: the whole decoder's semantics `decIR_sem` (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).
import LvmXDecIR3

/-!
# `decIR_sem`: the decoder program computes `decodeRec`

See `LvmXDecIR3` for the program. On a memory holding the word, `α` and `f₁` outside the workspace:
the flag at `okB dB` is `[2^13 ≤ |agreeL|]`; on `decodeRec … = some out` the message at `mB dB` is
`out`; the heap outside the workspace is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

theorem rdE_congr {M M' : Mem} {a : ℕ} (h : ∀ k < 3, rd M' (a + k) = rd M (a + k)) :
    rdE M' a = rdE M a := by
  simp only [rdE, rdK]
  rw [show a = a + 0 from rfl, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)]

theorem bW_xor_one (b : Bool) : bW b ^^^ 1 = bW (!b) := by cases b <;> decide

/-- **The flag**: `rOk = okB`'s cell `= [2^13 ≤ cnt]`. -/
theorem okIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB n : ℕ} (hdB : regs ≤ dB)
    (hdB2 : okB dB < 2 ^ 64) (hdBs : okB dB < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (okIR dB) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
    rd (semXIR I (okIR dB) s).M (okB dB) = bW (decide (2 ^ 13 ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ okB dB → rd (semXIR I (okIR dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (okIR dB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [okIR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (okB dB) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (by norm_num), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
      bW_xor_one]
    congr 1
    rw [← decide_not]
    simp only [Nat.not_lt]
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk ps) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zK, rOk] <;> omega
  have z1 := size_sem I (.blk ps) s
  generalize semXIR I (.blk ps) s = s1 at hM1 v1 k1 z1
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := okB dB) (by decide)
    (by decide) v1.2 (by simp only [regs, okB]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, okB]; omega) (by decide), v1.1]

/-- **The decoder computes `decodeRec`.** -/
theorem decIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 13, rdE s.M (fB + 3 * v) = f₁ v) :
    rd (semXIR I (decIR dB wB aB fB) s).M (okB dB) =
      bW (decide (2 ^ 13 ≤ (agreeL wd α f₁).length)) ∧
    (∀ out, decodeRec wd α f₁ = some out →
      ∀ i < 2 ^ 19, rdK (semXIR I (decIR dB wB aB fB) s).M (mB dB + i) = out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decIR dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decIR dB wB aB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  -- 1. the basis table
  rw [decIR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_eqA I s1 hM1 (aB := aB) (qB := qB dB) (by simp only [regs]; omega)
    (by omega) (by simp only [regs, qB]; omega) (by simp only [qB]; omega)
    (by rw [z1]; simp only [qB]; omega) (by simp only [qB]; omega)
  have z2 := size_sem I (eqtIR 6 aB (qB dB)) s1
  generalize semXIR I (eqtIR 6 aB (qB dB)) s1 = s2 at q1 q2 hM2 z2
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2 x (by simp only [regs]; omega) (by simp only [qB]; omega)
  have hQ2 : ∀ l < 64, rdE s2.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [q1 l hl]
    refine eqA_congr (fun i hi => ?_) l
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  -- the inputs outside the workspace are kept by every phase
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₀(f₁)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := encIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (encIR dB fB) s2
  generalize semXIR I (encIR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2 x hx (by simp only [qB]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 13, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s3.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [encB]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ l < 64, rdE s3.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [← hQ2 l hl]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, qB]; omega) (by simp only [qB, encB]; omega)
  have hE3 : ∀ q < 2 ^ 15, enc0 f₁ q = mkE (rdK s3.M (encB dB + q)) (rdK s3.M (encB dB + 2 ^ 15 + q))
      (rdK s3.M (encB dB + 2 * 2 ^ 15 + q)) := fun q hq => by
    rw [enc0_coords f₁ (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (encB dB + c * 2 ^ 15 + q) := fun c hc => by
      rw [e1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agreeM s3.M wB (qB dB) (encB dB) (2 ^ 15) = agreeL wd α f₁ :=
    agreeM_eq_agreeL wd α f₁ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agreeIR_sem I s3 hM3 (wB := wB) (qB := qB dB) (eB := encB dB)
    (agB := agB dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, qB]; omega)
    (by simp only [qB]; omega) (by simp only [regs, encB]; omega) (by simp only [encB]; omega)
    (by simp only [regs, agB]; omega) (by simp only [agB]; omega)
    (by rw [z3, z2, z1]; simp only [agB]; omega)
    ⟨by simp only [agB]; omega, by simp only [agB, qB]; omega, by simp only [agB, encB]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3
  generalize semXIR I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agreeL wd α f₁).length < 2 ^ 64 := by
    have : (agreeL wd α f₁).length ≤ 2 ^ 15 := by
      rw [agreeL]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okIR_sem I s4 hM4 (dB := dB) (n := (agreeL wd α f₁).length)
    (by simp only [regs]; omega) (by simp only [okB]; omega)
    (by rw [z4, z3, z2, z1]; simp only [okB]; omega) hlen64 g1
  have z5 := size_sem I (okIR dB) s4
  generalize semXIR I (okIR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [okB]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [agB]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [encB]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [okB]; omega), g3 x hx (by simp only [agB]; omega),
      e2 x hx (by simp only [encB]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 13 ≤ (agreeL wd α f₁).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : DecLay dB wB aB fB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s5.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 13, rd s5.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0) := fun t ht => by
      rw [o3 _ (by simp only [regs, agB]; omega) (by simp only [agB, okB]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := decTail_sem I s5 hM5 hL5 hT5 wd α f₁ hW5 hk hJ5
    refine ⟨?_, fun out hout' i hi => ?_, fun x hx hx2 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, okB]; omega) (by simp only [okB]; omega), o2, decide_eq_true hk]
    · rw [decodeRec, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range]
    · rw [d2 x hx (by omega), h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun out hout' => ?_, h5, hM5⟩
    rw [decodeRec, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
