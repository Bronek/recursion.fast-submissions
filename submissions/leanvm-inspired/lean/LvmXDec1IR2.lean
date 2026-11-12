-- lvm2 X-REC2 (helper DEC): the level-1 decoder program `dec1IR` and its semantics. Adapted from this
-- entry's `LvmXDecIR3.lean`/`LvmXDecIR4.lean` (v1's `decTail_sem`, `decIR`, `decIR_sem`).
import LvmXDec1IR

/-!
# The level-1 decoder of `C_rec` on the machine

`dec1IR dB wB aB fB oB`: the basis table (`wtabIR`); `eq(α₁, ·)` (`eqtIR 4`); `Enc₁(f₂)`
(`enc1IR`); the agreement scan (`agree1IR`); the flag (`ok1IR`); on success the interpolation
of the 48 lanes, their inverse NTTs and the transpose into the output (`dec1Tail`).

**`dec1IR_sem`**: on a memory holding the level-1 word `wd` at `wB + 48q + t` (`q < 2^12`,
`t < 48`), `α_i` at `aB + 3i` (`i < 4`) and `f₂(v)` at `fB + 3v` (`v < 2^9`, `rdE`), with the
layout `Dec1Lay`:
* the cell `ok1B dB` holds `[2^9 ≤ |agree1L wd α f₂|]`, i.e. `decodeRec1 wd α f₂ ≠ none`;
* if `decodeRec1 wd α f₂ = some f₁`, then `rdE (oB + 3v) = f₁ v` for every `v < 2^13`: the
  layout v1's `decIR` reads its `f₁` from (`fB := oB`);
* the heap outside the workspace `[dB, dB + 2^16)` and the output `[oB, oB + 3·2^13)` is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-1 decoder program.** -/
def dec1IR (dB wB aB fB oB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 4 aB (q1B dB)) (.seq (enc1IR dB fB)
    (.seq (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) (.seq (ok1IR dB)
      (.ite rOk (dec1Tail dB wB oB) (.blk []))))))

theorem eqA1_congr {α α' : ℕ → Ext3} (h : ∀ i < 4, α i = α' i) (u : ℕ) : eqA1 α u = eqA1 α' u := by
  simp only [eqA1, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

/-- **The decoding proper**: on a list of `≥ 2^9` agreeing positions at `ag1B`, the decoded
message at `oB`. -/
theorem dec1Tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₂ : ℕ → Ext3) (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hlen : 2 ^ 9 ≤ (agree1L wd α f₂).length)
    (hJ : ∀ t < 2 ^ 9, rd s.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0)) :
    (∀ v < 2 ^ 13, rdE (semXIR I (dec1Tail dB wB oB) s).M (oB + 3 * v) = dec1At wd α f₂ v) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 10 ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1Tail dB wB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1Tail dB wB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rW rO
  set Jl := sel1J wd α f₂ with hJl
  have hJlen : Jl.length = 2 ^ 9 := by
    rw [hJl, sel1J, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agree1L wd α f₂).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 12 := fun j hj => (mem_agree1L.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, ag1B, wb1B, eb1B, ob1B]) <;> omega
  have hget : ∀ t < 2 ^ 9, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hJlt _ (List.getElem_mem (l := Jl) (n := t) (by omega)); omega
  rw [dec1Tail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_sem I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, sel1J, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s
  generalize semXIR I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : Dec1Lay dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
      (by simp only [ob1B]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bfly1All_sem I s1 hM1 hL1 hT1
    (fun t i => rdK s1.M (ob1B dB + t * 2 ^ 9 + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bfly1All dB) s1
  generalize semXIR I (bfly1All dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := tr1IR_sem I s2 hM2 (ob := ob1B dB) (oB := oB)
    (by simp only [regs, ob1B]; omega) (by simp only [ob1B]; omega) (by simp only [regs]; omega)
    (by omega) (by rw [z2, z1]; omega) (by simp only [ob1B]; omega)
  generalize semXIR I (tr1IR (ob1B dB) oB) s2 = s3 at d1 d2 hM3
  refine ⟨fun v hv => ?_, fun x hx hx2 hx3 => ?_, hM3⟩
  · -- the decoded entry `v = u + 16 v'`
    have hval : ∀ c < 3, rdK s3.M (oB + 3 * v + c) = coef1 wd α f₂ (3 * (v % 16) + c) (v / 16) := by
      intro c hc
      have hu : v % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hv' : v / 16 < 2 ^ 9 := by omega
      have e : oB + 3 * v + c = oB + 48 * (v / 16) + (3 * (v % 16) + c) := by omega
      simp only [rdK]
      rw [e, d1 (v / 16) hv' (3 * (v % 16) + c) (by omega),
        show ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + v / 16 =
          ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16 by ring,
        show wK (rd s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16)) =
          rdK s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16) from rfl,
        c1 (3 * (v % 16) + c) (by omega) (v / 16) hv', coef1]
      refine coeffsAt_congr ptK nLog 9 0 _ _ (fun j hj => ?_) (v / 16) hv'
      rw [show ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + j = ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + j
        by ring, b1 j hj _ (by omega), show (2 : ℕ) ^ 9 = Jl.length from hJlen.symm,
        baryValK_eq hJnd (fun j hj => by have := hJlt j hj; omega) (by omega)]
      refine interpF_congr ptK _ (fun q hq => ?_) j
      have hq' := hJlt q (List.mem_toFinset.1 hq)
      rw [hW q hq' _ (by omega), lane1]
    have h0 := hval 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [rdE, h0, hval 1 (by norm_num), hval 2 (by norm_num), dec1At]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by omega),
      c2 x (by simp only [regs]; omega) (by simp only [ob1B]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
        (by simp only [ob1B]; omega)]

/-- **The level-1 decoder computes `decodeRec1`.** -/
theorem dec1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 9, rdE s.M (fB + 3 * v) = f₂ v) :
    rd (semXIR I (dec1IR dB wB aB fB oB) s).M (ok1B dB) =
      bW (decide (2 ^ 9 ≤ (agree1L wd α f₂).length)) ∧
    (∀ f₁, decodeRec1 wd α f₂ = some f₁ →
      ∀ v < 2 ^ 13, rdE (semXIR I (dec1IR dB wB aB fB oB) s).M (oB + 3 * v) = f₁ v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1IR dB wB aB fB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF rO hs
  -- 1. the basis table
  rw [dec1IR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_sem I s1 hM1 (ℓ := 4) (aB := aB) (qB := q1B dB) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by rw [z1]; simp only [q1B]; omega) (by simp only [q1B]; omega)
  have z2 := size_sem I (eqtIR 4 aB (q1B dB)) s1
  generalize semXIR I (eqtIR 4 aB (q1B dB)) s1 = s2 at q1 q2 hM2 z2
  have q2' : ∀ x, regs ≤ x → (x < q1B dB ∨ q1B dB + 48 ≤ x) → rd s2.M x = rd s1.M x :=
    fun x hx hx2 => q2 x (.inr (lt_of_lt_of_le (by decide) hx)) (by omega)
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2' x (by simp only [regs]; omega) (by simp only [q1B]; omega)
  have hQ2 : ∀ u < 16, rdE s2.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [q1 u hu]
    refine eqA1_congr (fun i hi => ?_) u
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  have hL2 : Dec1Lay dB wB aB fB oB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₁(f₂)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := enc1IR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (enc1IR dB fB) s2
  generalize semXIR I (enc1IR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2' x hx (by simp only [q1B]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 9, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s3.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [enc1B]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ u < 16, rdE s3.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [← hQ2 u hu]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, q1B]; omega)
      (by simp only [q1B, enc1B]; omega)
  have hE3 : ∀ q < 2 ^ 12, enc1 f₂ q = mkE (rdK s3.M (enc1B dB + q))
      (rdK s3.M (enc1B dB + 2 ^ 12 + q)) (rdK s3.M (enc1B dB + 2 * 2 ^ 12 + q)) := fun q hq => by
    have hc : ∀ c < 3, ∑ v ∈ range (2 ^ 9), rdK s.M (fB + 3 * v + c) * nbAt v q =
        rdK s3.M (enc1B dB + c * 2 ^ 12 + q) := fun c hc => by
      rw [e1 c hc q hq, sum_nbAt_eq_encN]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    have hc0 := hc 0 (by norm_num)
    have hc1 := hc 1 (by norm_num)
    have hc2 := hc 2 (by norm_num)
    rw [Nat.zero_mul, Nat.add_zero] at hc0
    rw [Nat.one_mul] at hc1
    rw [enc1, ← hc0, ← hc1, ← hc2, ← mkE_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← mkE_mul_ofK, ← hF v (mem_range.1 hv)]
    rfl
  have hAg : agree1M s3.M wB (q1B dB) (enc1B dB) (2 ^ 12) = agree1L wd α f₂ :=
    agree1M_eq_agree1L wd α f₂ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agree1IR_sem I s3 hM3 (wB := wB) (qB := q1B dB) (eB := enc1B dB)
    (agB := ag1B dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by simp only [regs, enc1B]; omega) (by simp only [enc1B]; omega)
    (by simp only [regs, ag1B]; omega) (by simp only [ag1B]; omega)
    (by rw [z3, z2, z1]; simp only [ag1B]; omega)
    ⟨by simp only [ag1B]; omega, by simp only [ag1B, q1B]; omega, by simp only [ag1B, enc1B]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3
  generalize semXIR I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agree1L wd α f₂).length < 2 ^ 64 := by
    have : (agree1L wd α f₂).length ≤ 2 ^ 12 := by
      rw [agree1L]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := ok1IR_sem I s4 hM4 (dB := dB) (n := (agree1L wd α f₂).length)
    (by simp only [regs]; omega) (by simp only [ok1B]; omega)
    (by rw [z4, z3, z2, z1]; simp only [ok1B]; omega) hlen64 g1
  have z5 := size_sem I (ok1IR dB) s4
  generalize semXIR I (ok1IR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [ok1B]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [ag1B]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [enc1B]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [ok1B]; omega), g3 x hx (by simp only [ag1B]; omega),
      e2 x hx (by simp only [enc1B]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 9 ≤ (agree1L wd α f₂).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : Dec1Lay dB wB aB fB oB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s5.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 9, rd s5.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, ag1B]; omega) (by simp only [ag1B, ok1B]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := dec1Tail_sem I s5 hM5 hL5 hT5 wd α f₂ hW5 hk hJ5
    refine ⟨?_, fun f₁ hout' v hv => ?_, fun x hx hx2 hx3 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, ok1B]; omega) (by simp only [ok1B]; omega)
        (by simp only [ok1B]; omega), o2, decide_eq_true hk]
    · rw [decodeRec1, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 v hv]
      exact (if_pos hv).symm
    · rw [d2 x hx (by omega) hx3, h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun f₁ hout' => ?_, fun x hx hx2 _ => h5 x hx hx2, hM5⟩
    rw [decodeRec1, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
