-- Ported from `flock-recursive` `FRXSortSim.lean` (with its former `FRXSortSpec`, `FRXMerge`; rf-k kk/base
-- 8bff272b) for lvm (WP-3): namespace `Lvm.X`, FR's 3.x instance (`idxIR_sorted` at `posL`/`piSize`) dropped,
-- `decOk_idx` (lvm's instance of FR's `decOk_logIR`) added.
import LvmXLog

section LvmXSortSpec


/-!
# The sort's key comparison

`cmpIR` compares the entries at `src[i]` and `src[j]` by the key `keyW I x = [a₀, a₁, a₂, a₃, x]`
(the four answer words of the entry at tape position `x`, then `x` itself), lexicographically
and unsigned (`lexW`). **`cmpIR_sem`**: it leaves `1` in `rF` exactly when `keyLt I x y`.

This is the first brick of the sort's correctness (S-H2-RESULT, Part 3).
-/

namespace Lvm.X

open RecursionFast

/-- The answer position of the entry at tape position `x`, as the program computes it. -/
def aposW (I : Array Word) (x : Word) : Word := ceil8 (I.getD x.toNat 0) + x + 1

/-- The sort key of the entry at `x`: its four answer words, then `x`. -/
def keyW (I : Array Word) (x : Word) : List Word :=
  [I.getD (aposW I x + 0).toNat 0, I.getD (aposW I x + 1).toNat 0,
   I.getD (aposW I x + 2).toNat 0, I.getD (aposW I x + 3).toNat 0, x]

/-- Lexicographic `<` on word lists, unsigned. -/
def lexW : List Word → List Word → Bool
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexW as bs)
  | _, _ => false

/-- The sort order. -/
def keyLt (I : Array Word) (x y : Word) : Bool := lexW (keyW I x) (keyW I y)

/-- A 0/1 word. -/
def bW (p : Bool) : Word := if p then 1 else 0

/-- One step of the machine's lexicographic fold. -/
theorem fold_bW (a b : Word) (p : Bool) :
    XOp.or.eval (XOp.ltu.eval a b) (XOp.and.eval (XOp.eq.eval a b) (bW p)) =
      bW (decide (a < b) || (decide (a = b) && p)) := by
  by_cases h1 : a < b <;> by_cases h2 : a = b <;> cases p <;>
    simp [XOp.eval, bW, h1, h2]

theorem cmpWord_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) (hw : w < 2 ^ 64) :
    rd (semXIR I (cmpWord w) s).M rF =
      XOp.or.eval (XOp.ltu.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0))
        (XOp.and.eval (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0)) (rd s.M rF)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [cmpWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rPb, rKa, rKb, rG,
    rH, rF]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
    rd_set_ne]
  rfl

theorem wf_cmpWord (w : ℕ) : WF (cmpWord w) := by
  simp [cmpWord, WF, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF]

theorem cmpWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) {r : ℕ}
    (hr : r = rPa ∨ r = rPb) : rd (semXIR I (cmpWord w) s).M r = rd s.M r :=
  frame I _ s (wf_cmpWord w) hM r (by rcases hr with rfl | rfl <;> decide) (by
    rcases hr with rfl | rfl <;>
      simp [cmpWord, Writes, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF, rPa, rPb, cTmp])

theorem aposIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {d q : ℕ}
    (hdq : (d = rPa ∧ q = rX) ∨ (d = rPb ∧ q = rY)) :
    rd (semXIR I (aposIR d q) s).M d = aposW I (rd s.M q) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  rcases hdq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [aposIR, ceil8Ps, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rKc, rT2, rQL, rPa, rPb, rX, rY, cOne] at h1 ⊢
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne, h1]
    simp only [aposW, ceil8, XOp.eval]
    rfl

theorem wf_aposIR {d q : ℕ} (hd : d = rPa ∨ d = rPb) : WF (aposIR d q) := by
  rcases hd with rfl | rfl <;> simp [aposIR, ceil8Ps, WF, Prim.dst, rQL, rKc, rT2, rPa, rPb]

theorem aposIR_frame (I : Array Word) (s : St) (hM : Inv s.M) {d q r : ℕ}
    (hd : d = rPa ∨ d = rPb) (hr : r ∈ [rX, rY, rPa, rPb, rSrc, rI, rJ]) (hrd : r ≠ d) :
    rd (semXIR I (aposIR d q) s).M r = rd s.M r := by
  refine frame I _ s (wf_aposIR hd) hM r ?_ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hd with rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [aposIR, ceil8Ps, Writes, Prim.dst, rQL, rKc, rT2, rPa, rPb, rX, rY, rSrc, rI, rJ]

/-- **The comparison**: `rF := keyLt I x y` for `x = src[i]`, `y = src[j]`. -/
theorem cmpIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    (hi : regs ≤ (rd s.M rSrc + rd s.M rI).toNat) (hj : regs ≤ (rd s.M rSrc + rd s.M rJ).toNat) :
    rd (semXIR I cmpIR s).M rF = bW (keyLt I (rd s.M (rd s.M rSrc + rd s.M rI).toNat)
      (rd s.M (rd s.M rSrc + rd s.M rJ).toNat)) := by
  set x := rd s.M (rd s.M rSrc + rd s.M rI).toNat
  set y := rd s.M (rd s.M rSrc + rd s.M rJ).toNat
  have hs := hM.1
  simp only [regs] at hs hi hj
  -- the two loads
  have h4 : rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rX = x ∧
      rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rY = y := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, XOp.eval, rAd, rX, rY, rSrc, rI, rJ, x,
      y] at hi hj ⊢
    constructor <;>
      simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
        rd_set_ne]
  have hM4 : Inv (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M :=
    inv_sem I (P := .load rY rAd) (by simp [WF, rY]) (inv_sem I (by simp [WF, Prim.dst, rAd])
      (inv_sem I (P := .load rX rAd) (by simp [WF, rX]) (inv_sem I (by simp [WF, Prim.dst, rAd])
        hM)))
  rw [cmpIR, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s))) = s4 at h4 hM4
  obtain ⟨hx4, hy4⟩ := h4
  -- the answer positions
  rw [semXIR_seq]
  have hM5 := inv_sem I (wf_aposIR (q := rX) (.inl rfl)) hM4
  have ha5 := aposIR_sem I s4 hM4 (.inl ⟨rfl, rfl⟩)
  have hx5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rX) (by simp) (by decide)
  have hy5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPa rX) s4 = s5 at hM5 ha5 hx5 hy5
  rw [semXIR_seq]
  have hM6 := inv_sem I (wf_aposIR (q := rY) (.inr rfl)) hM5
  have hb6 := aposIR_sem I s5 hM5 (.inr ⟨rfl, rfl⟩)
  have ha6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rPa) (by simp) (by decide)
  have hx6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rX) (by simp) (by decide)
  have hy6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPb rY) s5 = s6 at hM6 hb6 ha6 hx6 hy6
  -- the position comparison
  rw [semXIR_seq]
  have hs6 := hM6.1
  simp only [regs] at hs6
  have hf7 : rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M rF = bW (lexW [x] [y]) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rF, rX, rY] at hx6 hy6 hx5 hy5 hx4 hy4 ⊢
    rw [rd_set_self (by omega), hx6, hy6, hx5, hy5, hx4, hy4]
    by_cases h : x < y <;> simp [XOp.eval, bW, lexW, h]
  have hwf7 : WF (.blk [.op .ltu rF rX rY]) := by simp [WF, Prim.dst, rF]
  have hM7 := inv_sem I hwf7 hM6
  have hfr7 : ∀ r, r = rPa ∨ r = rPb → rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M r =
      rd s6.M r := fun r hr => frame I _ s6 hwf7 hM6 r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;> simp [Writes, Prim.dst, rF, rPa, rPb])
  have ha7 := hfr7 rPa (.inl rfl)
  have hb7 := hfr7 rPb (.inr rfl)
  generalize semXIR I (.blk [.op .ltu rF rX rY]) s6 = s7 at hf7 hM7 ha7 hb7
  -- the four answer words
  have step : ∀ (s' : St), Inv s'.M → rd s'.M rPa = aposW I x → rd s'.M rPb = aposW I y →
      ∀ (w : ℕ) (p : Bool), w < 4 → rd s'.M rF = bW p →
      rd (semXIR I (cmpWord w) s').M rF = bW (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 <
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) ||
        (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 =
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) && p)) ∧
      Inv (semXIR I (cmpWord w) s').M ∧ rd (semXIR I (cmpWord w) s').M rPa = aposW I x ∧
      rd (semXIR I (cmpWord w) s').M rPb = aposW I y := fun s' hM' ha hb w p hw hf =>
    ⟨by rw [cmpWord_sem I s' hM' w (by omega), ha, hb, hf, fold_bW],
     inv_sem I (wf_cmpWord w) hM', by rw [cmpWord_frame I s' hM' w (.inl rfl), ha],
     by rw [cmpWord_frame I s' hM' w (.inr rfl), hb]⟩
  rw [ha6, ha5, hx4] at ha7
  rw [hb6, hy5, hy4] at hb7
  rw [semXIR_seq]
  obtain ⟨f3, m3, a3, b3⟩ := step s7 hM7 ha7 hb7 3 _ (by decide) hf7
  generalize semXIR I (cmpWord 3) s7 = s8 at f3 m3 a3 b3
  rw [semXIR_seq]
  obtain ⟨f2, m2, a2, b2⟩ := step s8 m3 a3 b3 2 _ (by decide) f3
  generalize semXIR I (cmpWord 2) s8 = s9 at f2 m2 a2 b2
  rw [semXIR_seq]
  obtain ⟨f1, m1, a1, b1⟩ := step s9 m2 a2 b2 1 _ (by decide) f2
  generalize semXIR I (cmpWord 1) s9 = s10 at f1 m1 a1 b1
  obtain ⟨f0, -, -, -⟩ := step s10 m1 a1 b1 0 _ (by decide) f1
  rw [f0]
  rfl

end Lvm.X

end LvmXSortSpec

section LvmXMerge


/-!
# The merge pass, as a pure state machine

`mstep` is one step of `stepIR` on abstract state (`MS`: the heads `i`, `j`, the run ends `iE`,
`jE`, the output index `k`, the destination as a function, and a ghost block start `lo`).
`Good` is the invariant; **`pass_ok`**: `n` steps from the empty state, on a source whose runs of
width `w` are strictly sorted and which is injective on `[0, n)`, leave a destination whose
blocks of width `2w` are strictly sorted and draw their values from the same source block.
No permutation is tracked (S-H2-RESULT, Part 3, steps 3–4).
-/

namespace Lvm.X

open RecursionFast

/-- A strict order, total on distinct words (`keyLt`'s properties, `keyLt_order`). -/
structure SOrd (lt : Word → Word → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- The abstract state of a merge pass. -/
structure MS where
  lo : ℕ
  i : ℕ
  iE : ℕ
  j : ℕ
  jE : ℕ
  k : ℕ
  dst : ℕ → Word

/-- `f` with `v` at `k`. -/
def upd (f : ℕ → Word) (k : ℕ) (v : Word) : ℕ → Word := fun a => if a = k then v else f a

/-- A new block when both runs are used up (`blockIR`). -/
def bstart (n w : ℕ) (s : MS) : MS :=
  if s.i = s.iE ∧ s.j = s.jE then
    { s with lo := s.k, i := s.k, iE := min (s.k + w) n, j := min (s.k + w) n,
             jE := min (s.k + w + w) n }
  else s

/-- The left head goes next. -/
def takeL (lt : Word → Word → Bool) (src : ℕ → Word) (s : MS) : Bool :=
  decide (s.i < s.iE) && (!decide (s.j < s.jE) || lt (src s.i) (src s.j))

/-- **One step** (`stepIR`). -/
def mstep (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : MS :=
  let s := bstart n w s
  if takeL lt src s then { s with dst := upd s.dst s.k (src s.i), i := s.i + 1, k := s.k + 1 }
  else { s with dst := upd s.dst s.k (src s.j), j := s.j + 1, k := s.k + 1 }

/-- The invariant. -/
structure Good (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : Prop where
  ord : s.lo ≤ s.i ∧ s.i ≤ s.iE ∧ s.iE ≤ s.j ∧ s.j ≤ s.jE ∧ s.jE ≤ n
  ends : s.iE ≤ s.lo + w ∧ s.jE ≤ s.lo + 2 * w ∧ (s.j < s.jE → s.iE = s.lo + w) ∧
    (s.jE = min (s.lo + 2 * w) n ∨ s.jE = s.lo)
  algn : 2 * w ∣ s.lo
  kk : s.k + s.iE = s.i + s.j
  srt : ∀ a b, s.lo ≤ a → a < b → b < s.k → lt (s.dst a) (s.dst b) = true
  mem : ∀ a, s.lo ≤ a → a < s.k → ∃ c, s.lo ≤ c ∧ c < s.jE ∧ s.dst a = src c
  heads : ∀ a, s.lo ≤ a → a < s.k → (s.i < s.iE → lt (s.dst a) (src s.i) = true) ∧
    (s.j < s.jE → lt (s.dst a) (src s.j) = true)
  dmem : ∀ a, a < s.lo → ∃ c, c < s.lo ∧ c / (2 * w) = a / (2 * w) ∧ s.dst a = src c
  dsrt : ∀ a b, a < b → b < s.lo → a / (2 * w) = b / (2 * w) → lt (s.dst a) (s.dst b) = true

theorem div_eq_of_block {w m a : ℕ} (h1 : w * m ≤ a) (h2 : a < w * m + w) : a / w = m :=
  Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.succ_mul, Nat.mul_comm]; exact h2)

theorem good_init (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) :
    Good lt src n w ⟨0, 0, 0, 0, 0, 0, d⟩ where
  ord := by simp
  ends := by simp
  algn := dvd_zero _
  kk := rfl
  srt := fun _ _ _ _ h => absurd h (by dsimp only; omega)
  mem := fun _ _ h => absurd h (by dsimp only; omega)
  heads := fun _ _ h => absurd h (by dsimp only; omega)
  dmem := fun _ h => absurd h (by dsimp only; omega)
  dsrt := fun _ _ _ h => absurd h (by dsimp only; omega)

/-- **`bstart` keeps the invariant**, and afterwards a head is available. -/
theorem good_bstart {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (hw : 0 < w)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (bstart n w s) ∧ ((bstart n w s).i < (bstart n w s).iE ∨
      (bstart n w s).j < (bstart n w s).jE) ∧ (bstart n w s).k = s.k ∧
      (bstart n w s).dst = s.dst := by
  unfold bstart
  split
  · next h =>
    obtain ⟨hi, hj⟩ := h
    obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
    obtain ⟨e1, e2, e3, e4⟩ := hg.ends
    have hkj : s.k = s.jE := by have := hg.kk; omega
    obtain ⟨m, hm⟩ := hg.algn
    -- the closed block ends aligned: `jE = lo + 2w` or the block is empty
    have hal : 2 * w ∣ s.k := by
      rw [hkj]
      rcases e4 with e4 | e4
      · exact ⟨m + 1, by rw [e4, Nat.min_eq_left (by omega), hm]; ring⟩
      · exact ⟨m, by rw [e4, hm]⟩
    have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
      div_eq_of_block (by omega) (by omega)
    refine ⟨⟨by simp; omega, ⟨by simp, by simp; omega, fun h => by simp at h ⊢; omega,
      Or.inl (by simp; omega)⟩, hal, by simp,
      fun a b ha hab hb => absurd hb (by simp at ha ⊢; omega),
      fun a ha hak => absurd hak (by simp at ha ⊢; omega),
      fun a ha hak => absurd hak (by simp at ha ⊢; omega), fun a ha => ?_,
      fun a b hab hb hd => ?_⟩, by simp; omega, rfl, rfl⟩
    · simp only at ha ⊢
      by_cases hlo : a < s.lo
      · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
        exact ⟨c, by omega, hcd, hce⟩
      · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by omega) (by omega)
        exact ⟨c, by omega, by rw [hblk c hc1 hc2, hblk a (by omega) (by omega)], hce⟩
    · simp only at hb hd ⊢
      by_cases hb' : b < s.lo
      · exact hg.dsrt a b hab hb' hd
      · by_cases ha' : s.lo ≤ a
        · exact hg.srt a b ha' hab (by omega)
        · exfalso
          have h1 : a / (2 * w) < m := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [hm] at ha'; linarith
          have h2 : b / (2 * w) = m := hblk b (by omega) (by omega)
          omega
  · next h =>
    refine ⟨hg, ?_, rfl, rfl⟩
    have := hg.ord
    omega

/-- **One step keeps the invariant** and advances `k`. -/
theorem good_mstep {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w)
    (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (mstep lt src n w s) ∧ (mstep lt src n w s).k = s.k + 1 := by
  obtain ⟨hg', hav, hkk, -⟩ := good_bstart hw hg hk
  unfold mstep
  generalize bstart n w s = t at hg' hav hkk
  rw [← hkk] at hk ⊢
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg'.ord
  obtain ⟨e1, e2, e3, e4⟩ := hg'.ends
  obtain ⟨m, hm⟩ := hg'.algn
  -- the runs: `[lo, iE)` is run `2m`, `[iE, jE)` is run `2m + 1`
  have e2m : w * (2 * m) = 2 * w * m := by ring
  have e2m1 : w * (2 * m + 1) = 2 * w * m + w := by ring
  have runL : ∀ a, t.lo ≤ a → a < t.iE → a / w = 2 * m := fun a h1 h2 =>
    div_eq_of_block (by rw [e2m]; omega) (by rw [e2m]; omega)
  have runR : ∀ a, t.j < t.jE → t.iE ≤ a → a < t.jE → a / w = 2 * m + 1 := fun a hj h1 h2 => by
    have := e3 hj
    exact div_eq_of_block (by rw [e2m1]; omega) (by rw [e2m1]; omega)
  dsimp only
  by_cases hL : takeL lt src t = true
  · rw [if_pos hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt] at hL
    obtain ⟨hiL, hc⟩ := hL
    refine ⟨⟨by simp; omega, ⟨by simp; omega, by simp; omega, fun h => by simp at h; exact e3 h,
      by simp; exact e4⟩,
      ⟨m, hm⟩, by simp; have := hg'.kk; omega, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by omega)]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by omega)).1 hiL
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.i, by omega, by omega, rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by omega)
    · intro a ha hak
      have hiR : ∀ h : t.j < t.jE, lt (src t.i) (src t.j) = true := fun h => by
        rcases hc with hc | hc
        · omega
        · exact hc
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨fun h => hsrt _ _ (by omega) (by omega) (by rw [runL _ (by omega) (by omega),
          runL _ (by omega) h]), hiR⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by omega)
        exact ⟨fun h => ho.trans _ _ _ (hh.1 hiL) (hsrt _ _ (by omega) (by omega)
          (by rw [runL _ (by omega) (by omega), runL _ (by omega) h])), hh.2⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by omega)]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by omega), if_neg (by omega)]; exact hg'.dsrt a b hab hb hd
  · rw [if_neg hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt, not_and, not_or] at hL
    -- the right head is available, and below the left head when that one is
    have hjR : t.j < t.jE := by
      by_contra h
      rcases hav with h' | h'
      · exact (hL h').1 (by omega)
      · exact h h'
    have hji : t.i < t.iE → lt (src t.j) (src t.i) = true := fun h => by
      have hne : src t.i ≠ src t.j := fun he => by
        have := hinj _ _ (by omega) (by omega) he; omega
      rcases ho.total _ _ hne with h1 | h1
      · exact absurd h1 (by have := (hL h).2; simpa using this)
      · exact h1
    refine ⟨⟨by simp; omega, ⟨by simp; omega, by simp; omega, fun h => by
      simp at h; exact e3 (by omega), by simp; exact e4⟩, ⟨m, hm⟩, by simp; have := hg'.kk; omega, ?_, ?_, ?_, ?_,
      ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by omega)]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by omega)).2 hjR
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.j, by omega, by omega, rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨hji, fun h => hsrt _ _ (by omega) (by omega) (by rw [runR _ hjR (by omega) (by omega),
          runR _ hjR (by omega) h])⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by omega)
        exact ⟨hh.1, fun h => ho.trans _ _ _ (hh.2 hjR) (hsrt _ _ (by omega) (by omega)
          (by rw [runR _ hjR (by omega) (by omega), runR _ hjR (by omega) h]))⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by omega)]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by omega), if_neg (by omega)]; exact hg'.dsrt a b hab hb hd

/-! ## One pass -/

/-- `m` steps. -/
def mrun (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) : ℕ → MS → MS
  | 0, s => s
  | m + 1, s => mrun lt src n w m (mstep lt src n w s)

/-- **The pass**: `n` steps from the empty state. -/
def passF (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) : ℕ → Word :=
  (mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩).dst

theorem good_mrun {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ m (s : MS), Good lt src n w s → s.k + m ≤ n →
      Good lt src n w (mrun lt src n w m s) ∧ (mrun lt src n w m s).k = s.k + m
  | 0, s, hg, _ => ⟨hg, rfl⟩
  | m + 1, s, hg, hm => by
    obtain ⟨h1, h2⟩ := good_mstep ho hw hsrt hinj hg (by omega)
    obtain ⟨h3, h4⟩ := good_mrun ho hw hsrt hinj m _ h1 (by omega)
    exact ⟨h3, by simp only [mrun]; rw [h4, h2]; omega⟩

/-- What a pass delivers. -/
structure PassOut (lt : Word → Word → Bool) (src d : ℕ → Word) (n w : ℕ) : Prop where
  mem : ∀ a < n, ∃ c < n, c / (2 * w) = a / (2 * w) ∧ d a = src c
  srt : ∀ a b, a < b → b < n → a / (2 * w) = b / (2 * w) → lt (d a) (d b) = true

/-- **`pass_ok`**: a pass on a source with strictly sorted runs of width `w`, injective on
`[0, n)`, gives strictly sorted blocks of width `2w` drawn from the same source blocks. -/
theorem pass_ok {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) (d : ℕ → Word) :
    PassOut lt src (passF lt src n w d) n w := by
  obtain ⟨hg, hk⟩ := good_mrun ho hw hsrt hinj n _ (good_init lt src n w d) (by simp)
  simp only [Nat.zero_add] at hk
  unfold passF
  generalize mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩ = s at hg hk
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
  obtain ⟨e1, e2, -, -⟩ := hg.ends
  obtain ⟨m, hm⟩ := hg.algn
  have hkk := hg.kk
  have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
    div_eq_of_block (by omega) (by omega)
  have hlt : ∀ a, a < s.lo → a / (2 * w) < m := fun a ha => by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [hm] at ha; linarith
  refine ⟨fun a ha => ?_, fun a b hab hb hd => ?_⟩
  · by_cases hlo : a < s.lo
    · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
      exact ⟨c, by omega, hcd, hce⟩
    · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by omega) (by omega)
      exact ⟨c, by omega, by rw [hblk c hc1 hc2, hblk a (by omega) (by omega)], hce⟩
  · by_cases hb' : b < s.lo
    · exact hg.dsrt a b hab hb' hd
    · by_cases ha' : s.lo ≤ a
      · exact hg.srt a b ha' hab (by omega)
      · exfalso
        have := hlt a (by omega)
        have := hblk b (by omega) (by omega)
        omega

/-- A pass's output is injective on `[0, n)`. -/
theorem PassOut.inj {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hp : PassOut lt src d n w) (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ a b, a < n → b < n → d a = d b → a = b := by
  intro a b ha hb he
  by_contra hne
  have key : ∀ a b, a < b → b < n → d a = d b → False := fun a b hab hb he => by
    by_cases hd : a / (2 * w) = b / (2 * w)
    · have := hp.srt a b hab hb hd
      rw [he, ho.irrefl] at this; cases this
    · obtain ⟨c, hc, hcb, hca⟩ := hp.mem a (by omega)
      obtain ⟨c', hc', hcb', hca'⟩ := hp.mem b hb
      have := hinj c c' hc hc' (by rw [← hca, ← hca', he])
      subst this
      exact hd (hcb.symm.trans hcb')
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key a b h hb he
  · exact key b a h ha he.symm

/-- The runs of the next width `min(2w, n)` are sorted. -/
theorem PassOut.runs {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ}
    (hp : PassOut lt src d n w) :
    ∀ a b, a < b → b < n → a / min (2 * w) n = b / min (2 * w) n → lt (d a) (d b) = true := by
  intro a b hab hb hd
  refine hp.srt a b hab hb ?_
  by_cases h : 2 * w ≤ n
  · rwa [Nat.min_eq_left h] at hd
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-! ## 64 passes -/

/-- The run widths: `1`, then `min(2w, n)`. -/
def wseq (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | p + 1 => min (2 * wseq n p) n

theorem wseq_eq {n : ℕ} (hn : 0 < n) : ∀ p, wseq n p = min (2 ^ p) n
  | 0 => by simp [wseq]; omega
  | p + 1 => by
    rw [wseq, wseq_eq hn p, pow_succ]
    rcases Nat.le_total (2 ^ p) n with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

/-- **The sort's correctness, pure form**: if each array is a pass of the previous one at width
`wseq n p`, starting from an array `X 0` injective on `[0, n)`, then after 64 passes the array is
strictly sorted on `[0, n)` and holds exactly the values of `X 0` there. -/
theorem passes_ok {lt : Word → Word → Bool} (ho : SOrd lt) {n : ℕ} (hn : n < 2 ^ 63)
    (X : ℕ → ℕ → Word) (ds : ℕ → ℕ → Word)
    (hX : ∀ p, ∀ a < n, X (p + 1) a = passF lt (X p) n (wseq n p) (ds p) a)
    (hinj : ∀ a b, a < n → b < n → X 0 a = X 0 b → a = b) :
    (∀ a b, a < b → b < n → lt (X 64 a) (X 64 b) = true) ∧
    (∀ a < n, ∃ c < n, X 64 a = X 0 c) ∧ (∀ c < n, ∃ a < n, X 64 a = X 0 c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact ⟨fun _ _ _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩
  -- the invariant after `p` passes
  have inv : ∀ p, (∀ a b, a < n → b < n → X p a = X p b → a = b) ∧
      (∀ a b, a < b → b < n → a / wseq n p = b / wseq n p → lt (X p a) (X p b) = true) ∧
      (∀ a < n, ∃ c < n, X p a = X 0 c) := by
    intro p
    induction p with
    | zero =>
      refine ⟨hinj, fun a b hab _ hd => ?_, fun a ha => ⟨a, ha, rfl⟩⟩
      simp only [wseq, Nat.div_one] at hd; omega
    | succ p ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      have hw : 0 < wseq n p := by rw [wseq_eq hn0]; have := Nat.one_le_two_pow (n := p); omega
      have hp := pass_ok ho hw i2 i1 (ds p)
      have hp' : PassOut lt (X p) (X (p + 1)) n (wseq n p) :=
        ⟨fun a ha => by rw [hX p a ha]; exact hp.mem a ha, fun a b hab hb hd => by
          rw [hX p a (by omega), hX p b hb]; exact hp.srt a b hab hb hd⟩
      refine ⟨hp'.inj ho i1, hp'.runs, fun a ha => ?_⟩
      obtain ⟨c, hc, -, hce⟩ := hp'.mem a ha
      obtain ⟨c', hc', hce'⟩ := i3 c hc
      exact ⟨c', hc', hce.trans hce'⟩
  obtain ⟨i1, i2, i3⟩ := inv 64
  have hw64 : wseq n 64 = n := by rw [wseq_eq hn0]; exact Nat.min_eq_right (by omega)
  refine ⟨fun a b hab hb => i2 a b hab hb (by
    rw [hw64, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt hb]), i3, fun c hc => ?_⟩
  -- completeness: `n` distinct values among the `n` values of `X 0`
  classical
  have hsub : (Finset.range n).image (X 64) ⊆ (Finset.range n).image (X 0) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_range] at hv ⊢
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨c, hc, he⟩ := i3 a ha
    exact ⟨c, hc, he.symm⟩
  have hcard : ((Finset.range n).image (X 0)).card ≤ ((Finset.range n).image (X 64)).card := by
    rw [Finset.card_image_of_injOn (fun a ha b hb he => i1 a b (by simpa using ha)
      (by simpa using hb) he)]
    exact (Finset.card_image_le).trans (by simp)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : X 0 c ∈ (Finset.range n).image (X 64) := by
    rw [heq]; exact Finset.mem_image_of_mem _ (by simpa using hc)
  simp only [Finset.mem_image, Finset.mem_range] at this
  exact this

/-! ## `keyLt` is a strict total order -/

theorem lexW_irrefl : ∀ l : List Word, lexW l l = false
  | [] => rfl
  | a :: l => by simp [lexW, lexW_irrefl l]

theorem lexW_trans : ∀ l₁ l₂ l₃ : List Word, lexW l₁ l₂ = true → lexW l₂ l₃ = true →
    lexW l₁ l₃ = true
  | a :: l₁, b :: l₂, c :: l₃, h1, h2 => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; rw [BitVec.lt_def] at *; omega
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, lexW_trans l₁ l₂ l₃ h1 h2⟩
  | [], _, _, h, _ => by simp [lexW] at h
  | _ :: _, [], _, h, _ => by simp [lexW] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexW] at h

theorem lexW_total : ∀ l₁ l₂ : List Word, l₁.length = l₂.length → l₁ ≠ l₂ →
    lexW l₁ l₂ = true ∨ lexW l₂ l₁ = true
  | [], [], _, h => absurd rfl h
  | a :: l₁, b :: l₂, hl, h => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hab : a = b
    · subst hab
      rcases lexW_total l₁ l₂ (by simpa using hl) (fun e => h (by rw [e])) with h' | h'
      · exact .inl (.inr ⟨rfl, h'⟩)
      · exact .inr (.inr ⟨rfl, h'⟩)
    · have hne : a.toNat ≠ b.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact .inl (.inl (BitVec.lt_def.mpr h'))
      · exact .inr (.inl (BitVec.lt_def.mpr h'))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **`keyLt I` is a strict total order** (the position is the key's last word). -/
theorem keyLt_order (I : Array Word) : SOrd (keyLt I) where
  irrefl := fun a => lexW_irrefl _
  trans := fun a b c => lexW_trans _ _ _
  total := fun a b hab => lexW_total _ _ (by simp [keyW]) (fun e => hab (by
    simp only [keyW, List.cons.injEq] at e; exact e.2.2.2.2.1))

end Lvm.X

end LvmXMerge

section LvmXSortSim


/-!
# Simulating the merge sort: `stepIR` by `mstep`, `passIR` by `passF`, `sortIR` by `passes_ok`

* Word-level facts: the branch-free `min` (`minW_toWord`), the `eq`/`ltu` flags.
* `Rel S D n w src M σ`: the registers hold the pass state `σ : MS` (`Regs`), the heap holds the
  source at `S + ·` and `σ.dst` at `D + ·` on `[0, n)`; `Lay` is the pass layout.
* `blockIR_sem`, `choose_sem`, `tail_sem`, **`stepIR_sem`**: one step is `mstep (keyLt I)`.
* **`passIR_sem`**: a pass writes `passF` of the source into the destination, swaps the bases and
  sets `w := min(2w, n)`.
* **`sortIR_sem`**: 64 passes leave `X[0..n)` strictly sorted by `keyLt` and holding exactly the
  initial (distinct) values (`passes_ok`).
* **`idxIR4_sorted`**: on a domain tape of a SNARK proof, after `idxIR4` `X[0..|L|)` holds exactly
  the log entries' tape positions, sorted by (answer, position).

(S-H2-RESULT, Parts 5 and 6.)

**Parameters.** The sort and the index take the index base `bX` and the tape word `pL`
of `|L|` (`sortIR4`, `idxIR4`, `idxIR4_sorted`); lvm's instance is `memX`, `posL pz`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-- The branch-free `min` of `minPs`: `b ^^^ ((a ^^^ b) &&& (0 - [a < b]))`. -/
theorem minW (a b : Word) :
    b ^^^ ((a ^^^ b) &&& (0 - XOp.ltu.eval a b)) = if a < b then a else b := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    simp only [XOp.eval, h, ↓reduceIte, h1, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp only [XOp.eval, h, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

/-- `min` of two small numbers as words. -/
theorem minW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    toWord b ^^^ ((toWord a ^^^ toWord b) &&& (0 - XOp.ltu.eval (toWord a) (toWord b))) =
      toWord (min a b) := by
  rw [minW]
  by_cases h : a < b
  · rw [if_pos ((toWord_lt_toWord ha hb).2 h), Nat.min_eq_left h.le]
  · rw [if_neg (fun h' => h ((toWord_lt_toWord ha hb).1 h')), Nat.min_eq_right (by omega)]

/-- The `eq` flag on small numbers. -/
theorem eqW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = bW (decide (a = b)) := by
  simp only [XOp.eval, bW]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg (fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_toWord ha, toNat_toWord hb] at this))]
    simp [h]

/-- The `ltu` flag on small numbers. -/
theorem ltW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = bW (decide (a < b)) := by
  simp only [XOp.eval, bW, toWord_lt_toWord ha hb]
  by_cases h : a < b <;> simp [h]


/-! ## Word helpers -/

theorem add_toWord (a b : ℕ) : XOp.add.eval (toWord a) (toWord b) = toWord (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem or_self_eval (x : Word) : XOp.or.eval x x = x := BitVec.or_self

/-- `minPs` as the machine evaluates it. -/
theorem minP_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.xor.eval (toWord b) (XOp.and.eval (XOp.xor.eval (toWord a) (toWord b))
      (XOp.sub.eval 0 (XOp.ltu.eval (toWord a) (toWord b)))) = toWord (min a b) :=
  minW_toWord ha hb

theorem bW_and (p q : Bool) : XOp.and.eval (bW p) (bW q) = bW (p && q) := by
  cases p <;> cases q <;> decide

theorem bW_ne_zero : bW true ≠ 0 := by decide

theorem bW_false : bW false = 0 := rfl

/-! ## The heap frame of store-free, loop-free code -/

/-- No store, no loop, every destination a register. -/
def Lo : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => Lo p ∧ Lo q
  | .ite _ p q => Lo p ∧ Lo q
  | _ => False

/-- **Heap frame**: such code leaves every cell `≥ regs` alone. -/
theorem hframe (I : Array Word) : ∀ (P : XIR) (s : St), Lo P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframe I q _ h.2 x hx).trans (hframe I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframe I q s h.2 x hx
    · exact hframe I p s h.1 x hx
  | .store .., _, h, _, _ => h.elim
  | .loopK .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- Controls for `Lo`: a store, or a block writing a heap cell, is not `Lo`. -/
theorem not_lo_store : ¬ Lo (.store rAd rV) := id

theorem not_lo_heap : ¬ Lo (.blk [.const regs 0]) := by simp +decide only [Lo, Prim.dst]

/-! ## The relation between the machine and `MS` -/

/-- The nine registers of a merge pass. -/
def regL : List ℕ := [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst]

/-- The registers hold `σ`'s indices and the pass parameters `S`, `D` (the bases), `n`, `w`. -/
structure Regs (M : Mem) (S D n w : ℕ) (σ : MS) : Prop where
  i : rd M rI = toWord σ.i
  iE : rd M rIE = toWord σ.iE
  j : rd M rJ = toWord σ.j
  jE : rd M rJE = toWord σ.jE
  k : rd M rKk = toWord σ.k
  w : rd M rW2 = toWord w
  n : rd M rN = toWord n
  S : rd M rSrc = toWord S
  D : rd M rDst = toWord D

theorem Regs.frame {M M' : Mem} {S D n w : ℕ} {σ : MS} (h : Regs M S D n w σ)
    (hf : ∀ r ∈ regL, rd M' r = rd M r) : Regs M' S D n w σ where
  i := (hf rI (by simp [regL])).trans h.i
  iE := (hf rIE (by simp [regL])).trans h.iE
  j := (hf rJ (by simp [regL])).trans h.j
  jE := (hf rJE (by simp [regL])).trans h.jE
  k := (hf rKk (by simp [regL])).trans h.k
  w := (hf rW2 (by simp [regL])).trans h.w
  n := (hf rN (by simp [regL])).trans h.n
  S := (hf rSrc (by simp [regL])).trans h.S
  D := (hf rDst (by simp [regL])).trans h.D

theorem regL_lt : ∀ r ∈ regL, r < regs := by decide

theorem Regs.sem {I : Array Word} {P : XIR} {s : St} {S D n w : ℕ} {σ : MS}
    (h : Regs s.M S D n w σ) (hM : Inv s.M) (hP : WF P) (hw : ∀ r ∈ regL, ¬ Writes P r) :
    Regs (semXIR I P s).M S D n w σ :=
  h.frame fun r hr => Lvm.X.frame I P s hP hM r (regL_lt r hr) (hw r hr)

/-- The indices stay in range. -/
def Bnd (n : ℕ) (σ : MS) : Prop := σ.i ≤ σ.iE ∧ σ.j ≤ σ.jE ∧ σ.iE ≤ n ∧ σ.jE ≤ n

/-- The layout of a pass: source at `S`, destination at `D`, disjoint heap ranges of `n` cells. -/
structure Lay (S D n w sz : ℕ) : Prop where
  rS : regs ≤ S
  rD : regs ≤ D
  sS : S + n ≤ sz
  sD : D + n ≤ sz
  disj : S + n ≤ D ∨ D + n ≤ S
  bS : S + n < 2 ^ 64
  bD : D + n < 2 ^ 64
  bn : 3 * n + 2 < 2 ^ 64
  bw : w ≤ n + 1
  pw : 0 < n → 0 < w

/-- **The simulation relation**: the machine's memory holds the pass state `σ`. -/
structure Rel (S D n w : ℕ) (src : ℕ → Word) (M : Mem) (σ : MS) : Prop where
  inv : Inv M
  rg : Regs M S D n w σ
  hs : ∀ a < n, rd M (S + a) = src a
  hd : ∀ a < n, rd M (D + a) = σ.dst a
  bnd : Bnd n σ

theorem bstart_props {n w : ℕ} {σ : MS} (hB : Bnd n σ) (hk : σ.k < n) (hw : 0 < w) :
    (bstart n w σ).k = σ.k ∧ (bstart n w σ).dst = σ.dst ∧ Bnd n (bstart n w σ) ∧
      ((bstart n w σ).i < (bstart n w σ).iE ∨ (bstart n w σ).j < (bstart n w σ).jE) := by
  unfold bstart Bnd at *
  split
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only <;> omega
  · exact ⟨rfl, rfl, by omega, by omega⟩

/-! ## `blockIR` -/

theorem lo_blockIR : Lo blockIR := by
  simp +decide only [Lo, blockIR, minPs, Prim.dst, regs, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1,
    rT2, rKc, and_true, List.cons_append, List.nil_append]

theorem wf_blockIR : WF blockIR := by
  simp +decide only [WF, blockIR, minPs, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1, rT2, rKc,
    and_true, List.cons_append, List.nil_append]

/-- **`blockIR` computes `bstart`.** -/
theorem blockIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {σ : MS}
    (hR : Regs s.M S D n w σ) (hB : Bnd n σ) (hk : σ.k < n) (hn : 3 * n + 2 < 2 ^ 64)
    (hw : w ≤ n + 1) : Regs (semXIR I blockIR s).M S D n w (bstart n w σ) := by
  have hs := hM.1
  simp only [regs] at hs
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hwf1 : WF (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) := by
    simp +decide only [WF, Prim.dst, rG, rH]
  have h1 : rd (semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s).M
      rG = bW (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) := by
    have hi := hR.i; have hiE := hR.iE; have hj := hR.j; have hjE := hR.jE
    simp only [semXIR, runPrims, List.foldl, Prim.run, rG, rH, rI, rIE, rJ, rJE] at hi hiE hj hjE ⊢
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne]
    rw [hi, hiE, hj, hjE, eqW_toWord (by omega) (by omega), eqW_toWord (by omega) (by omega),
      bW_and]
  have hR1 := hR.sem (I := I) hM hwf1 (by simp +decide only [regL, Writes, Prim.dst, rG, rH, rI,
    rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  rw [blockIR, semXIR_seq, semXIR_ite]
  generalize semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s = s1
    at h1 hR1 hM1
  unfold bstart
  by_cases hc : σ.i = σ.iE ∧ σ.j = σ.jE
  · rw [if_pos hc, h1, decide_eq_true hc.1, decide_eq_true hc.2]
    rw [Bool.and_self, if_neg bW_ne_zero]
    have hs1 := hM1.1
    simp only [regs] at hs1
    obtain ⟨i1, iE1, j1, jE1, k1, w1, n1, S1, D1⟩ := hR1
    simp only [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst] at i1 iE1 j1 jE1 k1 w1 n1 S1 D1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, minPs, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst, rV, rT1, rT2,
      rKc] <;>
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne] <;>
    simp only [i1, iE1, j1, jE1, k1, w1, n1, S1, D1, or_self_eval, add_toWord] <;>
    simp (disch := omega) only [minP_toWord, add_toWord, or_self_eval]
  · rw [if_neg hc, h1, show (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) = false by simpa using hc,
      if_pos bW_false]
    exact hR1


/-! ## `stepIR`, piece by piece -/

/-- The run flags. -/
def flagsIR : XIR := .blk [.op .ltu rG rI rIE, .op .ltu rH rJ rJE]
/-- The choice: `rF := takeL`. -/
def chooseIR : XIR := .ite rG (.ite rH cmpIR (.blk [.const rF 1])) (.blk [.const rF 0])
/-- The head that goes next: its address in `rAd`, the head advanced. -/
def advIR : XIR := .ite rF (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
  (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
/-- The write `dst[k] := src[h]`, `k += 1`. -/
def tailIR : XIR :=
  .seq (.load rV rAd) (.seq (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]) (.store rAd rV))

theorem stepIR_eq : stepIR = .seq blockIR (.seq flagsIR (.seq chooseIR (.seq advIR tailIR))) :=
  rfl

theorem add_one_toWord (a : ℕ) : XOp.add.eval (toWord a) 1 = toWord (a + 1) :=
  (BitVec.ofNat_add a 1).symm

/-- **The choice** leaves `takeL` in `rF`. -/
theorem choose_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {src : ℕ → Word}
    {τ : MS} (hR : Regs s.M S D n w τ) (hrS : regs ≤ S) (hbS : S + n < 2 ^ 64) (hB : Bnd n τ)
    (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hG : rd s.M rG = bW (decide (τ.i < τ.iE))) (hH : rd s.M rH = bW (decide (τ.j < τ.jE))) :
    rd (semXIR I chooseIR s).M rF = bW (takeL (keyLt I) src τ) := by
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hs := hM.1
  simp only [regs] at hs hrS
  rw [chooseIR, semXIR_ite]
  by_cases g : τ.i < τ.iE
  · rw [hG, decide_eq_true g, if_neg bW_ne_zero, semXIR_ite]
    by_cases h : τ.j < τ.jE
    · rw [hH, decide_eq_true h, if_neg bW_ne_zero]
      have ha : ∀ a < n, regs ≤ (rd s.M rSrc + toWord a).toNat ∧
          rd s.M (rd s.M rSrc + toWord a).toNat = src a := fun a ha => by
        rw [hR.S, toWord_add, toNat_toWord (by omega), hsrc a ha]
        exact ⟨by simp only [regs]; omega, rfl⟩
      rw [cmpIR_sem I s hM (by rw [hR.i]; exact (ha _ (by omega)).1)
        (by rw [hR.j]; exact (ha _ (by omega)).1), hR.i, hR.j, (ha _ (by omega)).2,
        (ha _ (by omega)).2]
      simp [takeL, g, h]
    · rw [hH, decide_eq_false h, if_pos bW_false]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [rF]; omega)]
      simp [takeL, g, h, bW]
  · rw [hG, decide_eq_false g, if_pos bW_false]
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rF]; omega)]
    simp [takeL, g, bW]

theorem lo_cmpIR : Lo cmpIR := by
  simp +decide only [Lo, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, regs, rAd, rX, rY, rPa, rPb,
    rKa, rKb, rF, rG, rH, rQL, rKc, rT2, and_true, List.cons_append, List.nil_append]

theorem wf_cmpIR : WF cmpIR := by
  simp +decide only [WF, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY, rPa, rPb, rKa, rKb,
    rF, rG, rH, rQL, rKc, rT2, and_true, List.cons_append, List.nil_append]

/-- **The write**: `dst[k] := src[h]`, `k += 1`; the source and the other registers stay. -/
theorem tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w h : ℕ} {src : ℕ → Word}
    {τ : MS} (hL : Lay S D n w s.M.size) (hR : Regs s.M S D n w τ) (hk : τ.k < n) (hh : h < n)
    (hA : rd s.M rAd = toWord (S + h)) (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hdst : ∀ a < n, rd s.M (D + a) = τ.dst a) :
    Inv (semXIR I tailIR s).M ∧
    Regs (semXIR I tailIR s).M S D n w { τ with k := τ.k + 1, dst := upd τ.dst τ.k (src h) } ∧
    (∀ a < n, rd (semXIR I tailIR s).M (S + a) = src a) ∧
    (∀ a < n, rd (semXIR I tailIR s).M (D + a) = upd τ.dst τ.k (src h) a) := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  obtain ⟨Lr, Ld, LsS, LsD, Ldj, LbS, LbD, -, -, -⟩ := hL
  simp only [regs] at hs Lr Ld
  have e : semXIR I tailIR s = semXIR I (.store rAd rV) (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s) := rfl
  have hwf2 : WF (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) := by
    simp +decide only [WF, Prim.dst, rV, rAd, rKk, and_true]
  have hM2 := inv_sem I hwf2 hM
  have hH2 := hframe I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]))
    s (by simp +decide only [Lo, Prim.dst, regs, rV, rAd, rKk, and_true])
  have hz2 := size_sem I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk,
    .op .add rKk rKk cOne])) s
  have hF2 : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst], rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M r = rd s.M r := fun r hr =>
    frame I _ s hwf2 hM r (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [Writes, Prim.dst, rV, rAd, rKk, rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst,
          or_false])
  have hA2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rAd = toWord (D + τ.k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hR.D, hR.k, add_toWord]
  have hK2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rKk = toWord (τ.k + 1) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hR.k, hc1, add_one_toWord]
  have hV2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rV = src h := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, toNat_toWord (by omega), hsrc h hh]
  rw [e]
  generalize semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s = s2 at hM2 hH2 hz2 hF2 hA2 hK2 hV2
  have hst : ∀ i, i ≠ cTmp → rd (semXIR I (.store rAd rV) s2).M i =
      if i = D + τ.k then src h else rd s2.M i := fun i hi => by
    rw [← hV2]
    exact rd_storeM hM2 hA2 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
      (by decide) hi
  have hreg : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst],
      rd (semXIR I (.store rAd rV) s2).M r = rd s.M r := fun r hr => by
    have h1 : r < regs ∧ r ≠ cTmp := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hst r h1.2, if_neg (by simp only [regs] at h1; omega), hF2 r hr]
  refine ⟨inv_sem I (P := .store rAd rV) (by simp +decide only [WF, rAd, cTmp]) hM2,
    ⟨(hreg rI (by simp)).trans hR.i, (hreg rIE (by simp)).trans hR.iE,
      (hreg rJ (by simp)).trans hR.j, (hreg rJE (by simp)).trans hR.jE, ?_,
      (hreg rW2 (by simp)).trans hR.w, (hreg rN (by simp)).trans hR.n,
      (hreg rSrc (by simp)).trans hR.S, (hreg rDst (by simp)).trans hR.D⟩,
    fun a ha => ?_, fun a ha => ?_⟩
  · rw [hst rKk (by decide), if_neg (by simp only [rKk]; omega), hK2]
  · rw [hst _ (by simp only [cTmp]; omega), if_neg (by omega), hH2 _ (by simp only [regs]; omega),
      hsrc a ha]
  · rw [hst _ (by simp only [cTmp]; omega)]
    by_cases hak : a = τ.k
    · subst hak; rw [if_pos rfl]; simp [upd]
    · rw [if_neg (by omega), hH2 _ (by simp only [regs]; omega), hdst a ha]
      simp [upd, hak]


/-- **`advIR`** for a head register `r ∈ {rI, rJ}` holding `h`: `rAd := S + h`, `r := h + 1`. -/
theorem adv_blk (I : Array Word) (s : St) (hM : Inv s.M) {S h : ℕ} {r : ℕ} (hr : r = rI ∨ r = rJ)
    (hS : rd s.M rSrc = toWord S) (hh : rd s.M r = toWord h) :
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M rAd = toWord (S + h) ∧
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M r = toWord (h + 1) ∧
    ∀ q ∈ regL, q ≠ r → rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M q =
      rd s.M q := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have hr' : r < 256 ∧ r ≠ rAd ∧ r ≠ cOne := by rcases hr with rfl | rfl <;> decide
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, fun q hq hqr => ?_⟩
  · rw [rd_set_ne hr'.2.1, rd_set_self (by simp only [rAd]; omega), hS, hh, add_toWord]
  · rw [rd_set_self (by simp only [size_set]; omega), rd_set_ne (Ne.symm hr'.2.1),
      rd_set_ne (by decide : rAd ≠ cOne), hc1, hh, add_one_toWord]
  · have hq' : q ≠ rAd := by
      simp only [regL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rd_set_ne (Ne.symm hqr), rd_set_ne (Ne.symm hq')]

theorem lo_flagsIR : Lo flagsIR := by simp +decide only [Lo, flagsIR, Prim.dst, regs, rG, rH]
theorem wf_flagsIR : WF flagsIR := by simp +decide only [WF, flagsIR, Prim.dst, rG, rH]
theorem lo_chooseIR : Lo chooseIR := by
  simp only [Lo, chooseIR]; exact ⟨⟨lo_cmpIR, by simp [Prim.dst, regs, rF]⟩,
    by simp [Prim.dst, regs, rF]⟩
theorem wf_chooseIR : WF chooseIR := by
  simp only [WF, chooseIR]; exact ⟨⟨wf_cmpIR, by simp [Prim.dst, rF]⟩, by simp [Prim.dst, rF]⟩
theorem lo_advIR : Lo advIR := by simp +decide only [Lo, advIR, Prim.dst, regs, rAd, rI, rJ,
  and_true]
theorem wf_advIR : WF advIR := by simp +decide only [WF, advIR, Prim.dst, rAd, rI, rJ, and_true]

theorem nw_flagsIR : ∀ r ∈ regL, ¬ Writes flagsIR r := by
  simp +decide only [regL, Writes, flagsIR, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc,
    rDst, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
    exists_eq_left, or_false, and_true]

theorem nw_chooseIR : ∀ r ∈ regL, ¬ Writes chooseIR r := by
  simp +decide only [regL, Writes, chooseIR, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY,
    rPa, rPb, rKa, rKb, rF, rG, rH, rQL, rKc, rT2, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left,
    or_false, and_true, List.cons_append, List.nil_append]

/-- **One step**: `stepIR` maps a state holding `σ` to one holding `mstep σ`. -/
theorem stepIR_sem (I : Array Word) (s : St) {S D n w : ℕ} {src : ℕ → Word} {σ : MS}
    (hL : Lay S D n w s.M.size) (hR : Rel S D n w src s.M σ) (hk : σ.k < n) :
    Rel S D n w src (semXIR I stepIR s).M (mstep (keyLt I) src n w σ) ∧
      (mstep (keyLt I) src n w σ).k = σ.k + 1 := by
  obtain ⟨hM, hRg, hsrc, hdst, hB⟩ := hR
  obtain ⟨tk, tdst, tB, tav⟩ := bstart_props hB hk (hL.pw (by omega))
  have hR1 := blockIR_sem I s hM hRg hB hk hL.bn hL.bw
  have hM1 := inv_sem I wf_blockIR hM
  have hH1 := hframe I _ s lo_blockIR
  have hz1 := size_sem I blockIR s
  have Lr := hL.rS
  have Ld := hL.rD
  have LbS := hL.bS
  have Lbn := hL.bn
  simp only [regs] at Lr Ld
  simp only [mstep]
  rw [stepIR_eq, semXIR_seq]
  generalize bstart n w σ = τ at tk tdst tB tav hR1
  generalize semXIR I blockIR s = s1 at hR1 hM1 hH1 hz1
  obtain ⟨b1, b2, b3, b4⟩ := tB
  -- the flags
  have hfl : rd (semXIR I flagsIR s1).M rG = bW (decide (τ.i < τ.iE)) ∧
      rd (semXIR I flagsIR s1).M rH = bW (decide (τ.j < τ.jE)) := by
    have hs1 := hM1.1
    simp only [regs] at hs1
    simp only [flagsIR, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rG, rH]; omega)) only [rd_set_self,
      rd_set_ne]
    · rw [hR1.i, hR1.iE, ltW_toWord (by omega) (by omega)]
    · rw [hR1.j, hR1.jE, ltW_toWord (by omega) (by omega)]
  have hR2 := hR1.sem (I := I) hM1 wf_flagsIR nw_flagsIR
  have hM2 := inv_sem I wf_flagsIR hM1
  have hH2 := hframe I _ s1 lo_flagsIR
  have hz2 := size_sem I flagsIR s1
  rw [semXIR_seq]
  generalize semXIR I flagsIR s1 = s2 at hfl hR2 hM2 hH2 hz2
  -- the choice
  have hsrc2 : ∀ a < n, rd s2.M (S + a) = src a := fun a ha => by
    rw [hH2 _ (by simp only [regs]; omega), hH1 _ (by simp only [regs]; omega), hsrc a ha]
  have hF := choose_sem I s2 hM2 hR2 hL.rS LbS ⟨b1, b2, b3, b4⟩ hsrc2 hfl.1 hfl.2
  have hR3 := hR2.sem (I := I) hM2 wf_chooseIR nw_chooseIR
  have hM3 := inv_sem I wf_chooseIR hM2
  have hH3 := hframe I _ s2 lo_chooseIR
  have hz3 := size_sem I chooseIR s2
  rw [semXIR_seq]
  generalize semXIR I chooseIR s2 = s3 at hF hR3 hM3 hH3 hz3
  have hsrc3 : ∀ a < n, rd s3.M (S + a) = src a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; omega), hsrc2 a ha]
  have hdst3 : ∀ a < n, rd s3.M (D + a) = τ.dst a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; omega), hH2 _ (by simp only [regs]; omega),
      hH1 _ (by simp only [regs]; omega), hdst a ha, tdst]
  have hL3 : Lay S D n w s3.M.size := by rw [hz3, hz2, hz1]; exact hL
  -- the write
  rw [semXIR_seq, advIR, semXIR_ite, hF]
  by_cases hT : takeL (keyLt I) src τ = true
  · have hi : τ.i < τ.iE := by simp [takeL] at hT; exact hT.1
    rw [hT, if_neg bW_ne_zero, if_pos rfl]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inl rfl) hR3.S hR3.i
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) s3).M S D n w
        { τ with i := τ.i + 1 } := ⟨a2, (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE,
      (a3 rJ (by simp [regL]) (by decide)).trans hR3.j,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) := by
      simp +decide only [Lo, Prim.dst, regs, rAd, rI]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
      (by simp +decide only [WF, Prim.dst, rAd, rI]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; omega)
      (h := τ.i) (by omega) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨by show τ.i + 1 ≤ τ.iE; omega, b2, b3, b4⟩⟩, by simp only; omega⟩
  · have hj : τ.j < τ.jE := by
      by_contra hj
      apply hT
      simp only [takeL, hj, decide_false, Bool.not_false, Bool.true_or, Bool.and_true,
        decide_eq_true_eq]
      omega
    rw [Bool.not_eq_true] at hT
    rw [hT, if_pos bW_false, if_neg (by simp)]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inr rfl) hR3.S hR3.j
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) s3).M S D n w
        { τ with j := τ.j + 1 } := ⟨(a3 rI (by simp [regL]) (by decide)).trans hR3.i,
      (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE, a2,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) := by
      simp +decide only [Lo, Prim.dst, regs, rAd, rJ]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
      (by simp +decide only [WF, Prim.dst, rAd, rJ]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; omega)
      (h := τ.j) (by omega) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨b1, by show τ.j + 1 ≤ τ.jE; omega, b3, b4⟩⟩, by simp only; omega⟩


/-! ## The pass -/

theorem regL_ne {c : ℕ} (hc : c ∉ regL) : ∀ r ∈ regL, c ≠ r := fun _ hr he => hc (he ▸ hr)

/-- A write to a counter outside `regL` and below `regs` keeps the relation. -/
theorem Rel.set {S D n w : ℕ} {src : ℕ → Word} {M : Mem} {σ : MS} (h : Rel S D n w src M σ)
    {c : ℕ} (hc : c ∉ regL) (hc4 : 4 ≤ c) (hcr : c < regs) (hS : regs ≤ S) (hD : regs ≤ D)
    (v : Word) : Rel S D n w src (M.setIfInBounds c v) σ where
  inv := inv_of_frame h.inv (size_set ..) fun i hi => rd_set_ne (by omega)
  rg := h.rg.frame fun r hr => rd_set_ne (regL_ne hc r hr)
  hs := fun a ha => (rd_set_ne (by omega)).trans (h.hs a ha)
  hd := fun a ha => (rd_set_ne (by omega)).trans (h.hd a ha)
  bnd := h.bnd

theorem Rel.decS {S D n w : ℕ} {src : ℕ → Word} {s : St} {σ : MS}
    (h : Rel S D n w src s.M σ) (hS : regs ≤ S) (hD : regs ≤ D) :
    Rel S D n w src (decS rCS s).M σ :=
  h.set (by decide) (by decide) (by decide) hS hD _

/-- **`n − k` steps** of the pass's loop run `mrun`. -/
theorem stepLoop (I : Array Word) {S D n w : ℕ} {src : ℕ → Word} :
    ∀ (m : ℕ) (s : St) (σ : MS), Lay S D n w s.M.size → Rel S D n w src s.M σ → σ.k + m = n →
      Rel S D n w src (iterL (semXIR I stepIR) rCS m s).M (mrun (keyLt I) src n w m σ)
  | 0, _, _, _, hR, _ => hR
  | m + 1, s, σ, hL, hR, hm => by
    obtain ⟨h1, h2⟩ := stepIR_sem I s hL hR (by omega)
    simp only [iterL, mrun]
    exact stepLoop I m _ _ (by rw [size_decS, size_sem]; exact hL) (h1.decS hL.rS hL.rD)
      (by rw [h2]; omega)

/-! ## The sort: 64 passes -/

theorem iterL_succ' (f : St → St) (c : ℕ) :
    ∀ (k : ℕ) (s : St), iterL f c (k + 1) s = decS c (f (iterL f c k s))
  | 0, _ => rfl
  | k + 1, s => iterL_succ' f c k (decS c (f s))

theorem wseq_le (n : ℕ) : ∀ p, wseq n p ≤ n + 1
  | 0 => by simp [wseq]
  | p + 1 => by simp only [wseq]; omega

theorem wseq_pos {n : ℕ} (hn : 0 < n) (p : ℕ) : 0 < wseq n p := by
  rw [wseq_eq hn]; exact lt_min (Nat.two_pow_pos p) hn

/-- The count of the sort's loop. -/
theorem entryK64 {M : Mem} (hM : Inv M) (hN : rd M rNP = 64) :
    rd (entryK rCP rNP 64 M) rCP = 64 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds rCP 64) rNP = 64 := by rw [rd_set_ne (by decide), hN]
  have h2 : rd (M.setIfInBounds rCP 64) rCP = 64 := rd_set_self (by simp only [rCP]; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp]; omega)]
  rw [if_pos (by decide), rd_set_ne (by decide), h2]

/-! ## The log index after walk and sort -/

theorem entryOff_lt (L : Log) {a b : ℕ} (h : a < b) (hb : b ≤ L.length) :
    entryOff L a < entryOff L b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [entryOff_succ L (by omega)]
    have : 5 ≤ qWords L[b] := Nat.le_add_right _ _
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · have := ih h' (by omega); omega
    · subst h'; omega

/-! ## The sort and the index at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters; lvm's instance is
`bX = memX`, `pL = posL pz`. -/

section Idx

variable (bX pL : ℕ)

/-- Before a pass: empty runs, output index `0`, the step count `|L|`. -/
def passPre4 : XIR :=
  .seq (.blk [.const rI 0, .const rIE 0, .const rJ 0, .const rJE 0, .const rKk 0])
    (readAt rNS pL)


/-- **One merge pass.** -/
def passIR4 : XIR := .seq (.seq (passPre4 pL) (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR)) (.blk swapPs)


/-- Before the sort: `n`, `w = 1`, the bases, the pass count. -/
def sortPre4 : XIR :=
  .seq (readAt rN pL) (.blk [.const rW2 1, .const rSrc (BitVec.ofNat 64 bX),
    .op .add rDst rSrc rN, .const rNP 64])


/-- **The sort**: 64 passes. -/
def sortIR4 : XIR := .seq (sortPre4 bX pL) (.loopK rCP rNP 64 (passIR4 pL))


/-- Walk and sort. -/
def idxIR4 : XIR := .seq (walkIR4 bX pL) (sortIR4 bX pL)


/-- The source base of pass `p`: `X` on even passes, `Y = X + n` on odd ones. -/
def baseX4 (n p : ℕ) : ℕ := if p % 2 = 0 then bX else bX + n


theorem baseX4_ctl (n : ℕ) : baseX4 bX n 0 = bX ∧ baseX4 bX n 1 = bX + n := ⟨rfl, rfl⟩


theorem baseX4_two (n p : ℕ) : baseX4 bX n (p + 1 + 1) = baseX4 bX n p := by
  unfold baseX4
  by_cases h : p % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]


theorem wf_idxIR4 : WF (idxIR4 bX pL) := by
  simp +decide [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, WF, Writes, Prim.dst, rA, rN, rP,
    rXA, rQL, rT1, rT2, rKc, rCW, rW2, rSrc, rDst, rI, rIE, rJ, rJE, rKk, rAd, rX, rY, rPa, rPb, rKa,
    rKb, rF, rG, rH, rCP, rNP, rCS, rNS, rV, regs, cTmp, cOne]


/-- The index's cost (3.x's `cost_logIR`: the constants do not change it). -/
theorem cost_idxIR4 (t : ℕ) : cost (idxIR4 bX pL) t = 2592 + t / 5 * 11871 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, cost, blkSteps,
    List.length_cons, List.length_nil, List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  omega


theorem sizeIR_idxIR4 : sizeIR (idxIR4 bX pL) ≤ 2 ^ 19 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num


theorem outs_idxIR4 (t : ℕ) : outs (idxIR4 bX pL) t = 0 := by
  simp [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, readAt, outs]


/-- **The index's loop bounds**, on a tape whose word `pL < 2^64` is a count of at most `t / 5`
(3.x's `safe_logIR`). -/
theorem safe_idxIR4 {I : Array Word} {t : ℕ} (hp : pL < 2 ^ 64) (h : (I.getD pL 0).toNat ≤ t / 5) :
    Safe I t (idxIR4 bX pL) := by
  unfold idxIR4 walkIR4 sortIR4 passIR4
  have hcnt : ∀ (p : XIR) (d : ℕ), WF p → d < regs → ∀ s : St, Inv s.M →
      (rd (semXIR I (.seq p (readAt d pL)) s).M d).toNat ≤ Aff.eval ⟨0, 1, 5⟩ t :=
    fun p d hP hd s hM => by
      rw [rd_seq_readAt I p s hP hM hd hp]
      simpa [Aff.eval] using h
  refine .seq (.loopT (safe_of_noLoopT (by simp [walkPre4, readAt, NoLoopT]))
    (hcnt _ rN (by simp +decide [WF, Prim.dst, rP, rXA]) (by simp [rN, regs]))
    (safe_of_noLoopT (by simp [walkBody, NoLoopT]))) (.seq (safe_of_noLoopT (by
      simp [sortPre4, readAt, NoLoopT])) (.loopK (.seq (.loopT (safe_of_noLoopT (by
      simp [passPre4, readAt, NoLoopT])) (hcnt _ rNS (by simp +decide only [WF, Prim.dst, rI, rIE,
        rJ, rJE, rKk])
      (by simp [rNS, regs])) (safe_of_noLoopT (by
        simp [stepIR, blockIR, cmpIR, cmpWord, aposIR, NoLoopT]))) (.blk _))))


variable {bX pL} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One pass**: the destination holds `passF` of the source; the bases swap and
`w := min(2w, n)`. -/
theorem passIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ}
    (hL : Lay S D n w s.M.size) (hn : I.getD pL 0 = toWord n)
    (hS : rd s.M rSrc = toWord S) (hD : rd s.M rDst = toWord D) (hW : rd s.M rW2 = toWord w)
    (hN : rd s.M rN = toWord n) :
    Inv (semXIR I (passIR4 pL) s).M ∧ rd (semXIR I (passIR4 pL) s).M rSrc = toWord D ∧
    rd (semXIR I (passIR4 pL) s).M rDst = toWord S ∧
    rd (semXIR I (passIR4 pL) s).M rW2 = toWord (min (2 * w) n) ∧ rd (semXIR I (passIR4 pL) s).M rN = toWord n ∧
    ∀ a < n, rd (semXIR I (passIR4 pL) s).M (D + a) =
      passF (keyLt I) (fun a => rd s.M (S + a)) n w (fun a => rd s.M (D + a)) a := by
  have hs := hM.1
  have Lbn := hL.bn
  have Lbw := hL.bw
  simp only [regs] at hs
  have hP0 : WF (passPre4 pL) := by simp +decide [passPre4, readAt, WF, Prim.dst, rI, rIE, rJ, rJE,
    rKk, rNS, rA, and_true]
  have hlo0 : Lo (passPre4 pL) := by
    simp +decide [Lo, passPre4, readAt, Prim.dst, regs, rI, rIE, rJ, rJE, rKk, rNS, rA,
      and_true]
  have hcnt : rd (semXIR I (passPre4 pL) s).M rNS = toWord n := by
    rw [passPre4, rd_seq_readAt I _ s (by simp +decide only [WF, Prim.dst, rI, rIE, rJ, rJE, rKk]) hM
      (by decide) (by omega), hn]
  have hR0 : Regs (semXIR I (passPre4 pL) s).M S D n w ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [passPre4, readAt, semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rI, rIE, rJ, rJE, rKk, rNS, rA]; omega))
      only [rd_set_self, rd_set_ne] <;>
    first | exact hW | exact hN | exact hS | exact hD | rfl
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I (passPre4 pL) s
  rw [passIR4, semXIR_seq, semXIR_seq]
  generalize semXIR I (passPre4 pL) s = s0 at hcnt hR0 hM0 hH0 hz0
  have hs0 := hM0.1
  simp only [regs] at hs0
  have e : semXIR I (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR) s0 =
      iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ := by
    simp only [semXIR, rd_entryT (show rCS < s0.M.size by simp only [rCS]; omega), hcnt,
      toNat_toWord (show n < 2 ^ 64 by omega)]
  rw [e]
  have hRel : Rel S D n w (fun a => rd s.M (S + a)) (entryT rCS rNS s0.M)
      ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ :=
    Rel.set (M := s0.M) ⟨hM0, hR0, fun a ha => hH0 _ (le_trans hL.rS (by omega)),
      fun a ha => hH0 _ (le_trans hL.rD (by omega)), by simp [Bnd]⟩ (by decide) (by decide)
      (by decide) hL.rS hL.rD _
  have h1 := stepLoop I n ⟨entryT rCS rNS s0.M, s0.o⟩ _ (by rw [size_entryT, hz0]; exact hL) hRel
    (by simp)
  generalize iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ = s1 at h1
  obtain ⟨hM1, hR1, -, hd1, -⟩ := h1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have hlo : Lo (.blk swapPs) := by
    simp +decide only [Lo, swapPs, minPs, Prim.dst, regs, rV, rSrc, rDst, rW2, rT1, rT2, rKc]
  refine ⟨inv_sem I (by simp +decide only [WF, swapPs, minPs, Prim.dst, rV, rSrc, rDst, rW2, rT1,
    rT2, rKc])
    hM1, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  rotate_left 4
  · rw [hframe I _ s1 hlo _ (le_trans hL.rD (by omega)), hd1 a ha]; rfl
  all_goals
    simp only [swapPs, minPs, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run]
    simp (disch := first | decide | (simp only [size_set, rV, rSrc, rDst, rW2, rT1, rT2, rKc]; omega))
      only [rd_set_self, rd_set_ne]
    simp only [hR1.S, hR1.D, hR1.w, hR1.n, or_self_eval, add_toWord]
  rw [minP_toWord (by omega) (by omega), two_mul]


/-- **The sort's semantics**: on a heap whose `X[0..n)` holds distinct words, `sortIR4` leaves in
`X[0..n)` exactly those words, strictly sorted by `keyLt`. -/
theorem sortIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ}
    (hn : I.getD pL 0 = toWord n) (hn2 : n < 2 ^ 62) (hsz : bX + n + n ≤ s.M.size)
    (hinj : ∀ a b, a < n → b < n → rd s.M (bX + a) = rd s.M (bX + b) → a = b) :
    (∀ a b, a < b → b < n →
      keyLt I (rd (semXIR I (sortIR4 bX pL) s).M (bX + a)) (rd (semXIR I (sortIR4 bX pL) s).M (bX + b)) = true) ∧
    (∀ a < n, ∃ c < n, rd (semXIR I (sortIR4 bX pL) s).M (bX + a) = rd s.M (bX + c)) ∧
    (∀ c < n, ∃ a < n, rd (semXIR I (sortIR4 bX pL) s).M (bX + a) = rd s.M (bX + c)) := by
  have hs := hM.1
  simp only [regs] at hs
  have hP0 : WF (sortPre4 bX pL) := by simp +decide [sortPre4, readAt, WF, Prim.dst, rN, rA, rW2, rSrc,
    rDst, rNP, and_true]
  have hlo0 : Lo (sortPre4 bX pL) := by
    simp +decide [Lo, sortPre4, readAt, Prim.dst, regs, rN, rA, rW2, rSrc, rDst, rNP, and_true]
  -- the registers after `(sortPre4 bX pL)`
  have h0 : rd (semXIR I (sortPre4 bX pL) s).M rN = toWord n ∧ rd (semXIR I (sortPre4 bX pL) s).M rW2 = toWord 1 ∧
      rd (semXIR I (sortPre4 bX pL) s).M rSrc = toWord bX ∧
      rd (semXIR I (sortPre4 bX pL) s).M rDst = toWord (bX + n) ∧ rd (semXIR I (sortPre4 bX pL) s).M rNP = 64 := by
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by omega)
    have hM' := inv_sem I (P := readAt rN pL) (by simp +decide [readAt, WF, Prim.dst, rN, rA,
      and_true]) hM
    rw [hn] at hN
    rw [sortPre4, semXIR_seq]
    generalize semXIR I (readAt rN pL) s = s' at hN hM'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rN, rW2, rSrc, rDst, rNP]; omega)) only
      [rd_set_self, rd_set_ne]
    · exact hN
    · rfl
    · rfl
    · rw [hN]; exact add_toWord _ _
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I (sortPre4 bX pL) s
  rw [sortIR4, semXIR_seq]
  generalize semXIR I (sortPre4 bX pL) s = s0 at h0 hM0 hH0 hz0
  obtain ⟨n0, w0, S0, D0, P0⟩ := h0
  have e : semXIR I (.loopK rCP rNP 64 (passIR4 pL)) s0 =
      iterL (semXIR I (passIR4 pL)) rCP 64 ⟨entryK rCP rNP 64 s0.M, s0.o⟩ := by
    simp only [semXIR, entryK64 hM0 P0]
    rfl
  rw [e]
  have hE : ∀ i, i ≠ rCP → i ≠ cTmp → rd (entryK rCP rNP 64 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME : Inv (entryK rCP rNP 64 s0.M) := inv_of_frame hM0 (size_entryK ..)
    fun i hi => hE i (by simp only [rCP]; omega) (by simp only [cTmp]; omega)
  generalize hS0 : (⟨entryK rCP rNP 64 s0.M, s0.o⟩ : St) = T at hE hME
  -- the pass invariant
  have hLay : ∀ p, Lay (baseX4 bX n p) (baseX4 bX n (p + 1)) n (wseq n p) s.M.size := fun p => by
    have := wseq_le n p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, this, wseq_pos (p := p)⟩ <;>
      unfold baseX4 <;> simp only [regs] at hbX ⊢ <;> split_ifs <;> omega
  have hPI : ∀ p, Inv (iterL (semXIR I (passIR4 pL)) rCP p T).M ∧
      (iterL (semXIR I (passIR4 pL)) rCP p T).M.size = s.M.size ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rSrc = toWord (baseX4 bX n p) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rDst = toWord (baseX4 bX n (p + 1)) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rW2 = toWord (wseq n p) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rN = toWord n := by
    intro p
    induction p with
    | zero =>
      simp only [iterL]
      rw [← hS0]
      refine ⟨hME, by rw [size_entryK, hz0], ?_, ?_, ?_, ?_⟩
      · rw [hE _ (by decide) (by decide), S0]; simp only [baseX4, Nat.zero_mod, if_true]
      · rw [hE _ (by decide) (by decide), D0]; simp only [baseX4]; rfl
      · rw [hE _ (by decide) (by decide), w0]; rfl
      · rw [hE _ (by decide) (by decide), n0]
    | succ p ih =>
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
      obtain ⟨j1, j2, j3, j4, j5, -⟩ := passIR4_sem hbX hbX2 hpL I _ i1 (by rw [i2]; exact hLay p) hn i3 i4 i5 i6
      rw [iterL_succ']
      refine ⟨inv_of_frame j1 (size_decS ..) fun i hi => rd_decS (by simp only [rCP]; omega) _,
        by rw [size_decS, size_sem, i2], ?_, ?_, ?_, ?_⟩
      · rw [rd_decS (by decide), j2]
      · exact (rd_decS (by decide) _).trans (j3.trans (congrArg toWord (baseX4_two bX n p).symm))
      · exact (rd_decS (by decide) _).trans (j4.trans (by simp only [wseq]))
      · rw [rd_decS (by decide), j5]
  have hX : ∀ p, ∀ a < n, rd (iterL (semXIR I (passIR4 pL)) rCP (p + 1) T).M (baseX4 bX n (p + 1) + a) =
      passF (keyLt I) (fun a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n p + a)) n (wseq n p)
        (fun a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n (p + 1) + a)) a := fun p a ha => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hPI p
    have hL := hLay p
    rw [← i2] at hL
    rw [iterL_succ', rd_decS (by have := hL.rD; simp only [regs, rCP] at *; omega)]
    exact (passIR4_sem hbX hbX2 hpL I _ i1 hL hn i3 i4 i5 i6).2.2.2.2.2 a ha
  have hX0 : ∀ a < n, rd (iterL (semXIR I (passIR4 pL)) rCP 0 T).M (baseX4 bX n 0 + a) = rd s.M (bX + a) :=
    fun a ha => by
      simp only [iterL, baseX4, Nat.zero_mod, if_true]
      rw [← hS0, hE _ (by simp only [rCP, regs] at hbX ⊢; omega) (by simp only [cTmp, regs] at hbX ⊢; omega),
        hH0 _ (by simp only [regs] at hbX ⊢; omega)]
  obtain ⟨r1, r2, r3⟩ := passes_ok (keyLt_order I) (by omega)
    (fun p a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n p + a))
    (fun p a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n (p + 1) + a)) hX
    (fun a b ha hb h => hinj a b ha hb (by rwa [hX0 a ha, hX0 b hb] at h))
  have hB64 : baseX4 bX n 64 = bX := if_pos (by decide)
  simp only [hB64] at r1 r2 r3
  refine ⟨r1, fun a ha => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc, e⟩ := r2 a ha
    exact ⟨c, hc, by rw [e, hX0 c hc]⟩
  · obtain ⟨a, ha, e⟩ := r3 c hc
    exact ⟨a, ha, by rw [e, hX0 c hc]⟩


/-- **The log index** (`index_spec`, sort half): after `(idxIR4 bX pL)` (walk and sort) on a domain tape of a SNARK proof,
`X[0..|L|)` holds exactly the tape positions of the log's entries, strictly sorted by the key
(answer, position). -/
theorem idxIR4_sorted (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size) :
    (∀ a b, a < b → b < L.length →
      keyLt (extractorInput c π L).toArray
        (rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
        (rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + b)) = true) ∧
    (∀ a < L.length, ∃ k < L.length, rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M
      (bX + a) = toWord (pL + 1 + entryOff L k)) ∧
    (∀ k < L.length, ∃ a < L.length, rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M
      (bX + a) = toWord (pL + 1 + entryOff L k)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  have hW := fun {k : ℕ} (hk : k < L.length) => walk_spec4 hbX hbX2 hpL c π L hs hq ht s hM (by omega) hk
  have hwf : WF (walkIR4 bX pL) := wf_walkIR4 bX pL
  rw [idxIR4, semXIR_seq]
  obtain ⟨r1, r2, r3⟩ := sortIR4_sem hbX hbX2 hpL I (semXIR I (walkIR4 bX pL) s) (inv_sem I hwf hM) (n := L.length)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by omega) (by rw [size_sem]; exact hsz)
    (fun a b ha hb h => by
      rw [hW ha, hW hb] at h
      have hab := congrArg BitVec.toNat h
      have ea : entryOff L a < entryOff L L.length := entryOff_lt L ha le_rfl
      have eb : entryOff L b < entryOff L L.length := entryOff_lt L hb le_rfl
      rw [toNat_toWord (by omega), toNat_toWord (by omega)] at hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · have := entryOff_lt L h' hb.le; omega
      · have := entryOff_lt L h' ha.le; omega)
  refine ⟨r1, fun a ha => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, e⟩ := r2 a ha
    exact ⟨k, hk, e.trans (hW hk)⟩
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, e.trans (hW hk)⟩



end Idx

/-- **The log index at lvm's instance** (`bX = memX`, `pL = posL pz`) meets the SNARK branch's
obligations (FR's `decOk_logIR`). -/
theorem decOk_idx {pz : ℕ} (hpz : pz < 2 ^ 64) : DecOk pz (idxIR4 memX (posL pz)) where
  pz_lt := hpz
  wf := wf_idxIR4 _ _
  safe := fun c π L hs _ ht => safe_idxIR4 _ _ (by unfold posL; omega)
    (tape_count_le4 c π L (hs_posL hs) ht)
  cost := fun t => by
    rw [cost_idxIR4]; simp only [decBudget, fuelBase, fuelPerWord]; omega
  outs := fun t => by rw [outs_idxIR4]; exact Nat.zero_le _
  size := sizeIR_idxIR4 _ _

end Lvm.X

end LvmXSortSim
