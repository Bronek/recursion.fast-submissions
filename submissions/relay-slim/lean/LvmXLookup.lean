-- Ported from `flock-recursive` `FRXLookup.lean` (rf-k kk/base 8bff272b) for lvm (WP-3): namespace
-- `Lvm.X`; `ansIdx` (FR's `FRLog`) is defined here, FR's 3.x instances at `posL`/`piSize` are dropped.
import LvmXSort

/-!
# The lookup: the first entry with a given answer

* `tape_answer`, `ansW_entry`: the four answer words of entry `k` on the tape are
  `packBytes L[k].2`; the sort key of entry `k` is its answer then its position.
* `bsStep`/`bsRun`: the pure lower-bound search; `bsRun_spec`: on a predicate that holds on a
  prefix of `[0, n)`, 64 halvings from `(0, n)` end at the prefix's length.
* `lookIR_sem` (the machine runs `bsRun` and sets the found flag) and `idx_lookup`
  (`lookup_spec`: after `idxIR4`, any target's lookup finds its first preimage, `ansIdx`).

**Parameters.** The lookup takes the index base `bX` and the tape word `pL` of `|L|`
(`lookIR4`, `Sorted4`, `posE4`, `idx_lookup4`); lvm's instance is `memX`, `posL pz`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The first entry with an answer (FR's `ansIdx`) -/

/-- The index of the first log entry whose answer is `st`. -/
def ansIdx (L : Log) (st : Digest) : Option ℕ := L.findIdx? fun e => decide (e.2 = st)

theorem ansIdx_lt {L : Log} {st : Digest} {i : ℕ} (h : ansIdx L st = some i) :
    ∃ hi : i < L.length, L[i].2 = st := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa using hp⟩

/-! ## The answers on the tape -/

/-- The answer words of an entry within the log's words. -/
theorem entries_getD_ans : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (m : ℕ), m < 4 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) 0 = (packBytes L[k].2.toList).getD m 0
  | e :: L, 0, _, m, hm => by
    have hb : (bytesWords e.1.data.toList).length = 1 + (e.1.size + 7) / 8 := by
      simp only [bytesWords, List.length_cons, packBytes_length, Array.length_toList]
      have : e.1.data.size = e.1.size := rfl
      omega
    have hp := packBytes_digest_length e.2
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      List.getElem_cons_zero, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD, hb]
    congr 1
    omega
  | e :: L, k + 1, hk, m, hm => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := entries_getD_ans L k (by simp at hk; omega) m hm
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; omega), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    omega

/-- The four answer words of the entry at tape position `x`. -/
def ansW (I : Array Word) (x : Word) : List Word :=
  [I.getD (aposW I x + 0).toNat 0, I.getD (aposW I x + 1).toNat 0,
   I.getD (aposW I x + 2).toNat 0, I.getD (aposW I x + 3).toNat 0]

theorem keyW_eq (I : Array Word) (x : Word) : keyW I x = ansW I x ++ [x] := rfl

theorem ansW_length (I : Array Word) (x : Word) : (ansW I x).length = 4 := rfl

/-- `packBytes` is injective on digests. -/
theorem packBytes_digest_inj {d d' : Digest} (h : packBytes d.toList = packBytes d'.toList) :
    d = d' := by
  have h1 := readDigest_packBytes d []
  rw [h, readDigest_packBytes d' []] at h1
  simpa using h1.symm

/-! ## Lexicographic order on keys -/

theorem lexW_append : ∀ (a b : List Word), a.length = b.length → ∀ x y : Word,
    lexW (a ++ [x]) (b ++ [y]) = (lexW a b || (decide (a = b) && decide (x < y)))
  | [], [], _, x, y => by simp [lexW]
  | a :: as, b :: bs, hl, x, y => by
    have ih := lexW_append as bs (by simpa using hl) x y
    simp only [List.cons_append, lexW, ih, List.cons.injEq]
    by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-! ## The pure lower-bound search -/

/-- One halving of `[lo, lo + len)`. -/
def bsStep (p : ℕ → Bool) (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.2 = 0 then st
  else if p (st.1 + st.2 / 2) then (st.1 + st.2 / 2 + 1, st.2 - st.2 / 2 - 1)
  else (st.1, st.2 / 2)

/-- `m` halvings. -/
def bsRun (p : ℕ → Bool) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, st => st
  | m + 1, st => bsRun p m (bsStep p st)

/-- The search's invariant: `p` holds below `lo`, fails on `[lo + len, n)`. -/
def BsInv (p : ℕ → Bool) (n : ℕ) (st : ℕ × ℕ) : Prop :=
  st.1 + st.2 ≤ n ∧ (∀ a < st.1, p a = true) ∧ ∀ a, st.1 + st.2 ≤ a → a < n → p a = false

theorem bsStep_inv {p : ℕ → Bool} {n : ℕ}
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) {st : ℕ × ℕ} (h : BsInv p n st) :
    BsInv p n (bsStep p st) ∧ (bsStep p st).2 ≤ st.2 / 2 := by
  obtain ⟨lo, len⟩ := st
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  unfold bsStep
  by_cases h0 : len = 0
  · simp only [h0, if_true]; exact ⟨⟨by simpa [h0] using h1, h2, by simpa [h0] using h3⟩, by simp⟩
  rw [if_neg h0]
  by_cases hm : p (lo + len / 2) = true
  · rw [if_pos hm]
    refine ⟨⟨by simp only; omega, fun a ha => ?_, fun a ha han => h3 a (by simp only at ha; omega) han⟩,
      by simp only; omega⟩
    simp only at ha
    rcases Nat.lt_or_ge a lo with h | h
    · exact h2 a h
    · rcases Nat.lt_or_ge a (lo + len / 2) with h' | h'
      · exact hp a _ h' (by omega) hm
      · rw [show a = lo + len / 2 by omega]; exact hm
  · rw [if_neg hm]
    refine ⟨⟨by simp only; omega, h2, fun a ha han => ?_⟩, by simp only; omega⟩
    simp only at ha
    rcases Nat.lt_or_ge a (lo + len) with h | h
    · cases e : p a
      · rfl
      · rcases Nat.lt_or_ge (lo + len / 2) a with h' | h'
        · exact absurd (hp _ a h' han e) hm
        · exact absurd (show p (lo + len / 2) = true by rw [show lo + len / 2 = a by omega]; exact e)
            hm
    · exact h3 a h han

theorem bsRun_inv {p : ℕ → Bool} {n : ℕ}
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) :
    ∀ (m : ℕ) (st : ℕ × ℕ), BsInv p n st → BsInv p n (bsRun p m st) ∧
      (bsRun p m st).2 ≤ st.2 / 2 ^ m
  | 0, st, h => ⟨h, by simp [bsRun]⟩
  | m + 1, st, h => by
    obtain ⟨h1, h2⟩ := bsStep_inv hp h
    obtain ⟨h3, h4⟩ := bsRun_inv hp m _ h1
    refine ⟨h3, h4.trans ?_⟩
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right h2

/-- **The lower bound**: 64 halvings from `(0, n)` end at `lo` with `p` true below and false on
`[lo, n)`. -/
theorem bsRun_spec {p : ℕ → Bool} {n : ℕ} (hn : n < 2 ^ 64)
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) :
    (bsRun p 64 (0, n)).1 ≤ n ∧ (∀ a < (bsRun p 64 (0, n)).1, p a = true) ∧
      ∀ a, (bsRun p 64 (0, n)).1 ≤ a → a < n → p a = false := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := bsRun_inv hp 64 (0, n)
    ⟨by simp, fun a ha => absurd ha (Nat.not_lt_zero _), fun a ha han => by simp at ha; omega⟩
  have h0 : (bsRun p 64 (0, n)).2 = 0 := by
    have : n / 2 ^ 64 = 0 := Nat.div_eq_of_lt hn
    simp only at h4; omega
  rw [h0, Nat.add_zero] at h1 h3
  exact ⟨h1, h2, h3⟩


/-- Controls for the search: on a prefix predicate it finds the prefix's end; on a predicate that
is not a prefix (true only at `7`) it misses, so `bsRun_spec`'s monotonicity hypothesis is
needed. -/
theorem bsRun_ctl : (bsRun (fun a => decide (a < 3)) 64 (0, 10)).1 = 3 ∧
    (bsRun (fun a => decide (a = 7)) 64 (0, 10)).1 = 0 := by decide +kernel

/-! ## The first preimage in the sorted index -/

theorem lexW_asymm {A B : List Word} (h : lexW A B = true) : lexW B A = false := by
  cases e : lexW B A
  · rfl
  · have := lexW_trans _ _ _ h e
    rw [lexW_irrefl] at this
    exact absurd this (by decide)

/-- The search predicate: the answer at slot `a` is below the target words `T`. -/
def ltT (I : Array Word) (X : ℕ → Word) (T : List Word) (a : ℕ) : Bool := lexW (ansW I (X a)) T

/-! ## The machine: word helpers and the search registers -/

theorem shr_one_toWord {a : ℕ} (ha : a < 2 ^ 64) : XOp.shr.eval (toWord a) 1 = toWord (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_ushiftRight, toNat_toWord ha, toNat_toWord (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

theorem sub_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    XOp.sub.eval (toWord a) (toWord b) = toWord (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_sub, toNat_toWord ha, toNat_toWord (by omega), toNat_toWord (by omega)]
  omega

theorem eq_bW (a b : Word) : XOp.eq.eval a b = bW (decide (a = b)) := by
  by_cases h : a = b <;> simp [XOp.eval, bW, h]

/-- The answer words as the machine reads them. -/
theorem ansW_getD (I : Array Word) (x : Word) {w : ℕ} (hw : w < 4) :
    I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 = (ansW I x).getD w 0 := by
  interval_cases w <;> rfl

theorem ansW_eq (I : Array Word) (x : Word) : ansW I x =
    [(ansW I x).getD 0 0, (ansW I x).getD 1 0, (ansW I x).getD 2 0, (ansW I x).getD 3 0] := rfl

/-- The search's registers. -/
def srL : List ℕ := [rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3]

/-- The registers hold the search state `(lo, len)`, the count `n` and the target `T`. -/
structure SRegs (M : Mem) (n lo len : ℕ) (T : List Word) : Prop where
  lo : rd M rLo = toWord lo
  len : rd M rLn = toWord len
  n : rd M rN = toWord n
  q : [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = T

theorem srL_lt : ∀ r ∈ srL, r < regs := by decide

theorem SRegs.sem {I : Array Word} {P : XIR} {s : St} {n lo len : ℕ} {T : List Word}
    (h : SRegs s.M n lo len T) (hM : Inv s.M) (hP : WF P) (hw : ∀ r ∈ srL, ¬ Writes P r) :
    SRegs (semXIR I P s).M n lo len T := by
  have hf := fun r hr => Lvm.X.frame I P s hP hM r (srL_lt r hr) (hw r hr)
  exact ⟨(hf rLo (by simp [srL])).trans h.lo, (hf rLn (by simp [srL])).trans h.len,
    (hf rN (by simp [srL])).trans h.n, by
      rw [hf rQ0 (by simp [srL]), hf rQ1 (by simp [srL]), hf rQ2 (by simp [srL]),
        hf rQ3 (by simp [srL])]; exact h.q⟩

/-! ## `ansLtIR` and `eqTWord` -/

theorem cmpTWord_sem (I : Array Word) (s : St) (hM : Inv s.M) {w r : ℕ} (hw : w < 4)
    (hr : r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) :
    rd (semXIR I (cmpTWord w r) s).M rF =
      XOp.or.eval (XOp.ltu.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r))
        (XOp.and.eval (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r))
          (rd s.M rF)) := by
  have hs := hM.1
  simp only [regs] at hs
  rcases hr with rfl | rfl | rfl | rfl <;>
  · simp only [cmpTWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rKa, rG, rH, rF,
      rQ0, rQ1, rQ2, rQ3]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne]
    rfl

theorem wf_cmpTWord (w r : ℕ) : WF (cmpTWord w r) := by
  simp +decide only [cmpTWord, WF, Prim.dst, rKc, rAd, rKa, rG, rH, rF, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem lo_cmpTWord (w r : ℕ) : Lo (cmpTWord w r) := by
  simp +decide only [cmpTWord, Lo, Prim.dst, regs, rKc, rAd, rKa, rG, rH, rF, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

/-- Registers `cmpTWord` keeps. -/
theorem cmpTWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w r : ℕ) {q : ℕ}
    (hq : q ∈ [rPa, rX, rHf, rMd] ++ srL) : rd (semXIR I (cmpTWord w r) s).M q = rd s.M q :=
  frame I _ s (wf_cmpTWord w r) hM q
    ((by decide : ∀ r ∈ [rPa, rX, rHf, rMd] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [cmpTWord, Writes, Prim.dst, rKc, rAd, rKa, rG, rH, rF, rPa, rX, rHf, rMd,
        rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp,
        exists_eq_left, or_false])

theorem wf_aposIR' : WF (aposIR rPa rX) := wf_aposIR (.inl rfl)

theorem aposIR_frame' (I : Array Word) (s : St) (hM : Inv s.M) {q : ℕ}
    (hq : q ∈ [rX, rHf, rMd] ++ srL) : rd (semXIR I (aposIR rPa rX) s).M q = rd s.M q :=
  frame I _ s wf_aposIR' hM q
    ((by decide : ∀ r ∈ [rX, rHf, rMd] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [aposIR, ceil8Ps, Writes, Prim.dst, rQL, rKc, rT2, rPa, rX, rHf, rMd, rLo,
        rLn, rN, rQ0, rQ1, rQ2, rQ3, or_false, List.cons_append, List.nil_append])

/-- **The answer comparison**: `rF := ansW(rX) <_lex (rQ0, …, rQ3)`. -/
theorem ansLtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I ansLtIR s).M rF = bW (lexW (ansW I (rd s.M rX))
      [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3]) := by
  set x := rd s.M rX
  have hM1 := inv_sem I wf_aposIR' hM
  have ha1 := aposIR_sem I s hM (.inl ⟨rfl, rfl⟩)
  have hq1 : ∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd (semXIR I (aposIR rPa rX) s).M q = rd s.M q :=
    fun q hq => aposIR_frame' I s hM
      ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rX, rHf, rMd] ++ srL) q hq)
  rw [ansLtIR, semXIR_seq]
  generalize semXIR I (aposIR rPa rX) s = s1 at hM1 ha1 hq1
  have hs1 := hM1.1
  simp only [regs] at hs1
  rw [semXIR_seq]
  have hwf2 : WF (.blk [.const rF 0]) := by simp +decide only [WF, Prim.dst, rF]
  have hM2 := inv_sem I hwf2 hM1
  have hf2 : rd (semXIR I (.blk [.const rF 0]) s1).M rF = bW false := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rF]; omega)]; rfl
  have hfr2 : ∀ q ∈ [rPa, rQ0, rQ1, rQ2, rQ3], rd (semXIR I (.blk [.const rF 0]) s1).M q =
      rd s1.M q := fun q hq => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne ((by decide : ∀ r ∈ [rPa, rQ0, rQ1, rQ2, rQ3], rF ≠ r) q hq)
  generalize semXIR I (.blk [.const rF 0]) s1 = s2 at hM2 hf2 hfr2
  have step : ∀ (s' : St), Inv s'.M → rd s'.M rPa = aposW I x →
      (∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd s'.M q = rd s.M q) →
      ∀ (w r : ℕ) (p : Bool), w < 4 → (r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) → rd s'.M rF = bW p →
      rd (semXIR I (cmpTWord w r) s').M rF = bW (decide ((ansW I x).getD w 0 < rd s.M r) ||
        (decide ((ansW I x).getD w 0 = rd s.M r) && p)) ∧
      Inv (semXIR I (cmpTWord w r) s').M ∧ rd (semXIR I (cmpTWord w r) s').M rPa = aposW I x ∧
      (∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd (semXIR I (cmpTWord w r) s').M q = rd s.M q) :=
    fun s' hM' ha hq w r p hw hr hf => by
      have hrq : rd s'.M r = rd s.M r := hq r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
      refine ⟨?_, inv_sem I (wf_cmpTWord w r) hM', by
        rw [cmpTWord_frame I s' hM' w r (by simp), ha], fun q hqm => by
        rw [cmpTWord_frame I s' hM' w r
          ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rPa, rX, rHf, rMd] ++ srL) q hqm), hq q hqm]⟩
      rw [cmpTWord_sem I s' hM' hw hr, ha, hf, hrq, ansW_getD I x hw, fold_bW]
  rw [semXIR_seq]
  obtain ⟨f3, m3, a3, q3⟩ := step s2 hM2 (by rw [hfr2 rPa (by simp), ha1])
    (fun q hq => by rw [hfr2 q ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rPa, rQ0, rQ1, rQ2, rQ3]) q hq),
      hq1 q hq]) 3 rQ3 _ (by decide)
    (.inr (.inr (.inr rfl))) hf2
  generalize semXIR I (cmpTWord 3 rQ3) s2 = s3 at f3 m3 a3 q3
  rw [semXIR_seq]
  obtain ⟨f2, m2, a2, q2⟩ := step s3 m3 a3 q3 2 rQ2 _ (by decide) (.inr (.inr (.inl rfl))) f3
  generalize semXIR I (cmpTWord 2 rQ2) s3 = s4 at f2 m2 a2 q2
  rw [semXIR_seq]
  obtain ⟨f1, m1, a1, q1⟩ := step s4 m2 a2 q2 1 rQ1 _ (by decide) (.inr (.inl rfl)) f2
  generalize semXIR I (cmpTWord 1 rQ1) s4 = s5 at f1 m1 a1 q1
  obtain ⟨f0, -, -, -⟩ := step s5 m1 a1 q1 0 rQ0 _ (by decide) (.inl rfl) f1
  rw [f0, ansW_eq I x]
  rfl


theorem wf_ansLtIR : WF ansLtIR := by
  simp +decide only [ansLtIR, aposIR, ceil8Ps, cmpTWord, WF, Prim.dst, rQL, rKc, rT2, rPa, rAd, rKa,
    rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem lo_ansLtIR : Lo ansLtIR := by
  simp +decide only [ansLtIR, aposIR, ceil8Ps, cmpTWord, Lo, Prim.dst, regs, rQL, rKc, rT2, rPa,
    rAd, rKa, rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem ansLtIR_frame (I : Array Word) (s : St) (hM : Inv s.M) {q : ℕ}
    (hq : q ∈ [rHf, rMd] ++ srL) : rd (semXIR I ansLtIR s).M q = rd s.M q :=
  frame I _ s wf_ansLtIR hM q ((by decide : ∀ r ∈ [rHf, rMd] ++ srL, r < regs) q hq)
    ((by simp only [srL, ansLtIR, aposIR, ceil8Ps, cmpTWord, Writes, List.cons_append,
      List.nil_append]; decide : ∀ r ∈ [rHf, rMd] ++ srL, ¬ Writes ansLtIR r) q hq)

theorem nw_ansLtIR : ∀ r ∈ srL, ¬ Writes ansLtIR r := by
  simp only [srL, ansLtIR, aposIR, ceil8Ps, cmpTWord, Writes, List.cons_append, List.nil_append]
  decide

theorem bsStep_le {p : ℕ → Bool} {n lo len : ℕ} (h : lo + len ≤ n) :
    (bsStep p (lo, len)).1 + (bsStep p (lo, len)).2 ≤ n := by
  unfold bsStep; split_ifs <;> simp only <;> omega

/-! ## The search loop and the found flag -/

theorem SRegs.decS {s : St} {n lo len : ℕ} {T : List Word} (h : SRegs s.M n lo len T) :
    SRegs (decS rCB s).M n lo len T :=
  ⟨(rd_decS (by decide) s).trans h.lo, (rd_decS (by decide) s).trans h.len,
    (rd_decS (by decide) s).trans h.n, by
      rw [rd_decS (by decide), rd_decS (by decide), rd_decS (by decide), rd_decS (by decide)]
      exact h.q⟩

theorem bsRun_le {p : ℕ → Bool} {n : ℕ} :
    ∀ (m lo len : ℕ), lo + len ≤ n → (bsRun p m (lo, len)).1 + (bsRun p m (lo, len)).2 ≤ n
  | 0, _, _, h => h
  | m + 1, lo, len, h => bsRun_le m _ _ (bsStep_le h)

theorem eqTWord_sem (I : Array Word) (s : St) (hM : Inv s.M) {w r : ℕ}
    (hr : r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) :
    rd (semXIR I (eqTWord w r) s).M rFd = XOp.and.eval (rd s.M rFd)
      (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r)) := by
  have hs := hM.1
  simp only [regs] at hs
  rcases hr with rfl | rfl | rfl | rfl <;>
  · simp only [eqTWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rKa, rH, rFd,
      rQ0, rQ1, rQ2, rQ3]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne]
    rfl

theorem wf_eqTWord (w r : ℕ) : WF (eqTWord w r) := by
  simp +decide only [eqTWord, WF, Prim.dst, rKc, rAd, rKa, rH, rFd, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem eqTWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w r : ℕ) {q : ℕ}
    (hq : q ∈ [rPa] ++ srL) : rd (semXIR I (eqTWord w r) s).M q = rd s.M q :=
  frame I _ s (wf_eqTWord w r) hM q ((by decide : ∀ r ∈ [rPa] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [eqTWord, Writes, Prim.dst, rKc, rAd, rKa, rH, rFd, rPa, rLo, rLn, rN, rQ0,
        rQ1, rQ2, rQ3, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])

theorem decide_ansW (A : List Word) (hA : A.length = 4) (t0 t1 t2 t3 : Word) (p : Bool) :
    (p && decide (A.getD 0 0 = t0) && decide (A.getD 1 0 = t1) && decide (A.getD 2 0 = t2) &&
      decide (A.getD 3 0 = t3)) = (p && decide (A = [t0, t1, t2, t3])) := by
  match A, hA with
  | [a0, a1, a2, a3], _ => simp [Bool.and_assoc]

/-! ## The lookup -/

theorem entryKB {M : Mem} (hM : Inv M) (hN : rd M rNB = 64) :
    rd (entryK rCB rNB 64 M) rCB = 64 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds rCB 64) rNB = 64 := by rw [rd_set_ne (by decide), hN]
  have h2 : rd (M.setIfInBounds rCB 64) rCB = 64 := rd_set_self (by simp only [rCB]; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp]; omega)]
  rw [if_pos (by decide), rd_set_ne (by decide), h2]

/-! ## A lookup after the log index -/

/-! ## The lookup at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters; lvm's instance is
`bX = memX`, `pL = posL pz`. -/

section Idx

variable (bX pL : ℕ)

/-- One halving step of the lower-bound search on `[lo, lo + len)`; nothing when `len = 0`. -/
def bsBody4 : XIR :=
  .ite rLn (.seq (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
      .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) (.seq (.load rX rAd)
    (.seq ansLtIR (.ite rF (.blk [.op .add rLo rMd cOne, .op .sub rLn rLn rHf,
      .op .sub rLn rLn cOne]) (.blk [.op .or rLn rHf rHf]))))) (.blk [])


/-- After the search: `rFd := lo < n ∧ answer(X[lo]) = target`. -/
def foundIR4 : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc]) (.seq (.load rX rAd)
    (.seq (aposIR rPa rX) (.seq (.blk [.op .ltu rFd rLo rN]) (.seq (eqTWord 0 rQ0)
      (.seq (eqTWord 1 rQ1) (.seq (eqTWord 2 rQ2) (eqTWord 3 rQ3)))))))


/-- **The lookup** of the target `(rQ0 … rQ3)` in the sorted `X[0..n)`: `rLo :=` the first slot
whose answer is not below the target (64 halvings), `rFd := 1` iff its answer is the target. -/
def lookIR4 : XIR :=
  .seq (.seq (readAt rN pL) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64]))
    (.seq (.loopK rCB rNB 64 (bsBody4 bX)) (foundIR4 bX))



/-- Before the search: `n` from tape word `pL`, `lo := 0`, `len := n`, the step count `64`. -/
def lookPre4 : XIR := .seq (readAt rN pL) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64])


/-- The tape position of entry `k`. -/
def posE4 (L : Log) (k : ℕ) : ℕ := pL + 1 + entryOff L k


/-- What `idxIR4_sorted` gives: `X[0..|L|)` is the set of entry positions, strictly sorted. -/
structure Sorted4 (I : Array Word) (L : Log) (X : ℕ → Word) : Prop where
  srt : ∀ a b, a < b → b < L.length → keyLt I (X a) (X b) = true
  cov : ∀ a < L.length, ∃ k < L.length, X a = toWord (posE4 pL L k)
  all : ∀ k < L.length, ∃ a < L.length, X a = toWord (posE4 pL L k)


theorem lookIR4_eq : (lookIR4 bX pL) = .seq (lookPre4 pL) (.seq (.loopK rCB rNB 64 (bsBody4 bX)) (foundIR4 bX)) := rfl


variable {bX pL} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

omit hbX hbX2 hpL in
/-- **The tape at entry `k`'s answer**: word `m < 4` of `packBytes L[k].2`. -/
theorem tape_answer4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) {k : ℕ}
    (hk : k < L.length) {m : ℕ} (hm : m < 4) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) 0 =
      (packBytes L[k].2.toList).getD m 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, show pL + 1 + entryOff L k + 1 +
      (L[k].1.size + 7) / 8 + m = (pL + 1) + (entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) by
      omega, ← hl, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]
  exact entries_getD_ans L k hk m hm


omit hbX hbX2 hpL in
/-- **The answer read at entry `k`'s position is `packBytes L[k].2`.** -/
theorem ansW_entry4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : ℕ}
    (hk : k < L.length) :
    ansW (extractorInput c π L).toArray (toWord (posE4 pL L k)) = packBytes L[k].2.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have hq' := hq _ (List.getElem_mem hk)
  have hk1 : entryOff L (k + 1) ≤ entryOff L L.length := by
    rcases Nat.lt_or_ge (k + 1) L.length with h | h
    · exact (entryOff_lt L h le_rfl).le
    · rw [show k + 1 = L.length by omega]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have hx : (toWord (posE4 pL L k)).toNat = posE4 pL L k := toNat_toWord (by simp only [posE4]; omega)
  have hap : ∀ j < 4, (aposW I (toWord (posE4 pL L k)) + toWord j).toNat =
      pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + j := fun j hj => by
    have h1 : I.getD (posE4 pL L k) 0 = toWord L[k].1.size := by
      rw [hI, getD_toArray]; exact tape_entry4 c π L hs hk
    simp only [aposW, hx, h1]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_ceil8 hq', hx,
      toNat_toWord (show j < 2 ^ 64 by omega), show (1 : Word).toNat = 1 from rfl]
    simp only [posE4] at hx ⊢
    omega
  apply List.ext_getElem (by simp [ansW_length, packBytes_digest_length])
  intro m h1 h2
  have hm : m < 4 := h1
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, ← tape_answer4 c π L hs hk hm,
    ← getD_toArray (extractorInput c π L), ← hI]
  interval_cases m
  · exact congrArg (fun i => I.getD i 0) (hap 0 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 1 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 2 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 3 (by decide))


omit hbX hbX2 hpL in
theorem posE_lt4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : ℕ} (hk : k < L.length) :
    posE4 pL L k < 2 ^ 64 := by
  have := tape_entries_end4 c π L hs
  have := entryOff_lt L hk le_rfl
  simp only [posE4]; omega


omit hbX hbX2 hpL in
/-- **The first preimage is the search's boundary.** On the sorted index, the predicate "the
answer is below `packBytes t`" holds on a prefix; at the prefix's end `b` sits the first entry
of `L` whose answer is `t` (`ansIdx`), and if there is none, no slot has answer `t`. -/
theorem lookup_pure4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    {X : ℕ → Word} (hX : Sorted4 pL (extractorInput c π L).toArray L X) (t : Digest) :
    (∀ a b, a < b → b < L.length →
      ltT (extractorInput c π L).toArray X (packBytes t.toList) b = true →
      ltT (extractorInput c π L).toArray X (packBytes t.toList) a = true) ∧
    ∀ b ≤ L.length,
      (∀ a < b, ltT (extractorInput c π L).toArray X (packBytes t.toList) a = true) →
      (∀ a, b ≤ a → a < L.length →
        ltT (extractorInput c π L).toArray X (packBytes t.toList) a = false) →
      (∀ k, ansIdx L t = some k → b < L.length ∧ X b = toWord (posE4 pL L k)) ∧
      (ansIdx L t = none → ∀ a < L.length,
        ansW (extractorInput c π L).toArray (X a) ≠ packBytes t.toList) := by
  set I := (extractorInput c π L).toArray with hI
  set T := packBytes t.toList with hT
  have hA : ∀ a < L.length, ∃ k, ∃ hk : k < L.length, X a = toWord (posE4 pL L k) ∧
      ansW I (X a) = packBytes L[k].2.toList := fun a ha => by
    obtain ⟨k, hk, e⟩ := hX.cov a ha
    exact ⟨k, hk, e, by rw [e]; exact ansW_entry4 c π L hs hq ht hk⟩
  -- the key order splits into the answer order and, on equal answers, the position order
  have hkey : ∀ a b, a < b → b < L.length → lexW (ansW I (X a)) (ansW I (X b)) = true ∨
      (ansW I (X a) = ansW I (X b) ∧ X a < X b) := fun a b hab hb => by
    have := hX.srt a b hab hb
    rw [keyLt, keyW_eq, keyW_eq, lexW_append (ansW I (X a)) (ansW I (X b))
      (by rw [ansW_length, ansW_length])] at this
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hmono : ∀ a b, a < b → b < L.length → ltT I X T b = true → ltT I X T a = true :=
    fun a b hab hb h => by
      rcases hkey a b hab hb with h' | ⟨h', -⟩
      · exact lexW_trans _ _ _ h' h
      · simpa [ltT, h'] using h
  refine ⟨hmono, fun b hbn hlo hhi => ⟨fun k hk => ?_, fun hn a ha he => ?_⟩⟩
  · obtain ⟨hkl, hkt, hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
    simp only [decide_eq_true_eq] at hkt
    obtain ⟨a0, ha0, e0⟩ := hX.all k hkl
    have hA0 : ansW I (X a0) = T := by rw [e0, ansW_entry4 c π L hs hq ht hkl, hkt]
    -- `p` fails at `a0`, and holds below it
    have hf0 : ltT I X T a0 = false := by simp [ltT, hA0, lexW_irrefl]
    have ht0 : ∀ a < a0, ltT I X T a = true := fun a ha => by
      rcases hkey a a0 ha ha0 with h' | ⟨h', hlt⟩
      · rwa [hA0] at h'
      · exfalso
        obtain ⟨k', hk', e', hA'⟩ := hA a (by omega)
        have hkt' : L[k'].2 = t := packBytes_digest_inj (by rw [← hA', h', hA0])
        rw [e', e0, BitVec.lt_def, toNat_toWord (posE_lt4 c π L hs ht hk'),
          toNat_toWord (posE_lt4 c π L hs ht hkl)] at hlt
        have hkk : k' < k := by
          by_contra hge
          rcases Nat.lt_or_ge k k' with h2 | h2
          · have := entryOff_lt L h2 hk'.le; simp only [posE4] at hlt; omega
          · have : k = k' := by omega
            subst this; omega
        have := hfirst k' hkk
        simp [hkt'] at this
    have hb1 : b ≤ a0 := by
      by_contra h
      have := hlo a0 (by omega)
      rw [hf0] at this; exact absurd this (by decide)
    have hb2 : a0 ≤ b := by
      by_contra h
      have h1 := ht0 b (by omega)
      rw [hhi b le_rfl (by omega)] at h1; exact absurd h1 (by decide)
    have : b = a0 := by omega
    subst this
    exact ⟨ha0, e0⟩
  · obtain ⟨k, hk, -, hA'⟩ := hA a ha
    have := List.findIdx?_eq_none_iff.mp hn L[k] (List.getElem_mem hk)
    have e : L[k].2 = t := packBytes_digest_inj (by rw [← hA', he])
    simp [e] at this


/-- **One halving step** of the machine is `bsStep` on the predicate `ltT`. -/
theorem bsBody4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n lo len : ℕ} {T : List Word}
    {X : ℕ → Word} (hR : SRegs s.M n lo len T) (hb : lo + len ≤ n) (hn : n < 2 ^ 62)
    (hX : ∀ a < n, rd s.M (bX + a) = X a) :
    SRegs (semXIR I (bsBody4 bX) s).M n (bsStep (ltT I X T) (lo, len)).1
      (bsStep (ltT I X T) (lo, len)).2 T := by
  have hs := hM.1
  simp only [regs] at hs
  rw [bsBody4, semXIR_ite, hR.len]
  by_cases h0 : len = 0
  · subst h0
    have h00 : toWord 0 = (0 : Word) := rfl
    rw [if_pos h00]
    have e : bsStep (ltT I X T) (lo, 0) = (lo, 0) := by simp [bsStep]
    rw [e]; exact hR
  have hne : toWord len ≠ 0 := fun h => h0 (by
    have := congrArg BitVec.toNat h; rwa [toNat_toWord (by omega)] at this)
  rw [if_neg hne]
  have e : bsStep (ltT I X T) (lo, len) = if ltT I X T (lo + len / 2) = true then
      (lo + len / 2 + 1, len - len / 2 - 1) else (lo, len / 2) := by simp [bsStep, h0]
  rw [e]
  -- the probe
  have hwf1 : WF (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
      .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) := by
    simp +decide [WF, Prim.dst, rKc, rHf, rMd, rAd]
  have h1 : rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rHf = toWord (len / 2) ∧
      rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rMd =
        toWord (lo + len / 2) ∧
      rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rAd =
        toWord (lo + len / 2 + bX) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rKc, rHf, rMd, rAd]; omega)) only
      [rd_set_self, rd_set_ne] <;>
    rw [hR.len, shr_one_toWord (by omega)]
    · rw [hR.lo, add_toWord]
    · rw [hR.lo, add_toWord]; exact add_toWord _ _
  have hR1 := hR.sem (I := I) hM hwf1 (by
    simp +decide [srL, Writes, Prim.dst, rKc, rHf, rMd, rAd, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  have hH1 := hframe I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
    .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s
    (by simp +decide [Lo, Prim.dst, regs, rKc, rHf, rMd, rAd])
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
    .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s = s1 at h1 hR1 hM1 hH1
  obtain ⟨hf1, hd1, ha1⟩ := h1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the load of `X[mid]`
  have hx2 : rd (semXIR I (.load rX rAd) s1).M rX = X (lo + len / 2) := by
    simp only [semXIR]
    rw [rd_set_self (by simp only [rX]; omega), ha1, toNat_toWord (by omega),
      hH1 _ (by simp only [regs] at hbX ⊢; omega), show lo + len / 2 + bX = bX + (lo + len / 2) by
      omega, hX _ (by omega)]
  have hfr2 : ∀ q ∈ [rHf, rMd] ++ srL, rd (semXIR I (.load rX rAd) s1).M q = rd s1.M q :=
    fun q hq => by
      simp only [semXIR]
      exact rd_set_ne ((by decide : ∀ r ∈ [rHf, rMd] ++ srL, rX ≠ r) q hq)
  have hR2 := hR1.sem (I := I) (P := .load rX rAd) hM1 (by simp +decide [WF, rX]) (by
    simp +decide [srL, Writes, rX, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM2 := inv_sem I (P := .load rX rAd) (by simp +decide [WF, rX]) hM1
  rw [semXIR_seq]
  generalize semXIR I (.load rX rAd) s1 = s2 at hx2 hfr2 hR2 hM2
  -- the comparison
  have hF3 : rd (semXIR I ansLtIR s2).M rF = bW (ltT I X T (lo + len / 2)) := by
    rw [ansLtIR_sem I s2 hM2, hx2, hR2.q]; rfl
  have hfr3 := fun {q : ℕ} (hq : q ∈ [rHf, rMd] ++ srL) => ansLtIR_frame I s2 hM2 hq
  have hR3 := hR2.sem (I := I) (P := ansLtIR) hM2 wf_ansLtIR nw_ansLtIR
  have hM3 := inv_sem I wf_ansLtIR hM2
  have hhf3 : rd (semXIR I ansLtIR s2).M rHf = toWord (len / 2) := by
    rw [hfr3 (by simp), hfr2 _ (by simp), hf1]
  have hmd3 : rd (semXIR I ansLtIR s2).M rMd = toWord (lo + len / 2) := by
    rw [hfr3 (by simp), hfr2 _ (by simp), hd1]
  rw [semXIR_seq]
  generalize semXIR I ansLtIR s2 = s3 at hF3 hR3 hM3 hhf3 hmd3
  have hs3 := hM3.1
  have hc3 : rd s3.M cOne = 1 := hM3.2 0 (by decide)
  simp only [regs] at hs3
  rw [semXIR_ite, hF3]
  by_cases hp : ltT I X T (lo + len / 2) = true
  · rw [hp, if_neg bW_ne_zero, if_pos rfl]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rLo, rLn]; omega)) only
      [rd_set_self, rd_set_ne]
    · rw [hmd3, hc3, add_one_toWord]
    · rw [hR3.len, hhf3, hc3, sub_toWord (by omega) (by omega),
        show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega)]
    · exact hR3.n
    · exact hR3.q
  · rw [(Bool.not_eq_true _).mp hp, if_pos bW_false, if_neg (by simp)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rLn]; omega)) only
      [rd_set_self, rd_set_ne]
    · exact hR3.lo
    · rw [hhf3, or_self_eval]
    · exact hR3.n
    · exact hR3.q


omit hbX hbX2 hpL in
theorem wf_bsBody4 : WF (bsBody4 bX) := by
  simp +decide [bsBody4, ansLtIR, aposIR, ceil8Ps, cmpTWord, WF, Prim.dst, rQL, rKc, rT2, rPa,
    rAd, rKa, rG, rH, rF, rHf, rMd, rX, rLo, rLn, and_true, List.cons_append, List.nil_append]


omit hbX hbX2 hpL in
theorem lo_bsBody4 : Lo (bsBody4 bX) := by
  simp +decide [bsBody4, ansLtIR, aposIR, ceil8Ps, cmpTWord, Lo, Prim.dst, regs, rQL, rKc, rT2,
    rPa, rAd, rKa, rG, rH, rF, rHf, rMd, rX, rLo, rLn, and_true, List.cons_append, List.nil_append]


/-- **The search loop**: `m` iterations run `bsRun` and leave the heap alone. -/
theorem bsLoop4 (I : Array Word) {n : ℕ} {T : List Word} {X : ℕ → Word} (hn : n < 2 ^ 62) :
    ∀ (m : ℕ) (s : St) (lo len : ℕ), Inv s.M → SRegs s.M n lo len T → lo + len ≤ n →
      (∀ a < n, rd s.M (bX + a) = X a) →
      Inv (iterL (semXIR I (bsBody4 bX)) rCB m s).M ∧
      SRegs (iterL (semXIR I (bsBody4 bX)) rCB m s).M n (bsRun (ltT I X T) m (lo, len)).1
        (bsRun (ltT I X T) m (lo, len)).2 T ∧
      ∀ x, regs ≤ x → rd (iterL (semXIR I (bsBody4 bX)) rCB m s).M x = rd s.M x
  | 0, _, _, _, hM, hR, _, _ => ⟨hM, hR, fun _ _ => rfl⟩
  | m + 1, s, lo, len, hM, hR, hb, hX => by
    have h1 := bsBody4_sem hbX hbX2 hpL I s hM hR hb hn hX
    have hH := hframe I (bsBody4 bX) s (lo_bsBody4 (bX := bX))
    have hM1 := inv_sem I (wf_bsBody4 (bX := bX)) hM
    have hM' : Inv (decS rCB (semXIR I (bsBody4 bX) s)).M := inv_of_frame hM1 (size_decS ..)
      fun i hi => rd_decS (by simp only [rCB]; omega) _
    have hH' : ∀ x, regs ≤ x → rd (decS rCB (semXIR I (bsBody4 bX) s)).M x = rd s.M x :=
      fun x hx => (rd_decS (by simp only [rCB, regs] at *; omega) _).trans (hH x hx)
    obtain ⟨a, b, c⟩ := bsLoop4 I hn m _ _ _ hM' h1.decS (bsStep_le hb)
      (fun a ha => by rw [hH' _ (by simp only [regs] at hbX ⊢; omega), hX a ha])
    simp only [iterL, bsRun]
    exact ⟨a, b, fun x hx => (c x hx).trans (hH' x hx)⟩


/-- **The found flag**: `rFd = [lo < n ∧ ansW(X[lo]) = T]`; `rLo` is kept. -/
theorem foundIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n lo len : ℕ} {T : List Word}
    (hR : SRegs s.M n lo len T) (hlo : lo ≤ n) (hn : n < 2 ^ 62) :
    rd (semXIR I (foundIR4 bX) s).M rFd =
      bW (decide (lo < n) && decide (ansW I (rd s.M (bX + lo)) = T)) ∧
    rd (semXIR I (foundIR4 bX) s).M rLo = toWord lo := by
  have hs := hM.1
  simp only [regs] at hs
  set x := rd s.M (bX + lo)
  -- the address and the load
  have hwf1 : WF (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) := by simp +decide [WF, Prim.dst, rKc, rAd, rX, and_true]
  have hx1 : rd (semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) s).M rX = x := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rX]; omega)]
    simp (disch := first | decide | (simp only [size_set, rKc, rAd]; omega)) only [rd_set_self,
      rd_set_ne]
    rw [hR.lo, show XOp.add.eval (toWord lo) (BitVec.ofNat 64 bX) = toWord (lo + bX) from
      add_toWord _ _, toNat_toWord (by omega), rd_set_ne (by simp only [rAd, regs] at hbX ⊢; omega),
      rd_set_ne (by simp only [rKc, regs] at hbX ⊢; omega), show lo + bX = bX + lo by omega]
  have hR1 := hR.sem (I := I) hM hwf1 (by
    simp +decide [srL, Writes, Prim.dst, rKc, rAd, rX, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  have e : semXIR I (foundIR4 bX) s = semXIR I (.seq (aposIR rPa rX) (.seq (.blk [.op .ltu rFd rLo rN])
      (.seq (eqTWord 0 rQ0) (.seq (eqTWord 1 rQ1) (.seq (eqTWord 2 rQ2) (eqTWord 3 rQ3))))))
      (semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
        (.load rX rAd)) s) := rfl
  rw [e]
  generalize semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) s = s1 at hx1 hR1 hM1
  -- the answer position
  rw [semXIR_seq]
  have ha2 := aposIR_sem I s1 hM1 (.inl ⟨rfl, rfl⟩)
  rw [hx1] at ha2
  have hR2 := hR1.sem (I := I) (P := aposIR rPa rX) hM1 wf_aposIR' (by
    simp only [srL, aposIR, ceil8Ps, Writes, List.cons_append, List.nil_append]; decide)
  have hM2 := inv_sem I wf_aposIR' hM1
  generalize semXIR I (aposIR rPa rX) s1 = s2 at ha2 hR2 hM2
  -- `lo < n`
  rw [semXIR_seq]
  have hs2 := hM2.1
  simp only [regs] at hs2
  have hwf3 : WF (.blk [.op .ltu rFd rLo rN]) := by simp +decide [WF, Prim.dst, rFd]
  have hf3 : rd (semXIR I (.blk [.op .ltu rFd rLo rN]) s2).M rFd = bW (decide (lo < n)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rFd]; omega), hR2.lo, hR2.n, ltW_toWord (by omega) (by omega)]
  have hfr3 : ∀ q ∈ [rPa] ++ srL, rd (semXIR I (.blk [.op .ltu rFd rLo rN]) s2).M q =
      rd s2.M q := fun q hq => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne ((by decide : ∀ r ∈ [rPa] ++ srL, rFd ≠ r) q hq)
  have hM3 := inv_sem I hwf3 hM2
  generalize semXIR I (.blk [.op .ltu rFd rLo rN]) s2 = s3 at hf3 hfr3 hM3
  have step : ∀ (s' : St), Inv s'.M → (∀ q ∈ [rPa] ++ srL, rd s'.M q = rd s2.M q) →
      ∀ (w r : ℕ) (p : Bool), w < 4 → (r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) →
      rd s'.M rFd = bW p →
      rd (semXIR I (eqTWord w r) s').M rFd = bW (p && decide ((ansW I x).getD w 0 = rd s2.M r)) ∧
      Inv (semXIR I (eqTWord w r) s').M ∧
      (∀ q ∈ [rPa] ++ srL, rd (semXIR I (eqTWord w r) s').M q = rd s2.M q) :=
    fun s' hM' hq w r p hw hr hf => by
      have hrq : rd s'.M r = rd s2.M r := hq r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      refine ⟨?_, inv_sem I (wf_eqTWord w r) hM', fun q hqm => by
        rw [eqTWord_frame I s' hM' w r hqm, hq q hqm]⟩
      rw [eqTWord_sem I s' hM' hr, hf, hrq, hq rPa (by decide), ha2, ansW_getD I x hw, eq_bW,
        bW_and]
  rw [semXIR_seq]
  obtain ⟨f0, m0, q0⟩ := step s3 hM3 hfr3 0 rQ0 _ (by decide) (.inl rfl) hf3
  generalize semXIR I (eqTWord 0 rQ0) s3 = s4 at f0 m0 q0
  rw [semXIR_seq]
  obtain ⟨f1, m1, q1⟩ := step s4 m0 q0 1 rQ1 _ (by decide) (.inr (.inl rfl)) f0
  generalize semXIR I (eqTWord 1 rQ1) s4 = s5 at f1 m1 q1
  rw [semXIR_seq]
  obtain ⟨f2, m2, q2⟩ := step s5 m1 q1 2 rQ2 _ (by decide) (.inr (.inr (.inl rfl))) f1
  generalize semXIR I (eqTWord 2 rQ2) s5 = s6 at f2 m2 q2
  obtain ⟨f3, -, q3⟩ := step s6 m2 q2 3 rQ3 _ (by decide) (.inr (.inr (.inr rfl))) f2
  refine ⟨?_, by rw [q3 rLo (by decide), hR2.lo]⟩
  rw [f3, ← hR2.q, decide_ansW _ (ansW_length I x)]


/-- **The lookup's semantics**: `rLo` is the lower bound `bsRun` of the target `T` (the words in
`rQ0 … rQ3`) on `X[0..n)`, `rFd` says whether that slot exists and its answer is `T`; the heap
is unchanged. -/
theorem lookIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ} {T : List Word}
    {X : ℕ → Word} (hn : I.getD pL 0 = toWord n) (hn2 : n < 2 ^ 62)
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = T)
    (hX : ∀ a < n, rd s.M (bX + a) = X a) :
    rd (semXIR I (lookIR4 bX pL) s).M rLo = toWord (bsRun (ltT I X T) 64 (0, n)).1 ∧
    rd (semXIR I (lookIR4 bX pL) s).M rFd = bW (decide ((bsRun (ltT I X T) 64 (0, n)).1 < n) &&
      decide (ansW I (rd s.M (bX + (bsRun (ltT I X T) 64 (0, n)).1)) = T)) ∧
    ∀ x, regs ≤ x → rd (semXIR I (lookIR4 bX pL) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf0 : WF (lookPre4 pL) := by simp +decide [lookPre4, readAt, WF, Prim.dst, rN, rA, rLo, rLn,
    rNB, and_true]
  have hlo0 : Lo (lookPre4 pL) := by simp +decide [lookPre4, readAt, Lo, Prim.dst, regs, rN, rA, rLo,
    rLn, rNB, and_true]
  have hR0 : SRegs (semXIR I (lookPre4 pL) s).M n 0 n T ∧ rd (semXIR I (lookPre4 pL) s).M rNB = 64 := by
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by omega)
    have hwfr : WF (readAt rN pL) := by simp +decide [readAt, WF, Prim.dst, rN, rA, and_true]
    have hM' := inv_sem I hwfr hM
    have hq' : [rd (semXIR I (readAt rN pL) s).M rQ0, rd (semXIR I (readAt rN pL) s).M rQ1,
        rd (semXIR I (readAt rN pL) s).M rQ2, rd (semXIR I (readAt rN pL) s).M rQ3] = T := by
      have hf := fun r (hr : r ∈ [rQ0, rQ1, rQ2, rQ3]) => Lvm.X.frame I _ s hwfr hM r
        ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r < regs) r hr) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp +decide [readAt, Writes, Prim.dst, rN,
            rA, rQ0, rQ1, rQ2, rQ3, or_false])
      rw [hf rQ0 (by simp), hf rQ1 (by simp), hf rQ2 (by simp), hf rQ3 (by simp)]
      exact hT
    rw [hn] at hN
    rw [lookPre4, semXIR_seq]
    generalize semXIR I (readAt rN pL) s = s' at hN hM' hq'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLo, rLn, rNB]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hN, or_self_eval]
    · exact hN
    · exact hq'
  have hM0 := inv_sem I hwf0 hM
  have hH0 := hframe I (lookPre4 pL) s hlo0
  rw [lookIR4_eq, semXIR_seq, semXIR_seq]
  generalize semXIR I (lookPre4 pL) s = s0 at hR0 hM0 hH0
  obtain ⟨hR0, hB0⟩ := hR0
  have e : semXIR I (.loopK rCB rNB 64 (bsBody4 bX)) s0 =
      iterL (semXIR I (bsBody4 bX)) rCB 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ := by
    simp only [semXIR, entryKB hM0 hB0]
    rfl
  rw [e]
  have hE : ∀ i, i ≠ rCB → i ≠ cTmp → rd (entryK rCB rNB 64 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME : Inv (entryK rCB rNB 64 s0.M) := inv_of_frame hM0 (size_entryK ..)
    fun i hi => hE i (by simp only [rCB]; omega) (by simp only [cTmp]; omega)
  have hRE : SRegs (entryK rCB rNB 64 s0.M) n 0 n T :=
    ⟨(hE _ (by decide) (by decide)).trans hR0.lo, (hE _ (by decide) (by decide)).trans hR0.len,
      (hE _ (by decide) (by decide)).trans hR0.n, by
        rw [hE rQ0 (by decide) (by decide), hE rQ1 (by decide) (by decide),
          hE rQ2 (by decide) (by decide), hE rQ3 (by decide) (by decide)]; exact hR0.q⟩
  have hHE : ∀ x, regs ≤ x → rd (entryK rCB rNB 64 s0.M) x = rd s.M x := fun x hx => by
    rw [hE x (by simp only [rCB, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
      hH0 x hx]
  obtain ⟨l1, l2, l3⟩ := bsLoop4 hbX hbX2 hpL I (X := X) hn2 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ 0 n hME hRE
    (by omega) (fun a ha => by rw [hHE (bX + a) (by simp only [regs] at hbX ⊢; omega), hX a ha])
  generalize iterL (semXIR I (bsBody4 bX)) rCB 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ = s1 at l1 l2 l3
  have hle := bsRun_le (p := ltT I X T) (n := n) 64 0 n (by omega)
  obtain ⟨f1, f2⟩ := foundIR4_sem hbX hbX2 hpL I s1 l1 l2 (le_trans (Nat.le_add_right _ _) hle) hn2
  have hH1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => (l3 x hx).trans (hHE x hx)
  refine ⟨f2, ?_, fun x hx => (hframe I (foundIR4 bX) s1 (by
    simp +decide [foundIR4, aposIR, ceil8Ps, eqTWord, Lo, Prim.dst, regs, rKc, rAd, rX, rQL,
      rT2, rPa, rFd, rKa, rH, and_true, List.cons_append, List.nil_append]) x hx).trans (hH1 x hx)⟩
  rw [f1, hH1 _ (by simp only [regs] at hbX ⊢; omega)]


/-- **`lookup_spec`**, parametric in the target `t`. On a domain tape of a SNARK proof, take a
state `s₂` whose `X[0..|L|)` is the one `idxIR4` left and whose `rQ0 … rQ3` hold
`packBytes t`. If `t` is the answer of some log entry, `(lookIR4 bX pL)` sets `rFd = 1` and `rLo` to a
slot `b` whose `X[b]` is the tape position of the **first** such entry (`ansIdx`);
otherwise `rFd = 0`. `X` is unchanged, so it is still the sorted index. -/
theorem idx_lookup4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size) (t : Digest)
    (s₂ : St) (hM₂ : Inv s₂.M)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    (hT : [rd s₂.M rQ0, rd s₂.M rQ1, rd s₂.M rQ2, rd s₂.M rQ3] = packBytes t.toList) :
    (∀ k, ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rLo = toWord b ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 1 ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + b) = toWord (posE4 pL L k)) ∧
    (ansIdx L t = none →
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 0) ∧
    Sorted4 pL (extractorInput c π L).toArray L
      (fun a => rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + a)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  generalize semXIR I (idxIR4 bX pL) s = s1 at r1 r2 r3 hX₂
  set X : ℕ → Word := fun a => rd s1.M (bX + a) with hXd
  have hSX : Sorted4 pL I L X := ⟨r1, r2, r3⟩
  have hX₂' : ∀ a < L.length, rd s₂.M (bX + a) = X a := hX₂
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s₂ hM₂ (n := L.length) (X := X)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by omega) hT hX₂'
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hs hq ht hSX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I X (packBytes t.toList)) (n := L.length)
    (by omega) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  have hXb : ∀ a < L.length, rd (semXIR I (lookIR4 bX pL) s₂).M (bX + a) = X a := fun a ha => by
    rw [l3 _ (by simp only [regs] at hbX ⊢; omega), hX₂' a ha]
  refine ⟨fun k hk => ?_, fun hk => ?_, ⟨fun a b hab hb => ?_, fun a ha => ?_, fun k hk => ?_⟩⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, by rw [hXb _ hb, e]⟩
    rw [l2, hX₂' _ hb, e, ansW_entry4 c π L hs hq ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I X (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hX₂' _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]
  · rw [hXb a (by omega), hXb b hb]; exact r1 a b hab hb
  · rw [hXb a ha]; exact r2 a ha
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, by rw [hXb a ha]; exact e⟩



end Idx

end Lvm.X

