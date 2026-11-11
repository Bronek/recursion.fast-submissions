-- adapted from rf-k/submissions/flock-recursive/lean/FRXChainFlock.lean@kk/base (the instance of the
-- chain scan for FR's schedule) and FRXSeed (the seed block): lvm's targets, table and seed block.
import LvmXChain
import LvmXLayout

/-!
# The chain scan for `V_S`'s schedule (BLUEPRINT §6.2 step 3, A4)

* `fsQL π p st`: the query at chain position `p` when the previous answer is `st`: `q₀` at `p = 0`,
  else `st ‖ π[o, o + len)` with `(o, len) = fsMsgs pX` entry `p − 1` (`LvmDriver.fsQuery`,
  `seedQuery`). `stateIn_fsQL`: every query after `q₀` carries its state.
* `chTabL`, `tabW_chTabL`: the table realises `fsQL` on every tape of a proof of `piSize` bytes.
* `sdL`: the seed block (`H[0] := q₀`'s word), `seedOK_sdL`.
* **`chainL_spec`**: on a domain tape of an `S` proof whose log has no state hit, the machine's
  answer at `ansB + 4p` (`p < nChain pX`) is the first-match chain's (`fmAns`), i.e. `runLog`'s
  reading with the queries rebuilt exactly from π (A4).
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The chain's message of position `p ≥ 1` (irreducible: only its checked facts are used). -/
@[irreducible] def msgL (p : ℕ) : ℕ × ℕ := (fsMsgs pX).getD (p - 1) (0, 0)

/-- **The query at chain position `p`**, the previous answer being `st`. -/
def fsQL (π : Proof) (p : ℕ) (st : Digest) : ByteArray :=
  if p = 0 then q0Query else digestBytes st ++ π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)

/-- The all-zero digest (the scan's dummy start). -/
def zeroDL : Digest := Vector.replicate 32 0

/-- Every chain message is lane-aligned, inside π, and its query within `queryCap`. -/
def msgOkL (m : ℕ × ℕ) : Bool :=
  m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piSize pX && 32 + m.2 ≤ queryCap

theorem msgs_ok : ((fsMsgs pX).take (nChain pX - 1)).all msgOkL = true := layout_all_P20.2.2.2.2.2.1

theorem nChain_le : nChain pX - 1 ≤ (fsMsgs pX).length := by
  rw [layout_P20.2.1, layout_P20.2.2.2.2.2.1]; decide

theorem msgL_ok {p : ℕ} (hp0 : 0 < p) (hp : p < nChain pX) :
    (msgL p).1 % 8 = 0 ∧ (msgL p).2 % 8 = 0 ∧ (msgL p).1 + (msgL p).2 ≤ piSize pX ∧
      32 + (msgL p).2 ≤ queryCap := by
  have hl := nChain_le
  have hm : (fsMsgs pX)[p - 1]'(by omega) ∈ (fsMsgs pX).take (nChain pX - 1) :=
    List.mem_iff_getElem.mpr ⟨p - 1, by simp; omega, by simp⟩
  have h := List.all_eq_true.mp msgs_ok _ hm
  unfold msgL
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [msgOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem nChain_eq : nChain pX = 1314 := layout_P20.2.1

theorem msgL_last : (msgL (nChain pX)).1 = 229304 := by
  rw [layout_P20.2.1, msgL, show 1314 - 1 = 1313 from rfl, layout_P20.2.2.2.2.2.2]

theorem digestBytes_size (d : Digest) : (digestBytes d).size = 32 := by
  simp [digestBytes, ByteArray.size]

theorem packBytes_getDX (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = if 8 * j < l.length then toWord (ofLE ((l.drop (8 * j)).take 8))
      else 0 := by
  by_cases h : 8 * j < l.length
  · rw [if_pos h, List.getD_eq_getElem _ _ (by rw [packBytes_length]; omega)]
    simp [packBytes]
  · rw [if_neg h, List.getD_eq_default _ _ (by rw [packBytes_length]; omega)]

theorem packBytes_drop8X (l : List UInt8) (a j : ℕ) :
    (packBytes (l.drop (8 * a))).getD j 0 = (packBytes l).getD (a + j) 0 := by
  rw [packBytes_getDX, packBytes_getDX, List.length_drop, List.drop_drop]
  by_cases h : 8 * (a + j) < l.length
  · rw [if_pos (by omega), if_pos h, show 8 * a + 8 * j = 8 * (a + j) by ring]
  · rw [if_neg (by omega), if_neg h]

theorem packBytes_take8X (l : List UInt8) {n j : ℕ} (hj : j < n) :
    (packBytes (l.take (8 * n))).getD j 0 = (packBytes l).getD j 0 := by
  rw [packBytes_getDX, packBytes_getDX, List.length_take, List.drop_take, List.take_take]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, Nat.min_eq_left (by omega)]
  · rw [if_neg (by omega), if_neg h]

theorem piSize_eq : piSize pX = 1094248 := layout_all_P20.2.2.2.1

theorem extract_size (π : Proof) {o len : ℕ} (h : o + len ≤ π.size) :
    (π.extract o (o + len)).size = len := by
  rw [ByteArray.size_extract]; omega

theorem fsQL_size {π : Proof} (hs : π.size = piSize pX) {p : ℕ} (hp0 : 0 < p) (hp : p < nChain pX)
    (st : Digest) : (fsQL π p st).size = 32 + (msgL p).2 := by
  obtain ⟨-, -, h3, -⟩ := msgL_ok hp0 hp
  rw [fsQL, if_neg (by omega), ByteArray.size_append, extract_size π (by omega), digestBytes_size]

theorem fsQL_data {π : Proof} (p : ℕ) (hp0 : 0 < p) (st : Digest) :
    (fsQL π p st).data.toList =
      st.toList ++ (π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)).data.toList := by
  rw [fsQL, if_neg (by omega), ByteArray.data_append, Array.toList_append]
  rfl

theorem msgs_cap : (fsMsgs pX).all (fun m => 32 + m.2 ≤ queryCap) = true := layout_all_P20.2.2.2.2.1

theorem msgL_cap (p : ℕ) : 32 + (msgL p).2 ≤ queryCap := by
  unfold msgL
  by_cases h : p - 1 < (fsMsgs pX).length
  · rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true (List.all_eq_true.mp msgs_cap _ (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]; decide

/-- **Every query after `q₀` carries its state.** -/
theorem stateIn_fsQL (π : Proof) {p : ℕ} (hp0 : 0 < p) (st : Digest) :
    stateIn (fsQL π p st) = some st := by
  have hc := msgL_cap p
  have hd := fsQL_data (π := π) p hp0 st
  have hz : (fsQL π p st).size = 32 + (π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)).size := by
    rw [fsQL, if_neg (by omega), ByteArray.size_append, digestBytes_size]
  generalize msgL p = m at hc hd hz
  have he : (π.extract m.1 (m.1 + m.2)).size ≤ m.2 := by
    rw [ByteArray.size_extract]; omega
  generalize fsQL π p st = q at hd hz ⊢
  generalize π.extract m.1 (m.1 + m.2) = x at hd hz he
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [stateIn, if_pos ⟨by omega, by omega⟩]
  refine congrArg some (Vector.ext fun i hi => ?_)
  rw [Vector.getElem_ofFn, List.getD_eq_getElem _ _ (by omega), List.getElem_of_eq hd,
    List.getElem_append_left (by simp; omega), Vector.getElem_toList]

/-! ## The table -/

/-- One table entry: `tl`, the tape word of the message, two unused words (`q₀`: `tl = 7`). -/
def tabEntL (p : ℕ) : List Word :=
  if p = 0 then [toWord 7, 0, 0, 0] else [toWord (32 + (msgL p).2), toWord (5 + (msgL p).1 / 8), 0, 0]

/-- **The table**: entries `0 … nChain`. -/
def chTabL : List Word := (List.range (nChain pX + 1)).flatMap tabEntL

theorem tabEntL_length (p : ℕ) : (tabEntL p).length = 4 := by unfold tabEntL; split <;> rfl

theorem getD_flatMap4 (f : ℕ → List Word) (hf : ∀ p, (f p).length = 4) :
    ∀ (n p k : ℕ), p < n → k < 4 → ((List.range n).flatMap f).getD (4 * p + k) 0 = (f p).getD k 0
  | 0, p, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, p, k, hp, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl : ((List.range n).flatMap f).length = 4 * n := by
      rw [List.length_flatMap]
      simp only [hf, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]; ring
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h | rfl
    · rw [List.getD_append _ _ _ _ (by omega), getD_flatMap4 f hf n p k h hk]
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]

theorem chTabL_length : chTabL.length = 4 * (nChain pX + 1) := by
  -- generic in the entry count: at `nChain pX` the proof's casts made the kernel evaluate it (1 s)
  have h : ∀ n : ℕ, ((List.range n).flatMap tabEntL).length = 4 * n := fun n => by
    rw [List.length_flatMap]
    simp only [tabEntL_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  rw [chTabL]
  exact h _

theorem chTabL_getD {p k : ℕ} (hp : p ≤ nChain pX) (hk : k < 4) :
    chTabL.getD (4 * p + k) 0 = (tabEntL p).getD k 0 :=
  getD_flatMap4 tabEntL tabEntL_length _ p k (by omega) hk

/-- Packed words of a 32-byte prefix and the rest. -/
theorem packBytes_appendK (a b : List UInt8) {k : ℕ} (ha : a.length = 8 * k) (j : ℕ) :
    (packBytes (a ++ b)).getD j 0 =
      if j < k then (packBytes a).getD j 0 else (packBytes b).getD (j - k) 0 := by
  split_ifs with hj
  · rw [← packBytes_take8X (a ++ b) hj, List.take_left' ha]
  · have := packBytes_drop8X (a ++ b) k (j - k)
    rw [List.drop_left' ha, show k + (j - k) = j by omega] at this
    exact this.symm

/-- An aligned message's packed words are π's. -/
theorem extract_words (π : Proof) {a n : ℕ} (h : 8 * a + 8 * n ≤ π.size) {j : ℕ} (hj : j < n) :
    (packBytes (π.extract (8 * a) (8 * a + 8 * n)).data.toList).getD j 0 =
      (packBytes π.data.toList).getD (a + j) 0 := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    show 8 * a + 8 * n - 8 * a = 8 * n by omega, packBytes_take8X _ hj, packBytes_drop8X]

/-- **The table realises `V_S`'s chain** on every tape of a proof of `piSize` bytes. -/
theorem tabW_chTabL (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) :
    TabW (extractorInput c π L).toArray (fsQL π) (nChain pX) chTabL := by
  have hp1 : π.size = 1094248 := hs.trans piSize_eq
  refine ⟨chTabL_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTabL_getD hpN (by norm_num), tabEntL, if_neg (by omega)]
    show (toWord (5 + (msgL p).1 / 8)).toNat < 2 ^ 62
    have : (msgL p).1 ≤ 1094248 := by
      rcases Nat.lt_or_ge p (nChain pX) with h | h
      · have := (msgL_ok hp0 h).2.2.1; rw [piSize_eq] at this; omega
      · have hpe : p = nChain pX := by omega
        rw [hpe, msgL_last]; omega
    generalize msgL p = m at this
    rw [toNat_toWord (by omega)]; omega
  · obtain ⟨ho, hl, hol, hq⟩ := msgL_ok hp0 hpN'
    have e0 := chTabL_getD hpN (k := 0) (by norm_num)
    have e1 := chTabL_getD hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntL, if_neg (by omega)]
    have hz := fsQL_size hs hp0 hpN' st
    refine ⟨by rw [hz]; rfl, by rw [hz]; omega, fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQL_data p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgL p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · rw [piSize_eq] at hol
      generalize msgL p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by omega⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by omega), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by omega,
        tape_getD_proof c π L (by rw [hp1]; omega), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hp1]; omega) (by omega)]

/-! ## The seed block: `H[0] := q₀`'s word -/

/-- `q₀`'s packed word. -/
def q0W : Word := toWord (ofLE q0Bytes)

/-- **The seed block.** -/
def sdL : XIR := .seq (.blk [.const rAd4 (toWord hB), .const rKd q0W]) (.store rAd4 rKd)

theorem q0W_eq : (packBytes q0Query.data.toList).getD 0 0 = q0W := by decide

theorem wf_sdL : WF sdL := by
  refine ⟨fun p hp => ?_, show rAd4 ≠ cTmp by decide⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl <;> simp only [Prim.dst, rAd4, rKd] <;> omega

theorem nw_sdL (r : ℕ) (h1 : r ≠ rAd4) (h2 : r ≠ rKd) (h3 : r ≠ cTmp) : ¬ Writes sdL r := by
  rintro (⟨p, hp, he⟩ | he)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact h1 he.symm
    · exact h2 he.symm
  · exact h3 he

theorem seedOK_sdL (I : Array Word) : SeedOK sdL I q0Query := by
  refine ⟨wf_sdL, nw_sdL _ (by decide) (by decide) (by decide), fun s hM hsz => ?_⟩
  rw [show sdL = .seq (.blk [.const rAd4 (toWord hB), .const rKd q0W]) (.store rAd4 rKd) from rfl,
    semXIR_seq]
  have hs := hM.1
  simp only [regs] at hs
  have hM1 : Inv (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s).M :=
    inv_sem I wf_sdL.1 hM
  have a1 : rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s).M rAd4 = toWord hB := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [size_set, rAd4]; omega)]
  have k1 : rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s).M rKd = q0W := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rKd]; omega)]
  have f1 : ∀ i, i ≠ rAd4 → i ≠ rKd →
      rd (semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s).M i = rd s.M i :=
    fun i h1 h2 => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm h1
      · exact Ne.symm h2) _
  have z1 := size_sem I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s
  generalize semXIR I (.blk [.const rAd4 (toWord hB), .const rKd q0W]) s = s1 at hM1 a1 k1 f1 z1
  have hB' : hB < s1.M.size := by rw [z1]; simp only [hB_eq, chEnd] at hsz ⊢; omega
  have st : ∀ i, i ≠ cTmp → rd (storeM s1.M rAd4 rKd) i = if i = hB then rd s1.M rKd else rd s1.M i :=
    fun i hi => rd_storeM hM1 a1 (by simp only [hB_eq, regs]; omega) (by simp only [hB_eq]; omega)
      hB' (by decide) (by decide) hi
  have e8 : semXIR I (.store rAd4 rKd) s1 = ⟨storeM s1.M rAd4 rKd, s1.o⟩ := rfl
  rw [e8]
  refine ⟨?_, ?_, fun y hy hy' => ?_⟩
  · rw [st _ (by simp only [hB_eq, cTmp]; omega), if_pos rfl, k1, q0W_eq]
  · rw [st _ (by decide), if_neg (by simp only [hB_eq, rCn5]; omega), f1 _ (by decide) (by decide)]
  · simp only [regs] at hy
    rw [st _ (by simp only [cTmp]; omega), if_neg (by omega),
      f1 _ (by simp only [rAd4]; omega) (by simp only [rKd]; omega)]

/-! ## The specification -/

/-- **The chain program** of lvm's extractor. -/
def chainL : XIR := chainIR (posL (piSize pX)) (nChain pX) chTabL sdL

/-- **`chainL_spec`**: on a domain tape of an `S` proof (`piSize` bytes) whose log has no state
hit, for every position `p < nChain pX` that the first-match chain answers with `a`, the
machine's answer at `ansB + 4p` is `a`'s four words; the heap outside the chain's region is kept. -/
theorem chainL_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChain pX, ∀ a, fmAns (fsQL π) zeroDL L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray chainL s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray chainL s).M y = rd s.M y) := by
  have hT : ∀ p st, 0 < p → stateIn (fsQL π p st) = some st := fun p st hp => stateIn_fsQL π hp st
  obtain ⟨-, hans, hheap⟩ := chainIR_sem c π L (hs_posL hs) hq ht (N := nChain pX)
    (by rw [nChain_eq]; norm_num) (tabW_chTabL c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQL, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChain pX) (st₀ := zeroDL) hT hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChain pX) (st₀ := zeroDL) (L := L) (T := fsQL π) hT hS).1
  have hpl : p < (scanC (fsQL π) (nChain pX) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQL π) (nChain pX) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [show chainL = chainIR (posL (piSize pX)) (nChain pX) chTabL sdL from rfl, hans p hpl m hm, hg]

end Lvm.X
