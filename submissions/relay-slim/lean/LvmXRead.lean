-- adapted from rf-k/submissions/flock-recursive/lean/FRXRead.lean@8bff272b (sections "The
-- domain and the tape", "Straight-line blocks", "One step down the tree", "The leaf and the
-- copy", "The read at a parametric index base"): `Dom4`, `tp`, `ld4_sem`, `capLd_sem`,
-- `nodeChk_sem`, `child_sem`, `WalkSt`, `cpW`, `mask_ltu`, `Dom4.small`, `Dom4.posE_lt`,
-- `tp_posL4`, `tp_len`, `tp_q`, `nodeFlag`, `child_words`, `cpW_entry`, `look_spec`,
-- `getIR_sem`, `nodeBody_sem`, `nodeWalk`, `nodeLoop`, `colIR_sem`, `copyBody_sem`, `copyLoop`,
-- `copyIR_sem` and their `wf_`/`loK_`/`_nw` lemmas.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 2. lvm's
-- nodes are untagged 64-byte queries (a length check, no tag) and its leaves untagged rows (no
-- check; the copy keeps the query's `⌈|q|/8⌉` words and zeroes the rest up to 64).
import LvmXReadDefs

/-!
# The column reads: blocks, one step down the tree, the leaf, the copy

On a domain tape of a SNARK proof (`RdDom`) with the sorted index `Xi` at `bX` (`Sorted4`):

* `cr_look_spec`: the lookup of a digest finds the slot of its first preimage (`ansIdx`) or
  sets `rFd = 0`; it keeps the heap and the registers from `117` on.
* `cr_node_sem`: one machine step down the tree is `xStep`; `cr_nodeLoop`: the 8 steps keep the
  walk's state `crWalk` (the reading under the cap node is the reading under the current
  digest, or the walk has stopped and the reading is an erasure).
* `cr_leaf_sem`: after the leaf lookup, `crQe` and `crX` are such that the copy stores the leaf
  words of the reading (`crCpW`, `crLeafW`); `cr_copy_sem`: the copy of 64 words.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The domain and the tape -/

/-- The tape as the machine reads it. -/
abbrev crTape (c : Digest) (π : Proof) (L : Log) : Array Word := (extractorInput c π L).toArray

/-- A domain tape of a SNARK proof whose `|L|` sits at tape word `pL` (`5 + ⌈|π|/8⌉ = pL`). -/
structure RdDom (pL : ℕ) (c : Digest) (π : Proof) (L : Log) : Prop where
  hs : 5 + (π.size + 7) / 8 = pL
  hq : ∀ e ∈ L, e.1.size < 2 ^ 64
  ht : (extractorInput c π L).length ≤ 2 ^ 64

/-! ## Straight-line blocks -/

theorem cr_wf_ld4 : WF crLd4 := by
  simp +decide only [crLd4, WF, Prim.dst, rQ0, rQ1, rQ2, rQ3, crTA, and_true]

theorem cr_lo_ld4 : Lo crLd4 := by
  simp +decide only [crLd4, Lo, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3, crTA, and_true]

/-- **Four tape words** into `rQ0 … rQ3`. -/
theorem cr_ld4_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : a + 3 < 2 ^ 64)
    (hA : rd s.M crTA = toWord a) :
    [rd (semXIR I crLd4 s).M rQ0, rd (semXIR I crLd4 s).M rQ1, rd (semXIR I crLd4 s).M rQ2,
      rd (semXIR I crLd4 s).M rQ3] =
      [I.getD a 0, I.getD (a + 1) 0, I.getD (a + 2) 0, I.getD (a + 3) 0] := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [crLd4, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rQ0, rQ1, rQ2, rQ3, crTA]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hA, h1, add_one_toWord, add_one_toWord, add_one_toWord, toNat_toWord (by omega),
    toNat_toWord (by omega), toNat_toWord (by omega), toNat_toWord (by omega)]

/-- **The cap node's words**: after `crCapPs ; crLd4`, `rQ0 … rQ3` hold `cap[p / 256]`. -/
theorem cr_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW : ℕ} {cap : List Digest}
    (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 256 < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ3] =
      packBytes (cap[p / 256]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (crCapPs capW)) := by simp +decide only [crCapPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR I (.blk (crCapPs capW)) s).M crTA = toWord (capW + 4 * (p / 256)) := by
    simp only [crCapPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, show (8 : Word) = toWord 8 from rfl, shr_toWord (by omega) (by norm_num),
      show (2 : Word) = toWord 2 from rfl, shl_toWord (by norm_num) (by omega), add_toWord]
    congr 1
    omega
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by omega) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-- The node test `crChkPs`. -/
theorem cr_chk_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I (.blk crChkPs) s).M crB = bW (decide (rd s.M crQn = toWord 64)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [crChkPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, crK, crB]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [eq_bW]; rfl

/-- **The child's offset**: `crTA := X + 1 + 4 · bit_h(p)` at height `h + 1`. -/
theorem cr_child_sem (I : Array Word) (s : St) (hM : Inv s.M) {x p h : ℕ} (hp : p < 2 ^ 64)
    (hh : h + 1 < 64) (hX : rd s.M crX = toWord x) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) :
    rd (semXIR I (.blk crChildPs) s).M crTA = toWord (x + 1 + 4 * (p / 2 ^ h % 2)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [crChildPs, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
    [rd_set_self, rd_set_ne]
  have hb : p / 2 ^ h < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hp
  have hbit : p / 2 ^ h % 2 ≤ 1 := by omega
  rw [hH, h1, hP, hX, show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega),
    Nat.add_sub_cancel, shr_toWord hp (by omega), show (toWord 1 : Word) = 1 from rfl,
    and_one_toWord hb, show (2 : Word) = toWord 2 from rfl, shl_toWord (by omega) (by omega),
    add_toWord, add_one_toWord]
  congr 1
  omega

theorem cr_wf_chk : WF (.blk crChkPs) := by
  simp +decide only [crChkPs, WF, Prim.dst, crK, crB, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_wf_child : WF (.blk crChildPs) := by
  simp +decide only [crChildPs, WF, Prim.dst, crK, crB, crTA]

/-! ## The walk's state -/

/-- **The walk's state at height `h`**: either every entry so far was found and `rQ0 … rQ3`
hold a digest `d` whose descent from height `h` is the descent from the cap node `d₀`, or an
entry was missing (or of another length) and the descent from `d₀` is `none`. -/
def crWalk (L : Log) (d0 : Digest) (p h : ℕ) (M : Mem) : Prop :=
  (rd M crOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    xDescend L 8 d0 p = xDescend L h d p) ∨
  (rd M crOk = 0 ∧ xDescend L 8 d0 p = none)

/-! ## The copy's word -/

/-- What the copy stores as word `t`: tape word `x + 1 + t` if `8 t < ql`, else `0`. -/
def crCpW (I : Array Word) (x : Word) (ql t : ℕ) : Word :=
  if 8 * t < ql then I.getD (x + toWord (1 + t)).toNat 0 else 0

theorem crCpW_zero (I : Array Word) (x : Word) (t : ℕ) : crCpW I x 0 t = 0 := by simp [crCpW]

theorem cr_mask_ltu (v a b : Word) :
    XOp.and.eval v (XOp.sub.eval 0 (XOp.ltu.eval a b)) = if a < b then v else 0 := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_pos h, if_pos h, h1, BitVec.and_allOnes]
  · show v &&& (0 - (if a < b then 1 else 0)) = _
    rw [if_neg h, if_neg h, BitVec.sub_self, BitVec.and_zero]
    rfl

section Read

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}

theorem RdDom.small (hD : RdDom pL c π L) : L.length < 2 ^ 62 := by
  have := tape_entries_end4 c π L hD.hs
  have := cr_len_entries L; have := hD.ht
  omega

theorem RdDom.posE_lt (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    posE4 pL L k + 1 + (L[k].1.size + 7) / 8 + 4 ≤ 2 ^ 64 := by
  have hend := tape_entries_end4 c π L hD.hs
  have hk1 : entryOff L (k + 1) ≤ entryOff L L.length := by
    rcases Nat.lt_or_ge (k + 1) L.length with h | h
    · exact (entryOff_lt L h le_rfl).le
    · rw [show k + 1 = L.length by omega]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have := hD.ht
  simp only [posE4]; omega

theorem cr_tp_posL (hD : RdDom pL c π L) : (crTape c π L).getD pL 0 = toWord L.length := by
  rw [crTape, getD_toArray, tape_getD_posL4 c π L hD.hs]

/-- The entry's length word on the tape. -/
theorem cr_tp_len (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    (crTape c π L).getD (posE4 pL L k) 0 = toWord L[k].1.size := by
  rw [crTape, getD_toArray]; exact tape_entry4 c π L hD.hs hk

/-- The entry's query words on the tape. -/
theorem cr_tp_q (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) {j : ℕ}
    (hj : j < (L[k].1.size + 7) / 8) :
    (crTape c π L).getD (posE4 pL L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0 := by
  rw [crTape, getD_toArray]; exact cr_tape_query c π L hD.hs hk hj

/-- **The machine's node test is WP-5's `e.1.size = 64`.** -/
theorem cr_nodeFlag (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) :
    decide ((crTape c π L).getD (posE4 pL L k) 0 = toWord 64) = decide (L[k].1.size = 64) := by
  have hq := hD.hq _ (List.getElem_mem hk)
  rw [cr_tp_len hD hk]
  exact decide_eq_decide.mpr ⟨fun e => by
    have := congrArg BitVec.toNat e
    rwa [toNat_toWord hq, toNat_toWord (by norm_num)] at this, fun e => by rw [e]⟩

/-- **The child's words**: on a 64-byte node query, the tape words at `X + 1 + 4 b` are the
half `b` picks (WP-5's `win e.1 0` or `win e.1 32`). -/
theorem cr_child_words (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length)
    (h64 : L[k].1.size = 64) {b : ℕ} (hb : b ≤ 1) :
    [(crTape c π L).getD (posE4 pL L k + 1 + 4 * b) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 1) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 2) 0,
      (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + 3) 0] =
      packBytes (if b = 0 then xWin L[k].1 0 else xWin L[k].1 32).toList := by
  have e : (if b = 0 then xWin L[k].1 0 else xWin L[k].1 32) = xWin L[k].1 (8 * (4 * b)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> rfl
  rw [e, cr_pk_digest_eq4]
  have w : ∀ m < 4, (crTape c π L).getD (posE4 pL L k + 1 + 4 * b + m) 0 =
      (packBytes (xWin L[k].1 (8 * (4 * b))).toList).getD m 0 := fun m hm => by
    rw [cr_win_getD L[k].1 (a := 4 * b) (by omega) hm,
      ← cr_tp_q hD hk (j := 4 * b + m) (by omega)]
    congr 1
    omega
  rw [← w 0 (by decide), ← w 1 (by decide), ← w 2 (by decide), ← w 3 (by decide)]
  simp only [Nat.add_zero]

/-- **The copy of a found leaf is its packed words.** -/
theorem cr_cpW_entry (hD : RdDom pL c π L) {k : ℕ} (hk : k < L.length) (t : ℕ) :
    crCpW (crTape c π L) (toWord (posE4 pL L k)) L[k].1.size t =
      crLeafW (some (xQb L[k].1)) t := by
  have hxl := hD.posE_lt hk
  rw [crCpW, crLeafW, Option.getD_some, xQb]
  by_cases ht : 8 * t < L[k].1.size
  · rw [if_pos ht, toWord_add, toNat_toWord (by omega),
      show posE4 pL L k + (1 + t) = posE4 pL L k + 1 + t by omega, cr_tp_q hD hk (by omega)]
  · rw [if_neg ht, cr_pk_getD, if_neg (by rw [cr_size_toList]; omega)]

theorem cr_wf_get : WF (crGet bX) := by
  simp +decide [crGet, WF, Prim.dst, crK, crAd, crX, crQn, and_true]

theorem cr_lo_get : Lo (crGet bX) := by
  simp +decide [crGet, Lo, Prim.dst, regs, crK, crAd, crX, crQn, and_true]

theorem cr_wf_node : WF (crNode bX pL) := by
  have := cr_wf_look bX pL
  simp +decide only [crNode, crGet, crChkPs, crChildPs, crLd4, WF, Prim.dst, crK, crAd, crX, crQn,
    crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_loK_node : LoK (crNode bX pL) := by
  have := cr_loK_look bX pL
  simp +decide only [crNode, crGet, crChkPs, crChildPs, crLd4, LoK, Prim.dst, regs, crK, crAd,
    crX, crQn, crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, this, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

/-- The registers the walk keeps across a node step. -/
theorem cr_node_nw {r : ℕ} (hr : r = crP ∨ r = crWA ∨ r = crHc) : ¬ Writes (crNode bX pL) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r :=
    cr_look_nw bX pL (.inl (by rcases hr with rfl | rfl | rfl <;> decide))
  simp only [crNode, Writes, not_or]
  refine ⟨⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl | rfl <;>
  simp +decide only [crGet, crChkPs, crChildPs, crLd4, Writes, Prim.dst, crK, crAd, crX, crQn,
    crTA, crB, crOk, rQ0, rQ1, rQ2, rQ3, crP, crWA, crHc, List.mem_cons, List.mem_nil_iff,
    exists_eq_or_imp, exists_eq_left, or_false, and_true, not_or, exists_false, not_false_eq_true,
    and_self]

theorem cr_wf_leaf : WF (crLeaf bX pL) := by
  have := cr_wf_look bX pL
  simp +decide only [crLeaf, crGet, WF, Prim.dst, crK, crAd, crX, crQn, crQe, this,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_loK_leaf : LoK (crLeaf bX pL) := by
  have := cr_loK_look bX pL
  simp +decide only [crLeaf, crGet, LoK, Prim.dst, regs, crK, crAd, crX, crQn, crQe, this,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_leaf_nw {r : ℕ} (hr : r = crP ∨ r = crWA) : ¬ Writes (crLeaf bX pL) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r :=
    cr_look_nw bX pL (.inl (by rcases hr with rfl | rfl <;> decide))
  simp only [crLeaf, Writes, not_or]
  refine ⟨?_, ⟨hl, ?_⟩, ?_⟩ <;>
  rcases hr with rfl | rfl <;>
  simp +decide only [crGet, Writes, Prim.dst, crK, crAd, crX, crQn, crQe, crP, crWA,
    List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, and_true, not_or,
    exists_false, not_false_eq_true, and_self]

variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **The lookup** on a sorted index `Xi` held in `X[0..|L|)`: the first preimage's slot when
the target is answered, `rFd = 0` otherwise; the heap and the registers from `117` on are kept. -/
theorem cr_look_spec (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) (t : Digest)
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes t.toList) :
    (∀ k, ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rLo = toWord b ∧
      rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rFd = 1 ∧ Xi b = toWord (posE4 pL L k)) ∧
    (ansIdx L t = none → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M rFd = 0) ∧
    (∀ x, regs ≤ x → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M x = rd s.M x) ∧
    Inv (semXIR (crTape c π L) (lookIR4 bX pL) s).M ∧
    (∀ r, 117 ≤ r → r < regs → rd (semXIR (crTape c π L) (lookIR4 bX pL) s).M r = rd s.M r) := by
  set I := crTape c π L with hI
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s hM (n := L.length) (X := Xi) (cr_tp_posL hD)
    hD.small hT hXs
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hD.hs hD.hq hD.ht hX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I Xi (packBytes t.toList)) (n := L.length)
    (by have := hD.small; omega) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  refine ⟨fun k hk => ?_, fun hk => ?_, l3, inv_sem I (cr_wf_look bX pL) hM,
    fun r hr hr2 => frame I _ s (cr_wf_look bX pL) hM r hr2 (cr_look_nw bX pL (.inl hr))⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, e⟩
    rw [l2, hXs _ hb, e, ansW_entry4 c π L hD.hs hD.hq hD.ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I Xi (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hXs _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]

/-- **After a lookup**: the entry's position and its query length. -/
theorem cr_get_sem (I : Array Word) (s : St) (hM : Inv s.M) {b x : ℕ} (hb : b < 2 ^ 62)
    (hx : x < 2 ^ 64) (hL : rd s.M rLo = toWord b) (hX : rd s.M (bX + b) = toWord x) :
    rd (semXIR I (crGet bX) s).M crX = toWord x ∧ rd (semXIR I (crGet bX) s).M crQn = I.getD x 0 := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [crGet, semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, crK, crAd, crX, crQn]; omega))
    only [rd_set_self, rd_set_ne]
  all_goals
    rw [hL, add_toWord, toNat_toWord (by omega), rd_set_ne (by simp only [crAd, regs] at hbX ⊢; omega),
      rd_set_ne (by simp only [crK, regs] at hbX ⊢; omega), show b + bX = bX + b by omega, hX]
  rw [toNat_toWord hx]

/-- **One machine step down the tree is `xStep`**: from `crOk = 1` with the digest `d` in
`rQ0 … rQ3` at height `h + 1`, the step leaves `crOk = 1` and the child's digest, or `crOk = 0`
when the descent stops. -/
theorem cr_node_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hOk : rd s.M crOk = 1) {d : Digest}
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = packBytes d.toList) :
    (∀ d', xStep L p h d = some d' → rd (semXIR (crTape c π L) (crNode bX pL) s).M crOk = 1 ∧
      [rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ0,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ1,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ2,
        rd (semXIR (crTape c π L) (crNode bX pL) s).M rQ3] = packBytes d'.toList) ∧
    (xStep L p h d = none → rd (semXIR (crTape c π L) (crNode bX pL) s).M crOk = 0) := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crNode, semXIR_ite, hOk, if_neg (by decide), semXIR_seq]
  obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s hM hXs d hT
  have hP1 := (lk5 crP (by decide) (by decide)).trans hP
  have hH1 := (lk5 crHc (by decide) (by decide)).trans hH
  have hO1 := (lk5 crOk (by decide) (by decide)).trans hOk
  generalize semXIR I (lookIR4 bX pL) s = s1 at lk1 lk2 lk3 lk4 hP1 hH1 hO1
  have hs1 := lk4.1
  simp only [regs] at hs1
  rw [semXIR_ite]
  cases hk : ansIdx L d with
  | none =>
    have hn : xStep L p h d = none := by simp [xStep, xFindA_none hk]
    rw [lk2 hk, if_pos rfl]
    refine ⟨fun d' h' => (by rw [hn] at h'; cases h'), fun _ => ?_⟩
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crOk]; omega)
  | some k =>
    obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
    obtain ⟨hkL, hpre⟩ := xFindA_some hk
    rw [hfd, if_neg (by decide)]
    have hxl := hD.posE_lt hkL
    have hsm := hD.small
    obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by omega)
      (by omega) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; omega), hXs b hb, hxb])
    have fG : ∀ r, r = crOk ∨ r = crP ∨ r = crHc → rd (semXIR I (crGet bX) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 (cr_wf_get (bX := bX)) lk4 r
        (by rcases hr with rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl <;>
          simp +decide [crGet, Writes, Prim.dst, crK, crAd, crX, crQn, crOk, crP, crHc, or_false])
    have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
    rw [semXIR_seq]
    generalize semXIR I (crGet bX) s1 = s2 at g1 g2 fG hM2
    have hB := cr_chk_sem I s2 hM2
    rw [g2, cr_nodeFlag hD hkL] at hB
    have fC : ∀ r, r = crOk ∨ r = crP ∨ r = crHc ∨ r = crX →
        rd (semXIR I (.blk crChkPs) s2).M r = rd s2.M r :=
      fun r hr => frame I _ s2 cr_wf_chk hM2 r
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;>
          simp +decide only [crChkPs, Writes, Prim.dst, crK, crB, crOk, crP, crHc, crX,
            List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
    have hM3 := inv_sem I cr_wf_chk hM2
    rw [semXIR_seq]
    generalize semXIR I (.blk crChkPs) s2 = s3 at hB fC hM3
    have hs3 := hM3.1
    simp only [regs] at hs3
    rw [semXIR_ite, hB]
    by_cases hC : L[k].1.size = 64
    · rw [decide_eq_true hC, if_neg bW_ne_zero]
      have hsome : xStep L p h d =
          some (if p / 2 ^ h % 2 = 0 then xWin L[k].1 0 else xWin L[k].1 32) := by
        simp only [xStep, hpre, Option.bind_some, if_pos hC]
      refine ⟨fun d' h' => ?_, fun h' => by rw [hsome] at h'; cases h'⟩
      rw [hsome] at h'
      cases h'
      rw [semXIR_seq]
      have hA := cr_child_sem I s3 hM3 (x := posE4 pL L k) (p := p) (h := h) (by omega) hh
        (by rw [fC _ (.inr (.inr (.inr rfl))), g1])
        (by rw [fC _ (.inr (.inl rfl)), fG _ (.inr (.inl rfl)), hP1])
        (by rw [fC _ (.inr (.inr (.inl rfl))), fG _ (.inr (.inr rfl)), hH1])
      have hM4 := inv_sem I cr_wf_child hM3
      have hO4 : rd (semXIR I (.blk crChildPs) s3).M crOk = 1 := by
        rw [frame I _ s3 cr_wf_child hM3 crOk (by decide) (by
          simp +decide only [crChildPs, Writes, Prim.dst, crK, crB, crTA, crOk]), fC _ (.inl rfl),
          fG _ (.inl rfl), hO1]
      generalize semXIR I (.blk crChildPs) s3 = s4 at hA hM4 hO4
      have hbt : p / 2 ^ h % 2 ≤ 1 := by omega
      refine ⟨by
        rw [frame I _ s4 cr_wf_ld4 hM4 crOk (by decide) (by
          simp +decide only [crLd4, Writes, Prim.dst, rQ0, rQ1, rQ2, rQ3, crTA, crOk, or_false])]
        exact hO4, ?_⟩
      rw [cr_ld4_sem I s4 hM4 (by omega) hA]
      exact cr_child_words hD hkL hC hbt
    · rw [decide_eq_false hC, if_pos bW_false]
      have hnone : xStep L p h d = none := by
        simp only [xStep, hpre, Option.bind_some, if_neg hC]
      refine ⟨fun d' h' => (by rw [hnone] at h'; cases h'), fun _ => ?_⟩
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      exact rd_set_self (by simp only [crOk]; omega)

/-- **One node step keeps the walk's state**, one level down. -/
theorem cr_nodeWalk (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hW : crWalk L d0 p (h + 1) s.M) :
    crWalk L d0 p h (semXIR (crTape c π L) (crNode bX pL) s).M := by
  rcases hW with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · obtain ⟨n1, n2⟩ := cr_node_sem hbX hbX2 hpL hD hX s hM hXs hp hh hP hH hOk hT
    rw [xDescend_succ L h d p] at hc
    cases hn : xStep L p h d with
    | none =>
      rw [hn] at hc
      exact .inr ⟨n2 hn, hc⟩
    | some d' =>
      rw [hn] at hc
      obtain ⟨o1, o2⟩ := n1 d' hn
      exact .inl ⟨o1, d', o2, hc⟩
  · have e : semXIR (crTape c π L) (crNode bX pL) s = s := by
      rw [crNode, semXIR_ite, hOk, if_pos rfl]; rfl
    rw [e]; exact .inr ⟨hOk, hc⟩

/-- **The height loop**: `m` node steps from height `m` reach height `0`; the heap, `crP` and
`crWA` are kept. -/
theorem cr_nodeLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {d0 : Digest} {p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M crP = toWord p → rd s.M crHc = toWord m → crWalk L d0 p m s.M →
      crWalk L d0 p 0 (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      Inv (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crP = rd s.M crP ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crWA = rd s.M crWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := crTape c π L
    have h1 := cr_nodeWalk hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (cr_wf_node (bX := bX) (pL := pL)) hM
    have hH1 := hframeK I (crNode bX pL) s cr_loK_node
    have fr : ∀ r, (r = crP ∨ r = crWA ∨ r = crHc) →
        rd (semXIR I (crNode bX pL) s).M r = rd s.M r :=
      fun r hr => frame I _ s (cr_wf_node (bX := bX) (pL := pL)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (cr_node_nw hr)
    have hM' : Inv (decS crHc (semXIR I (crNode bX pL) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS crHc (semXIR I (crNode bX pL) s)).M crHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by omega)
    have dk : ∀ r, r ≠ crHc → rd (decS crHc (semXIR I (crNode bX pL) s)).M r =
        rd (semXIR I (crNode bX pL) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : crWalk L d0 p m (decS crHc (semXIR I (crNode bX pL) s)).M := by
      unfold crWalk at h1 ⊢
      rw [dk crOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS crHc (semXIR I (crNode bX pL) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [crHc, regs] at *; omega)).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := cr_nodeLoop hD hX hp m _ (by omega) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `crLeaf`, `crX` and `crQe` are such that the copy stores the leaf words of
the reading under the cap node `d₀` (`crLeafW`, zeros for an erasure). -/
theorem cr_leaf_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p : ℕ}
    (hW : crWalk L d0 p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crQe = toWord ql ∧
      ∀ t, crCpW (crTape c π L) (rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crX) ql t =
        crLeafW (crRd L d0 p) t := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crLeaf, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const crQe 0]) (by simp +decide only [WF, Prim.dst, crQe]) hM
  have hQ0 : rd (semXIR I (.blk [.const crQe 0]) s).M crQe = toWord 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crQe]; omega)
  have fr0 : ∀ r, r ≠ crQe → rd (semXIR I (.blk [.const crQe 0]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  have hXs0 : ∀ a < L.length, rd (semXIR I (.blk [.const crQe 0]) s).M (bX + a) = Xi a :=
    fun a ha => by rw [fr0 _ (by simp only [crQe, regs] at hbX ⊢; omega), hXs a ha]
  have hW0 : crWalk L d0 p 0 (semXIR I (.blk [.const crQe 0]) s).M := by
    unfold crWalk at hW ⊢
    rw [fr0 crOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const crQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq]
    have hrd : crRd L d0 p = (xFindA L d).map fun e => xQb e.1 := by
      rw [crRd, hc]; rfl
    rw [hrd]
    obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s0 hM0 hXs0 d hT
    have hQ1 := (lk5 crQe (by decide) (by decide)).trans hQ0
    generalize semXIR I (lookIR4 bX pL) s0 = s1 at lk1 lk2 lk3 lk4 hQ1
    have hs1 := lk4.1
    simp only [regs] at hs1
    rw [semXIR_ite]
    cases hk : ansIdx L d with
    | none =>
      rw [lk2 hk, if_pos rfl, xFindA_none hk]
      refine ⟨0, by norm_num, hQ1, fun t => ?_⟩
      simp [crCpW_zero, crLeafW_none]
    | some k =>
      obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
      obtain ⟨hkL, hpre⟩ := xFindA_some hk
      rw [hfd, if_neg (by decide), hpre, Option.map_some]
      have hxl := hD.posE_lt hkL
      have hsm := hD.small
      have hq := hD.hq _ (List.getElem_mem hkL)
      obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by omega)
        (by omega) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; omega), hXs0 b hb, hxb])
      have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
      rw [semXIR_seq]
      generalize semXIR I (crGet bX) s1 = s2 at g1 g2 hM2
      have hs2 := hM2.1
      simp only [regs] at hs2
      refine ⟨L[k].1.size, hq, ?_, fun t => ?_⟩
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [crQe]; omega), g2, cr_tp_len hD hkL, or_self_eval]
      · have e : rd (semXIR I (.blk [.op .or crQe crQn crQn]) s2).M crX =
            toWord (posE4 pL L k) := by
          simp only [semXIR, runPrims, List.foldl, Prim.run]
          rw [rd_set_ne (by decide), g1]
        rw [e, cr_cpW_entry hD hkL t]
  · rw [hOk, if_pos rfl]
    have hrd : crRd L d0 p = none := by rw [crRd, hc]; rfl
    rw [hrd]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) crQe = _
      rw [runPrims_nil, hQ0], fun t => ?_⟩
    rw [crCpW_zero, crLeafW_none]

end Read

/-! ## The copy -/

theorem cr_wf_copyBody : WF crCopyBody := by
  simp +decide only [crCopyBody, WF, Prim.dst, crV, crMk, crK, crWA, crTA, cr8, cTmp, and_true]

/-- **One copy step**: cell `a + j` gets `crCpW I x ql j`; the pointers advance. -/
theorem cr_copyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a j : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a + j) (ha2 : a + j + 1 < 2 ^ 64) (hj : 8 * (j + 1) < 2 ^ 64)
    (has : a + j < s.M.size) (hA : rd s.M crWA = toWord (a + j))
    (hT : rd s.M crTA = x + toWord (1 + j)) (h8 : rd s.M cr8 = toWord (8 * j))
    (hQ : rd s.M crQe = toWord ql) :
    rd (semXIR I crCopyBody s).M (a + j) = crCpW I x ql j ∧
    (∀ y, regs ≤ y → y ≠ a + j → rd (semXIR I crCopyBody s).M y = rd s.M y) ∧
    rd (semXIR I crCopyBody s).M crWA = toWord (a + (j + 1)) ∧
    rd (semXIR I crCopyBody s).M crTA = x + toWord (1 + (j + 1)) ∧
    rd (semXIR I crCopyBody s).M cr8 = toWord (8 * (j + 1)) ∧
    rd (semXIR I crCopyBody s).M crQe = toWord ql ∧
    rd (semXIR I crCopyBody s).M crP = rd s.M crP := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs ha
  -- the masked word
  have wf1 : WF (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) := by
    simp +decide only [WF, Prim.dst, crV, crMk, crK, and_true]
  have v1 : rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M crV = crCpW I x ql j := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crV, crMk, crK]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hT, h8, hQ, cr_mask_ltu, crCpW]
    by_cases hc : 8 * j < ql
    · rw [if_pos ((toWord_lt_toWord (by omega) hql).2 hc), if_pos hc]
    · rw [if_neg (fun h => hc ((toWord_lt_toWord (by omega) hql).1 h)), if_neg hc]
  have fr1 : ∀ r, r = crWA ∨ r = crTA ∨ r = cr8 ∨ r = crQe ∨ r = crP ∨ r = cOne →
      rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
        .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M r = rd s.M r := fun r hr =>
    frame I _ s wf1 hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [Writes, Prim.dst, crV, crMk, crK, crWA, crTA, cr8, crQe, crP, cOne,
          or_false])
  have hh1 : ∀ y, regs ≤ y → rd (semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe,
      .const crK 0, .op .sub crMk crK crMk, .op .and crV crV crMk])) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crMk, crK, and_true])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
      .op .sub crMk crK crMk, .op .and crV crV crMk])) s
  have e : semXIR I crCopyBody s = semXIR I (.seq (.store crWA crV) (.blk [.op .add crWA crWA cOne,
      .op .add crTA crTA cOne, .const crK 8, .op .add cr8 cr8 crK])) (semXIR I (.seq (.input crV crTA)
      (.blk [.op .ltu crMk cr8 crQe, .const crK 0, .op .sub crMk crK crMk, .op .and crV crV crMk]))
      s) := rfl
  rw [e]
  generalize semXIR I (.seq (.input crV crTA) (.blk [.op .ltu crMk cr8 crQe, .const crK 0,
    .op .sub crMk crK crMk, .op .and crV crV crMk])) s = s1 at v1 fr1 hh1 hM1 hsz1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the store
  have hA1 : rd s1.M crWA = toWord (a + j) := (fr1 _ (.inl rfl)).trans hA
  have hsz : a + j < s1.M.size := by omega
  have st : ∀ i, i ≠ cTmp → rd (storeM s1.M crWA crV) i =
      if i = a + j then rd s1.M crV else rd s1.M i := fun i hi =>
    rd_storeM hM1 hA1 (by simp only [regs]; omega) (by omega) hsz (by decide) (by decide) hi
  rw [semXIR_seq]
  have e2 : semXIR I (.store crWA crV) s1 = ⟨storeM s1.M crWA crV, s1.o⟩ := rfl
  rw [e2]
  have hc1 : rd s1.M cOne = 1 := (fr1 _ (.inr (.inr (.inr (.inr (.inr rfl)))))).trans h1
  have hM2 : Inv (storeM s1.M crWA crV) := inv_sem I (P := .store crWA crV)
    (by simp +decide only [WF, crWA, cTmp]) hM1
  have hs2 := hM2.1
  simp only [regs, size_storeM] at hs2
  have reg : ∀ r, r < 256 → r ≠ cTmp → rd (storeM s1.M crWA crV) r = rd s1.M r := fun r hr hrt => by
    rw [st r hrt, if_neg (by omega)]
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, fun y hy hne => ?_, ?_⟩
  · rw [rd_set_ne (by simp only [cr8]; omega), rd_set_ne (by simp only [crK]; omega),
      rd_set_ne (by simp only [crTA]; omega), rd_set_ne (by simp only [crWA]; omega),
      st _ (by simp only [cTmp]; omega), if_pos rfl, v1]
  · simp only [regs] at hy
    rw [rd_set_ne (by simp only [cr8]; omega), rd_set_ne (by simp only [crK]; omega),
      rd_set_ne (by simp only [crTA]; omega), rd_set_ne (by simp only [crWA]; omega),
      st _ (by simp only [cTmp]; omega), if_neg hne, hh1 y (by simp only [regs]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, size_storeM, crWA, crTA, crK, cr8]; omega))
    only [rd_set_self, rd_set_ne]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), hA1, hc1, add_one_toWord,
      Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), reg _ (by decide) (by decide), fr1 _ (.inr (.inl rfl)), hT,
      hc1]
    show x + toWord (1 + j) + 1 = _
    rw [BitVec.add_assoc, toWord_add_one, Nat.add_assoc]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inl rfl))), h8,
      show (8 : Word) = toWord 8 from rfl, add_toWord]
    congr 1
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inl rfl)))), hQ]
  · rw [reg _ (by decide) (by decide), fr1 _ (.inr (.inr (.inr (.inr (.inl rfl)))))]

/-- **The copy loop**: `m` steps from word `j` store `crCpW I x ql i` at `a + i`,
`j ≤ i < j + m`. -/
theorem cr_copyLoop (I : Array Word) {x : Word} {ql a nw : ℕ} (hql : ql < 2 ^ 64) (ha : regs ≤ a)
    (ha2 : a + nw + 2 < 2 ^ 64) (hnw : nw < 2 ^ 60) :
    ∀ (m j : ℕ) (s : St), j + m ≤ nw → Inv s.M → a + nw ≤ s.M.size →
      rd s.M crWA = toWord (a + j) → rd s.M crTA = x + toWord (1 + j) →
      rd s.M cr8 = toWord (8 * j) → rd s.M crQe = toWord ql →
      (∀ i, j ≤ i → i < j + m →
        rd (iterL (semXIR I crCopyBody) crCw m s).M (a + i) = crCpW I x ql i) ∧
      (∀ y, regs ≤ y → (y < a + j ∨ a + j + m ≤ y) →
        rd (iterL (semXIR I crCopyBody) crCw m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR I crCopyBody) crCw m s).M ∧
      rd (iterL (semXIR I crCopyBody) crCw m s).M crWA = toWord (a + (j + m)) ∧
      rd (iterL (semXIR I crCopyBody) crCw m s).M crP = rd s.M crP
  | 0, j, s, _, hM, _, hA, _, _, _ =>
    ⟨fun i h1 h2 => by omega, fun _ _ _ => rfl, hM, by show rd s.M crWA = _; rw [hA, Nat.add_zero],
      rfl⟩
  | m + 1, j, s, hjm, hM, hsz, hA, hT, h8, hQ => by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := cr_copyBody_sem I s hM hql
      (by simp only [regs] at *; omega) (by omega) (by omega) (by omega) hA hT h8 hQ
    have hM1 := inv_sem I cr_wf_copyBody hM
    have hM' : Inv (decS crCw (semXIR I crCopyBody s)).M := inv_decS hM1 (by decide)
    have dk : ∀ r, r ≠ crCw → rd (decS crCw (semXIR I crCopyBody s)).M r =
        rd (semXIR I crCopyBody s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hsz' : a + nw ≤ (decS crCw (semXIR I crCopyBody s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    have hy : ∀ y, regs ≤ y → y ≠ crCw := fun y hy => by simp only [crCw, regs] at *; omega
    obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I hql ha ha2 hnw m (j + 1) _ (by omega) hM' hsz'
      (by rw [dk _ (by decide), c3])
      (by rw [dk _ (by decide), c4]) (by rw [dk _ (by decide), c5]) (by rw [dk _ (by decide), c6])
    simp only [iterL]
    refine ⟨fun i h1 h2 => ?_, fun y hy1 hy2 => ?_, d3,
      by rw [d4, show j + 1 + m = j + (m + 1) by omega], ?_⟩
    · by_cases hij : i = j
      · subst hij
        rw [d2 _ (by simp only [regs] at *; omega) (.inl (by omega)), dk _ (hy _ (by
          simp only [regs] at *; omega)), c1]
      · exact d1 i (by omega) (by omega)
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), c2 _ hy1 (by omega)]
    · rw [d5, dk _ (by decide), c7]

theorem cr_wf_copy : WF crCopy := by
  simp +decide only [crCopy, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK, crWA, crTA, cr8, crNw,
    crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + 63` get
`crCpW I x ql ·`; every other heap cell is kept; `crWA` ends at `a + 64`. -/
theorem cr_copy_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < 64, rd (semXIR I crCopy s).M (a + i) = crCpW I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) → rd (semXIR I crCopy s).M y = rd s.M y) ∧
    Inv (semXIR I crCopy s).M ∧ rd (semXIR I crCopy s).M crWA = toWord (a + 64) ∧
    rd (semXIR I crCopy s).M crP = rd s.M crP := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hM
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)]) s
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)]) s
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M crNw = toWord 64 ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M crWA = toWord (a + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
        s).M crP = rd s.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ | exact hA | (rw [hX, h1]; all_goals rfl)
  rw [crCopy, semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 64)])
    s = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord 64) s0.M) crCw = toWord 64 :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord 64) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord 64) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw 64 ⟨entryK crCw crNw (toWord 64) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 64 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; omega
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I hql ha ha2 (by norm_num) 64 0
    ⟨entryK crCw crNw (toWord 64) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  refine ⟨fun i hi => d1 i (by omega) (by omega), fun y hy1 hy2 => ?_, d3,
    by rw [d4, Nat.zero_add], ?_⟩
  · rw [d2 y hy1 (by omega)]
    show rd (entryK crCw crNw (toWord 64) s0.M) y = rd s.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  · rw [d5]
    show rd (entryK crCw crNw (toWord 64) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0]

end Lvm.X
