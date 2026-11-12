-- New for lvm (INB): `hinb` for the assembled node programs `QAsm.Q cfg20` and `QAsm.Q cfg8`
-- (WP-16a's `LvmQAsmProg`): WP-16a's position classes cover the cap bits (`capCov_pos`), Q_sig and
-- Q_arith have no `readd` (decided), and `LvmQAsmInbNode.hinb_node`/`inb_of_m3` do the rest.
import LvmQAsmInbNode
import LvmQAsmProg

/-!
# `hinb` for `Q20` and `Q8`

* **`posSpecs_hit`**: every output of an opening's lane-`l` row (`laneOuts`) is an output of a row of
  lane class `l` (`posSpecs`, lvm2 EV-DIET B), at its `posCell`; **`posSpecs_bit`** for the bit cells.
* **`capCov_pos`**: the position classes `posSpecs C bpl` (one `BITS` row per 8 padded positions,
  `nRows`, per lane) put a `bit` output on every cap bit cell `bitBase k + H·j + z`, `j < padT t`, `z < H`,
  given that their cells lie inside `Q` (`PosCellsLt`, a static bound like Q_sig's `SigCellsLt`,
  independent of the placement).
* **`hinb20`**: `nodeSound_layout`'s `hinb` at WP-16a's `P20` node program (`lay cfg20`, `sigIn cfg20`,
  `qarith cfg20`, `nK cfg20`, `0`, `aux cfg20 D`), from `nodeSound_layout`'s `hT`, `hst`, `hQ`, `hqlt`
  and `PosCellsLt`. **`inb8`**: the same fact for `Q cfg8` on any stack with `M3Holds`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-! ## The position classes cover the cap bits -/

/-- The position classes' cells lie inside `Q` (as Q_sig's `SigCellsLt`): per lane class `l` and class
row `r = (k, o, x, sb)`, the word cell (a stream lane) and every output cell (`posOc`). Independent of
the placement `bpl`. -/
def PosCellsLt (Q : Program) (C : QCfg) : Prop :=
  ∀ l < nPosCls C, ∀ r ∈ posRows C l, ansLane C.p (r.2.1.pe + r.2.2.1) + l < Q.cells .K ∧
    ∀ j < (lnOuts C.p l).length, posOc C l (lnOuts C.p l) r j < Q.cells .K

theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simp; omega
  · have := @Nat.lt_log2_self (n - 1); rw [Nat.pow_succ] at this ⊢; omega

theorem filter_range_lt : ∀ (n m : Nat),
    (List.range n).filter (fun z => decide (z < m)) = List.range (min n m)
  | 0, m => by simp
  | n + 1, m => by
    rw [List.range_succ, List.filter_append, filter_range_lt n m]
    by_cases h : n < m
    · rw [show min (n + 1) m = min n m + 1 by omega, List.range_succ, show min n m = n by omega]
      simp [h]
    · rw [show min (n + 1) m = min n m by omega]; simp [h]

/-- The bit outputs of lane `l`'s row: `bit 0 … bit (laneBits − 1)`. -/
theorem laneOuts_bits (H l : Nat) :
    ((List.range 64).filter (fun z => decide (64 * l + z < 8 * H))).map
      (fun z => ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat)) =
      (List.range (laneBits H l)).map (fun z => ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat)) := by
  have hf : (List.range 64).filter (fun z => decide (64 * l + z < 8 * H)) = List.range (min 64 (8 * H - 64 * l)) := by
    rw [← filter_range_lt]
    congr 1; funext y; exact decide_eq_decide.mpr (by omega)
  rw [hf]; rfl

/-- The first outputs of lane `l`'s row are its bits. -/
theorem laneOuts_bit {H l z : Nat} (hz : z < 64) (h : 64 * l + z < 8 * H) :
    z < (laneOuts H l).length ∧ (laneOuts H l).getD z (.bit 0, 0, 0) = (.bit z, 0, 64 * l + z) := by
  unfold laneOuts
  rw [laneOuts_bits]
  have hl : z < ((List.range (laneBits H l)).map fun z => ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat)).length := by
    simp [laneBits]; omega
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl]
  simp

theorem mem_laneOuts_bit {H l z : Nat} (hz : z < 64) (h : 64 * l + z < 8 * H) :
    ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat) ∈ laneOuts H l := by
  obtain ⟨h1, h2⟩ := laneOuts_bit hz h
  rw [← h2, List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1

/-- An output of lane `l`'s row: a bit `z < laneBits` or a field `lo`/`hi` of a position `i < 8` in the
lane. -/
theorem mem_laneOuts {H l : Nat} {e : BOut × Nat × Nat} (h : e ∈ laneOuts H l) :
    (∃ z < laneBits H l, e = (.bit z, 0, 64 * l + z)) ∨
    ∃ i < 8, ((fields H i).1.1 = l ∧
        e = (.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2, 1, i)) ∨
      ((fields H i).2.1 = l ∧
        e = (.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2, 2, i)) := by
  unfold laneOuts at h
  rw [laneOuts_bits, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨z, List.mem_range.mp hz, rfl⟩
  · right
    obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    rw [List.mem_append] at h
    rcases h with h | h <;> split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    · exact Or.inl ⟨‹_›, h⟩
    · exact Or.inr ⟨‹_›, h⟩

/-- **No two outputs of a lane's row have one word function** (`1 ≤ H`): bits by their index; a `lo`
field has `d = 0`, a `hi` field `d = m₁ ≥ 1` (or `m = H − m₁ = 1 ≠ m₁` when `H = 1`); two `lo`s (two `hi`s)
of the lane start at bit `64 l + z` (`64 l + z = s + m₁`), so their positions agree. -/
theorem laneOuts_inj {H l : Nat} (hH : 1 ≤ H) {e e' : BOut × Nat × Nat} (he : e ∈ laneOuts H l)
    (he' : e' ∈ laneOuts H l) (h : e.1 = e'.1) : e = e' := by
  have key : ∀ {i i' : Nat}, i * H = i' * H → i = i' := fun h => Nat.eq_of_mul_eq_mul_right hH h
  rcases mem_laneOuts he with ⟨z, -, rfl⟩ | ⟨i, -, ⟨hl, rfl⟩ | ⟨hl, rfl⟩⟩ <;>
  rcases mem_laneOuts he' with ⟨z', -, rfl⟩ | ⟨i', -, ⟨hl', rfl⟩ | ⟨hl', rfl⟩⟩ <;>
  simp only [BOut.bit.injEq, BOut.fld.injEq, reduceCtorEq] at h
  · rw [h]
  all_goals
    simp only [fields] at hl hl' h ⊢
    generalize hs : i * H = s at hl h ⊢
    generalize hs' : i' * H = s' at hl' h ⊢
  · obtain ⟨h1, -, -⟩ := h
    have : s = s' := by omega
    subst this; rw [key (hs.trans hs'.symm)]
  · obtain ⟨h1, h2, h3⟩ := h
    split_ifs at h1 h2 h3 hl hl' <;> omega
  · obtain ⟨h1, h2, h3⟩ := h
    split_ifs at h1 h2 h3 hl hl' <;> omega
  · obtain ⟨h1, h2, h3⟩ := h
    have : s = s' := by split_ifs at h1 h2 h3 hl hl' <;> omega
    subst this; rw [key (hs.trans hs'.symm)]

/-- `find?` by word function returns the output itself. -/
theorem find?_out {L : List (BOut × Nat × Nat)} {e : BOut × Nat × Nat} (he : e ∈ L)
    (hu : ∀ e' ∈ L, e'.1 = e.1 → e' = e) : L.find? (fun e' => e'.1 == e.1) = some e := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    rw [List.find?_cons]
    by_cases ha : a.1 = e.1
    · rw [beq_iff_eq.mpr ha, hu a (List.mem_cons_self ..) ha]
    · rw [show (a.1 == e.1) = false from beq_eq_false_iff_ne.mpr ha]
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl ha
      · exact ih he fun e' h' => hu e' (List.mem_cons_of_mem _ h')

theorem mem_lnOps {p : Params} {l : Nat} {ko : Nat × OpenInfo} :
    ko ∈ lnOps p l ↔ ko.1 < (opens p).length ∧ ko.2 = (opens p).getD ko.1 default ∧ l < nLanes ko.2.L.height := by
  obtain ⟨k, o⟩ := ko
  simp only [lnOps, List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', hk, rfl, rfl⟩, hl⟩; exact ⟨hk, rfl, hl⟩
  · rintro ⟨hk, rfl, hl⟩; exact ⟨⟨k, hk, rfl, rfl⟩, hl⟩

theorem le_foldl_max : ∀ (L : List Nat) (a : Nat), a ≤ L.foldl max a
  | [], _ => le_refl _
  | b :: L, a => le_trans (le_max_left a b) (le_foldl_max L (max a b))

theorem mem_le_foldl_max : ∀ {L : List Nat} {x : Nat} (a : Nat), x ∈ L → x ≤ L.foldl max a
  | b :: L, x, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (le_foldl_max L _)
    · exact mem_le_foldl_max (L := L) (max a b) h

theorem laneBits_le_lnBits {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l) :
    laneBits ko.2.L.height l ≤ lnBits p l :=
  mem_le_foldl_max 0 (List.mem_map.mpr ⟨ko, h, rfl⟩)

theorem lt_nPosCls {C : QCfg} {k l : Nat} (hk : k < (opens C.p).length)
    (hl : l < nLanes ((opens C.p).getD k default).L.height) : l < nPosCls C := by
  have hm : ((opens C.p).getD k default) ∈ opens C.p := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  exact lt_of_lt_of_le hl (mem_le_foldl_max 0 (List.mem_map.mpr ⟨_, hm, rfl⟩))

theorem mem_foldl_addNew {α : Type} (f : α → BOut) :
    ∀ (L : List α) (a : List BOut) (u : BOut), u ∈ a → u ∈ L.foldl (fun a e => addNew a (f e)) a
  | [], _, _, h => h
  | e :: L, a, u, h => mem_foldl_addNew f L _ u (by show u ∈ addNew a (f e); unfold addNew; split <;> simp [h])

theorem mem_foldl_addNew' {α : Type} (f : α → BOut) :
    ∀ (L : List α) (a : List BOut) {e : α}, e ∈ L → f e ∈ L.foldl (fun a e => addNew a (f e)) a
  | e' :: L, a, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_addNew f L _ _ (by show f e ∈ addNew a (f e); unfold addNew; split <;> simp_all)
    · exact mem_foldl_addNew' f L _ h

theorem mem_lnFlds_of (p : Params) (l : Nat) :
    ∀ (ops : List (Nat × OpenInfo)) (a : List BOut),
      (∀ u ∈ a, u ∈ ops.foldl (fun a ko => (laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a) a) ∧
      ∀ ko ∈ ops, ∀ e ∈ laneFlds ko.2.L.height l,
        e.1 ∈ ops.foldl (fun a ko => (laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a) a
  | [], _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | ko :: ops, a => by
    obtain ⟨h1, h2⟩ := mem_lnFlds_of p l ops ((laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a)
    refine ⟨fun u hu => h1 u (mem_foldl_addNew (fun e : BOut × Nat × Nat => e.1) _ _ u hu), fun ko' hko e he => ?_⟩
    rcases List.mem_cons.mp hko with rfl | hko
    · exact h1 _ (mem_foldl_addNew' (fun e : BOut × Nat × Nat => e.1) _ _ he)
    · exact h2 ko' hko e he

/-- **Every output of an opening's lane-`l` row is a class output.** -/
theorem mem_lnOuts {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l)
    {e : BOut × Nat × Nat} (he : e ∈ laneOuts ko.2.L.height l) : e.1 ∈ lnOuts p l := by
  unfold laneOuts at he
  rw [laneOuts_bits, List.mem_append] at he
  unfold lnOuts
  rcases he with he | he
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
    refine List.mem_append_left _ (List.mem_map.mpr ⟨z, List.mem_range.mpr ?_, rfl⟩)
    exact lt_of_lt_of_le (List.mem_range.mp hz) (laneBits_le_lnBits h)
  · exact List.mem_append_right _ ((mem_lnFlds_of p l _ []).2 ko h e he)

/-- A class output that is not the opening's lies past its bits. -/
theorem laneBits_le_of_find {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l) {j : Nat}
    (hn : (laneOuts ko.2.L.height l).find? (fun e => e.1 == (lnOuts p l).getD j (.bit 0)) = none) :
    laneBits ko.2.L.height l ≤ j := by
  by_contra hj
  have hb : j < lnBits p l := lt_of_lt_of_le (by omega) (laneBits_le_lnBits h)
  have hu : (lnOuts p l).getD j (.bit 0) = .bit j := by
    unfold lnOuts
    rw [List.getD_append _ _ _ _ (by simpa using hb)]
    simp [hb]
  have hm := mem_laneOuts_bit (H := ko.2.L.height) (l := l) (z := j) (by simp only [laneBits] at hj; omega)
    (by simp only [laneBits] at hj; omega)
  rw [List.find?_eq_none] at hn
  exact hn _ hm (by rw [hu]; simp)

theorem mem_posRowsAux (u l : Nat) :
    ∀ (b : Nat) (ops : List (Nat × OpenInfo)) {r : Nat × OpenInfo × Nat × Nat}, r ∈ posRowsAux u l b ops →
      (r.1, r.2.1) ∈ ops ∧ r.2.2.1 < nRows r.2.1 ∧ b ≤ r.2.2.2 ∧
        r.2.2.2 + (u - laneBits r.2.1.L.height l) ≤ b + spTot u l ops
  | b, [], r, h => by cases h
  | b, (k, o) :: ops, r, h => by
    simp only [posRowsAux, List.mem_append, List.mem_map, List.mem_range] at h
    simp only [spTot, List.map_cons, List.sum_cons] at *
    rcases h with ⟨x, hx, rfl⟩ | h
    · dsimp only
      refine ⟨List.mem_cons_self .., hx, by omega, ?_⟩
      have : x * (u - laneBits o.L.height l) + (u - laneBits o.L.height l) ≤
          nRows o * (u - laneBits o.L.height l) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hx
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := mem_posRowsAux u l _ ops h
      exact ⟨List.mem_cons_of_mem _ h1, h2, by omega, by unfold spTot at h4; omega⟩

theorem posRowsAux_hit (u l : Nat) :
    ∀ (b : Nat) (ops : List (Nat × OpenInfo)) {k : Nat} {o : OpenInfo} {x : Nat}, (k, o) ∈ ops → x < nRows o →
      ∃ sb, (k, o, x, sb) ∈ posRowsAux u l b ops
  | b, [], k, o, x, h, _ => by cases h
  | b, (k', o') :: ops, k, o, x, h, hx => by
    simp only [posRowsAux, List.mem_append, List.mem_map, List.mem_range]
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨_, Or.inl ⟨x, hx, rfl⟩⟩
    · obtain ⟨sb, hs⟩ := posRowsAux_hit u l _ ops h hx
      exact ⟨sb, Or.inr hs⟩

/-- **The class row of an opening's output**: output `e` of lane `l` of answer `x` of opening `k` is
output `jo` (`lnOuts[jo] = e.1`) of a row `y` of lane class `l`, with the cell `posCell C k o x e`. -/
theorem posSpecs_hit (C : QCfg) (bpl : Nat → Nat → Bool × Nat) {k l x : Nat} (hk : k < (opens C.p).length)
    (hl : l < nLanes ((opens C.p).getD k default).L.height) (hx : x < nRows ((opens C.p).getD k default))
    {e : BOut × Nat × Nat} (he : e ∈ laneOuts ((opens C.p).getD k default).L.height l) :
    ∃ S ∈ posSpecs C bpl, S.n ≤ 2 ^ S.τ ∧ S.rd = true ∧ ∃ y < S.n,
      S.wc y = ansLane C.p (((opens C.p).getD k default).pe + x) + l ∧
      ∃ jo < S.outs.length, S.out jo = e.1 ∧ S.oc jo y = posCell C k ((opens C.p).getD k default) x e := by
  have hko : (k, (opens C.p).getD k default) ∈ lnOps C.p l := mem_lnOps.mpr ⟨hk, rfl, hl⟩
  obtain ⟨sb, hr⟩ := posRowsAux_hit (lnOuts C.p l).length l (spBase C l) (lnOps C.p l) hko hx
  have hr' : (k, (opens C.p).getD k default, x, sb) ∈ posRows C l := hr
  obtain ⟨y, hy, hry⟩ := List.mem_iff_getElem.mp hr'
  have hu := mem_lnOuts hko he
  have hjo := List.idxOf_lt_length_of_mem hu
  have hH : 1 ≤ ((opens C.p).getD k default).L.height := by unfold nLanes at hl; omega
  have hg : (posRows C l).getD y default = (k, (opens C.p).getD k default, x, sb) := by
    rw [List.getD_eq_getElem _ _ hy, hry]
  have hn : (posSpec C bpl l).n ≤ 2 ^ (posSpec C bpl l).τ := by
    rw [posSpec_n, posSpec_τ]; exact le_two_pow_clog2 _
  have hy' : y < (posSpec C bpl l).n := by rw [posSpec_n]; exact hy
  have hjo' : (lnOuts C.p l).idxOf e.1 < (posSpec C bpl l).outs.length := by rw [posSpec_outs]; exact hjo
  refine ⟨posSpec C bpl l, List.mem_map_of_mem (List.mem_range.mpr (lt_nPosCls hk hl)), hn, posSpec_rd C bpl l,
    y, hy', ?_, (lnOuts C.p l).idxOf e.1, hjo', ?_, ?_⟩
  · rw [posSpec_wc, hg]
  · rw [BSpec.out, posSpec_outs, List.getD_eq_getElem _ _ hjo, List.getElem_idxOf hjo]
  · rw [posSpec_oc, hg]
    unfold posOc
    dsimp only
    rw [List.getD_eq_getElem _ _ hjo, List.getElem_idxOf hjo,
      find?_out he fun e' h' hq => laneOuts_inj hH h' he hq]

/-- **A class row's cells lie inside `Q`** (`PosCellsLt`). -/
theorem posCellsLt_spec {Q : Program} {C : QCfg} (hpc : PosCellsLt Q C) (bpl : Nat → Nat → Bool × Nat)
    {S : BSpec} (hS : S ∈ posSpecs C bpl) {y : Nat} (hy : y < S.n) :
    (S.rd = true → S.wc y < Q.cells .K) ∧ ∀ j < S.outs.length, S.oc j y < Q.cells .K := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hS
  rw [posSpec_n] at hy
  have h := hpc l (List.mem_range.mp hl) _ (List.getElem_mem hy)
  refine ⟨fun _ => ?_, fun j hj => ?_⟩
  · rw [posSpec_wc, List.getD_eq_getElem _ _ hy]; exact h.1
  · rw [posSpec_outs] at hj
    rw [posSpec_oc, List.getD_eq_getElem _ _ hy]; exact h.2 j hj

/-- **The bit cell of a position's bit** (`j < padT t`, `z < H`, `n = (j % 8)·H + z`): output `bit (n % 64)`
of lane `n / 64` at answer `j / 8`, at a row of lane class `n / 64`. -/
theorem posSpecs_bit (C : QCfg) (bpl : Nat → Nat → Bool × Nat) {k j z : Nat} (hk : k < (opens C.p).length)
    (hj : j < padT ((opens C.p).getD k default).L.t) (hz : z < ((opens C.p).getD k default).L.height) :
    ∃ S ∈ posSpecs C bpl, S.n ≤ 2 ^ S.τ ∧ S.rd = true ∧ ∃ y < S.n,
      S.wc y = ansLane C.p (((opens C.p).getD k default).pe + j / 8) +
        (j % 8 * ((opens C.p).getD k default).L.height + z) / 64 ∧
      ∃ jo < S.outs.length, S.out jo = .bit ((j % 8 * ((opens C.p).getD k default).L.height + z) % 64) ∧
        S.oc jo y = bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z := by
  generalize hn : j % 8 * ((opens C.p).getD k default).L.height + z = n
  have h7 : j % 8 * ((opens C.p).getD k default).L.height ≤ 7 * ((opens C.p).getD k default).L.height :=
    Nat.mul_le_mul_right _ (by omega)
  have hl0 : n / 64 < nLanes ((opens C.p).getD k default).L.height := by unfold nLanes; omega
  have hx : j / 8 < nRows ((opens C.p).getD k default) := by unfold nRows; omega
  have hdm := Nat.div_add_mod n 64
  have hm := mem_laneOuts_bit (H := ((opens C.p).getD k default).L.height) (l := n / 64) (z := n % 64)
    (Nat.mod_lt _ (by norm_num)) (by omega)
  obtain ⟨S, hS, hτ, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ := posSpecs_hit C bpl hk hl0 hx hm
  refine ⟨S, hS, hτ, hrd, y, hy, hwc, jo, hjo, hout, ?_⟩
  rw [hoc]
  generalize (opens C.p).getD k default = o at hj hz hn h7 ⊢
  generalize hH : o.L.height = H at hz hn h7 ⊢
  have hnH : n / H = j % 8 := by
    rw [← hn, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hz, Nat.zero_add]
  have hnm : n % H = z := by
    rw [← hn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  rw [show 64 * (n / 64) + n % 64 = n by omega]
  have hjj : 8 * (j / 8) + n / H = j := by rw [hnH]; omega
  simp only [posCell, hH, hjj, if_pos hj, hnm]

/-- **The position classes cover the cap bits.** -/
theorem capCov_pos (C : QCfg) (Q : Program) (aux : List Tab) (bpl : Nat → Nat → Bool × Nat)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) : CapCov C.p Q (lay C) aux := by
  intro k hk j hj z hz
  obtain ⟨S, hS, hτ, -, y, hy, -, jo, hjo, hout, hoc⟩ := posSpecs_bit C bpl hk hj hz
  have hc := posCellsLt_spec hpc bpl hS hy
  exact ⟨S, haux _ hS, hτ, y, hy, hc.1, hc.2, jo, hjo, _, Nat.mod_lt _ (by norm_num), hout, hoc⟩

theorem posSpecs_aux (C : QCfg) (D : QData) {S : BSpec} (h : S ∈ posSpecs C fun c => bplOf D (6 + c)) :
    S.tab ∈ aux C D :=
  List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_right _ h))

/-! ## Decided: Q_sig reads no cell by address

Q_arith's fact `noReaddSegs (qarith C (p2C C)).2 = true` is a hypothesis (`hna`) of `hinb20`/`inb8`
(WP-16a2): with HAR's full Q_arith the kernel cannot evaluate it (`List.mergeSort` in the table phase
does not reduce; with a structural sort the table gadget alone exceeds 12 GB at `P8`). Natively it holds
(`P8`: 33,736 segments, no `readd`); a structural proof (no gadget of Q_arith emits a `readd`) is owed. -/

set_option maxRecDepth 100000 in
theorem noReadd_sig20 : noReaddSegs (qsig (sigIn cfg20) (p1C cfg20)).2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noReadd_sig8 : noReaddSegs (qsig (sigIn cfg8) (p1C cfg8)).2 = true := by decide +kernel

theorem qlt_le_nK20 (hQ : QOk P20 (lay cfg20)) : (lay cfg20).qt + (qltData P20 (lay cfg20)).length ≤ nK cfg20 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg20 + 3 * 2 ^ 11 ≤ qtB cfg20 + 2 ^ 13 + 2 ^ 15
  omega

theorem qlt_le_nK8 (hQ : QOk P8 (lay cfg8)) : (lay cfg8).qt + (qltData P8 (lay cfg8)).length ≤ nK cfg8 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg8 + 3 * 2 ^ 11 ≤ qtB cfg8 + 2 ^ 13 + 2 ^ 16
  omega

/-! ## `hinb` at `P20` (`nodeSound_layout`'s form) -/

section P20

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}

/-- **`hinb` for WP-16a's `P20` node program** (`NodeHyp.hinb`): from `nodeSound_layout`'s `hT`,
`hst`, `hQ`, `hqlt` and the position classes' cell bounds. -/
theorem hinb20 {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D) (arrsX x))
    (hQ : QOk P20 (lay cfg20))
    (hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
          ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : noReaddSegs (qarith cfg20 (p2C cfg20)).2 = true) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true :=
  hinb_node hT hst hQ (qlt_le_nK20 hQ)
    (capCov_pos cfg20 _ (aux cfg20 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc)
    noReadd_sig20 hna hqlt

end P20

/-! ## `inb` at `P8` (any stack with `M3Holds`) -/

section P8

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {D : QData} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Q cfg8) pl groups arrs (aux cfg8 D), t.τ ≤ L.μ}

/-- **Every `readd` of WP-16a's `P8` node program finds its cell** on a stack with `M3Holds` (in
`AuxH0`), with the program check, Q_link's static checks, the `QLT` inputs and the position classes'
cell bounds. -/
theorem inb8 {q : Column L.μ} (hwf : (Q cfg8).wf = true)
    (H0 : AuxH0 (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q) (hQ : QOk P8 (lay cfg8))
    (htab : ∀ y < (qltData P8 (lay cfg8)).length,
      (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q).getD ((lay cfg8).qt + y) 0 = (qltData P8 (lay cfg8)).getD y 0)
    (hpc : PosCellsLt (Q cfg8) cfg8) (hna : noReaddSegs (qarith cfg8 (p2C cfg8)).2 = true) :
    ((Q cfg8).interp (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)
      (inEOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)).inb = true :=
  inb_of_m3 (p := P8) (lay := lay cfg8) (I := sigIn cfg8) (qa := qarith cfg8) hwf H0 hQ
    (fun y hy => ⟨by have := qlt_le_nK8 hQ; omega, htab y hy⟩)
    (capCov_pos cfg8 _ (aux cfg8 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg8 D h) hpc)
    noReadd_sig8 hna

end P8

end Lvm.QAsm
