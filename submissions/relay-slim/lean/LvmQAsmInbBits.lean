-- New for lvm (INB): the `BITS` outputs on the seed (committed) memory, without `inb`. Adapted from
-- WP-9b `LvmM3Aux.aux_read`/`aux_read_at` and WP-12b `LvmBitsTab.out_sound`: the same proofs with
-- their last step (`seedMem_eq_interp`, which needs `inb` through `interp_unique`) dropped, so the
-- conclusions are about `seedMem` (`Q.seedMem (witOf q) (inKOf q) (inEOf q)`) instead of `interpMem`.
import LvmBitsTab

/-!
# `BITS` outputs on the committed memory

`AuxH0` is WP-9b's `AuxHyps` without `wf`, `inj`'s use for the interpreter and `inb`. **`out_sound0`**:
at a real row of a `BITS` table in `aux`, the output cells of the seed memory hold the word functions
of the row's word. **`seedK_bit`**: a `bit z` output cell holds `0` or `1`.
-/

set_option autoImplicit false

namespace Lvm.Inb

open LeanVM.Parameters LeanVM.Protocol CompPoly Lvm Lvm.Bits Lvm.M3 Lvm.Loop Lvm.BitsTab

section Aux

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- WP-9b's `AuxHyps` without `wf` and `inb`. -/
structure AuxH0 (q : Column L.μ) : Prop where
  grp : GrpOk Q groups
  inOk : InOk Q arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  holds : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q

/-- The seed memory's `K` cells on the stack `q`. -/
noncomputable def seedK (q : Column L.μ) : Nat → FK :=
  (Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
    (inEOf Q pl groups arrs aux L hτ q)).k

/-- **An auxiliary table's read is a cell of the interpreter's run** (the `BITS` bridge). At row `x`
of auxiliary table `k` (instance table `groups.length + arrs.length + k`), the read `r`'s
separator, address and value limbs, evaluated on the row, are those of cell `e` of memory `τ` of
`seedMem (witOf q) (inKOf q) (inEOf q)`, for some `e` below the cell count. -/
theorem aux_read0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) :
    ∃ τ e, e < Q.cells τ ∧ r.1.sep = sep τ ∧
      CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) r.1.addr =
        FK.toBF64 (FK.x ^ e) ∧
      ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
          (r.1.val.getD l []) =
        FK.toBF64 ((limbsOf τ ((Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ e)).getD l 0) := by
  set W := witOf Q pl groups arrs aux L hτ q
  set inK := inKOf Q pl groups arrs aux L hτ q
  set inE := inEOf Q pl groups arrs aux L hτ q
  have hget := get_aux Q pl groups arrs aux hk hj
  set row := (lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x
  have hrd : r ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).reads := by rw [hget]; exact hr
  have hu : evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, x, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q
    H.holds.2.1 H.holds.2.2.1 H.cnt H.len _ hu)
  obtain ⟨m', -, hm', he⟩ := seed_key Q pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds q hs
  obtain ⟨τ, e, hec, h1, h2, h3⟩ := Q.seed_cases W inK inE hm'
  have hkey : keyT (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r)) =
      keyT (encT m') := hks.symm.trans he
  have hcoord : ∀ i (hi : i < 16), i ≠ 2 →
      (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r))[i] = (encT m')[i] :=
    fun i hi hi2 ↦ keyT_coord hkey i hi hi2
  refine ⟨τ, e, hec, ?_, ?_, fun l hl ↦ ?_⟩
  · have := hcoord 0 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      if_true, MvPolynomial.eval_C] at this
    exact (FK.toBF64_injective this).trans h1
  · have := hcoord 1 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show (1 : ℕ) ≠ 0 from by decide, if_true, if_false, CPoly.eval_toMv] at this
    rw [this, h2]
  · have := hcoord (l + 3) (by omega) (by omega)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show l + 3 ≠ 0 from by omega, show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega,
      if_false, Nat.add_sub_cancel, CPoly.eval_toMv] at this
    rw [this, h3]


/-- **An auxiliary table's read at a known address is that cell of the interpreter's run**: if the
read names memory `τ` and evaluates its address to `g^a` with `a` below the cell count, its value
limbs are cell `a`'s. -/
theorem aux_read_at0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) {τ : Ty} {a : ℕ} (hsep : r.1.sep = sep τ) (ha : a < Q.cells τ)
    (haddr : CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
      r.1.addr = FK.toBF64 (FK.x ^ a)) :
    ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
        (r.1.val.getD l []) =
      FK.toBF64 ((limbsOf τ ((Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ a)).getD l 0) := by
  obtain ⟨τ', e, he, h1, h2, h3⟩ := aux_read0 Q pl groups arrs aux L hτ q H hk hj x hr
  obtain rfl : τ' = τ := sep_inj' (h1.symm.trans hsep)
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ ↦ by cases σ <;> simp
  obtain rfl : e = a := H.inj _ _ (lt_of_lt_of_le he (hN _)) (lt_of_lt_of_le ha (hN _))
    (FK.toBF64_injective (h2.symm.trans haddr))
  exact h3


/-- **`BITS` soundness through the bus.** At a real row `x` of a `BITS` table of `aux`, whose
cells lie below `Q.cells .K`, the row's word `w` is the word cell's value (when `rd`) and output
cell `oc j x` holds output `j`'s word function of `w`. -/
theorem out_sound0 (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K) :
    ∃ w : FK, (S.rd = true → seedK Q pl groups arrs aux L hτ q (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        seedK Q pl groups arrs aux L hτ q (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp hS
  have hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hT : (lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩ = S.tab :=
    (get_aux Q pl groups arrs aux hk hj).trans hak
  have hxT : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by
    rw [hT]; show x < 2 ^ S.τ; omega
  set xF : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ) := ⟨x, hxT⟩
  set u := CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ xF) with hu
  set M := Q.seedMem (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)
  have hrow : S.row x = x := if_pos hx
  -- the fixed address columns
  have hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a →
      u c = FK.toBF64 (FK.x ^ a x) := by
    intro c a hc hcol
    have hcw : c < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
      rw [hT, BSpec.tab_w]; exact hc
    have hf : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf c =
        some fun x => FK.x ^ a (S.row x) := by
      rw [hT, Tab.fixedOf, BSpec.tab_cols S c hc, hcol]; rfl
    have := row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ xF ⟨c, hcw⟩ hf
    rw [hu, CPoly.ext, dif_pos hcw, this, hrow]
  -- a read at a fixed address column is the cell's value
  have hread : ∀ (r : Key × Nat) (c : Nat) (a : Nat → Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      r.1.addr = CPoly.var c → r.1.val = [P] → c < S.width → S.col c = S.adrCol a →
      a x < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k (a x)) := by
    intro r c a P hr hsep haddr hval hc hcol hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at0 Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt
      (by rw [haddr, BitsTab.evalB_var]; exact hfix c a hc hcol) 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- the constraints on the `FK` row
  set v : Nat → FK := fun i => FK.ofBF64 (u i)
  have hcons : ∀ C ∈ cons, evalK v C = 0 := by
    intro C hC
    have hC' : C ∈ aux[k].cons := by rw [hak]; exact hC
    have := aux_cons Q pl groups arrs aux L hτ q H.holds hk hj xF hC'
    rw [evalB_eq] at this
    exact FK.toBF64_injective (this.trans FK.toBF64_zero.symm)
  obtain ⟨-, hout⟩ := row_sound (rowOf_cons hcons)
  have hwid : 66 < S.width := by unfold BSpec.width; omega
  refine ⟨(rowOf v).w, fun hrd => ?_, fun j hj' hv => ?_⟩
  · have h := hread BSpec.wread 66 S.wc (CPoly.var 0)
      (by simp [BSpec.reads, hrd]) rfl rfl rfl hwid (by simp [BSpec.col]) (hw hrd)
    rw [BitsTab.evalB_var] at h
    show M.k (S.wc x) = FK.ofBF64 (u 0)
    rw [h]; rfl
  · have hc : 68 + 2 * j < S.width := by unfold BSpec.width; omega
    have h := hread (S.oread j) (68 + 2 * j) (S.oc j) (outPoly (S.out j))
      (by simp only [BSpec.reads, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨j, hj', rfl⟩)
      rfl rfl rfl hc
      (by rw [BSpec.col, if_neg (by omega), if_pos (by omega),
            show (68 + 2 * j - 68) / 2 = j by omega])
      (ho j hj')
    rw [evalB_eq, rowOf_out, hout _ hv] at h
    exact (FK.toBF64_injective h).symm

theorem and_one_01 (u : UInt64) : u &&& 1 = 0 ∨ u &&& 1 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one u.toNat with h | h
  · left; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_and, Nat.and_one_is_mod, h]
  · right; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_and, Nat.and_one_is_mod, h]

/-- **A `bit` output cell holds `0` or `1`** on the seed memory. -/
theorem seedK_bit (q : Column L.μ) (H : AuxH0 Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K)
    {j z : Nat} (hj : j < S.outs.length) (hb : S.out j = .bit z) (hz : z < 64) :
    seedK Q pl groups arrs aux L hτ q (S.oc j x) = 0 ∨ seedK Q pl groups arrs aux L hτ q (S.oc j x) = 1 := by
  obtain ⟨w, -, h2⟩ := out_sound0 Q pl groups arrs aux L hτ q H S hS hx hn hw ho
  have := h2 j hj (by rw [hb]; exact hz)
  rw [this, hb]
  rcases and_one_01 (w.val >>> z.toUInt64) with h | h
  · left; simp only [BOut.word, h]; rfl
  · right; simp only [BOut.word, h]; rfl

end Aux

end Lvm.Inb
