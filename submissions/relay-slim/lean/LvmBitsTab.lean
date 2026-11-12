-- new for lvm (WP-12b): WP-12's `BITS` row (`LvmBits`) as an auxiliary table of WP-9's lvm M3
-- instance (`LvmM3Tab.Tab`), read through the bus (WP-9b `LvmM3Aux`: `aux_read_at`, `aux_cons`).
-- Searched for reuse: WP-9's `InArr.tab` (the fixed address-column pattern, followed here),
-- `LvmM3Loop.evalB_ofPoly2` (the `evalB` transport pattern); FR has no bus-read bit table.
import LvmBits
import LvmM3Aux
import LvmM3FidFixC

/-!
# The `BITS` table and its soundness through the bus

**The table** (`BSpec.tab`). A `BITS` class `S` (one output list for all rows) is a table of
height `2^τ`. Columns:
* `0`: the word `w`; `1 + z` (`z < 64`): the bit column `β_z` (committed);
* `65`: the count column of the word's read; `66`: its address `g^{wc x}` (fixed);
* `67 + 2j`, `68 + 2j`: output `j`'s read count (committed) and address `g^{oc j x}` (fixed).

Constraints (degree 2, `CPoly`): `w + Σ_z x^z·β_z` and `β_z·β_z + β_z`. Reads of the `K` memory:
the word (value polynomial `w`; only when `rd`) and every output `j`, whose value polynomial is
the linear form `Σ_z coef_z·β_z` of `LvmBits` (`outPoly`). Rows `x < n` are the real ones; rows
`n ≤ x < 2^τ` repeat row `0`'s addresses (`BSpec.row`): `CountsNonzero` forbids count-`0` padding
(`rows = 2^τ`), so the honest prover fills them with further reads of row `0`'s cells, their counts
continuing those cells' `g`-power read sequences (finalize counts include them). With `rd = false`
columns `65`, `66` are don't-care (committed / fixed, never read).
A fixed column's closed form is its multilinear extension (`Loop.mle`, `O(2^τ)` for the native
verifier), so `FixOk` holds by definition (`fixOk_tab`).

**Soundness** (`out_sound`): under WP-9b's `AuxHyps` (the hypotheses of `loopir_sound`), at a real
row `x` of a `BITS` table in `aux`, with the cells it names below `Q.cells .K`, there is a word
`w` (the row's) such that the read word cell holds `w` (when `rd`) and output cell `oc j x` holds
`⟨outs[j].word w.val⟩`, in the interpreter's memory: WP-12's `row_sound` transported through
`FK.toBF64` (WP-1's ring isomorphism `ringEquivBF64`).

**Completeness** (`honest_cons`, `honest_out`): the honest row of any word (its bits) makes every
constraint vanish and every output polynomial its word function.
-/

set_option autoImplicit false

namespace Lvm.BitsTab

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

/-! ## `CPoly`s over `FK` -/

/-- A `CPoly`'s value at an `FK` row. -/
def evalK (v : Nat → FK) (P : CPoly) : FK := (P.map fun m => m.1 * (m.2.map v).prod).sum

/-- **`evalB` is `evalK` through `FK.toBF64`.** -/
theorem evalB_eq (u : Nat → K) (P : CPoly) :
    CPoly.evalB u P = FK.toBF64 (evalK (fun i => FK.ofBF64 (u i)) P) := by
  unfold CPoly.evalB evalK
  rw [← FK.ringEquivBF64_apply, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp, map_mul, map_list_prod, List.map_map, FK.ringEquivBF64_apply,
    FK.toBF64_ofBF64]
  rfl

theorem sum_range (g : Nat → FK) : ∀ n, ((List.range n).map g).sum = lsum g n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range g n]; simp [lsum]

theorem evalB_var (u : Nat → K) (i : Nat) : CPoly.evalB u (CPoly.var i) = u i := by
  simp [CPoly.evalB, CPoly.var]

/-! ## The table -/

/-- The word constraint `w + Σ_z x^z·β_z`. -/
def wcons : CPoly := (1, [0]) :: (List.range 64).map fun z => (wt z, [1 + z])

/-- The bit constraint `β_z·β_z + β_z`. -/
def bcons (z : Nat) : CPoly := [(1, [1 + z, 1 + z]), (1, [1 + z])]

/-- The constraints. -/
def cons : List CPoly := wcons :: (List.range 64).map bcons

/-- An output's value polynomial: `Σ_z coef_z·β_z`. -/
def outPoly (o : BOut) : CPoly := (List.range 64).map fun z => (o.coef z, [1 + z])

/-- **A `BITS` class**: `n` real rows of `2^τ`; row `x` reads the word of `K` cell `wc x` (when
`rd`) and writes output `outs[j]` to `K` cell `oc j x`; `pl c` places committed column `c`. -/
structure BSpec where
  /-- Log-height. -/
  τ : Nat
  /-- The real rows. -/
  n : Nat
  /-- The outputs of every row. -/
  outs : List BOut
  /-- Whether the word is read from a cell (else it is a free committed word). -/
  rd : Bool
  /-- The word's cell. -/
  wc : Nat → Nat
  /-- Output `j`'s cell at row `x`. -/
  oc : Nat → Nat → Nat
  /-- The committed columns' placements. -/
  pl : Nat → Bool × Nat

namespace BSpec

variable (S : BSpec)

/-- Output `j`. -/
def out (j : Nat) : BOut := S.outs.getD j (.bit 0)

/-- The real row whose addresses row `x` uses (padding rows repeat row `0`). -/
def row (x : Nat) : Nat := if x < S.n then x else 0

/-- The width. -/
def width : Nat := 67 + 2 * S.outs.length

/-- The fixed address column `x ↦ g^{a (row x)}`, its closed form the extension. -/
def adrCol (a : Nat → Nat) : ColSrc :=
  .fix (fun x => FK.x ^ a (S.row x)) fun r => Loop.mle r fun x => FE.ofK (FK.x ^ a (S.row x))

/-- Column `c`. -/
def col (c : Nat) : ColSrc :=
  if c = 66 then S.adrCol S.wc
  else if 68 ≤ c ∧ c % 2 = 0 then S.adrCol (S.oc ((c - 68) / 2))
  else .com (S.pl c).1 (S.pl c).2

/-- The word's read. -/
def wread : Key × Nat := (⟨sep .K, CPoly.var 66, [CPoly.var 0]⟩, 65)

/-- Output `j`'s read. -/
def oread (j : Nat) : Key × Nat := (⟨sep .K, CPoly.var (68 + 2 * j), [outPoly (S.out j)]⟩, 67 + 2 * j)

/-- The reads. -/
def reads : List (Key × Nat) :=
  (if S.rd then [wread] else []) ++ (List.range S.outs.length).map S.oread

theorem deg_var (i : Nat) : CPoly.Deg2 (CPoly.var i) := fun m hm => by
  simp [CPoly.var] at hm; subst hm; simp

/-- **The `BITS` table.** -/
def tab : Tab where
  τ := S.τ
  cols := (List.range S.width).map S.col
  cons := cons
  reads := S.reads
  seeds := []
  deg := by
    refine ⟨fun C hC m hm => ?_, fun r hr => ?_, fun s hs => by simp at hs⟩
    · simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
      rcases hC with rfl | ⟨z, -, rfl⟩
      · simp only [wcons, List.mem_cons, List.mem_map, List.mem_range] at hm
        rcases hm with rfl | ⟨z, -, rfl⟩ <;> simp
      · simp only [bcons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> simp
    · simp only [reads, List.mem_append, List.mem_map, List.mem_range] at hr
      rcases hr with h | ⟨j, -, rfl⟩
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact ⟨deg_var 66, fun P hP => by simp [wread] at hP; subst hP; exact deg_var 0⟩
        · simp at h
      · refine ⟨deg_var _, fun P hP => ?_⟩
        simp only [oread, List.mem_singleton] at hP; subst hP
        intro m hm
        simp only [outPoly, List.mem_map, List.mem_range] at hm
        obtain ⟨z, -, rfl⟩ := hm; simp

theorem tab_w : S.tab.w = S.width := by simp [Tab.w, tab]

theorem tab_seeds : S.tab.seeds = [] := rfl

/-- The read-count columns lie inside the width (`AuxHyps.cnt`). -/
theorem tab_cnt : ∀ r ∈ S.tab.reads, r.2 < S.tab.w := by
  intro r hr
  rw [tab_w]
  simp only [tab, reads, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with h | ⟨j, hj, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp only [wread, width]; omega
    · simp at h
  · simp only [oread, width]; omega

theorem tab_cols (c : Nat) (hc : c < S.width) : S.tab.cols[c]? = some (S.col c) := by
  simp [tab, hc]

/-- **The closed forms are the extensions** (`FixOk`). -/
theorem fixOk_tab : FixOk [S.tab] := by
  intro t ht f ev hf r _
  simp only [List.mem_singleton] at ht; subst ht
  simp only [tab, List.mem_map, List.mem_range] at hf
  obtain ⟨c, -, hc⟩ := hf
  unfold col adrCol at hc
  split at hc
  · cases hc; rfl
  · split at hc
    · cases hc; rfl
    · cases hc

theorem fixOk_append {a b : List Tab} (ha : FixOk a) (hb : FixOk b) : FixOk (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem fixOk_tabs (Ss : List BSpec) : FixOk (Ss.map tab) := by
  intro t ht
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp ht
  exact S.fixOk_tab _ (List.mem_singleton_self _)

end BSpec

/-! ## The row lemma on `FK` rows -/

theorem evalK_wcons (v : Nat → FK) : evalK v wcons = v 0 + lsum (fun z => wt z * v (1 + z)) 64 := by
  simp only [evalK, wcons, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, sum_range]

theorem evalK_bcons (v : Nat → FK) (z : Nat) :
    evalK v (bcons z) = v (1 + z) * v (1 + z) + v (1 + z) := by
  simp [evalK, bcons]

theorem evalK_outPoly (v : Nat → FK) (o : BOut) :
    evalK v (outPoly o) = lsum (fun z => o.coef z * v (1 + z)) 64 := by
  simp only [evalK, outPoly, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, sum_range]

/-- The `LvmBits` row of an `FK` row of the table. -/
def rowOf (v : Nat → FK) : Bits.Row := ⟨v 0, fun z => v (1 + z)⟩

theorem rowOf_cons {v : Nat → FK} (h : ∀ C ∈ cons, evalK v C = 0) : (rowOf v).Constraints := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have := h (bcons z) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩))
    rwa [evalK_bcons] at this
  · have := h wcons (List.mem_cons_self ..)
    rwa [evalK_wcons] at this

theorem rowOf_out (v : Nat → FK) (o : BOut) : evalK v (outPoly o) = (rowOf v).out o := by
  rw [evalK_outPoly]; rfl

/-! ## Soundness through the bus -/

section Sound

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The interpreter's `K` cells on the inputs read off the stack `q`. -/
noncomputable def memK (q : Column L.μ) : Nat → FK :=
  (Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).k

/-- **`BITS` soundness through the bus.** At a real row `x` of a `BITS` table of `aux`, whose
cells lie below `Q.cells .K`, the row's word `w` is the word cell's value (when `rd`) and output
cell `oc j x` holds output `j`'s word function of `w`. -/
theorem out_sound (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K) :
    ∃ w : FK, (S.rd = true → memK Q pl groups arrs aux L hτ q (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        memK Q pl groups arrs aux L hτ q (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp hS
  have hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hT : (lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩ = S.tab :=
    (get_aux Q pl groups arrs aux hk hj).trans hak
  have hxT : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by
    rw [hT]; show x < 2 ^ S.τ; omega
  set xF : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ) := ⟨x, hxT⟩
  set u := CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ xF) with hu
  set M := Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)
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
    have := aux_read_at Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt
      (by rw [haddr, evalB_var]; exact hfix c a hc hcol) 0 (by norm_num)
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
    rw [evalB_var] at h
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

end Sound

/-! ## Completeness: the honest row -/

/-- The honest `FK` row of a word: `w`, then its bits. -/
def honest (w : FK) (i : Nat) : FK :=
  if i = 0 then w else if ubit w.val (i - 1) then 1 else 0

theorem lsum_honest (w : FK) : lsum (fun z => wt z * honest w (1 + z)) 64 = w := by
  have hb : ∀ z, honest w (1 + z) = if ubit w.val z then 1 else 0 := fun z => by
    simp [honest, show 1 + z ≠ 0 by omega, show 1 + z - 1 = z by omega]
  have key : (lsum (fun z => wt z * honest w (1 + z)) 64).val = w.val := by
    apply u64_ext
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [ubit_lsum _ (fun z => ubit w.val z) id i 64 (fun z hz => by
        rw [hb, wt, ubit_mul_bit _ (by split <;> simp), ubit_one_shl hz]
        have h01 : ((0 : FK) = 1) ↔ False := by decide
        by_cases hz' : ubit w.val z = true <;> simp [hz', h01, @eq_comm _ i z])
      (fun z _ z' _ _ _ h => h)]
    exact ⟨fun ⟨z, _, h1, h2⟩ => h2 ▸ h1, fun h1 => ⟨i, hi, h1, rfl⟩⟩
  exact congrArg FK.mk key

/-- **Completeness of the row**: the honest row of any word satisfies the constraints. -/
theorem honest_cons (w : FK) : ∀ C ∈ cons, evalK (honest w) C = 0 := by
  intro C hC
  simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
  rcases hC with rfl | ⟨z, -, rfl⟩
  · rw [evalK_wcons, lsum_honest]
    show w + w = 0
    exact CharTwo.add_self_eq_zero w
  · rw [evalK_bcons]
    have : honest w (1 + z) = 0 ∨ honest w (1 + z) = 1 := by
      simp only [honest, show 1 + z ≠ 0 by omega, if_false]; split <;> simp
    rcases this with h | h <;> rw [h] <;> decide

/-- **Completeness of the outputs**: on the honest row every output polynomial is the output's
word function. -/
theorem honest_out (w : FK) {o : BOut} (ho : o.Valid) : evalK (honest w) (outPoly o) = ⟨o.word w.val⟩ := by
  rw [rowOf_out, (row_sound (rowOf_cons (honest_cons w))).2 o ho]
  rfl

/-- **The honest table row satisfies the table** (as `aux_cons` reads it): on the honest row of any
word, every constraint of every `BITS` table vanishes and every output read's value polynomial is
the output's word function. -/
theorem honest_tab (S : BSpec) (w : FK) :
    (∀ C ∈ S.tab.cons, CPoly.evalB (fun i => FK.toBF64 (honest w i)) C = 0) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        CPoly.evalB (fun i => FK.toBF64 (honest w i)) (outPoly (S.out j)) =
          FK.toBF64 ⟨(S.out j).word w.val⟩ := by
  refine ⟨fun C hC => ?_, fun j _ hv => ?_⟩
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_cons w C hC]; rfl
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_out w hv]

end Lvm.BitsTab
