-- New for lvm (AC-Q): the two sums of Q_acc (BLUEPRINT §12.5 steps 1 and 4). Reuses QA2's
-- `eqTab`/`eqTab_spec`/`eqW_append` (`LvmQWhirBatch`) and the building blocks of `LvmQAccBase`.
import LvmQAccBase

/-!
# Q_acc's sums

* **`qyown kb la dk z one fx`** (step 1): `y' = Σ_{k<|fx|} eq(κ', k) · v'_k`, `κ'` the `dk` `E` cells
  from `kb`, `v'_k` the cell `fx[k]` (the child's evaluations of `fixCols`, the table gadget's cells). The
  `eq` table is built as two halves (`la` low coordinates, `dk − la` high ones, `eqW_append`) and
  multiplied per column: `2^la + 2^(dk−la)` table entries instead of `2^dk`.
* **`qpub al z one τp hd vkc nL`** (step 4): `Σ_{i<nL} eq(r', i) · L_i` (`r'` the `τp` cells `al i`), the extension of the
  child's `PUB` lanes `L` at the table point's first `τp` coordinates: `L_i` is stream lane `hd + i`
  except the key lanes `1 … 4`, which are the current proof's `PUB` cells `vkc …` (the child's `pubOf`
  takes `vk` from `V`'s argument, not from its header).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

variable {c : Ctx} {M : Mem}

/-! ## Lists of gadgets with pointer-generic values -/

theorem seqAll_vals {α : Type} [Inhabited α] (f : Nat → BM α) (V : α → FE) (val : Nat → FE)
    (hf : ∀ k q, SegsHold c M q (f k q).2 → V (f k q).1 = val k) :
    ∀ (ks : List Nat) (p : Ptr), SegsHold c M p (seqAll (ks.map f) p).2 →
      ∀ i < ks.length, V ((seqAll (ks.map f) p).1.getD i default) = val (ks.getD i 0)
  | [], _, _, i, hi => absurd hi (by simp)
  | k :: ks, p, h, i, hi => by
    simp only [List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    cases i with
    | zero => exact hf k p h.1
    | succ i => simpa using seqAll_vals f V val hf ks _ h.2.1 i (by simpa using hi)

theorem forN_vals {α : Type} [Inhabited α] {n : Nat} {f : Nat → BM α} (V : α → FE) (val : Nat → FE)
    (hf : ∀ k q, SegsHold c M q (f k q).2 → V (f k q).1 = val k) {p : Ptr}
    (h : SegsHold c M p (forN n f p).2) : ∀ i < n, V ((forN n f p).1.getD i default) = val i := by
  intro i hi
  have := seqAll_vals f V val hf (List.range n) p h i (by simpa using hi)
  simpa [forN, List.getD_eq_getElem?_getD, hi] using this

theorem sum_map_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]; simp

/-! ## `Σ_k eq(pt, k)·x_k` by blocks -/

/-- **`Σ_{k<|xs|} eq(pt, k) · x_k`**, `pt` the `dk` `E` cells `al i`: two half `eq` tables (`la` low
coordinates, `dk − la` high ones), per block `h` of `2^la` entries the chain `Σ_l eqL[l]·x_{h·2^la+l}`,
then `Σ_h eqH[h]·acc_h` (entries past `|xs|` are `z`). -/
def eqDot (al : Nat → Cell) (la dk : Nat) (z one : Cell) (xs : List Cell) : BM Cell := do
  let eL ← eqTab al z one false la
  let eH ← eqTab (fun i => al (la + i)) z one false (dk - la)
  let accs ← forN ((xs.length + 2 ^ la - 1) / 2 ^ la) fun h =>
    macChain ((List.range (2 ^ la)).map fun l => (ec (eL + l), xs.getD (h * 2 ^ la + l) z)) z
  macChain ((List.range ((xs.length + 2 ^ la - 1) / 2 ^ la)).map fun h =>
    (ec (eH + h), accs.getD h default)) z

theorem sum_blocks (f : Nat → FE) (B : Nat) : ∀ n : Nat,
    ∑ k ∈ Finset.range (n * B), f k = ∑ h ∈ Finset.range n, ∑ l ∈ Finset.range B, f (h * B + l)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_blocks f B n, Finset.sum_range_succ]

theorem eqW_split (v : Nat → FE) (la dk : Nat) (hla : la ≤ dk) (x : Nat) :
    eqW ((List.range dk).map v) x =
      eqW ((List.range la).map v) (x % 2 ^ la) *
        eqW ((List.range (dk - la)).map fun i => v (la + i)) (x / 2 ^ la) := by
  have e : (List.range dk).map v = (List.range la).map v ++ (List.range (dk - la)).map fun i => v (la + i) := by
    obtain ⟨m, rfl⟩ : ∃ m, dk = la + m := ⟨dk - la, by omega⟩
    rw [List.range_add, List.map_append, List.map_map, Nat.add_sub_cancel_left]; rfl
  rw [e, eqW_append, List.length_map, List.length_range]

theorem eqDot_spec {al : Nat → Cell} {la dk : Nat} {z one : Cell} {xs : List Cell} {p : Ptr}
    (hal : ∀ i, (al i).ty = .E) (hla : la ≤ dk) (hn : xs.length ≤ 2 ^ dk)
    (hz : z.val M = 0) (hone : M.e one.n = 1) (h : SegsHold c M p (eqDot al la dk z one xs p).2) :
    (eqDot al la dk z one xs p).1.val M =
      ∑ k ∈ Finset.range xs.length,
        eqW ((List.range dk).map fun i => (al i).val M) k * (xs.getD k z).val M := by
  simp only [eqDot, bind_apply] at h ⊢
  rw [segsHold_append, segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have eL := eqTab_spec al z one false la h1 hz hal hone
  have eH := eqTab_spec (fun i => al (la + i)) z one false (dk - la) h2 hz (fun i => hal _) hone
  simp only [eqCoord, Bool.false_eq_true, ite_false] at eL eH
  have hB0 : 0 < 2 ^ la := by positivity
  have hacc := forN_vals (n := (xs.length + 2 ^ la - 1) / 2 ^ la) (Cell.val M)
    (fun h => ∑ l ∈ Finset.range (2 ^ la), M.e ((eqTab al z one false la p).1 + l) *
      (xs.getD (h * 2 ^ la + l) z).val M)
    (fun k q hk => by rw [macChain_spec _ _ _ hk, hz, zero_add, List.map_map, sum_map_range]; rfl) h3
  rw [macChain_spec _ _ _ h4, hz, zero_add, List.map_map, sum_map_range]
  have hE : 2 ^ dk = 2 ^ la * 2 ^ (dk - la) := by rw [← pow_add, Nat.add_sub_cancel' hla]
  have hblk : ∀ hh < (xs.length + 2 ^ la - 1) / 2 ^ la, hh < 2 ^ (dk - la) := by
    intro hh hh'
    have h1 : (hh + 1) * 2 ^ la ≤ xs.length + 2 ^ la - 1 := (Nat.le_div_iff_mul_le hB0).mp (by omega)
    have h2 : 2 ^ la * hh < 2 ^ la * 2 ^ (dk - la) := by
      rw [Nat.succ_mul] at h1; rw [← hE, mul_comm]; omega
    exact Nat.lt_of_mul_lt_mul_left h2
  have hlen : xs.length ≤ (xs.length + 2 ^ la - 1) / 2 ^ la * 2 ^ la := by
    have h1 := Nat.div_add_mod (xs.length + 2 ^ la - 1) (2 ^ la)
    have h2 := Nat.mod_lt (xs.length + 2 ^ la - 1) hB0
    rw [mul_comm]; omega
  refine (Finset.sum_congr rfl (g := fun hh => ∑ l ∈ Finset.range (2 ^ la),
    eqW ((List.range dk).map fun i => (al i).val M) (hh * 2 ^ la + l) * (xs.getD (hh * 2 ^ la + l) z).val M)
    fun hh hh' => ?_).trans ?_
  · rw [Finset.mem_range] at hh'
    simp only [Function.comp_apply, Cell.val_E]
    rw [hacc hh hh', Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [eqW_split _ la dk hla, eL l hl, eH hh (hblk hh hh'),
      show (hh * 2 ^ la + l) % 2 ^ la = l by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl],
      show (hh * 2 ^ la + l) / 2 ^ la = hh by
        rw [Nat.mul_comm, Nat.mul_add_div hB0, Nat.div_eq_of_lt hl, Nat.add_zero]]
    ring
  · rw [← sum_blocks (fun k => eqW ((List.range dk).map fun i => (al i).val M) k * (xs.getD k z).val M)]
    obtain ⟨m, hm⟩ : ∃ m, (xs.length + 2 ^ la - 1) / 2 ^ la * 2 ^ la = xs.length + m :=
      ⟨_, (Nat.add_sub_cancel' hlen).symm⟩
    rw [hm, Finset.sum_range_add]
    have h0 : ∑ j ∈ Finset.range m, eqW ((List.range dk).map fun i => (al i).val M) (xs.length + j) *
        (xs.getD (xs.length + j) z).val M = 0 := by
      apply Finset.sum_eq_zero; intro j _
      rw [List.getD_eq_default _ _ (by omega), hz, mul_zero]
    rw [h0, add_zero]

/-! ## Step 1: `y' = Σ_k eq(κ', k)·v'_k` -/

/-- `y'`: `eqDot` over `κ'` (the `dk` cells from `kb`) and the child's `fixCols` evaluations. -/
def qyown (kb la dk : Nat) (z one : Cell) (fx : List Cell) : BM Cell :=
  eqDot (fun i => ec (kb + i)) la dk z one fx

theorem qyown_spec {kb la dk : Nat} {z one : Cell}
    {fx : List Cell} {p : Ptr} (hla : la ≤ dk) (hn : fx.length ≤ 2 ^ dk)
    (hz : z.val M = 0) (hone : M.e one.n = 1)
    (h : SegsHold c M p (qyown kb la dk z one fx p).2) :
    (qyown kb la dk z one fx p).1.val M =
      ∑ k ∈ Finset.range fx.length,
        eqW ((List.range dk).map fun i => M.e (kb + i)) k * (fx.getD k z).val M :=
  eqDot_spec (fun _ => rfl) hla hn hz hone h

/-! ## Step 4: the child's `PUB` evaluation -/

/-- The child's `PUB` lane `i` in the circuit: the key from the cells `vkc …`, else stream lane `hd + i`. -/
def pubLane (M : Mem) (hd vkc i : Nat) : FK := if 1 ≤ i ∧ i < 5 then M.k (vkc + (i - 1)) else M.k (hd + i)

/-- Its cell. -/
def pubLaneC (hd vkc i : Nat) : Cell := if 1 ≤ i ∧ i < 5 then kc (vkc + (i - 1)) else kc (hd + i)

/-- `Σ_{i<nL} eq(r', i) · L_i` (`r'` the `τp` cells `al i`; `eqDot` split `τp/2`). -/
def qpub (al : Nat → Cell) (z one : Cell) (τp hd vkc nL : Nat) : BM Cell :=
  eqDot al (τp / 2) τp z one ((List.range nL).map (pubLaneC hd vkc))

theorem qpub_spec {al : Nat → Cell} {z one : Cell} {τp hd vkc nL : Nat} {p : Ptr} (hz : z.val M = 0)
    (hal : ∀ i, (al i).ty = .E) (hone : M.e one.n = 1) (hn : nL ≤ 2 ^ τp)
    (h : SegsHold c M p (qpub al z one τp hd vkc nL p).2) :
    (qpub al z one τp hd vkc nL p).1.val M =
      ∑ i ∈ Finset.range nL, eqW ((List.range τp).map fun i => (al i).val M) i *
        FE.ofK (pubLane M hd vkc i) := by
  rw [qpub, eqDot_spec hal (by omega) (by simpa using hn) hz hone h, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  congr 1
  simp only [pubLaneC, pubLane]
  split_ifs <;> rfl

end Lvm.QAcc
