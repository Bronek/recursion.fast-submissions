-- New for lvm (WP-11b-QA2, helper H1). Searched for reuse: FR `FRRingSwitch.lean` (Φ as a staged
-- Frobenius map on a generic `CommRing`, weight lemmas), leanerVM
-- `Protocol/ToArkLib/Flock/RingSwitch.lean`, our `LvmRingFidelity` (`ringWeight_fold`,
-- `phiMap_eq_sum` on the protocol's `E`). None has LoopIR gadgets; the weight fold of
-- `LvmQRingWeight` is adapted from `LvmRingFidelity.ringWeight_fold` (restated on `Lvm.FE`).
import LvmQBuildLemmas
import LvmDecideKeccak
import LvmSelfEval

/-!
# QA2 ring switching, part 1: one-row loops and the Frobenius coefficients

`F`'s ring switching (`LvmDecideKeccak`: `ringCoefficients`, `phiMap`, `ringWeight`, `ringSwitch`)
as LoopIR gadgets written with the builder (`LvmQBuild`). This module:

* `madL`, `linL`, `loadL`: a loop of one `E` row with affine operands (`a₀·a₁ + a₂`,
  `a₀ + k·a₁ + k'`, `loadE`); `madL_spec` etc.: the result at flat index `jf` is cell `p.e + jf`.
* `frobTab b f z`: the Frobenius table `f^(2^m)`, `m ≤ 2^b` (a copy of `f`, then `2^b` squarings);
  `2^b + 1` rows.
* `coeffs ch z`: the 64 coefficients `c_k` (`ringCoefficients`) from the six challenges in the
  `E` cells `ch + i`: tables for the shifts `32, …, 2` (the shift-1 table is the challenge cell),
  `c₀ = 1`, then per level `b`: `c_{2^b + m} = c_m · f_{5-b}^(2^m)` (`m < 2^b`). 131 rows (tables
  5 copies + 62 squarings, `c₀`, 63 level rows); the coefficients are the 64 cells before the
  pointer after the gadget (`coeffs_out`, `coeffs_adv`).
* `coeffs_eq`: **the cells are `F`'s `ringCoefficients ch`** (via the closed form `coefV`,
  `ringCoefficients_getD`, and its level recursion `coefV_level`).
-/

set_option autoImplicit false

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## One-row loops -/

/-- An `E` operand `base + Σ_d strides[d]·j_d`. -/
abbrev eA (base : Nat) (s : List Nat) : Addr := ⟨.E, base, s⟩

/-- A loop of one `E` row `a₀·a₁ + a₂`. -/
def madL (dims : List Nat) (a₀ a₁ a₂ : Addr) : BM LoopOut :=
  loop dims [⟨.muladd, .E, [.abs a₀, .abs a₁, .abs a₂]⟩]

/-- A loop of one `E` row `a₀ + k·a₁ + k'`. -/
def linL (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) : BM LoopOut :=
  loop dims [⟨.lin k k', .E, [.abs a₀, .abs a₁]⟩]

/-- A loop of one `loadE` row (`E` from three `K` operands). -/
def loadL (dims : List Nat) (a₀ a₁ a₂ : Addr) : BM LoopOut :=
  loop dims [⟨.loadE, .E, [.abs a₀, .abs a₁, .abs a₂]⟩]

variable {c : Ctx} {M : Mem}

theorem madL_adv (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (madL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [madL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem linL_adv (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) (p : Ptr) :
    p.adv (linL dims k k' a₀ a₁ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [linL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem loadL_adv (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (loadL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [loadL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem madL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (madL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + n⟩ := by rw [madL_adv, hn]

theorem linL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (k k' : FK) (a₀ a₁ : Addr)
    (p : Ptr) : p.adv (linL dims k k' a₀ a₁ p).2 = ⟨p.k, p.e + n⟩ := by rw [linL_adv, hn]

theorem loadL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (loadL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + n⟩ := by rw [loadL_adv, hn]

@[simp] theorem madL_p (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    (madL dims a₀ a₁ a₂ p).1.p = p := rfl
@[simp] theorem linL_p (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) (p : Ptr) :
    (linL dims k k' a₀ a₁ p).1.p = p := rfl
@[simp] theorem loadL_p (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    (loadL dims a₀ a₁ a₂ p).1.p = p := rfl

-- adapted from LvmQWhirBase.lt_size_la
theorem lt_two_dims {l a k q : Nat} (hk : k < 2 ^ l) (hq : q < 2 ^ a) :
    k + 2 ^ l * q < 2 ^ (l + a) := by
  rw [pow_add]
  calc k + 2 ^ l * q < 2 ^ l * (q + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ 2 ^ l * 2 ^ a := Nat.mul_le_mul_left _ hq

theorem madL_spec {dims : List Nat} {a₀ a₁ a₂ : Addr} {p : Ptr}
    (h : SegsHold c M p (madL dims a₀ a₁ a₂ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) * M.rd a₁.ty (a₁.at (unflat dims jf)) +
      M.rd a₂.ty (a₂.at (unflat dims jf)) := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

theorem linL_spec {dims : List Nat} {k k' : FK} {a₀ a₁ : Addr} {p : Ptr}
    (h : SegsHold c M p (linL dims k k' a₀ a₁ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) +
      FE.ofK k * M.rd a₁.ty (a₁.at (unflat dims jf)) + FE.ofK k' := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

theorem loadL_spec {dims : List Nat} {a₀ a₁ a₂ : Addr} {p : Ptr}
    (h : SegsHold c M p (loadL dims a₀ a₁ a₂ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) +
      FE.y * M.rd a₁.ty (a₁.at (unflat dims jf)) + FE.y * FE.y * M.rd a₂.ty (a₂.at (unflat dims jf)) := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

/-- The `E` copy row: result at `p.e`, value of `a`. -/
theorem copyE_spec {a : Nat} {p : Ptr} (h : SegsHold c M p (copy (ec a) p).2) :
    (copy (ec a) p).1 = ec p.e ∧ M.e p.e = M.e a := by
  have := lin_spec h
  refine ⟨rfl, ?_⟩
  simpa [copy, lin, rowRes, Cell.val, Mem.rd, Ptr.at, ofK_zero] using this

theorem copyE_adv (a : Nat) (p : Ptr) : p.adv (copy (ec a) p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [copy, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-- Sequencing a gadget with known output `x` and pointer after `p'`. -/
theorem hold_bind_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') :
    SegsHold c M p ((m >>= f) p).2 ↔ SegsHold c M p (m p).2 ∧ SegsHold c M p' (f x p').2 := by
  rw [hold_bind, hx, hp]

theorem bind_fst_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') : ((m >>= f) p).1 = (f x p').1 := by
  rw [bind_apply, hx, hp]

theorem bind_adv_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') :
    p.adv ((m >>= f) p).2 = p'.adv (f x p').2 := by
  rw [bind_apply, Ptr.adv_append, hp, hx]

theorem getPtr_out (p : Ptr) : (getPtr p).1 = p := rfl
theorem getPtr_adv (p : Ptr) : p.adv (getPtr p).2 = p := Ptr.adv_nil p

theorem copy_out (a : Cell) (p : Ptr) : (copy a p).1 = ⟨a.ty, p.at a.ty⟩ := rfl

/-- The `E` constant `k'` (`x + 1·x + k'`): result at `p.e`. -/
theorem constE_spec {k' : FK} {x : Nat} {p : Ptr} (h : SegsHold c M p (const .E k' (ec x) p).2) :
    M.e p.e = FE.ofK k' := by
  have := lin_spec h
  simp only [const, lin, rowRes, Cell.val, Mem.rd, Ptr.at, ec, ofK_one, one_mul] at this
  rw [this, CharTwo.add_self_eq_zero, zero_add]

theorem const_out (τ : Ty) (k' : FK) (x : Cell) (p : Ptr) : (const τ k' x p).1 = ⟨τ, p.at τ⟩ := rfl

theorem constE_adv (k' : FK) (x : Cell) (p : Ptr) : p.adv (const .E k' x p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-! ## Frobenius tables -/

/-- `f^(2^m)` for `m ≤ 2^b` at the returned cell `+ m`: a copy of `f`, then `2^b` squarings. -/
def frobTab (b f z : Nat) : BM Nat := do
  let q ← copy (ec f)
  let _ ← madL [b] (eA q.n [1]) (eA q.n [1]) (eA z [])
  pure q.n

theorem frobTab_apply (b f z : Nat) (p : Ptr) : frobTab b f z p =
    (p.e, (copy (ec f) p).2 ++ ((madL [b] (eA p.e [1]) (eA p.e [1]) (eA z []) ⟨p.k, p.e + 1⟩).2 ++ [])) :=
  rfl

theorem frobTab_out (b f z : Nat) (p : Ptr) : (frobTab b f z p).1 = p.e := rfl

theorem frobTab_adv (b f z : Nat) (p : Ptr) :
    p.adv (frobTab b f z p).2 = ⟨p.k, p.e + 1 + 2 ^ b⟩ := by
  rw [frobTab_apply, Ptr.adv_append, copyE_adv, Ptr.adv_append, madL_adv]
  simp [Ptr.adv, segsW]

theorem frobTab_spec {b f z : Nat} {p : Ptr} (h : SegsHold c M p (frobTab b f z p).2)
    (hz : M.e z = 0) :
    (frobTab b f z p).1 = p.e ∧ p.adv (frobTab b f z p).2 = ⟨p.k, p.e + 1 + 2 ^ b⟩ ∧
      ∀ m ≤ 2 ^ b, M.e (p.e + m) = M.e f ^ 2 ^ m := by
  rw [frobTab_apply] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, -⟩ := h
  obtain ⟨-, hv⟩ := copyE_spec h1
  rw [copyE_adv] at h2
  refine ⟨rfl, ?_, ?_⟩
  · rw [Ptr.adv_append, copyE_adv, Ptr.adv_append, madL_adv]
    simp [Ptr.adv, segsW]
  · intro m hm
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      have hs := madL_spec h2 (jf := m) (by simp; omega)
      simp only [Mem.rd, Addr.at, unflat_one (show m < 2 ^ b by omega), dot, hz, add_zero,
        Nat.one_mul, Nat.add_zero] at hs
      rw [show p.e + (m + 1) = p.e + 1 + m by omega, hs, ih (by omega), ← pow_two, ← pow_mul,
        pow_succ]

/-! ## The coefficients -/

/-- The coefficient `c_k` of `F`'s map in closed form: the product over the set bits `b` of `k`
of `f_{5-b}^(2^(k mod 2^b))` (`fc i` the challenge of shift `2^(5-i)`). -/
def coefV (fc : Nat → FE) (k : Nat) : FE :=
  ∏ b ∈ Finset.range 6, if k &&& 2 ^ b ≠ 0 then fc (5 - b) ^ 2 ^ (k % 2 ^ b) else 1

theorem coefV_zero (fc : Nat → FE) : coefV fc 0 = 1 := by simp [coefV]

/-- The bits of `2^b + m`, `m < 2^b` (a finite check, on the `m < 2^b` only: 378 cases instead of
the 2304 of `level_bits_list`). -/
theorem level_bits_list' : ∀ b ∈ List.range 6, ∀ m ∈ List.range (2 ^ b), ∀ b' ∈ List.range 6,
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) := by
  decide

/-- The bits of `2^b + m`, `m < 2^b` (from `level_bits_list'`). -/
theorem level_bits_list : ∀ b ∈ List.range 6, ∀ m ∈ List.range 64, ∀ b' ∈ List.range 6, m < 2 ^ b →
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) :=
  fun b hb m _ b' hb' hm => level_bits_list' b hb m (List.mem_range.2 hm) b' hb'

theorem level_bits {b m b' : Nat} (hb : b < 6) (hm : m < 2 ^ b) (hb' : b' < 6) :
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) := by
  have h64 : m < 64 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega : b ≤ 6))
  exact level_bits_list b (List.mem_range.2 hb) m (List.mem_range.2 h64) b' (List.mem_range.2 hb') hm

/-- **The level recursion**: `c_{2^b + m} = c_m · f_{5-b}^(2^m)`. -/
theorem coefV_level (fc : Nat → FE) {b m : Nat} (hb : b < 6) (hm : m < 2 ^ b) :
    coefV fc (2 ^ b + m) = coefV fc m * fc (5 - b) ^ 2 ^ m := by
  have hbr := Finset.mem_range.2 hb
  unfold coefV
  rw [← Finset.mul_prod_erase _ _ hbr, ← Finset.mul_prod_erase _ _ hbr]
  obtain ⟨-, hself⟩ := level_bits hb hm hb
  obtain ⟨h1, h2, h3⟩ := hself rfl
  rw [if_pos h1, h2, if_neg (by simpa using h3), one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun b' hb' => ?_
  obtain ⟨hne, hb'r⟩ := Finset.mem_erase.1 hb'
  obtain ⟨hlow, -⟩ := level_bits hb hm (Finset.mem_range.1 hb'r)
  obtain ⟨hiff, hmod⟩ := hlow hne
  by_cases hc : m &&& 2 ^ b' ≠ 0
  · rw [if_pos (hiff.2 hc), if_pos hc, hmod hc]
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

theorem foldl_filter_mul {α : Type} (P : α → Bool) (g : α → FE) : ∀ (l : List α) (a : FE),
    (l.filter P).foldl (fun acc x => acc * g x) a =
      a * (l.map fun x => if P x then g x else 1).prod
  | [], a => by simp
  | x :: l, a => by
    by_cases hx : P x
    · simp [List.filter_cons, hx, foldl_filter_mul P g l, mul_assoc]
    · simp [List.filter_cons, hx, foldl_filter_mul P g l]

/-- **`F`'s coefficients are `coefV`.** -/
theorem ringCoefficients_getD {chs : List FE} (hl : chs.length = 6) {k : Nat} (hk : k < 64) :
    (ringCoefficients chs).getD k 0 = coefV (fun i => chs.getD i 0) k := by
  match chs, hl with
  | [f0, f1, f2, f3, f4, f5], _ =>
    have e1 : (fun (acc : FE) (x : FE × Nat) => match x with | (f, s) => acc * FE.frob (k % s) f) =
        fun acc x => acc * FE.frob (k % x.2) x.1 := by
      funext acc x; rcases x with ⟨f, s⟩; rfl
    have e2 : (fun (x : FE × Nat) => match x with | (_, s) => decide (k &&& s ≠ 0)) =
        fun x => decide (k &&& x.2 ≠ 0) := by
      funext x; rcases x with ⟨f, s⟩; rfl
    simp only [ringCoefficients, kBits, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some]
    rw [e2, e1, foldl_filter_mul]
    simp only [ringMapShifts, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, coefV, Finset.prod_range_succ, Finset.prod_range_zero,
      FE.frob_eq_pow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      decide_eq_true_eq, one_mul, mul_one, Nat.reducePow, Nat.reduceSub]
    ring

/-- One level of the coefficient table: `c_{2^b + m} = c_m · F[m] + z`. -/
def cLevels (cb z : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | b, fb :: fbs => do
    let _ ← madL [b] (eA cb [1]) (eA fb [1]) (eA z [])
    cLevels cb z (b + 1) fbs

theorem cLevels_adv (cb z : Nat) : ∀ (fbs : List Nat) (b : Nat) (p : Ptr),
    p.adv (cLevels cb z b fbs p).2 = ⟨p.k, p.e + (2 ^ (b + fbs.length) - 2 ^ b)⟩
  | [], b, p => by simp [cLevels, pure_apply]
  | fb :: fbs, b, p => by
    simp only [cLevels]
    rw [bind_apply, Ptr.adv_append, madL_adv, cLevels_adv cb z fbs (b + 1)]
    simp only [List.length_cons, List.sum_cons, List.sum_nil, Nat.add_zero, Ptr.mk.injEq, true_and]
    rw [show b + (fbs.length + 1) = b + 1 + fbs.length by omega]
    have h1 : 2 ^ (b + 1) ≤ 2 ^ (b + 1 + fbs.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := pow_succ 2 b
    omega

/-- The Frobenius tables a run of levels reads: level `b`'s table holds `f_{5-b}^(2^m)`. -/
def TabsOk (M : Mem) (fc : Nat → FE) : Nat → List Nat → Prop
  | _, [] => True
  | b, fb :: fbs => (∀ m < 2 ^ b, M.e (fb + m) = fc (5 - b) ^ 2 ^ m) ∧ TabsOk M fc (b + 1) fbs

theorem cLevels_spec (fc : Nat → FE) {cb z : Nat} (hz : M.e z = 0) : ∀ (fbs : List Nat) (b : Nat)
    (p : Ptr), p.e = cb + 2 ^ b → b + fbs.length ≤ 6 → TabsOk M fc b fbs →
    (∀ k < 2 ^ b, M.e (cb + k) = coefV fc k) → SegsHold c M p (cLevels cb z b fbs p).2 →
    p.adv (cLevels cb z b fbs p).2 = ⟨p.k, cb + 2 ^ (b + fbs.length)⟩ ∧
      ∀ k < 2 ^ (b + fbs.length), M.e (cb + k) = coefV fc k
  | [], b, p, hp, _, _, hc, _ => by
    refine ⟨?_, by simpa using hc⟩
    simp only [cLevels, pure_apply, Ptr.adv_nil, List.length_nil, Nat.add_zero]
    rw [← hp]
  | fb :: fbs, b, p, hp, hb, ht, hc, h => by
    simp only [cLevels] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h2⟩ := h
    rw [madL_adv] at h2
    obtain ⟨ht1, ht2⟩ := ht
    have hb6 : b < 6 := by simp at hb; omega
    have hc' : ∀ k < 2 ^ (b + 1), M.e (cb + k) = coefV fc k := by
      intro k hk
      by_cases hk' : k < 2 ^ b
      · exact hc k hk'
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 ^ b + m := ⟨k - 2 ^ b, by omega⟩
        have hm : m < 2 ^ b := by rw [pow_succ] at hk; omega
        have hs := madL_spec h1 (jf := m) (by simpa using hm)
        simp only [Mem.rd, Addr.at, unflat_one hm, dot, hz,
          add_zero, Nat.one_mul, Nat.add_zero, Nat.zero_mul] at hs
        rw [← Nat.add_assoc, ← hp, hs, hc m hm, ht1 m hm, coefV_level fc hb6 hm]
    have ih := cLevels_spec fc hz fbs (b + 1) _ (by simp [hp, pow_succ]; omega)
      (by simp at hb; omega) ht2 hc' h2
    rw [bind_apply, Ptr.adv_append, madL_adv]
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih

/-- **The coefficients** from the challenges in `E` cells `ch + i` (`z` an `E` zero cell): the
returned cell `+ k`, `k < 64`, holds `c_k`; they are the 64 cells before the pointer after it. -/
def coeffs (ch z : Nat) : BM Nat := do
  let t5 ← frobTab 5 ch z
  let t4 ← frobTab 4 (ch + 1) z
  let t3 ← frobTab 3 (ch + 2) z
  let t2 ← frobTab 2 (ch + 3) z
  let t1 ← frobTab 1 (ch + 4) z
  let c0 ← const .E 1 (ec z)
  cLevels c0.n z 0 [ch + 5, t1, t2, t3, t4, t5]
  pure c0.n

end Lvm.Loop.QRing

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

theorem coeffs_out (ch z : Nat) (p : Ptr) : (coeffs ch z p).1 = p.e + 67 := by
  simp only [coeffs]
  rw [bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (const_out _ _ _ _) (constE_adv _ _ _), bind_apply]
  simp only [pure_apply, Ptr.at]
  omega

theorem coeffs_adv (ch z : Nat) (p : Ptr) : p.adv (coeffs ch z p).2 = ⟨p.k, p.e + 131⟩ := by
  simp only [coeffs]
  rw [bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (const_out _ _ _ _) (constE_adv _ _ _), bind_apply, Ptr.adv_append,
    cLevels_adv]
  simp only [pure_apply, Ptr.adv_nil, List.length_cons, List.length_nil]
  simp only [Ptr.mk.injEq, true_and]
  omega

/-- **Q_arith_eq, ring coefficients.** With the challenges in the `E` cells `ch + i` and a zero
cell `z`, the 64 cells from `(coeffs ch z p).1 = p.e + 67` hold `F`'s `ringCoefficients ch`. -/
theorem coeffs_eq {ch z : Nat} {chs : List FE} (hl : chs.length = 6)
    (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (hz : M.e z = 0) {p : Ptr}
    (h : SegsHold c M p (coeffs ch z p).2) :
    ∀ k < 64, M.e (p.e + 67 + k) = (ringCoefficients chs).getD k 0 := by
  simp only [coeffs] at h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h5, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h4, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h3, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h2, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h1, h⟩ := h
  rw [hold_bind_eq (const_out _ _ _ _) (constE_adv _ _ _)] at h
  obtain ⟨h0, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨hL, -⟩ := h
  have v5 := (frobTab_spec h5 hz).2.2
  have v4 := (frobTab_spec h4 hz).2.2
  have v3 := (frobTab_spec h3 hz).2.2
  have v2 := (frobTab_spec h2 hz).2.2
  have v1 := (frobTab_spec h1 hz).2.2
  have v0 := constE_spec h0
  simp only [Ptr.at, Nat.reducePow] at v5 v4 v3 v2 v1 v0 hL
  have hL' := cLevels_spec (fun i => chs.getD i 0) hz _ 0 _ (by simp) (by simp) ?_ ?_ hL
  · intro k hk
    rw [ringCoefficients_getD hl hk, ← hL'.2 k (by simpa using hk)]
  · simp only [TabsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · intro m hm
      obtain rfl : m = 0 := by simpa using hm
      simpa using hch 5 (by norm_num)
    · intro m hm; rw [v1 m (by simpa using hm.le), hch 4 (by norm_num)]
    · intro m hm; rw [v2 m (by simpa using hm.le), hch 3 (by norm_num)]
    · intro m hm; rw [v3 m (by simpa using hm.le), hch 2 (by norm_num)]
    · intro m hm; rw [v4 m (by simpa using hm.le), hch 1 (by norm_num)]
    · intro m hm
      have h0' := hch 0 (by norm_num)
      rw [Nat.add_zero] at h0'
      rw [v5 m (by simpa using hm.le), h0']
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rw [coefV_zero, Nat.add_zero, v0, ofK_one]

end Lvm.Loop.QRing
