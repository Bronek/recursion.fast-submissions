-- New for lvm (WP-11b-QA2, H2): `countRoot ≠ 0` without an inverse operation. Searched leanerVM
-- `Protocol/Bus.lean` (`prod_countLeaves_ne_zero_iff`: the leaves' side, not the root check) and
-- FR (no nonzero gadget); the norm argument `x^(|E|−1) = 1` is Mathlib's
-- `FiniteField.pow_card_sub_one_eq_one` with `Lvm.FE.card_FE`.
import LvmQBusBase

/-!
# The count root is not zero (`F`: `require (countRoot != 0)`)

LoopIR has no inverse. In `E = GF(2^192)`, `x^(2^192 − 1)` is `1` for `x ≠ 0` and `0` for `x = 0`,
so `x ≠ 0` iff `x^(2^193 − 2) = (x^(2^192−1))² = 1`. The gadget `countNZ`:

* two copies (`s₋₁ = x`, `P₋₁ = 1`), the cells the first iteration's `prev` reads;
* `192 = 128 + 64` iterations of the template `s = prev(s)·prev(s) + z`, `P = prev(P)·s + z`
  (two loops of one template, contiguous: `runLoops … [7, 6]`), so `s_i = x^(2^(i+1))` and
  `P_i = x^(2^(i+2) − 2)`;
* `t = P₁₉₁ + 1` and `assert0 t gate`.

388 rows: 384 `E·E+E` (16 words), 3 `E` `lin` (12), one `assert0` (6): 6,186 words.

Theorems: `countNZ_P` (the last product cell is `x^(2^193 − 2)`), `pow_norm_eq_one_iff`, and
**`countNZ_spec`**: with the gate on, the assertion holds iff `F`'s `countRoot != 0` passes.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-- The squaring and running-product template (`z` a zero cell). -/
def tplNorm (z : Cell) : List LRow :=
  [⟨.muladd, .E, [.prev 0, .prev 0, z.opd]⟩,
   ⟨.muladd, .E, [.prev 1, .cur 0, z.opd]⟩]

theorem tplNorm_allE (z : Cell) : AllE (tplNorm z) := by simp [AllE, tplNorm]

/-- **`x ≠ 0` without an inverse** (`gate · (x^(2^193 − 2) + 1) = 0`). -/
def countNZ (z o gate x : Cell) : BM Unit := do
  let _ ← lin .E 0 0 x x
  let _ ← lin .E 0 0 o o
  runLoops (fun _ => tplNorm z) [7, 6] 0
  let q ← getPtr
  let t ← lin .E 0 1 (ec (q.e - 1)) (ec (q.e - 1))
  assert0 t gate

/-- The law of one iteration at base `e`: `s = s₋² `, `P = P₋ · s`. -/
def LawN (M : Mem) (e _i : Nat) : Prop :=
  M.e e = M.e (e - 2) * M.e (e - 2) ∧ M.e (e + 1) = M.e (e - 1) * M.e e

section
variable {c : Ctx} {M : Mem}

theorem lawN {z : Cell} (hz : z.val M = 0) (p : Ptr) (d : Nat) (hp : 2 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplNorm z) p).2) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawN M (p.e + 2 * jf) jf := by
  have hok : OpdsOk (tplNorm z) := by simp [OpdsOk, tplNorm, opdOk, Cell.opd]
  have E := fun t (ht : t < 2) => loop1_eqs h (tplNorm_allE z) hok (L := 2) rfl hjf ht
  have r0 := E 0 (by decide)
  have r1 := E 1 (by decide)
  simp only [tplNorm, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, Cell.opd, Cell.addr,
    Addr.at, dot, Nat.add_zero] at r0 r1
  have hz' : M.rd z.ty z.n = 0 := hz
  rw [hz', add_zero] at r0 r1
  refine ⟨?_, ?_⟩
  · rw [r0, show p.e - 2 + 2 * jf = p.e + 2 * jf - 2 by omega]
  · rw [show p.e + 2 * jf + 1 = p.e + 1 + 2 * jf by omega, r1,
      show p.e + 1 - 2 + 2 * jf = p.e + 2 * jf - 1 by omega]

/-- The cells of the chain: `s_i = x^(2^(i+1))` at `e₀ + 2 + 2i`, `P_i = x^(2^(i+2) − 2)` at
`e₀ + 3 + 2i`, from `s₋₁ = x` at `e₀` and `P₋₁ = 1` at `e₀ + 1`. -/
theorem norm_chain (e₀ : Nat) (x : FE) (h0 : M.e e₀ = x) (h1 : M.e (e₀ + 1) = 1) (n : Nat)
    (hlaw : ∀ i < n, LawN M (e₀ + 2 + 2 * i) i) :
    ∀ i < n, M.e (e₀ + 2 + 2 * i) = x ^ (2 ^ (i + 1)) ∧ M.e (e₀ + 3 + 2 * i) = x ^ (2 ^ (i + 2) - 2) := by
  intro i hi
  induction i with
  | zero =>
    obtain ⟨a, b⟩ := hlaw 0 hi
    simp only [Nat.mul_zero, Nat.add_zero] at a b
    rw [show e₀ + 2 - 2 = e₀ by omega] at a
    rw [show e₀ + 2 - 1 = e₀ + 1 by omega, show e₀ + 2 + 1 = e₀ + 3 by omega] at b
    refine ⟨by rw [a, h0]; ring, ?_⟩
    rw [b, h1, a, h0]; norm_num; ring
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨a, b⟩ := hlaw (i + 1) hi
    rw [show e₀ + 2 + 2 * (i + 1) - 2 = e₀ + 2 + 2 * i by omega] at a
    rw [show e₀ + 2 + 2 * (i + 1) - 1 = e₀ + 3 + 2 * i by omega,
      show e₀ + 2 + 2 * (i + 1) + 1 = e₀ + 3 + 2 * (i + 1) by omega] at b
    have hs : M.e (e₀ + 2 + 2 * (i + 1)) = x ^ (2 ^ (i + 1 + 1)) := by
      rw [a, ih1, ← pow_add, pow_succ 2 (i + 1)]; congr 1; ring
    refine ⟨hs, ?_⟩
    rw [b, ih2, hs, ← pow_add]
    congr 1
    have h4 : 4 ≤ 2 ^ (i + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (i + 1 + 1) = 2 ^ (i + 2) := by ring_nf
    have e2 : 2 ^ (i + 1 + 2) = 2 * 2 ^ (i + 2) := by
      rw [show i + 1 + 2 = (i + 2) + 1 by omega, pow_succ]; ring
    rw [e1, e2]
    omega

/-- `x^(2^193 − 2) = 1` iff `x ≠ 0` in `E` (`|E| = 2^192`). -/
theorem pow_norm_eq_one_iff (x : FE) : x ^ (2 ^ 193 - 2) = 1 ↔ x ≠ 0 := by
  have hcard : Fintype.card FE = 2 ^ 192 := FE.card_FE
  have he : 2 ^ 193 - 2 = (2 ^ 192 - 1) * 2 := by
    have : (2 : Nat) ^ 193 = 2 ^ 192 * 2 := pow_succ 2 192
    have h1 : 1 ≤ 2 ^ 192 := Nat.one_le_two_pow
    rw [this, Nat.sub_mul]
  constructor
  · intro h hx
    rw [hx, zero_pow (by norm_num)] at h
    exact zero_ne_one h
  · intro hx
    rw [he, pow_mul, ← hcard, FiniteField.pow_card_sub_one_eq_one x hx, one_pow]

/-- **The count root is not zero.** With `z = 0`, `o = 1` and the gate on, the gadget's
assertion holds iff `F`'s check `countRoot != 0` passes (`countRoot` the value of `x`). -/
theorem countNZ_spec {z o gate x : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : gate.val M = 1)
    (p : Ptr) (h : SegsHold c M p (countNZ z o gate x p).2) :
    SegsAssert M p (countNZ z o gate x p).2 ↔ (x.val M != 0) = true := by
  rw [FE.bne_iff]
  unfold countNZ at h ⊢
  rw [hold_bind] at h
  rw [assert_bind]
  obtain ⟨hx, h⟩ := h
  rw [linE_adv] at h ⊢
  rw [hold_bind] at h
  rw [assert_bind]
  obtain ⟨ho', h⟩ := h
  rw [linE_adv] at h ⊢
  rw [hold_bind] at h
  rw [assert_bind]
  obtain ⟨hR, h⟩ := h
  obtain ⟨hlaw, hadv⟩ := runLoops_law (c := c) (M := M) (fun _ => tplNorm z) 2
    (fun _ => ⟨tplNorm_allE z, rfl⟩) (fun e i => LawN M e i) 2 [7, 6] 0 ⟨p.k, p.e + 1 + 1⟩
    (fun p' _ d _ hp' hh jf hjf => lawN hz p' d hp' hh jf hjf) (by simp) hR
  rw [hadv] at h ⊢
  simp only [getPtr, bind_apply, Ptr.adv_nil, pure_apply, List.nil_append] at h ⊢
  rw [segsHold_append, linE_adv] at h
  rw [segsAssert_append, linE_adv]
  have hcx := lin_spec hx
  have hco := lin_spec ho'
  have ht := lin_spec h.1
  simp only [lin, rowRes, Cell.val, Ptr.at, ofK_zero, ofK_one, zero_mul, add_zero, Mem.rd] at hcx hco ht
  -- the chain
  have hch := norm_chain (M := M) p.e (x.val M) hcx (by rw [hco]; exact ho) 192
    (fun i hi => by
      have := hlaw i (by simp [nRounds]; omega)
      rw [show p.e + 1 + 1 + 2 * i = p.e + 2 + 2 * i by omega] at this
      exact this) 191 (by omega)
  have hP : M.e (p.e + 1 + 1 + 2 * nRounds [7, 6] - 1) = x.val M ^ (2 ^ 193 - 2) := by
    rw [show p.e + 1 + 1 + 2 * nRounds [7, 6] - 1 = p.e + 3 + 2 * 191 by simp [nRounds]]
    exact hch.2
  rw [hP] at ht
  have hA := (aspec_assert0 (c := c) (M := M) _ gate _ h.2).2
  have hnA : SegsAssert M ⟨p.k, p.e + 1 + 1⟩ (runLoops (fun _ => tplNorm z) [7, 6] 0 ⟨p.k, p.e + 1 + 1⟩).2 :=
    runLoops_noassert _ (fun _ => tplNorm_allE z) _ _ _
  have hl1 : SegsAssert M p (lin .E 0 0 x x p).2 := ((aspec_lin (c := c) .E 0 0 x x) p hx).2.mpr trivial
  have hl2 : SegsAssert M ⟨p.k, p.e + 1⟩ (lin .E 0 0 o o ⟨p.k, p.e + 1⟩).2 :=
    ((aspec_lin (c := c) .E 0 0 o o) _ ho').2.mpr trivial
  have hl3 := ((aspec_lin (c := c) (M := M) .E 0 1 (ec (p.e + 1 + 1 + 2 * nRounds [7, 6] - 1))
    (ec (p.e + 1 + 1 + 2 * nRounds [7, 6] - 1))) _ h.1).2.mpr trivial
  simp only [hl1, hl2, hnA, hl3, true_and]
  rw [hA, hg, one_mul]
  show M.e (p.e + 1 + 1 + 2 * nRounds [7, 6]) = 0 ↔ _
  rw [ht, add_eq_zero_iff', pow_norm_eq_one_iff]

end

/-- Non-vacuity: the gadget passes the program check. -/
theorem countNZ_segsOk : segsOk ⟨1, 20⟩ (countNZ (ec 0) (ec 1) (kc 0) (ec 2) ⟨1, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
