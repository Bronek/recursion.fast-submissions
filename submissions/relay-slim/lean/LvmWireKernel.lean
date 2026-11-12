-- New for lvm2 (WP T-K): the tape's wiring kernels `ι`, `MS` and the threshold sum, their verifier
-- evaluators (automata over the bits) and the multilinear-extension lemmas (BLUEPRINT2 §1.2 T3,
-- "Closed forms"). Pattern: v1's `LvmShift` (adapted from flock-recursive `FRShift.lean`).
import LvmShift

/-!
# The wiring kernels

The tape's GKR ends at the input claim `C_in = Σ_i ι(i)·⟨ω, in(i)⟩` with

* `iota ρ μ i = eq(ρ, i ≫ 4)·μ[i & 15]` (`ρ` the last pack point, `μ` the sixteen slot weights;
  `μ` is not a tensor, so the low four bits of `i` are one digit of sixteen values).

The wiring sumcheck (T3) needs three closed forms, generic in a row offset `base` (a multiple of
`2^w`) and a width `w ≥ 4` (`|σ| = w`, `|ρ| ≥ w − 4`):

* **`sum_msK`**: `MS_w^base(σ; t) = Σ_{x<2^w} eq(σ, x)·ι(base + x + 1)·[x + 1 ≤ t]` for `t < 2^w` is
  `msEval`, a four-state automaton over the bits, low bit first, state `(c, s)` = (carry of the
  `+1`, "the low bits of `x + 1` exceed those of `t`"); the low four bits are one sixteen-valued
  digit, and the bits of `base` above `w` give the fixed factor `eq(ρ_{≥ w−4}, base / 2^w)`.
  `K̃_ch(σ) = MS_20^0(σ; m)` (`sum_msK_zero`); an interval `[a, b]` is a difference of two
  (`sum_msIntK`), so `K̃_ks` is four evaluations.
* **`sum_ikK`**: `Σ_{x<2^w} eq(σ, x)·ι(base + x) = (Σ_d eq(σ_{<4}, d)·μ[d])·eq(ρ_{<w−4}, σ_{≥4})·
  eq(ρ_{≥w−4}, base / 2^w)` (`ikEval`; `Ĩ_ks` at `w = 15`, `base = 2^20`).
* **`thrEval_eq`**: `Σ_{i ≤ t} ι(i)` is `thrEval`, the two-state threshold automaton;
  `sum_range_iota_succ`: `Σ_{i=1}^{t} ι(i) = thrEval − ι(0)` (T3's `const`).
* `sum_eqAt_lowPad`: a table supported on `x < 2^w` has the extension of its low part times
  `eq(σ_{≥w}, 0)` (T3's factor `e'`).

For the circuit (T-Q), `msEvalA` and `thrEvalA` take the bits of `t` as field elements (`bitsE`)
and use no comparison on `t` (`msEvalA_bitsE`, `thrEvalA_bitsE`).

All of it is over `E`, characteristic two; the verifier's `FE` twins are T-V's.
-/

set_option autoImplicit false

namespace Lvm.WK

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

/-! ## The weight `ι` and the kernels -/

/-- The input claim's row weight `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]`. -/
def iota (ρ μ : List E) (i : ℕ) : E := eqAt ρ (i / 16) * μ.getD (i % 16) 0

/-- The equality weight of one bit. -/
def eqBit (a : E) (b : Bool) : E := if b then a else 1 + a

/-- `MS`'s kernel on the cube: `ι(base + x + 1)·[x + 1 ≤ t]` (`K_ch` at `base = 0`, `t = m`). -/
def msK (ρ μ : List E) (base t x : ℕ) : E := if x + 1 ≤ t then iota ρ μ (base + x + 1) else 0

/-- The interval kernel `ι(base + x + 1)·[a ≤ x + 1 ≤ b]` (one interval of `cont` in `K_ks`). -/
def msIntK (ρ μ : List E) (base a b x : ℕ) : E :=
  if a ≤ x + 1 ∧ x + 1 ≤ b then iota ρ μ (base + x + 1) else 0

/-- The unshifted kernel `ι(base + x)` (`I_ks` at `base = 2^20`). -/
def ikK (ρ μ : List E) (base x : ℕ) : E := iota ρ μ (base + x)

/-! ## The `MS` automaton -/

/-- The automaton's value vector, `v c s` for the carry `c` and the strict flag `s`. -/
structure MS4 where
  v00 : E
  v01 : E
  v10 : E
  v11 : E

/-- Entry `(c, s)`. -/
def MS4.get (q : MS4) : Bool → Bool → E
  | false, false => q.v00
  | false, true => q.v01
  | true, false => q.v10
  | true, true => q.v11

/-- The strict flag after a bit: `[y₀ + s > t₀]` for the output bit `y₀` and `t`'s bit `t₀`. -/
def nextS (y0 s tb : Bool) : Bool := if tb then y0 && s else y0 || s

/-- One bit `(σ_k, ρ_k, t_k)` of `MS`, from the value vector `q` of the higher bits: the input bit
`b` has weight `eq(σ_k, b)`, the output bit `y₀ = b ⊕ c` weight `eq(ρ_k, y₀)`, the carry becomes
`b ∧ c`. -/
def msStep (a r : E) (tb : Bool) (q : MS4) : MS4 :=
  let f : Bool → Bool → E := fun c s =>
    (1 + a) * eqBit r c * q.get false (nextS c s tb) + a * eqBit r (!c) * q.get c (nextS (!c) s tb)
  ⟨f false false, f false true, f true false, f true true⟩

/-- The automaton over the high bits, highest bit innermost; at the top no carry is left and the
strict flag needs `1 ≤ t ≫ |σ|`. -/
def msTail : List E → List E → ℕ → MS4
  | a :: σ, r :: ρ, t => msStep a r (t % 2 == 1) (msTail σ ρ (t / 2))
  | _, _, t => ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩

/-- **`MS_w^base(σ; t)`, the verifier's evaluator** (`w = |σ|`): the low digit `d = x mod 16` gives
`y = (d + 1) mod 16`, carry `[d = 15]`, flag `[y > t mod 16]`; the high bits run `msTail`; the bits
of `base` above `w` give `eq(ρ_{≥ w−4}, base / 2^w)`. About `16 + 8(w − 4)` products. -/
def msEval (ρ μ σ : List E) (base t : ℕ) : E :=
  let q := msTail (σ.drop 4) (ρ.take (σ.length - 4)) (t / 16)
  eqAt (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length) *
    sumE ((List.range 16).map fun d =>
      eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * q.get (d == 15) (decide (t % 16 < (d + 1) % 16)))

/-! ## The threshold automaton and `Ĩ` -/

/-- The two-state threshold automaton (`(s = false, s = true)`) over the bits of the pack index. -/
def thrTail : List E → ℕ → E × E
  | r :: ρ, t =>
    let q := thrTail ρ (t / 2)
    let tb := t % 2 == 1
    let g : Bool → E := fun s =>
      (1 + r) * (if nextS false s tb then q.2 else q.1) + r * (if nextS true s tb then q.2 else q.1)
    (g false, g true)
  | [], t => (1, if 1 ≤ t then 1 else 0)

/-- **`Σ_{i ≤ t} ι(i)`, the verifier's evaluator**: the low digit `d` with flag `[d > t mod 16]`. -/
def thrEval (ρ μ : List E) (t : ℕ) : E :=
  let q := thrTail ρ (t / 16)
  sumE ((List.range 16).map fun d => μ.getD d 0 * (if t % 16 < d then q.2 else q.1))

/-- **`Σ_{x<2^w} eq(σ, x)·ι(base + x)`, the verifier's evaluator** (`w = |σ|`). -/
def ikEval (ρ μ σ : List E) (base : ℕ) : E :=
  sumE ((List.range 16).map fun d => eqAt (σ.take 4) d * μ.getD d 0) *
    eqEval (ρ.take (σ.length - 4)) (σ.drop 4) * eqAt (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length)

/-! ## Arithmetic twins for the circuit: `t` as field bits -/

/-- `msStep` with `t`'s bit as a field element (`0` or `1`): a selection by `tb`. -/
def msStepA (a r tb : E) (q : MS4) : MS4 :=
  let q1 := msStep a r true q
  let q0 := msStep a r false q
  ⟨tb * q1.v00 + (1 + tb) * q0.v00, tb * q1.v01 + (1 + tb) * q0.v01,
    tb * q1.v10 + (1 + tb) * q0.v10, tb * q1.v11 + (1 + tb) * q0.v11⟩

/-- `msTail` on `t`'s bits (as many as `σ`'s coordinates; nothing above them). -/
def msTailA : List E → List E → List E → MS4
  | a :: σ, r :: ρ, b :: tb => msStepA a r b (msTailA σ ρ tb)
  | _, _, _ => ⟨1, 0, 0, 0⟩

/-- `[u < e]` for the four low bits `tb4` of `u`: `Σ_{j<e} eq(tb4, j)`. -/
def ltE (tb4 : List E) (e : ℕ) : E := sumE ((List.range e).map (eqAt tb4))

/-- `msEval` on `t`'s bits `tb` (`|tb| = |σ|`) with the top factor `cTop` given:
`q(c, s) = q(c, 0) + s·(q(c, 1) + q(c, 0))`, the flag `[t mod 16 < e]` as `ltE`. -/
def msEvalA (ρ μ σ tb : List E) (cTop : E) : E :=
  let q := msTailA (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4)
  let A : ℕ → E := fun d => eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0
  cTop * (sumE ((List.range 15).map A) * q.v00 + A 15 * q.v10 +
    (q.v01 + q.v00) * sumE ((List.range 15).map fun d => A d * ltE (tb.take 4) (d + 1)))

/-- `thrTail` on the bits of `t` (as many as `ρ`'s coordinates). -/
def thrTailA : List E → List E → E × E
  | r :: ρ, b :: tb =>
    let q := thrTailA ρ tb
    -- t's bit 1: s' = y₀ ∧ s; bit 0: s' = y₀ ∨ s
    let g1 : Bool → E := fun s =>
      (1 + r) * (if nextS false s true then q.2 else q.1) + r * (if nextS true s true then q.2 else q.1)
    let g0 : Bool → E := fun s =>
      (1 + r) * (if nextS false s false then q.2 else q.1) + r * (if nextS true s false then q.2 else q.1)
    (b * g1 false + (1 + b) * g0 false, b * g1 true + (1 + b) * g0 true)
  | _, _ => (1, 0)

/-- `thrEval` on `t`'s bits `tb` (`|tb| = |ρ| + 4`). -/
def thrEvalA (ρ μ tb : List E) : E :=
  let q := thrTailA ρ (tb.drop 4)
  sumE ((List.range 16).map fun d => μ.getD d 0) * q.1 +
    (q.2 + q.1) * sumE ((List.range 16).map fun d => μ.getD d 0 * ltE (tb.take 4) d)

/-! ## Semantics of the automata (proof help) -/

/-- What `msTail σ ρ t` computes in state `(c, s)`:
`Σ_x eq(σ, x)·eq(ρ, x + c)·[x + c < 2^|σ|]·[x + c + s ≤ t]`. -/
def msSem (σ ρ : List E) (c s : Bool) (t : ℕ) : E :=
  ∑ x ∈ range (2 ^ σ.length),
    if x + c.toNat < 2 ^ σ.length ∧ x + c.toNat + s.toNat ≤ t then eqAt σ x * eqAt ρ (x + c.toNat)
    else 0

/-- What `thrTail ρ t` computes in state `s`: `Σ_y eq(ρ, y)·[y + s ≤ t]`. -/
def thrSem (ρ : List E) (s : Bool) (t : ℕ) : E :=
  ∑ y ∈ range (2 ^ ρ.length), if y + s.toNat ≤ t then eqAt ρ y else 0

theorem eqAt_cons_bit (r : E) (ρ : List E) (y : ℕ) (b : Bool) :
    eqAt (r :: ρ) (2 * y + b.toNat) = eqBit r b * eqAt ρ y := by
  cases b
  · rw [Bool.toNat_false, add_zero, eqAt_cons, if_neg (by omega), show 2 * y / 2 = y by omega]; rfl
  · rw [Bool.toNat_true, eqAt_cons, if_pos (by omega), show (2 * y + 1) / 2 = y by omega]; rfl

/-- The comparison passes to the high bits through the strict flag. -/
theorem le_iff_nextS (y0 s : Bool) (y t : ℕ) :
    2 * y + y0.toNat + s.toNat ≤ t ↔ y + (nextS y0 s (t % 2 == 1)).toNat ≤ t / 2 := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> cases y0 <;> cases s <;>
    simp [nextS, h] <;> omega

theorem ite_mul_congr {P Q : Prop} [Decidable P] [Decidable Q] (hPQ : P ↔ Q) (X Y k : E)
    (hXY : X = k * Y) : (if P then X else 0) = k * (if Q then Y else 0) := by
  by_cases hq : Q
  · rw [if_pos (hPQ.2 hq), if_pos hq, hXY]
  · rw [if_neg (fun hp ↦ hq (hPQ.1 hp)), if_neg hq, mul_zero]

theorem msStep_get (a r : E) (tb : Bool) (q : MS4) (c s : Bool) :
    (msStep a r tb q).get c s = eqBit a false * eqBit r c * q.get false (nextS c s tb) +
      eqBit a true * eqBit r (!c) * q.get c (nextS (!c) s tb) := by
  cases c <;> cases s <;> rfl

/-- One term of `msSem` on `a :: σ` at the input `2y + b`: the output bit is `b ⊕ c`, the carry
`b ∧ c`. -/
theorem msSem_term (a r : E) (σ ρ : List E) (n y t : ℕ) (b c s : Bool) :
    (if 2 * y + b.toNat + c.toNat < 2 ^ (n + 1) ∧ 2 * y + b.toNat + c.toNat + s.toNat ≤ t then
        eqAt (a :: σ) (2 * y + b.toNat) * eqAt (r :: ρ) (2 * y + b.toNat + c.toNat) else 0) =
      eqBit a b * eqBit r (b ^^ c) *
        (if y + (b && c).toNat < 2 ^ n ∧
            y + (b && c).toNat + (nextS (b ^^ c) s (t % 2 == 1)).toNat ≤ t / 2 then
          eqAt σ y * eqAt ρ (y + (b && c).toNat) else 0) := by
  have hsplit : 2 * y + b.toNat + c.toNat = 2 * (y + (b && c).toNat) + (b ^^ c).toNat := by
    cases b <;> cases c <;> simp <;> omega
  refine ite_mul_congr ?_ _ _ _ ?_
  · rw [hsplit, add_assoc, ← le_iff_nextS, pow_succ]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> omega, by omega⟩
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> omega, by omega⟩
  · rw [hsplit, eqAt_cons_bit, eqAt_cons_bit]
    ring

theorem msTail_get : ∀ (σ ρ : List E), σ.length = ρ.length → ∀ (t : ℕ) (c s : Bool),
    (msTail σ ρ t).get c s = msSem σ ρ c s t
  | [], [], _, t, c, s => by
    cases c <;> cases s <;>
      simp only [msTail, MS4.get, msSem, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil,
        mul_one, Bool.toNat_false, Bool.toNat_true, zero_add, add_zero] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: σ, r :: ρ, h, t, c, s => by
    have h' : σ.length = ρ.length := by simpa using h
    rw [msTail, msStep_get, msTail_get σ ρ h' (t / 2), msTail_get σ ρ h' (t / 2), msSem, msSem, msSem,
      List.length_cons, sum_cube_succ, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun y _ ↦ ?_) (Finset.sum_congr rfl fun y _ ↦ ?_)
    · have := msSem_term a r σ ρ σ.length y t false c s
      simp only [Bool.toNat_false, add_zero, Bool.false_xor, Bool.false_and] at this
      rw [this]; simp only [Bool.toNat_false, add_zero]
    · have := msSem_term a r σ ρ σ.length y t true c s
      simp only [Bool.toNat_true, Bool.true_xor, Bool.true_and] at this
      rw [this]

theorem thrTail_get : ∀ (ρ : List E) (t : ℕ) (s : Bool),
    (if s then (thrTail ρ t).2 else (thrTail ρ t).1) = thrSem ρ s t
  | [], t, s => by
    cases s <;>
      simp only [thrTail, thrSem, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil,
        Bool.toNat_false, Bool.toNat_true, zero_add, add_zero, ite_true, ite_false] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | r :: ρ, t, s => by
    have ih := thrTail_get ρ (t / 2)
    have hterm : ∀ (y : ℕ) (y0 : Bool), (if 2 * y + y0.toNat + s.toNat ≤ t then
        eqAt (r :: ρ) (2 * y + y0.toNat) else 0) =
        eqBit r y0 * (if y + (nextS y0 s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) :=
      fun y y0 ↦ ite_mul_congr (le_iff_nextS y0 s y t) _ _ _ (eqAt_cons_bit r ρ y y0)
    have e0 := ih (nextS false s (t % 2 == 1))
    have e1 := ih (nextS true s (t % 2 == 1))
    rw [thrSem, List.length_cons, sum_cube_succ, Finset.sum_add_distrib]
    have h0 : ∀ y, (if 2 * y + s.toNat ≤ t then eqAt (r :: ρ) (2 * y) else 0) =
        eqBit r false * (if y + (nextS false s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) := by
      intro y; have := hterm y false; simpa using this
    have h1 : ∀ y, (if 2 * y + 1 + s.toNat ≤ t then eqAt (r :: ρ) (2 * y + 1) else 0) =
        eqBit r true * (if y + (nextS true s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) := by
      intro y; have := hterm y true; simpa using this
    simp only [h0, h1, ← Finset.mul_sum]
    rw [← thrSem, ← thrSem, ← e0, ← e1]
    cases s <;> simp only [thrTail, eqBit] <;> simp

/-- `ι` at a row of an aligned block: the low digit, the low `w − 4` pack bits, and `base`'s bits. -/
theorem iota_block (ρ μ : List E) (w base y : ℕ) (h4 : 4 ≤ w) (hρ : w - 4 ≤ ρ.length)
    (hb : 2 ^ w ∣ base) (hy : y < 2 ^ w) :
    iota ρ μ (base + y) =
      eqAt (ρ.take (w - 4)) (y / 16) * μ.getD (y % 16) 0 * eqAt (ρ.drop (w - 4)) (base / 2 ^ w) := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 4 := ⟨w - 4, by omega⟩
  rw [Nat.add_sub_cancel] at hρ ⊢
  have hP : 0 < 2 ^ v := Nat.two_pow_pos v
  have h16 : 2 ^ (v + 4) = 16 * 2 ^ v := by rw [pow_add]; ring
  have hz : y / 16 < 2 ^ v := by omega
  have hlen : (ρ.take v).length = v := by simp; omega
  have hsplit : 2 ^ (v + 4) * k + y = 16 * (2 ^ v * k) + y := by rw [h16]; ring
  have e1 : (2 ^ (v + 4) * k + y) / 16 = 2 ^ v * k + y / 16 := by rw [hsplit]; omega
  have e3 : (2 ^ (v + 4) * k + y) % 16 = y % 16 := by rw [hsplit]; omega
  have e2 : (2 ^ v * k + y / 16) % 2 ^ v = y / 16 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hz]
  have e4 : (2 ^ v * k + y / 16) / 2 ^ v = k := by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hz, add_zero]
  have e5 : 2 ^ (v + 4) * k / 2 ^ (v + 4) = k := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
  rw [iota, e1, e3, e5]
  conv_lhs => rw [← List.take_append_drop v ρ]
  rw [eqAt_append, hlen, eqAt_mod (ρ.take v), hlen, e2, e4]
  ring

/-! ## The closed forms -/

/-- **`MS`'s extension is the automaton** (`K̃_ch`, and the ends of `K̃_ks`'s intervals). -/
theorem sum_msK (ρ μ σ : List E) (base t : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msK ρ μ base t x = msEval ρ μ σ base t := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 4 := ⟨σ.length - 4, by omega⟩
  have hσh : (σ.drop 4).length = v := by simp; omega
  have hσ4 : (σ.take 4).length = 4 := by simp; omega
  have hρh : (ρ.take (σ.length - 4)).length = v := by simp; omega
  have hpow : 2 ^ σ.length = 2 ^ v * 16 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 16, ∀ x' ∈ range (2 ^ v),
      eqAt σ (16 * x' + d) * msK ρ μ base t (16 * x' + d) =
        eqAt (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length) *
          (eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 *
            (if x' + (d == 15).toNat < 2 ^ v ∧
                x' + (d == 15).toNat + (decide (t % 16 < (d + 1) % 16)).toNat ≤ t / 16 then
              eqAt (σ.drop 4) x' * eqAt (ρ.take (σ.length - 4)) (x' + (d == 15).toNat) else 0)) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : eqAt σ (16 * x' + d) = eqAt (σ.take 4) d * eqAt (σ.drop 4) x' := by
      conv_lhs => rw [← List.take_append_drop 4 σ]
      rw [eqAt_append, hσ4, eqAt_mod (σ.take 4), hσ4,
        show (16 * x' + d) % 2 ^ 4 = d by norm_num; omega,
        show (16 * x' + d) / 2 ^ 4 = x' by norm_num; omega]
    have hcv : ((16 * x' + d + 1 ≤ t) ↔ (x' + (d == 15).toNat < 2 ^ v ∧
        x' + (d == 15).toNat + (decide (t % 16 < (d + 1) % 16)).toNat ≤ t / 16)) ∧
        (16 * x' + d + 1) / 16 = x' + (d == 15).toNat ∧ (16 * x' + d + 1) % 16 = (d + 1) % 16 := by
      rcases (show d = 15 ∨ d < 15 by omega) with h | h
      · subst h; simp; omega
      · have h15 : (d == 15) = false := by simp; omega
        rw [h15, Nat.mod_eq_of_lt (show d + 1 < 16 by omega)]
        by_cases hs : t % 16 < d + 1 <;> simp [hs] <;> omega
    rw [msK]
    by_cases hc' : 16 * x' + d + 1 ≤ t
    · rw [if_pos hc', if_pos (hcv.1.1 hc'), show base + (16 * x' + d) + 1 = base + (16 * x' + d + 1) by ring,
        iota_block ρ μ σ.length base _ h4 hρ hb (by omega), hcv.2.1, hcv.2.2, hes]
      ring
    · rw [if_neg hc', if_neg (fun h ↦ hc' (hcv.1.2 h))]
      ring
  have hq : ∀ c s, (msTail (σ.drop 4) (ρ.take (σ.length - 4)) (t / 16)).get c s =
      msSem (σ.drop 4) (ρ.take (σ.length - 4)) c s (t / 16) :=
    msTail_get _ _ (by rw [hσh, hρh]) _
  simp only [msEval]
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]
  conv_lhs => rw [hpow, sum_range_mul]
  simp only [hq, msSem, hσh, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

/-- `sum_msK` at `base = 0` (`K̃_ch(σ) = MS_20^0(σ; m)`). -/
theorem sum_msK_zero (ρ μ σ : List E) (t : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msK ρ μ 0 t x = msEval ρ μ σ 0 t :=
  sum_msK ρ μ σ 0 t h4 hρ (dvd_zero _) ht

/-- **An interval `[a, b]` is a difference of two `MS`** (`1 ≤ a ≤ b < 2^w`). -/
theorem sum_msIntK (ρ μ σ : List E) (base a b : ℕ) (h4 : 4 ≤ σ.length)
    (hρ : σ.length - 4 ≤ ρ.length) (hb : 2 ^ σ.length ∣ base) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbw : b < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msIntK ρ μ base a b x =
      msEval ρ μ σ base b - msEval ρ μ σ base (a - 1) := by
  have hk : ∀ x, msIntK ρ μ base a b x = msK ρ μ base b x - msK ρ μ base (a - 1) x := by
    intro x
    simp only [msIntK, msK]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [hk, mul_sub, Finset.sum_sub_distrib]
  rw [sum_msK ρ μ σ base b h4 hρ hb hbw, sum_msK ρ μ σ base (a - 1) h4 hρ hb (by omega)]

/-- **`Ĩ`'s closed form** (`Ĩ_ks(σ')` at `w = 15`, `base = 2^20`). -/
theorem sum_ikK (ρ μ σ : List E) (base : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * ikK ρ μ base x = ikEval ρ μ σ base := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 4 := ⟨σ.length - 4, by omega⟩
  have hσh : (σ.drop 4).length = v := by simp; omega
  have hσ4 : (σ.take 4).length = 4 := by simp; omega
  have hρh : (ρ.take (σ.length - 4)).length = v := by simp; omega
  have hpow : 2 ^ σ.length = 2 ^ v * 16 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 16, ∀ x' ∈ range (2 ^ v),
      eqAt σ (16 * x' + d) * ikK ρ μ base (16 * x' + d) =
        eqAt (σ.take 4) d * μ.getD d 0 * (eqAt (ρ.take (σ.length - 4)) x' * eqAt (σ.drop 4) x') *
          eqAt (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : eqAt σ (16 * x' + d) = eqAt (σ.take 4) d * eqAt (σ.drop 4) x' := by
      conv_lhs => rw [← List.take_append_drop 4 σ]
      rw [eqAt_append, hσ4, eqAt_mod (σ.take 4), hσ4,
        show (16 * x' + d) % 2 ^ 4 = d by norm_num; omega,
        show (16 * x' + d) / 2 ^ 4 = x' by norm_num; omega]
    rw [ikK, iota_block ρ μ σ.length base _ h4 hρ hb (by omega), hes,
      show (16 * x' + d) / 16 = x' by omega, show (16 * x' + d) % 16 = d by omega]
    ring
  rw [ikEval, LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range,
    ← Lvm.KG.sum_eqAt_mul_eqAt _ _ (by rw [hρh, hσh]), hρh, Finset.sum_mul_sum, Finset.sum_mul]
  conv_lhs => rw [hpow, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

/-- **The threshold sum** `Σ_{i ≤ t} ι(i)` is the two-state automaton. -/
theorem thrEval_eq (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 4)) :
    ∑ i ∈ range (t + 1), iota ρ μ i = thrEval ρ μ t := by
  have hpow : 2 ^ (ρ.length + 4) = 2 ^ ρ.length * 16 := by rw [pow_add]; norm_num
  have hsub : range (t + 1) ⊆ range (2 ^ (ρ.length + 4)) := Finset.range_subset_range.2 (by omega)
  have h1 : ∑ i ∈ range (t + 1), iota ρ μ i =
      ∑ i ∈ range (2 ^ (ρ.length + 4)), if i ≤ t then iota ρ μ i else 0 := by
    rw [← Finset.sum_subset hsub (fun x _ hx ↦ by rw [if_neg (by simp at hx; omega)])]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [if_pos (by simp at hi; omega)]
  rw [h1, hpow, sum_range_mul, Finset.sum_comm]
  simp only [thrEval]
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Finset.mem_range.1 hd
  have hq : (if t % 16 < d then (thrTail ρ (t / 16)).2 else (thrTail ρ (t / 16)).1) =
      thrSem ρ (decide (t % 16 < d)) (t / 16) := by
    rw [← thrTail_get ρ (t / 16) (decide (t % 16 < d))]
    simp
  rw [hq, thrSem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [iota, show (16 * y + d) / 16 = y by omega, show (16 * y + d) % 16 = d by omega, mul_ite, mul_zero]
  by_cases hs : t % 16 < d
  · simp only [hs, decide_true, Bool.toNat_true]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp only [hs, decide_false, Bool.toNat_false, add_zero]
    split_ifs <;> first | (exfalso; omega) | ring

/-- `Σ_{i=1}^{t} ι(i) = thrEval − ι(0)` (T3's `const` at `t = m`). -/
theorem sum_range_iota_succ (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 4)) :
    ∑ i ∈ range t, iota ρ μ (i + 1) = thrEval ρ μ t - iota ρ μ 0 := by
  rw [← thrEval_eq ρ μ t ht, Finset.sum_range_succ']
  ring

/-- The threshold sum with `ρ`'s top coordinates `ρ''` above `t`'s range is `eq(ρ'', 0)` times the sum on
`ρ'` (at `|ρ| = 17`, `m < 2^20`: `(1 + ρ_16)·thrEval ρ_{<16}`, so 20 bits of `m` suffice). -/
theorem thrEval_append (ρ' ρ'' μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ'.length + 4)) :
    thrEval (ρ' ++ ρ'') μ t = eqAt ρ'' 0 * thrEval ρ' μ t := by
  have ht' : t < 2 ^ ((ρ' ++ ρ'').length + 4) :=
    lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by simp))
  rw [← thrEval_eq _ μ t ht', ← thrEval_eq _ μ t ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have h16 : i / 16 < 2 ^ ρ'.length := by rw [pow_add] at ht; omega
  rw [iota, iota, eqAt_append, Nat.div_eq_of_lt h16]
  ring

/-- `MS` at `t = 0` is zero (an interval starting at `a = 1` needs one evaluation). -/
theorem msEval_zero (ρ μ σ : List E) (base : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) : msEval ρ μ σ base 0 = 0 := by
  rw [← sum_msK ρ μ σ base 0 h4 hρ hb (Nat.two_pow_pos _)]
  exact Finset.sum_eq_zero fun x _ ↦ by simp [msK]

/-- A table supported on `x < 2^w`: its extension is the low part's times `eq(σ_{≥w}, 0)`. -/
theorem sum_eqAt_lowPad (σ : List E) (w : ℕ) (hw : w ≤ σ.length) (f : ℕ → E) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * (if x < 2 ^ w then f x else 0) =
      (∑ x ∈ range (2 ^ w), eqAt (σ.take w) x * f x) * eqAt (σ.drop w) 0 := by
  have hlen : (σ.take w).length = w := by simp; omega
  have hsub : range (2 ^ w) ⊆ range (2 ^ σ.length) :=
    Finset.range_subset_range.2 (Nat.pow_le_pow_right (by norm_num) hw)
  rw [← Finset.sum_subset hsub (fun x _ hx ↦ by rw [if_neg (by simpa using hx), mul_zero]),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  rw [if_pos hx']
  conv_lhs => rw [← List.take_append_drop w σ]
  rw [eqAt_append, hlen, Nat.div_eq_of_lt hx']
  ring

/-! ## The circuit's twins agree on bits -/

theorem bitsE_add : ∀ (t m k : ℕ), bitsE t (m + k) = bitsE t m ++ bitsE (t / 2 ^ m) k
  | t, 0, k => by simp [bitsE]
  | t, m + 1, k => by
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [bitsE, bitsE_add (t / 2) m k, List.cons_append, Nat.div_div_eq_div_mul, pow_succ,
      mul_comm 2 (2 ^ m)]

theorem bitsE_mod : ∀ (t m : ℕ), bitsE t m = bitsE (t % 2 ^ m) m
  | t, 0 => rfl
  | t, m + 1 => by
    simp only [bitsE]
    rw [Nat.mod_mod_of_dvd t (dvd_pow_self 2 (Nat.succ_ne_zero m)), pow_succ',
      Nat.mod_mul_right_div_self, ← bitsE_mod (t / 2) m]

theorem msStepA_bit (a r : E) (b : Bool) (q : MS4) :
    msStepA a r (if b then 1 else 0) q = msStep a r b q := by
  cases b <;> simp [msStepA, LeanVM.Protocol.Whir.Complete.one_add_one_E]

theorem msTailA_bitsE (σ ρ : List E) (h : σ.length = ρ.length) (t : ℕ) (ht : t < 2 ^ σ.length) :
    msTailA σ ρ (bitsE t σ.length) = msTail σ ρ t := by
  induction σ generalizing ρ t with
  | nil =>
    cases ρ with
    | nil =>
      have : t = 0 := by simpa using ht
      subst this; rfl
    | cons _ _ => simp at h
  | cons a σ ih =>
    cases ρ with
    | nil => simp at h
    | cons r ρ =>
      have h' : σ.length = ρ.length := by simpa using h
      have ht' : t / 2 < 2 ^ σ.length := by
        rw [List.length_cons, pow_succ] at ht; omega
      simp only [List.length_cons, bitsE, msTailA, ih ρ h' (t / 2) ht', msTail]
      by_cases h1 : t % 2 = 1
      · rw [show (t % 2 == 1) = true by simp [h1], ← msStepA_bit, if_pos h1]; rfl
      · rw [show (t % 2 == 1) = false by simp [h1], ← msStepA_bit, if_neg h1]; rfl

/-- `ltE` on the bits of `u < 16` is `[u < e]`. -/
theorem ltE_bitsE (u e : ℕ) (hu : u < 16) (he : e ≤ 16) :
    ltE (bitsE u 4) e = if u < e then 1 else 0 := by
  rw [ltE, LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range,
    Finset.sum_congr rfl fun j hj ↦ eqAt_bitsE_lt (m := 4) (z := u) (w := j) (by norm_num; omega)
      (by have := Finset.mem_range.1 hj; norm_num; omega),
    Finset.sum_ite_eq']
  by_cases h : u < e <;> simp [h]

theorem bits_split (t v : ℕ) :
    (bitsE t (v + 4)).take 4 = bitsE (t % 16) 4 ∧ (bitsE t (v + 4)).drop 4 = bitsE (t / 16) v := by
  rw [add_comm v 4, bitsE_add, bitsE_mod t 4]
  simp

/-- **The circuit's `MS`** on the bits of `t` and the top factor is `msEval`. -/
theorem msEvalA_bitsE (ρ μ σ : List E) (base t : ℕ) (h4 : 4 ≤ σ.length)
    (hρ : σ.length - 4 ≤ ρ.length) (ht : t < 2 ^ σ.length) :
    msEvalA ρ μ σ (bitsE t σ.length) (eqAt (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length)) =
      msEval ρ μ σ base t := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 4 := ⟨σ.length - 4, by omega⟩
  have hσh : (σ.drop 4).length = v := by simp; omega
  have hρh : (ρ.take (σ.length - 4)).length = v := by simp; omega
  have hpow : 2 ^ σ.length = 2 ^ v * 16 := by rw [hv, pow_add]; norm_num
  have hq : msTailA (σ.drop 4) (ρ.take (σ.length - 4)) (bitsE (t / 16) v) =
      msTail (σ.drop 4) (ρ.take (σ.length - 4)) (t / 16) := by
    have := msTailA_bitsE (σ.drop 4) (ρ.take (σ.length - 4)) (by rw [hσh, hρh]) (t / 16)
      (by rw [hσh]; omega)
    rwa [hσh] at this
  have hb := bits_split t v
  rw [← hv] at hb
  simp only [msEvalA, msEval, hb.1, hb.2, hq]
  set q := msTail (σ.drop 4) (ρ.take (σ.length - 4)) (t / 16)
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, LeanVM.Protocol.Whir.Complete.sumE_eq,
    LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range, Lvm.KG.list_sum_map_range,
    Lvm.KG.list_sum_map_range, Finset.sum_range_succ _ 15]
  have hB : ∀ d ∈ range 15, eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 *
      q.get (d == 15) (decide (t % 16 < (d + 1) % 16)) =
      eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * q.v00 + (q.v01 + q.v00) *
        (eqAt (σ.take 4) d * μ.getD ((d + 1) % 16) 0 * ltE (bitsE (t % 16) 4) (d + 1)) := by
    intro d hd
    have hd' := Finset.mem_range.1 hd
    have h15 : (d == 15) = false := by simp; omega
    rw [h15, Nat.mod_eq_of_lt (show d + 1 < 16 by omega), ltE_bitsE _ _ (by omega) (by omega)]
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    by_cases hs : t % 16 < d + 1
    · simp only [hs, decide_true, if_true, MS4.get]
      linear_combination (-(eqAt (σ.take 4) d * μ.getD (d + 1) 0 * q.v00)) * h2
    · simp only [hs, decide_false, if_false, MS4.get]
      ring
  rw [Finset.sum_congr rfl hB, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [show (15 == 15) = true from rfl, show (15 + 1) % 16 = 0 from rfl, Nat.not_lt_zero,
    decide_false, MS4.get]
  ring

theorem thrTailA_bitsE (ρ : List E) (t : ℕ) (ht : t < 2 ^ ρ.length) :
    thrTailA ρ (bitsE t ρ.length) = thrTail ρ t := by
  induction ρ generalizing t with
  | nil =>
    have : t = 0 := by simpa using ht
    subst this; rfl
  | cons r ρ ih =>
    have ht' : t / 2 < 2 ^ ρ.length := by
      rw [List.length_cons, pow_succ] at ht; omega
    simp only [List.length_cons, bitsE, thrTailA, ih (t / 2) ht', thrTail]
    rcases Nat.mod_two_eq_zero_or_one t with h1 | h1 <;>
      simp [h1, nextS, LeanVM.Protocol.Whir.Complete.one_add_one_E]

/-- **The circuit's threshold sum** on the bits of `t` is `thrEval`. -/
theorem thrEvalA_bitsE (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 4)) :
    thrEvalA ρ μ (bitsE t (ρ.length + 4)) = thrEval ρ μ t := by
  have hb := bits_split t ρ.length
  have hq : thrTailA ρ (bitsE (t / 16) ρ.length) = thrTail ρ (t / 16) :=
    thrTailA_bitsE ρ (t / 16) (by rw [pow_add] at ht; omega)
  simp only [thrEvalA, thrEval, hb.1, hb.2, hq]
  set q := thrTail ρ (t / 16)
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, LeanVM.Protocol.Whir.Complete.sumE_eq,
    LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range, Lvm.KG.list_sum_map_range,
    Lvm.KG.list_sum_map_range, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Finset.mem_range.1 hd
  rw [ltE_bitsE _ _ (by omega) (by omega)]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  by_cases hs : t % 16 < d
  · simp only [hs, if_true]
    linear_combination (μ.getD d 0 * q.1) * h2
  · simp only [hs, if_false]
    ring

end Lvm.WK
