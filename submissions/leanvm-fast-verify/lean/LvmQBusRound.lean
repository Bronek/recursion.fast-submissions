-- New for lvm (WP-11b-QA2, H2): sumcheck rounds as LoopIR loops (QL's builder). Searched FR
-- `FRSumcheck` (R1CS, one constraint set per round) and leanerVM `Protocol/Bus.lean` (no circuit):
-- nothing to adapt beyond the pattern of `LvmQWhirFold` (loop rows → `F`'s function).
import LvmQBusBase

/-!
# Sumcheck rounds as loops (`F`'s `sumcheck`)

A run of `n` rounds of `F`'s `sumcheck claim count eqs` is one loop per binary chunk of `n`
(`runLoops`), with one iteration per round. Every chunk uses the same all-`E` template of width
`L`, so the chunks' cells are contiguous and the claim is carried by `Opd.prev` of the template's
last row across iterations *and* chunks (no prologue: the run starts with one copy of the claim).
An iteration loads its `m = count − 1` scalars and its challenge from stream lanes (`loadE`, the
round's FS entry: lanes `a + 3k + S·i`, the challenge at `a + 3m + S·i`) and computes the next
claim `polyEval (roundPoly claim eq msg) challenge` in a few rows:

* `tplP3` (plain, count 3, `m = 2`): `u = c₂ + claim`, `v = c₂ r + u`, `out = v r + c₀`;
* `tplP4` (plain, count 4, `m = 3`): `ρ = r + 1`, `α = c₃ ρ + c₂`, `β = α ρ + claim`,
  `out = β r + c₀` (characteristic 2: `c₂(1 + r) + c₃(1 + r²) = ρ(c₂ + ρ c₃)`);
* `tplQ3` (equality mode, count 3, `m = 2`): `σ = t₁ + t₂`, `A = e σ + claim`, `H = t₂ r + t₁`,
  `out = H r + A`;
* `tplQ5` (equality mode, count 5, `m = 4`): `σ = t₁ + … + t₄`, `A = e σ + claim`, Horner `H`,
  `out = H r + A`.

The equality factor `e` of round `i` is the `E` cell `eb + es·i` (the GKR point's coordinates).

Theorems: `lawP3`, `lawP4`, `lawQ3`, `lawQ5` (one iteration), `scRun_cells` (the run: claims and
challenges by round), and **`scRun_eq`** (= `F`'s `sumcheck` final claim and challenges, when the
`K` cells hold the stream's lanes from an entry boundary).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-! ## The templates -/

/-- Plain mode, count 3: scalars `c₀, c₂` at lanes `a, a + 3`, the challenge at `a + 6`. -/
def tplP3 (a S : Nat) : List LRow :=
  [ldRow a S, ldRow (a + 3) S, ldRow (a + 6) S,
   ⟨.lin 1 0, .E, [.cur 1, .prev 5]⟩,
   ⟨.muladd, .E, [.cur 1, .cur 2, .cur 3]⟩,
   ⟨.muladd, .E, [.cur 4, .cur 2, .cur 0]⟩]

/-- Plain mode, count 4: scalars `c₀, c₂, c₃` at lanes `a, a + 3, a + 6`, the challenge at `a + 9`. -/
def tplP4 (a S : Nat) : List LRow :=
  [ldRow a S, ldRow (a + 3) S, ldRow (a + 6) S, ldRow (a + 9) S,
   ⟨.lin 0 1, .E, [.cur 3, .cur 3]⟩,
   ⟨.muladd, .E, [.cur 2, .cur 4, .cur 1]⟩,
   ⟨.muladd, .E, [.cur 5, .cur 4, .prev 7]⟩,
   ⟨.muladd, .E, [.cur 6, .cur 3, .cur 0]⟩]

/-- Equality mode, count 3: scalars `t₁, t₂` at lanes `a, a + 3`, the challenge at `a + 6`, the
factor `e` at `E` cell `eb + es·j`. -/
def tplQ3 (a S eb es : Nat) : List LRow :=
  [ldRow a S, ldRow (a + 3) S, ldRow (a + 6) S,
   ⟨.lin 1 0, .E, [.cur 0, .cur 1]⟩,
   ⟨.muladd, .E, [.abs ⟨.E, eb, [es]⟩, .cur 3, .prev 6]⟩,
   ⟨.muladd, .E, [.cur 1, .cur 2, .cur 0]⟩,
   ⟨.muladd, .E, [.cur 5, .cur 2, .cur 4]⟩]

/-- Equality mode, count 5: scalars `t₁ … t₄` at lanes `a, a + 3, a + 6, a + 9`, the challenge at
`a + 12`, the factor at `E` cell `eb + es·j`. -/
def tplQ5 (a S eb es : Nat) : List LRow :=
  [ldRow a S, ldRow (a + 3) S, ldRow (a + 6) S, ldRow (a + 9) S, ldRow (a + 12) S,
   ⟨.lin 1 0, .E, [.cur 0, .cur 1]⟩,
   ⟨.lin 1 0, .E, [.cur 5, .cur 2]⟩,
   ⟨.lin 1 0, .E, [.cur 6, .cur 3]⟩,
   ⟨.muladd, .E, [.abs ⟨.E, eb, [es]⟩, .cur 7, .prev 12]⟩,
   ⟨.muladd, .E, [.cur 3, .cur 4, .cur 2]⟩,
   ⟨.muladd, .E, [.cur 9, .cur 4, .cur 1]⟩,
   ⟨.muladd, .E, [.cur 10, .cur 4, .cur 0]⟩,
   ⟨.muladd, .E, [.cur 11, .cur 4, .cur 8]⟩]

theorem tplP3_allE (a S : Nat) : AllE (tplP3 a S) := by simp [AllE, tplP3, ldRow]
theorem tplP4_allE (a S : Nat) : AllE (tplP4 a S) := by simp [AllE, tplP4, ldRow]
theorem tplQ3_allE (a S eb es : Nat) : AllE (tplQ3 a S eb es) := by simp [AllE, tplQ3, ldRow]
theorem tplQ5_allE (a S eb es : Nat) : AllE (tplQ5 a S eb es) := by simp [AllE, tplQ5, ldRow]

/-! ## The law of one iteration -/

/-- Round `i` read from memory: the factor, the `m` scalars in `K` cells `a + 3k + S·i`, the
challenge in `a + 3m + S·i`. -/
def memRnd (M : Mem) (a S m : Nat) (eqv : Nat → Option FE) (i : Nat) : Option FE × List FE × FE :=
  (eqv i, (List.range m).map (fun k => kE M (a + 3 * k + S * i)), kE M (a + 3 * m + S * i))

/-- **One round's cells** at base `e` (round `i`): rows `0 … m` hold the round's scalars and
challenge from the lanes, and the last row (`e + L − 1`) the next claim from the claim at `e − 1`. -/
def LawR (M : Mem) (a S m L : Nat) (eqv : Nat → Option FE) (e i : Nat) : Prop :=
  (∀ k ≤ m, M.e (e + k) = kE M (a + 3 * k + S * i)) ∧
    M.e (e + (L - 1)) = rstep (M.e (e - 1)) (memRnd M a S m eqv i)

theorem two_eq_zero_FE : (2 : FE) = 0 := CharTwo.two_eq_zero

theorem kE_idx (M : Mem) {x y : Nat} (h : x = y) : kE M x = kE M y := by rw [h]

section
variable {c : Ctx} {M : Mem}

theorem lawP4 (a S : Nat) (p : Ptr) (i₀ d : Nat) (hp : 1 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplP4 (a + S * i₀) S) p).2) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawR M a S 3 8 (fun _ => none) (p.e + 8 * jf) (i₀ + jf) := by
  have hA := tplP4_allE (a + S * i₀) S
  have hok : OpdsOk (tplP4 (a + S * i₀) S) := by simp [OpdsOk, tplP4, ldRow, kOp, opdOk]
  have E := fun t (ht : t < 8) => loop1_eqs h hA hok (L := 8) rfl hjf ht
  have l0 : M.e (p.e + 0 + 8 * jf) = kE M (a + S * i₀ + S * jf) := rowEq_ld (E 0 (by decide))
  have l1 : M.e (p.e + 1 + 8 * jf) = kE M (a + S * i₀ + 3 + S * jf) := rowEq_ld (E 1 (by decide))
  have l2 : M.e (p.e + 2 + 8 * jf) = kE M (a + S * i₀ + 6 + S * jf) := rowEq_ld (E 2 (by decide))
  have l3 : M.e (p.e + 3 + 8 * jf) = kE M (a + S * i₀ + 9 + S * jf) := rowEq_ld (E 3 (by decide))
  have r4 := E 4 (by decide)
  have r5 := E 5 (by decide)
  have r6 := E 6 (by decide)
  have r7 := E 7 (by decide)
  simp only [tplP4, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, ofK_zero, ofK_one,
    zero_mul, add_zero] at r4 r5 r6 r7
  have hs : ∀ t, p.e + t + 8 * jf = p.e + 8 * jf + t := fun t => by omega
  have hq : p.e + 7 - 8 + 8 * jf = p.e + 8 * jf - 1 := by omega
  rw [hq] at r6
  simp only [hs] at l0 l1 l2 l3 r4 r5 r6 r7
  generalize p.e + 8 * jf = e at *
  have k0 : kE M (a + S * i₀ + S * jf) = kE M (a + 3 * 0 + S * (i₀ + jf)) := kE_idx M (by ring)
  have k1 : kE M (a + S * i₀ + 3 + S * jf) = kE M (a + 3 * 1 + S * (i₀ + jf)) := kE_idx M (by ring)
  have k2 : kE M (a + S * i₀ + 6 + S * jf) = kE M (a + 3 * 2 + S * (i₀ + jf)) := kE_idx M (by ring)
  have k3 : kE M (a + S * i₀ + 9 + S * jf) = kE M (a + 3 * 3 + S * (i₀ + jf)) := kE_idx M (by ring)
  rw [k0] at l0; rw [k1] at l1; rw [k2] at l2; rw [k3] at l3
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
  · simp only [memRnd, rstep, roundPoly, polyEval, sumE, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.headD_cons, List.tail_cons,
      List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, Nat.add_zero, Nat.mul_zero,
      show (8 : Nat) - 1 = 7 from rfl] at l0 l1 l2 l3 ⊢
    rw [← l0, ← l1, ← l2, ← l3, r7, r6, r5, r4]
    linear_combination (M.e (e + 2) * M.e (e + 3) ^ 2) * two_eq_zero_FE

theorem lawP3 (a S : Nat) (p : Ptr) (i₀ d : Nat) (hp : 1 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplP3 (a + S * i₀) S) p).2) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawR M a S 2 6 (fun _ => none) (p.e + 6 * jf) (i₀ + jf) := by
  have hA := tplP3_allE (a + S * i₀) S
  have hok : OpdsOk (tplP3 (a + S * i₀) S) := by simp [OpdsOk, tplP3, ldRow, kOp, opdOk]
  have E := fun t (ht : t < 6) => loop1_eqs h hA hok (L := 6) rfl hjf ht
  have l0 : M.e (p.e + 0 + 6 * jf) = kE M (a + S * i₀ + S * jf) := rowEq_ld (E 0 (by decide))
  have l1 : M.e (p.e + 1 + 6 * jf) = kE M (a + S * i₀ + 3 + S * jf) := rowEq_ld (E 1 (by decide))
  have l2 : M.e (p.e + 2 + 6 * jf) = kE M (a + S * i₀ + 6 + S * jf) := rowEq_ld (E 2 (by decide))
  have r3 := E 3 (by decide)
  have r4 := E 4 (by decide)
  have r5 := E 5 (by decide)
  simp only [tplP3, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, ofK_zero, ofK_one,
    one_mul, add_zero] at r3 r4 r5
  have hs : ∀ t, p.e + t + 6 * jf = p.e + 6 * jf + t := fun t => by omega
  have hq : p.e + 5 - 6 + 6 * jf = p.e + 6 * jf - 1 := by omega
  rw [hq] at r3
  simp only [hs] at l0 l1 l2 r3 r4 r5
  generalize p.e + 6 * jf = e at *
  rw [kE_idx M (show a + S * i₀ + S * jf = a + 3 * 0 + S * (i₀ + jf) by ring)] at l0
  rw [kE_idx M (show a + S * i₀ + 3 + S * jf = a + 3 * 1 + S * (i₀ + jf) by ring)] at l1
  rw [kE_idx M (show a + S * i₀ + 6 + S * jf = a + 3 * 2 + S * (i₀ + jf) by ring)] at l2
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact l0
    · exact l1
    · exact l2
  · simp only [memRnd, rstep, roundPoly, polyEval, sumE, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.headD_cons, List.tail_cons,
      List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, Nat.add_zero, Nat.mul_zero,
      show (6 : Nat) - 1 = 5 from rfl] at l0 l1 l2 ⊢
    rw [← l0, ← l1, ← l2, r5, r4, r3]
    ring

theorem lawQ3 (a S eb es : Nat) (eqv : Nat → Option FE) (p : Ptr) (i₀ d : Nat) (hp : 1 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplQ3 (a + S * i₀) S eb es) p).2)
    (heqv : ∀ jf < 2 ^ d, eqv (i₀ + jf) = some (M.e (eb + es * jf))) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawR M a S 2 7 eqv (p.e + 7 * jf) (i₀ + jf) := by
  have hA := tplQ3_allE (a + S * i₀) S eb es
  have hok : OpdsOk (tplQ3 (a + S * i₀) S eb es) := by
    simp [OpdsOk, tplQ3, ldRow, kOp, opdOk]
  have E := fun t (ht : t < 7) => loop1_eqs h hA hok (L := 7) rfl hjf ht
  have l0 : M.e (p.e + 0 + 7 * jf) = kE M (a + S * i₀ + S * jf) := rowEq_ld (E 0 (by decide))
  have l1 : M.e (p.e + 1 + 7 * jf) = kE M (a + S * i₀ + 3 + S * jf) := rowEq_ld (E 1 (by decide))
  have l2 : M.e (p.e + 2 + 7 * jf) = kE M (a + S * i₀ + 6 + S * jf) := rowEq_ld (E 2 (by decide))
  have r3 := E 3 (by decide)
  have r4 := E 4 (by decide)
  have r5 := E 5 (by decide)
  have r6 := E 6 (by decide)
  simp only [tplQ3, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, ofK_zero, ofK_one,
    one_mul, add_zero, Addr.at, dot, Mem.rd] at r3 r4 r5 r6
  have hs : ∀ t, p.e + t + 7 * jf = p.e + 7 * jf + t := fun t => by omega
  have hq : p.e + 6 - 7 + 7 * jf = p.e + 7 * jf - 1 := by omega
  rw [hq] at r4
  simp only [hs] at l0 l1 l2 r3 r4 r5 r6
  generalize p.e + 7 * jf = e at *
  rw [kE_idx M (show a + S * i₀ + S * jf = a + 3 * 0 + S * (i₀ + jf) by ring)] at l0
  rw [kE_idx M (show a + S * i₀ + 3 + S * jf = a + 3 * 1 + S * (i₀ + jf) by ring)] at l1
  rw [kE_idx M (show a + S * i₀ + 6 + S * jf = a + 3 * 2 + S * (i₀ + jf) by ring)] at l2
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact l0
    · exact l1
    · exact l2
  · simp only [memRnd, rstep, roundPoly, polyEval, sumE, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append,
      List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, Nat.add_zero, Nat.mul_zero,
      show (7 : Nat) - 1 = 6 from rfl, heqv jf hjf] at l0 l1 l2 ⊢
    rw [← l0, ← l1, ← l2, r6, r5, r4, r3]
    ring

theorem lawQ5 (a S eb es : Nat) (eqv : Nat → Option FE) (p : Ptr) (i₀ d : Nat) (hp : 1 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplQ5 (a + S * i₀) S eb es) p).2)
    (heqv : ∀ jf < 2 ^ d, eqv (i₀ + jf) = some (M.e (eb + es * jf))) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawR M a S 4 13 eqv (p.e + 13 * jf) (i₀ + jf) := by
  have hA := tplQ5_allE (a + S * i₀) S eb es
  have hok : OpdsOk (tplQ5 (a + S * i₀) S eb es) := by
    simp [OpdsOk, tplQ5, ldRow, kOp, opdOk]
  have E := fun t (ht : t < 13) => loop1_eqs h hA hok (L := 13) rfl hjf ht
  have l0 : M.e (p.e + 0 + 13 * jf) = kE M (a + S * i₀ + S * jf) := rowEq_ld (E 0 (by decide))
  have l1 : M.e (p.e + 1 + 13 * jf) = kE M (a + S * i₀ + 3 + S * jf) := rowEq_ld (E 1 (by decide))
  have l2 : M.e (p.e + 2 + 13 * jf) = kE M (a + S * i₀ + 6 + S * jf) := rowEq_ld (E 2 (by decide))
  have l3 : M.e (p.e + 3 + 13 * jf) = kE M (a + S * i₀ + 9 + S * jf) := rowEq_ld (E 3 (by decide))
  have l4 : M.e (p.e + 4 + 13 * jf) = kE M (a + S * i₀ + 12 + S * jf) := rowEq_ld (E 4 (by decide))
  have r5 := E 5 (by decide)
  have r6 := E 6 (by decide)
  have r7 := E 7 (by decide)
  have r8 := E 8 (by decide)
  have r9 := E 9 (by decide)
  have r10 := E 10 (by decide)
  have r11 := E 11 (by decide)
  have r12 := E 12 (by decide)
  simp only [tplQ5, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, ofK_zero, ofK_one,
    one_mul, add_zero, Addr.at, dot, Mem.rd] at r5 r6 r7 r8 r9 r10 r11 r12
  have hs : ∀ t, p.e + t + 13 * jf = p.e + 13 * jf + t := fun t => by omega
  have hq : p.e + 12 - 13 + 13 * jf = p.e + 13 * jf - 1 := by omega
  rw [hq] at r8
  simp only [hs] at l0 l1 l2 l3 l4 r5 r6 r7 r8 r9 r10 r11 r12
  generalize p.e + 13 * jf = e at *
  rw [kE_idx M (show a + S * i₀ + S * jf = a + 3 * 0 + S * (i₀ + jf) by ring)] at l0
  rw [kE_idx M (show a + S * i₀ + 3 + S * jf = a + 3 * 1 + S * (i₀ + jf) by ring)] at l1
  rw [kE_idx M (show a + S * i₀ + 6 + S * jf = a + 3 * 2 + S * (i₀ + jf) by ring)] at l2
  rw [kE_idx M (show a + S * i₀ + 9 + S * jf = a + 3 * 3 + S * (i₀ + jf) by ring)] at l3
  rw [kE_idx M (show a + S * i₀ + 12 + S * jf = a + 3 * 4 + S * (i₀ + jf) by ring)] at l4
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
  · simp only [memRnd, rstep, roundPoly, polyEval, sumE, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append,
      List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, Nat.add_zero, Nat.mul_zero,
      show (13 : Nat) - 1 = 12 from rfl, heqv jf hjf] at l0 l1 l2 l3 l4 ⊢
    rw [← l0, ← l1, ← l2, ← l3, ← l4, r12, r11, r10, r9, r8, r7, r6, r5]
    ring

end

/-! ## A run of rounds -/

/-- **A run of sumcheck rounds**: a copy of the claim (the cell the first iteration's `prev`
reads), then one loop per chunk (`runLoops`). The result is the run's last cell: the final claim. -/
def scRunG (tplOf : Nat → List LRow) (ds : List Nat) (claim : Cell) : BM Cell := do
  let _ ← lin .E 0 0 claim claim
  runLoops tplOf ds 0
  let q ← getPtr
  pure (ec (q.e - 1))

theorem scRunG_out (tplOf : Nat → List LRow) (ds : List Nat) (claim : Cell) (p : Ptr) :
    (scRunG tplOf ds claim p).1 = ec (((p.adv (lin .E 0 0 claim claim p).2).adv
      (runLoops tplOf ds 0 (p.adv (lin .E 0 0 claim claim p).2)).2).e - 1) := rfl

theorem scRunG_segs (tplOf : Nat → List LRow) (ds : List Nat) (claim : Cell) (p : Ptr) :
    (scRunG tplOf ds claim p).2 = (lin .E 0 0 claim claim p).2 ++
      ((runLoops tplOf ds 0 (p.adv (lin .E 0 0 claim claim p).2)).2 ++ ([] ++ [])) := rfl

/-- **The run's cells.** With a law of one iteration for every chunk's loop: the result is the
cell `p.e + L·n` and holds the fold of the rounds read from memory (`memRnd`), and round `i`'s
scalars and challenge are the cells `p.e + 1 + L·i + k`, `k ≤ m`. -/
theorem scRunG_spec {c : Ctx} {M : Mem} (tplOf : Nat → List LRow) (L m a S : Nat)
    (eqv : Nat → Option FE) (hL : ∀ i, AllE (tplOf i) ∧ (tplOf i).length = L) (hL1 : 1 ≤ L)
    (ds : List Nat)
    (hlaw : ∀ (p : Ptr) (i₀ d : Nat), (i₀, d) ∈ chunkStarts ds 0 → 1 ≤ p.e →
      SegsHold c M p (loop [d] (tplOf i₀) p).2 →
      ∀ jf < 2 ^ d, LawR M a S m L eqv (p.e + L * jf) (i₀ + jf))
    (claim : Cell) (p : Ptr) (h : SegsHold c M p (scRunG tplOf ds claim p).2) :
    (scRunG tplOf ds claim p).1 = ec (p.e + L * nRounds ds) ∧
      M.e (p.e + L * nRounds ds) =
        scFold (claim.val M) ((List.range (nRounds ds)).map (memRnd M a S m eqv)) ∧
      ∀ i < nRounds ds, ∀ k ≤ m, M.e (p.e + 1 + L * i + k) = kE M (a + 3 * k + S * i) := by
  rw [scRunG_segs, segsHold_append, linE_adv] at h
  have hc := lin_spec h.1
  simp only [lin, rowRes, Cell.val, Ptr.at, ofK_zero, zero_mul, add_zero] at hc
  obtain ⟨hr, hadv⟩ := runLoops_law tplOf L hL (LawR M a S m L eqv) 1 ds 0 ⟨p.k, p.e + 1⟩ hlaw
    (by simp) ((segsHold_append c M _ _ _).mp h.2).1
  simp only [Nat.zero_add] at hr
  have hout : (scRunG tplOf ds claim p).1 = ec (p.e + L * nRounds ds) := by
    rw [scRunG_out, linE_adv, hadv]; congr 1; simp only; omega
  refine ⟨hout, ?_, fun i hi k hk => (hr i hi).1 k hk⟩
  have := chain_fold M.e p.e L (memRnd M a S m eqv) (nRounds ds) fun i hi => by
    have h2 := (hr i hi).2
    rw [show p.e + 1 + L * i + (L - 1) = p.e + L * (i + 1) by rw [Nat.mul_succ]; omega,
      show p.e + 1 + L * i - 1 = p.e + L * i by omega] at h2
    exact h2
  rw [this]
  congr 1

/-! ## `F`'s rounds are the rounds in memory -/

/-- With the run's `K` cells holding the stream's lanes from the entry boundary `L₀` on, the rounds
read from memory are the rounds `F` reads (`scRounds`). -/
theorem memRnd_eq {M : Mem} (sig : ByteArray) (count : Nat) (L₀ n : Nat) (eqs : List (Option FE))
    (hn : eqs.length = n) (eqv : Nat → Option FE) (heq : ∀ i < n, eqv i = eqs.getD i none)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + (9 + 3 * (count - 1)) * n → M.k j = lane sig j) :
    (List.range n).map (memRnd M (L₀ + 5) (9 + 3 * (count - 1)) (count - 1) eqv) =
      scRounds sig count (8 * L₀) eqs := by
  unfold scRounds
  rw [hn]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have hk : ∀ k ≤ count - 1, kE M (L₀ + 5 + 3 * k + (9 + 3 * (count - 1)) * i) =
      feAt sig (8 * L₀ + entB (count - 1) * i + 40 + 24 * k) := by
    intro k hk
    rw [kE_lanes]
    · congr 1; simp only [entB]; ring
    · intro j hj
      apply hlanes
      · omega
      · have : (9 + 3 * (count - 1)) * i + (9 + 3 * (count - 1)) ≤ (9 + 3 * (count - 1)) * n := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'
        omega
  simp only [memRnd, msgAt, chAt, heq i hi', Prod.mk.injEq, true_and]
  refine ⟨List.map_congr_left fun k hk' => hk k (by have := List.mem_range.mp hk'; omega), ?_⟩
  exact hk _ le_rfl

theorem getD_map_range {α : Type} (f : Nat → α) (d : α) {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

/-- **A run against `F`**: if the template's law holds and the `K` cells hold the lanes of the
run's entries, the result is `F`'s `sumcheck` final claim and round `i`'s challenge cell is `F`'s
challenge `i` (the cursor `s` at the entry boundary `8 L₀`). -/
theorem scRunG_eq {c : Ctx} {M : Mem} (count : Nat) (hc : 2 ≤ count) (tplOf : Nat → List LRow)
    (L L₀ : Nat) (eqv : Nat → Option FE) (hL : ∀ i, AllE (tplOf i) ∧ (tplOf i).length = L)
    (hL1 : 1 ≤ L) (ds : List Nat)
    (hlaw : ∀ (p : Ptr) (i₀ d : Nat), (i₀, d) ∈ chunkStarts ds 0 → 1 ≤ p.e →
      SegsHold c M p (loop [d] (tplOf i₀) p).2 →
      ∀ jf < 2 ^ d, LawR M (L₀ + 5) (9 + 3 * (count - 1)) (count - 1) L eqv (p.e + L * jf) (i₀ + jf))
    (claim : Cell) (p : Ptr) (h : SegsHold c M p (scRunG tplOf ds claim p).2)
    (sig : ByteArray) (s : RS) (hs : s.msg = 0) (hent : s.ent = 8 * L₀) (eqs : List (Option FE))
    (hn : eqs.length = nRounds ds) (heq : ∀ i < nRounds ds, eqv i = eqs.getD i none)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + (9 + 3 * (count - 1)) * nRounds ds → M.k j = lane sig j) :
    (scRunG tplOf ds claim p).1.val M = (sumcheck (claim.val M) count eqs sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + L * i + (count - 1)) =
        (sumcheck (claim.val M) count eqs sig s).1.1.getD i 0 := by
  obtain ⟨h1, h2, h3⟩ := scRunG_spec tplOf L (count - 1) (L₀ + 5) (9 + 3 * (count - 1)) eqv hL hL1
    ds hlaw claim p h
  have hR := memRnd_eq (M := M) sig count L₀ (nRounds ds) eqs hn eqv heq hlanes
  rw [sumcheck_run count hc sig eqs _ s hs, hent, ← hR, h1]
  refine ⟨h2, fun i hi => ?_⟩
  rw [h3 i hi _ le_rfl, List.map_map, getD_map_range _ _ hi]
  rfl

/-! ## The four modes -/

/-- Plain rounds, count 3 (the FS entries from lane `L₀` on). -/
def scRunP3 (ds : List Nat) (L₀ : Nat) (claim : Cell) : BM Cell :=
  scRunG (fun i => tplP3 (L₀ + 5 + 15 * i) 15) ds claim

/-- Plain rounds, count 4. -/
def scRunP4 (ds : List Nat) (L₀ : Nat) (claim : Cell) : BM Cell :=
  scRunG (fun i => tplP4 (L₀ + 5 + 18 * i) 18) ds claim

/-- Equality-mode rounds, count 3. The chunk starting at round `i₀` reads its factors from the
`E` cells `ebOf i₀ + esOf i₀ · j` (a GKR point is pieces of challenge cells: `y ++ x`). -/
def scRunQ3 (ds : List Nat) (L₀ : Nat) (ebOf esOf : Nat → Nat) (claim : Cell) : BM Cell :=
  scRunG (fun i => tplQ3 (L₀ + 5 + 15 * i) 15 (ebOf i) (esOf i)) ds claim

/-- Equality-mode rounds, count 5. -/
def scRunQ5 (ds : List Nat) (L₀ : Nat) (ebOf esOf : Nat → Nat) (claim : Cell) : BM Cell :=
  scRunG (fun i => tplQ5 (L₀ + 5 + 21 * i) 21 (ebOf i) (esOf i)) ds claim

/-- The factor cells of an equality-mode run hold the point's coordinates. -/
def PointCells (M : Mem) (ds : List Nat) (ebOf esOf : Nat → Nat) (point : List FE) : Prop :=
  ∀ i₀ d, (i₀, d) ∈ chunkStarts ds 0 → ∀ jf < 2 ^ d, M.e (ebOf i₀ + esOf i₀ * jf) = point.getD (i₀ + jf) 0

theorem chunk_lt : ∀ (ds : List Nat) (i₀ i d : Nat), (i, d) ∈ chunkStarts ds i₀ →
    ∀ jf < 2 ^ d, i + jf < i₀ + nRounds ds
  | [], _, _, _, h => by simp [chunkStarts] at h
  | d' :: ds, i₀, i, d, h => by
    simp only [chunkStarts, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · intro jf hjf; simp only [nRounds, List.map_cons, List.sum_cons]; omega
    · intro jf hjf
      have := chunk_lt ds (i₀ + 2 ^ d') i d h jf hjf
      simp only [nRounds, List.map_cons, List.sum_cons] at this ⊢; omega

theorem pointCells_eqv {M : Mem} {ds : List Nat} {ebOf esOf : Nat → Nat} {point : List FE}
    (hn : point.length = nRounds ds) (hP : PointCells M ds ebOf esOf point) {i₀ d : Nat}
    (hm : (i₀, d) ∈ chunkStarts ds 0) :
    ∀ jf < 2 ^ d, (fun i => (point.map some).getD i none) (i₀ + jf) = some (M.e (ebOf i₀ + esOf i₀ * jf)) := by
  intro jf hjf
  have hlt := chunk_lt ds 0 i₀ d hm jf hjf
  simp only [Nat.zero_add] at hlt
  simp only
  rw [hP i₀ d hm jf hjf, List.getD_eq_getElem _ _ (by simp [hn, hlt]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [hn, hlt])]

section
variable {c : Ctx} {M : Mem}

/-- **Q_arith_eq, plain rounds of count 3** (`F`'s `sumcheck claim 3 (replicate n none)`). -/
theorem scRunP3_eq (ds : List Nat) (L₀ : Nat) (claim : Cell) (p : Ptr)
    (h : SegsHold c M p (scRunP3 ds L₀ claim p).2) (sig : ByteArray) (s : RS) (hs : s.msg = 0)
    (hent : s.ent = 8 * L₀)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + 15 * nRounds ds → M.k j = lane sig j) :
    (scRunP3 ds L₀ claim p).1.val M =
        (sumcheck (claim.val M) 3 (List.replicate (nRounds ds) none) sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + 6 * i + 2) =
        (sumcheck (claim.val M) 3 (List.replicate (nRounds ds) none) sig s).1.1.getD i 0 :=
  scRunG_eq 3 (by decide) _ 6 L₀ (fun _ => none) (fun i => ⟨tplP3_allE _ _, rfl⟩) (by decide) ds
    (fun p i₀ d _ hp h jf hjf => lawP3 (L₀ + 5) 15 p i₀ d hp h jf hjf) claim p h sig s hs hent _
    (by simp) (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hlanes

/-- **Q_arith_eq, plain rounds of count 4** (the table sumcheck's). -/
theorem scRunP4_eq (ds : List Nat) (L₀ : Nat) (claim : Cell) (p : Ptr)
    (h : SegsHold c M p (scRunP4 ds L₀ claim p).2) (sig : ByteArray) (s : RS) (hs : s.msg = 0)
    (hent : s.ent = 8 * L₀)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + 18 * nRounds ds → M.k j = lane sig j) :
    (scRunP4 ds L₀ claim p).1.val M =
        (sumcheck (claim.val M) 4 (List.replicate (nRounds ds) none) sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + 8 * i + 3) =
        (sumcheck (claim.val M) 4 (List.replicate (nRounds ds) none) sig s).1.1.getD i 0 :=
  scRunG_eq 4 (by decide) _ 8 L₀ (fun _ => none) (fun i => ⟨tplP4_allE _ _, rfl⟩) (by decide) ds
    (fun p i₀ d _ hp h jf hjf => lawP4 (L₀ + 5) 18 p i₀ d hp h jf hjf) claim p h sig s hs hent _
    (by simp) (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hlanes

/-- **Q_arith_eq, equality-mode rounds of count 3** (a GKR step of one level): round `i`'s factor
is `point[i]` (`PointCells`). -/
theorem scRunQ3_eq (ds : List Nat) (L₀ : Nat) (ebOf esOf : Nat → Nat) (claim : Cell) (p : Ptr)
    (h : SegsHold c M p (scRunQ3 ds L₀ ebOf esOf claim p).2) (sig : ByteArray) (s : RS)
    (hs : s.msg = 0) (hent : s.ent = 8 * L₀) (point : List FE) (hn : point.length = nRounds ds)
    (hP : PointCells M ds ebOf esOf point)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + 15 * nRounds ds → M.k j = lane sig j) :
    (scRunQ3 ds L₀ ebOf esOf claim p).1.val M =
        (sumcheck (claim.val M) 3 (point.map some) sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + 7 * i + 2) =
        (sumcheck (claim.val M) 3 (point.map some) sig s).1.1.getD i 0 :=
  scRunG_eq 3 (by decide) _ 7 L₀ (fun i => (point.map some).getD i none)
    (fun i => ⟨tplQ3_allE _ _ _ _, rfl⟩) (by decide) ds
    (fun p i₀ d hm hp h jf hjf => lawQ3 (L₀ + 5) 15 _ _ _ p i₀ d hp h (pointCells_eqv hn hP hm) jf hjf)
    claim p h sig s hs hent _ (by simp [hn]) (fun _ _ => rfl) hlanes

/-- **Q_arith_eq, equality-mode rounds of count 5** (a GKR step of two levels). -/
theorem scRunQ5_eq (ds : List Nat) (L₀ : Nat) (ebOf esOf : Nat → Nat) (claim : Cell) (p : Ptr)
    (h : SegsHold c M p (scRunQ5 ds L₀ ebOf esOf claim p).2) (sig : ByteArray) (s : RS)
    (hs : s.msg = 0) (hent : s.ent = 8 * L₀) (point : List FE) (hn : point.length = nRounds ds)
    (hP : PointCells M ds ebOf esOf point)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + 21 * nRounds ds → M.k j = lane sig j) :
    (scRunQ5 ds L₀ ebOf esOf claim p).1.val M =
        (sumcheck (claim.val M) 5 (point.map some) sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + 13 * i + 4) =
        (sumcheck (claim.val M) 5 (point.map some) sig s).1.1.getD i 0 :=
  scRunG_eq 5 (by decide) _ 13 L₀ (fun i => (point.map some).getD i none)
    (fun i => ⟨tplQ5_allE _ _ _ _, rfl⟩) (by decide) ds
    (fun p i₀ d hm hp h jf hjf => lawQ5 (L₀ + 5) 21 _ _ _ p i₀ d hp h (pointCells_eqv hn hP hm) jf hjf)
    claim p h sig s hs hent _ (by simp [hn]) (fun _ _ => rfl) hlanes

end

/-! ## Non-vacuity: the runs pass the program check (`segsOk`, hence `Program.wf`) -/

theorem scRun_segsOk :
    segsOk ⟨400, 20⟩ (scRunP3 [3] 0 (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunP4 [2, 0] 0 (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunQ3 [1, 0] 0 (fun _ => 3) (fun _ => 1) (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunQ5 [1] 0 (fun _ => 3) (fun _ => 1) (ec 0) ⟨400, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
