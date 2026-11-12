import LvmQKeccakTB
import LvmQEqKeccakRead

/-!
# QA1: the Keccak layer's rounds as template gadgets (pack rounds, position rounds)

Unrolled inside the layer template (the layer is the loop). Stream scalars are loads of lanes;
`lv xv str q` is the value of the load at lane `q` (`gLoad_spec`), and a view `v` of `F`'s scalars
matches it at an offset: `lv q = v (8q + off)`. With that, **`gPackRounds_spec`** is `F`'s
`packSpec` (equality-mode rounds with the scale, `keccakPackRounds`) and **`gLocalRounds_spec`** is
`F`'s `scSpec` with four coefficients (the eleven position rounds).

Rows: a pack round 3 loads + 7 rows (`c₀ = r(c₁+c₂) + v`, Horner 2, `1 + r + ρ`, two products);
a position round 4 loads + 5 rows (`c₁ = v + c₂ + c₃`, Horner 3).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- The load at lane `q` (a loop's iteration fixed by `xv`). -/
def lv (xv : Src → FE) (str : List Nat) (q : Nat) : FE :=
  xv (.ext ⟨.K, q, str⟩) + FE.y * xv (.ext ⟨.K, q + 1, str⟩) + FE.y * FE.y * xv (.ext ⟨.K, q + 2, str⟩)

theorem gLoad_lv {xv : Src → FE} {V : Nat → FE} {n q : Nat} {str : List Nat} (h : THold xv V n (gLoad q str n).2) :
    (gLoad q str n).1.valF xv V = lv xv str q := gLoad_spec h

/-! ## Pack rounds -/

/-- One pack round: message `c₁, c₂` at lanes `q, q+3`, challenge at `q+6`. Returns the new value,
the new scale and the challenge. -/
def gPackRound (z : Src) (q : Nat) (str : List Nat) (r value scale : Src) : TB (Src × Src × Src) :=
  gLoad q str >>= fun c1 => gLoad (q + 3) str >>= fun c2 => gLoad (q + 6) str >>= fun ch =>
  gAdd c1 c2 >>= fun s => gMul r s value >>= fun c0 => gMul c2 ch c1 >>= fun h =>
  gMul h ch c0 >>= fun pe => gLin 1 1 r ch >>= fun g => gMul g pe z >>= fun v' =>
  gMul scale g z >>= fun s' => pure (v', s', ch)

/-- The pack rounds from lane `q` (15 lanes a round). -/
def gPackRounds (z : Src) (str : List Nat) : Nat → List Src → Src → Src → TB (Src × Src × List Src)
  | _, [], value, scale => pure (value, scale, [])
  | q, r :: rs, value, scale =>
    gPackRound z q str r value scale >>= fun a =>
      gPackRounds z str (q + 15) rs a.1 a.2.1 >>= fun b => pure (b.1, b.2.1, a.2.2 :: b.2.2)

theorem one_add_one_mul (x : FE) : FE.ofK 1 * x = x := by rw [show FE.ofK 1 = 1 from rfl, one_mul]

theorem gPackRound_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {v : Nat → FE}
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) (hN : q + 6 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (r value scale : Src) (n : Nat) (h : THold xv V n (gPackRound z q str r value scale n).2) :
    (gPackRound z q str r value scale n).1.1.valF xv V =
        (1 + r.valF xv V + v (p + 88)) *
          polyEval (roundPoly v p 3 (value.valF xv V) (some (r.valF xv V))) (v (p + 88)) ∧
    (gPackRound z q str r value scale n).1.2.1.valF xv V = scale.valF xv V * (1 + r.valF xv V + v (p + 88)) ∧
    (gPackRound z q str r value scale n).1.2.2.valF xv V = v (p + 88) := by
  unfold gPackRound at h ⊢
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h4, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h9, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h10, -⟩ := (thold_bind _ _).mp h
  have e1 := gLoad_lv h1
  have e2 := gLoad_lv h2
  have e3 := gLoad_lv h3
  have e4 := gAdd_spec h4
  have e5 := gMul_spec h5
  have e6 := gMul_spec h6
  have e7 := gMul_spec h7
  have e8 := gLin_spec h8
  have e9 := gMul_spec h9
  have e10 := gMul_spec h10
  simp only [tb_bind, tb_pure]
  rw [hv _ (by omega)] at e1; rw [hv _ (by omega)] at e2; rw [hv _ (by omega)] at e3
  have q1 : 8 * q + off = p + 40 := by omega
  have q2 : 8 * (q + 3) + off = p + 64 := by omega
  have q3 : 8 * (q + 6) + off = p + 88 := by omega
  rw [q1] at e1; rw [q2] at e2; rw [q3] at e3
  simp only [roundPoly, scalarsAt, show (3 - 1 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumE, polyEval, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [e9, e8, e7, e6, e5, e4, e1, e2, e3, hz, one_add_one_mul]
    simp only [show (FE.ofK 1) = 1 from rfl, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    ring
  · rw [e10, e8, e3, hz, one_add_one_mul]
    simp only [show (FE.ofK 1) = 1 from rfl]
    ring
  · exact e3

/-- **The pack rounds are `F`'s `packSpec`.** -/
theorem gPackRounds_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {v : Nat → FE}
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) :
    ∀ (rs : List Src) (q p : Nat), q + 15 * rs.length ≤ N → p + 40 = 8 * q + off → ∀ (value scale : Src) (n : Nat),
      THold xv V n (gPackRounds z str q rs value scale n).2 →
      (gPackRounds z str q rs value scale n).1.1.valF xv V =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).1 ∧
      (gPackRounds z str q rs value scale n).1.2.1.valF xv V =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).2.1 ∧
      (gPackRounds z str q rs value scale n).1.2.2.map (Src.valF xv V) =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).2.2.1
  | [], q, p, _, _, value, scale, n, _ => by simp [gPackRounds, tb_pure, packSpec]
  | r :: rs, q, p, hN, hp, value, scale, n, h => by
    simp only [gPackRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    obtain ⟨e1, e2, e3⟩ := gPackRound_spec hz hv (by simp at hN; omega) hp r value scale n h1
    have ih := gPackRounds_spec hz hv rs (q + 15) (p + 120) (by simp at hN; omega) (by omega) _ _ _ h2
    simp only [tb_bind, tb_pure, List.map_cons, packSpec]
    rw [e1, e2] at ih
    exact ⟨ih.1, ih.2.1, congrArg₂ List.cons e3 ih.2.2⟩

/-! ## Position rounds (plain, four coefficients) -/

/-- One position round: `c₀, c₂, c₃` at lanes `q, q+3, q+6`, challenge at `q+9`. Returns the new
claim and the challenge. -/
def gLocalRound (q : Nat) (str : List Nat) (value : Src) : TB (Src × Src) :=
  gLoad q str >>= fun c0 => gLoad (q + 3) str >>= fun c2 => gLoad (q + 6) str >>= fun c3 =>
  gLoad (q + 9) str >>= fun ch => gAdd value c2 >>= fun s => gAdd s c3 >>= fun c1 =>
  gMul c3 ch c2 >>= fun h1 => gMul h1 ch c1 >>= fun h2 => gMul h2 ch c0 >>= fun h3 => pure (h3, ch)

/-- The position rounds from lane `q` (18 lanes a round). -/
def gLocalRounds (str : List Nat) : Nat → Nat → Src → TB (Src × List Src)
  | 0, _, value => pure (value, [])
  | k + 1, q, value =>
    gLocalRound q str value >>= fun a => gLocalRounds str k (q + 18) a.1 >>= fun b => pure (b.1, a.2 :: b.2)

theorem gLocalRound_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE}
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) (hN : q + 9 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (value : Src) (n : Nat) (h : THold xv V n (gLocalRound q str value n).2) :
    (gLocalRound q str value n).1.1.valF xv V =
        polyEval (roundPoly v p 4 (value.valF xv V) none) (v (p + 40 + 24 * (4 - 1))) ∧
    (gLocalRound q str value n).1.2.valF xv V = v (p + 40 + 24 * (4 - 1)) := by
  unfold gLocalRound at h ⊢
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h4, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h9, -⟩ := (thold_bind _ _).mp h
  have e1 := gLoad_lv h1
  have e2 := gLoad_lv h2
  have e3 := gLoad_lv h3
  have e4 := gLoad_lv h4
  have e5 := gAdd_spec h5
  have e6 := gAdd_spec h6
  have e7 := gMul_spec h7
  have e8 := gMul_spec h8
  have e9 := gMul_spec h9
  simp only [tb_bind, tb_pure]
  rw [hv _ (by omega)] at e1; rw [hv _ (by omega)] at e2; rw [hv _ (by omega)] at e3
  rw [hv _ (by omega)] at e4
  rw [show 8 * q + off = p + 40 by omega] at e1
  rw [show 8 * (q + 3) + off = p + 64 by omega] at e2
  rw [show 8 * (q + 6) + off = p + 88 by omega] at e3
  rw [show 8 * (q + 9) + off = p + 40 + 24 * (4 - 1) by omega] at e4
  refine ⟨?_, e4⟩
  simp only [roundPoly, scalarsAt, show (4 - 2 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumE, polyEval, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil]
  rw [e9, e8, e7, e6, e5, e1, e2, e3, e4]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show p + 64 + 24 = p + 88 by omega]
  ring

/-- **The position rounds are `F`'s `scSpec` with four coefficients.** -/
theorem gLocalRounds_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE}
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) :
    ∀ (k q p : Nat), q + 18 * k ≤ N → p + 40 = 8 * q + off → ∀ (value : Src) (n : Nat),
      THold xv V n (gLocalRounds str k q value n).2 →
      (gLocalRounds str k q value n).1.1.valF xv V = (scSpec v 4 p (value.valF xv V) (List.replicate k none)).2 ∧
      (gLocalRounds str k q value n).1.2.map (Src.valF xv V) = (scSpec v 4 p (value.valF xv V) (List.replicate k none)).1
  | 0, q, p, _, _, value, n, _ => by simp [gLocalRounds, tb_pure, scSpec]
  | k + 1, q, p, hN, hp, value, n, h => by
    simp only [gLocalRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    obtain ⟨e1, e2⟩ := gLocalRound_spec hv (by omega) hp value n h1
    have ih := gLocalRounds_spec hv k (q + 18) (p + roundLen 4) (by omega) (by simp [roundLen]; omega) _ _ h2
    simp only [tb_bind, tb_pure, List.map_cons, List.replicate_succ, scSpec]
    rw [e1] at ih
    exact ⟨ih.1, congrArg₂ List.cons e2 ih.2⟩

end Lvm.Q1
