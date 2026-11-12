import LvmSelfEval

/-!
# A toy LoopIR program: one sumcheck round, an `eq` table, and its own self-evaluation

The acceptance test of WP-10 (A0 §3): a program that verifies one sumcheck round's arithmetic, has
loop blocks, and evaluates its own glue columns at a point read from its inputs, with the fixed
point closed on small parameters (`dc = 5`, `dx = 3`).

Inputs (`K` cells): `0` the gate flag `b`; `1–3` the claim `C`; `4–12` the round polynomial
`a₀ + a₁X + a₂X²`; `13–15` the challenge `ρ`; `16–24` the point `r = (r₀, r₁, r₂)` (each `E` value
three lanes). Blocks:

| block | dims | content | `E` cells |
|---|---|---|---|
| 0 `G1` (glue) | — | load `C, a₀, a₁, a₂, ρ, r₀, r₁, r₂`; `0`, `1`; `p(0) + p(1) + C`, gated `assert0`; `p(ρ)` by Horner; `1 - rᵢ` | `0–18` |
| 1–3 | `[0]`, `[1]`, `[2]` | `eqLevel`: `eq(r, ·)` on 8 cells (variables in reverse) | `19–32` |
| 4 | `[5]` | `fixPro`: 32 zero accumulators | `33–64` |
| 5 | `[5, 3]` | `fixBlock`: `acc[c, x] = F_c(x)·eq[x] + acc[c, x-1]` | `65–320` |
| 6 `G2` (glue) | — | copy of `p(ρ)` | `321` |

* `toy_wf`, `toy_noReadd`, `toy_fit` (kernel-checked): the program check passes; the glue matrix has
  25 ≤ 2^5 columns, every glue piece at most 2^3 rows: **the fixed point closes** (`fixmul`'s
  shape is fixed by the glue it evaluates, and the glue includes the rows `1 - rᵢ` the `eq` table
  needs).
* `toy_round`: in every memory satisfying the rows and the assertions, `b = 1 ⇒ p(0) + p(1) = C`,
  and cell 15 is `p(ρ)`.
* **`toy_selfeval`**: in every memory satisfying the rows, the accumulator of glue column `c` is the
  extension of that column (zero-extended to 8 rows) at `r`.
* `toy_selfeval_interp`: the same for the interpreter's run on any inputs.
-/

namespace Lvm.Loop

open FE Program

/-- An `E` operand that does not move. -/
abbrev eA (n : Nat) : Addr := ⟨.E, n, []⟩
/-- A `K` operand that does not move. -/
abbrev kA (n : Nat) : Addr := ⟨.K, n, []⟩

/-- The first glue block: loads, constants, the round check, Horner, `1 - rᵢ`. -/
def toyG1 : Block :=
  ⟨[], [⟨.loadE, .E, [kA 1, kA 2, kA 3]⟩,          -- E0  C
        ⟨.loadE, .E, [kA 4, kA 5, kA 6]⟩,          -- E1  a₀
        ⟨.loadE, .E, [kA 7, kA 8, kA 9]⟩,          -- E2  a₁
        ⟨.loadE, .E, [kA 10, kA 11, kA 12]⟩,       -- E3  a₂
        ⟨.loadE, .E, [kA 13, kA 14, kA 15]⟩,       -- E4  ρ
        ⟨.loadE, .E, [kA 16, kA 17, kA 18]⟩,       -- E5  r₀
        ⟨.loadE, .E, [kA 19, kA 20, kA 21]⟩,       -- E6  r₁
        ⟨.loadE, .E, [kA 22, kA 23, kA 24]⟩,       -- E7  r₂
        ⟨.lin 1 0, .E, [eA 0, eA 0]⟩,              -- E8  0 = C + C
        ⟨.lin 0 1, .E, [eA 8, eA 8]⟩,              -- E9  1
        ⟨.lin 1 0, .E, [eA 1, eA 2]⟩,              -- E10 a₀ + a₁
        ⟨.lin 1 0, .E, [eA 10, eA 3]⟩,             -- E11 p(1)
        ⟨.lin 1 0, .E, [eA 1, eA 11]⟩,             -- E12 p(0) + p(1)
        ⟨.lin 1 0, .E, [eA 12, eA 0]⟩,             -- E13 p(0) + p(1) + C
        ⟨.assert0, .K, [eA 13, kA 0]⟩,             --     b · E13 = 0
        ⟨.muladd, .E, [eA 3, eA 4, eA 2]⟩,         -- E14 a₂ρ + a₁
        ⟨.muladd, .E, [eA 14, eA 4, eA 1]⟩,        -- E15 p(ρ)
        ⟨.lin 0 1, .E, [eA 5, eA 5]⟩,              -- E16 1 - r₀
        ⟨.lin 0 1, .E, [eA 6, eA 6]⟩,              -- E17 1 - r₁
        ⟨.lin 0 1, .E, [eA 7, eA 7]⟩]⟩             -- E18 1 - r₂

/-- The second glue block. -/
def toyG2 : Block := ⟨[], [⟨.lin 0 0, .E, [eA 15, eA 15]⟩]⟩

/-- **The toy program.** -/
def toy : Program where
  nInK := 25
  nInE := 0
  blocks := [toyG1, eqLevel 0 9 7 18 8, eqLevel 1 19 6 17 8, eqLevel 2 21 5 16 8, fixPro 5 8,
    fixBlock 5 3 25 65, toyG2]
  glue := [0, 6]

theorem toy_wf : toy.wf = true := by decide

theorem toy_noReadd : toy.noReadd = true := by decide

/-- **The fixed point closes**: 25 glue columns fit the `2^5` columns of the `fixmul` block, and
every glue piece has at most `2^3` rows, the `eq` table's size. -/
theorem toy_fit : toy.glueCols.length = 25 ∧ ∀ pc ∈ toy.glueCols, toy.height pc.1 ≤ 3 := by
  decide

theorem toy_starts : toy.start .E 1 = 19 ∧ toy.start .E 2 = 21 ∧ toy.start .E 3 = 25 ∧
    toy.start .E 4 = 33 ∧ toy.start .E 5 = 65 ∧ toy.start .E 6 = 321 := by decide

theorem toy_glue_inst {t : Nat} (ht : t < 20) : toy.inst 0 0 t ∈ toy.insts :=
  (toy.mem_insts _).mpr ⟨0, by decide, 0, by decide, t, by simpa [toy, Program.blk, toyG1] using ht,
    rfl⟩

theorem FE.add_self (x : FE) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- The constant cells of the toy. -/
theorem toy_consts {M : Mem} (hM : toy.Holds M) :
    M.e 8 = 0 ∧ M.e 9 = 1 ∧ ∀ i < 3, M.e (16 + i) = 1 - M.e (5 + i) := by
  have h8 : M.e 8 = M.e 0 + FE.ofK 1 * M.e 0 + FE.ofK 0 := hM _ (toy_glue_inst (t := 8) (by omega))
  have h9 : M.e 9 = M.e 8 + FE.ofK 0 * M.e 8 + FE.ofK 1 := hM _ (toy_glue_inst (t := 9) (by omega))
  have h16 : M.e 16 = M.e 5 + FE.ofK 0 * M.e 5 + FE.ofK 1 := hM _ (toy_glue_inst (t := 17) (by omega))
  have h17 : M.e 17 = M.e 6 + FE.ofK 0 * M.e 6 + FE.ofK 1 := hM _ (toy_glue_inst (t := 18) (by omega))
  have h18 : M.e 18 = M.e 7 + FE.ofK 0 * M.e 7 + FE.ofK 1 := hM _ (toy_glue_inst (t := 19) (by omega))
  have h0 : FE.ofK 0 = 0 := rfl
  have h1 : FE.ofK 1 = 1 := rfl
  have hsub : ∀ r : FE, r + 1 = 1 - r := fun r => by rw [add_comm]; rfl
  refine ⟨by rw [h8, h1, h0, one_mul, add_zero, FE.add_self], ?_, fun i hi => ?_⟩
  · rw [h9, h8, h1, h0, one_mul, add_zero, FE.add_self]; ring
  · interval_cases i
    · rw [h16, h0, h1, zero_mul, add_zero, hsub]
    · rw [h17, h0, h1, zero_mul, add_zero, hsub]
    · rw [h18, h0, h1, zero_mul, add_zero, hsub]

/-- **The round check**: with the rows and the assertions, `b = 1 ⇒ p(0) + p(1) = C`, and cell 15
is `p(ρ) = a₀ + a₁ρ + a₂ρ²`. -/
theorem toy_round {M : Mem} (hM : toy.Holds M) (hA : toy.Asserts M) :
    (M.k 0 = 1 → M.e 1 + (M.e 1 + M.e 2 + M.e 3) = M.e 0) ∧
      M.e 15 = M.e 1 + M.e 2 * M.e 4 + M.e 3 * (M.e 4 * M.e 4) := by
  have h10 : M.e 10 = M.e 1 + FE.ofK 1 * M.e 2 + FE.ofK 0 := hM _ (toy_glue_inst (t := 10) (by omega))
  have h11 : M.e 11 = M.e 10 + FE.ofK 1 * M.e 3 + FE.ofK 0 :=
    hM _ (toy_glue_inst (t := 11) (by omega))
  have h12 : M.e 12 = M.e 1 + FE.ofK 1 * M.e 11 + FE.ofK 0 :=
    hM _ (toy_glue_inst (t := 12) (by omega))
  have h13 : M.e 13 = M.e 12 + FE.ofK 1 * M.e 0 + FE.ofK 0 :=
    hM _ (toy_glue_inst (t := 13) (by omega))
  have hz : FE.ofK (M.k 0) * M.e 13 = 0 := hA _ (toy_glue_inst (t := 14) (by omega))
  have h14 : M.e 14 = M.e 3 * M.e 4 + M.e 2 := hM _ (toy_glue_inst (t := 15) (by omega))
  have h15 : M.e 15 = M.e 14 * M.e 4 + M.e 1 := hM _ (toy_glue_inst (t := 16) (by omega))
  have h0 : FE.ofK 0 = 0 := rfl
  have h1 : FE.ofK 1 = 1 := rfl
  refine ⟨fun hb => ?_, by rw [h15, h14]; ring⟩
  rw [hb, h1, one_mul, h13, h12, h11, h10, h1, h0] at hz
  simp only [one_mul, add_zero] at hz
  have := congrArg (· + M.e 0) hz
  simp only [zero_add] at this
  rw [← this, add_assoc _ (M.e 0) (M.e 0), FE.add_self, add_zero]

/-- **Self-evaluation closes on the toy.** In every memory satisfying the rows, the last
accumulator of glue column `c` (of 32) is the extension of that glue column, zero-extended to 8 rows,
at the point `r = (r₀, r₁, r₂)` the program loaded from its inputs. -/
theorem toy_selfeval {M : Mem} (hM : toy.Holds M) {c : Nat} (hc : c < 2 ^ 5) :
    M.e (65 + (c + 2 ^ 5 * (2 ^ 3 - 1))) =
      mle [M.e 5, M.e 6, M.e 7] (fun x => FE.ofK (toy.fixMat [c, x])) := by
  obtain ⟨hz, hone, homr⟩ := toy_consts hM
  obtain ⟨s1, s2, s3, s4, s5, -⟩ := toy_starts
  have e0 := eqLevel_spec (Q := toy) (b := 1) (by decide) rfl hM (pt := [])
    (fun x hx => by
      have : x = 0 := by simpa using hx
      subst this; simpa [eqW] using hone) hz (homr 2 (by omega))
  rw [s1] at e0
  have e1 := eqLevel_spec (Q := toy) (b := 2) (by decide) rfl hM (pt := [M.e 7])
    (fun x hx => e0 x hx) hz (homr 1 (by omega))
  rw [s2] at e1
  have e2 := eqLevel_spec (Q := toy) (b := 3) (by decide) rfl hM (pt := [M.e 6, M.e 7])
    (fun x hx => e1 x hx) hz (homr 0 (by omega))
  rw [s3] at e2
  have zs := fixPro_spec (Q := toy) (b := 4) (by decide) rfl hM hz
  rw [s4] at zs
  exact fixmul_mle (Q := toy) (b := 5) (by decide) rfl s5.symm (by norm_num) hM (by rfl)
    (fun x hx => e2 x hx) (fun c hc => by simpa using zs c hc) hc

/-- The same for the interpreter's run on any inputs. -/
theorem toy_selfeval_interp (inK : Array FK) (hK : inK.size = 25) {c : Nat} (hc : c < 2 ^ 5) :
    (toy.interpMem inK #[]).e (65 + (c + 2 ^ 5 * (2 ^ 3 - 1))) =
      mle [(toy.interpMem inK #[]).e 5, (toy.interpMem inK #[]).e 6, (toy.interpMem inK #[]).e 7]
        (fun x => FE.ofK (toy.fixMat [c, x])) :=
  toy_selfeval (toy.interp_holds toy_wf inK #[] ⟨hK, rfl⟩ (inb_of_noReadd _ toy_noReadd _ _)).1 hc

end Lvm.Loop
