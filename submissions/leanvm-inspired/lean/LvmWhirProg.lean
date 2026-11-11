-- New for lvm (WP-7). The threaded state and loops (`WhirStateT`, `foldRoundsT`, `tailRoundsT`, `glueT`) are ported
-- verbatim from leanVM `formal/lean_vm/LeanVM/Protocol/Verifier/WhirTarget.lean` (formal rev 40f877dc); the level
-- loop `whirLevelsUd` is leanVM's `whirLevelsT` without the out-of-domain step and the proof of work, with the
-- levels as a parameter, `per` positions per challenge, and per-level commitment indices.
/-
  LeanVM.Protocol.Verifier (lvm: WHIR in the unique-decoding regime)

  The WHIR opening of the lvm verifier as a program of the verifier language: leanVM's level loop
  with the running claim threaded through every level, in the unique-decoding regime.
-/

import LvmClaims
import LvmVCore
import LvmDslProg
import LvmNovelBasis

/-!
# The unique-decoding WHIR opening

leanVM's `verify_whir` (`crates/verifier/src/whir.rs:141-265`, the threaded form of
`Verifier/WhirTarget.lean`) runs, per level: the fold rounds; the next commitment and its
out-of-domain sample, answer and intro polynomial (or, on the final level, the residual); a proof
of work; the query positions, the batching challenge `λ`, the openings and the query intro
polynomial; the glue; and, after the final level, the tail rounds and the terminal check.

lvm's opening (BLUEPRINT §3, A11, A13; `docs/lvm/ref/params.py`, `Sched.whir`) is the same loop with:

* **no out-of-domain step** (list size `1` makes it useless): a level with a next commitment
  glues one claim (the batched queries, with `λ¹`), as leanVM's final level does;
* **the proof of work as a read nonce** (PI-GRIND, `UdConfig.grind = g`): with `g > 0`, a
  separating challenge, the nonce (a prover scalar) and a PoW challenge with its top `g` bits
  zero before the positions; no `grind` node (the compiler needs `NoGrind`); `g = 0` is v1's level;
* the levels given as a list (`UdConfig.levels`), not derived by `Whir.ladder`;
* query positions drawn `per` at a time from a challenge (`samplePositions`: bit fields of
  `depth` bits, low first, `min per remaining` per challenge; lvm: `per = 8`);
* with `direct` (lvm's `C_rec`, BLUEPRINT A10; WP-11a `LvmDecideWhir.directFinal`), the final level
  also checks every opened position against the residual's encoding, `fold_q = Enc(f)(x_q)`,
  before the tail rounds (a `require`: it only rejects more);
* level `j` opens commitment `cidx c₀ n₀ j`: `c₀` for level `0` (a root committed before the
  opening, one of the `n₀` commitments present when it starts), `n₀ + j − 1` for the commitment
  level `j − 1` added. Two openings share a history this way (lvm: `C_main`'s root is commitment
  `0`, `C_rec`'s `1`, `n₀ = 2`; `C_rec`'s one-level opening adds no commitment).

`verifyStackedUd` batches the stack claims with powers of one challenge into one opening (leanVM
`verify_stacked_opening`). `viewC c₀ n₀ cs` is the opening's view of the commitments: its level-0
word, then the words it added; the soundness proofs reason on the view with leanVM's level
indices (`getElem?_viewC`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile Claims

section

/-! ## The threaded state (leanVM `WhirTarget`) -/

/-- `WhirState` with the running claim. -/
structure WhirStateT where
  target : E
  quad : List E
  folds : List E
  glued : List GluedClaim

/-- `foldRounds`, folding the running claim. -/
def foldRoundsT : ℕ → WhirStateT → List E → VerifierProgram (WhirStateT × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsT n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` from a running claim, which it returns when there is no round. -/
def tailRoundsT : ℕ → E → List E → VerifierProgram (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsT n target quad
      return (challenge :: rest, target)

/-- `glue`, adding the pending claims' values to the running claim. -/
def glueT (lam : E) (s : WhirStateT) (pending : List (E × List E × (List E → E))) : WhirStateT :=
  (pending.foldl (fun (acc : WhirStateT × E) (value, intro, weightAt) ↦
    let scalar := acc.2 * lam
    let s := acc.1
    ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad intro,
              target := s.target + scalar * value,
              glued := s.glued ++ [⟨scalar, s.folds.length, weightAt⟩] }, scalar)) (s, 1)).1

/-! ## Positions and commitment indices -/

/-- The loop of the positions: each challenge yields up to `per` positions of `depth` bits, low
bits first (leanVM `sampleQueriesAux` with `per` in place of `192 / depth`). -/
def samplePositionsAux (per depth : ℕ) : ℕ → ℕ → VerifierProgram (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← VerifierProgram.sampleChallenge)
      let n := min per remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← samplePositionsAux per depth fuel (remaining - n)
      return chunk ++ rest

/-- `count` positions below `2^depth`, `per` per challenge. -/
def samplePositions (per depth count : ℕ) : VerifierProgram (List ℕ) :=
  samplePositionsAux per depth count count

/-- The commitment level `j` opens: `c₀` for level `0`, then the ones the opening added. -/
def cidx (c₀ n₀ : ℕ) : ℕ → ℕ
  | 0 => c₀
  | j + 1 => n₀ + j

/-- The encoding of the residual (its table on `κ` variables) at position `q` (`0` off the
domain). -/
def encRes (κ R : ℕ) (residual : List E) (q : ℕ) : E :=
  if h : q < 2 ^ (κ + R) then
    Whir.enc κ R (fun x ↦ residual.getD (Whir.bitsToNat x) 0) ⟨q, h⟩
  else 0

/-- **The direct final check**: every opened position's lane fold is the residual's encoding
there. -/
def directOK (κ R : ℕ) (residual : List E) (queries : List ℕ) (rows : List (List E))
    (levelFolds : List E) : Prop :=
  ∀ p ∈ List.zip queries rows, encRes κ R residual p.1 = dot p.2 (eqKernel levelFolds)

instance (κ R : ℕ) (residual : List E) (queries : List ℕ) (rows : List (List E))
    (levelFolds : List E) : Decidable (directOK κ R residual queries rows levelFolds) := by
  unfold directOK; infer_instance

/-! ## The configuration and the program -/

/-- **The configuration of a unique-decoding WHIR opening**: the stack's variables `μ`, the levels
(fold, rate exponent, positions), the positions per challenge, the index of the level-0
commitment and the number of commitments present when the opening starts. -/
structure UdConfig where
  /-- The stack's variables. -/
  μ : ℕ
  /-- The levels, first first. -/
  levels : List Whir.Level
  /-- Positions per challenge. -/
  per : ℕ
  /-- The level-0 commitment. -/
  c₀ : ℕ
  /-- The commitments present at the start. -/
  n₀ : ℕ
  /-- The direct final check (A10). -/
  direct : Bool
  /-- The proof-of-work bits on every level's query group (PI-GRIND; `0`: none, v1's program). -/
  grind : ℕ

/-! ## In-answer grinding (PI-GRIND)

With `g > 0`, a level's query group starts with a proof of work: after the cap (or the final
scalars) the verifier draws a **separating challenge** (its query absorbs the cap or the final, so
that a nonce attempt is one short query `st ‖ nonce`), reads the **nonce** (a prover scalar, so
the query group starts at the boundary it ends), then draws the **PoW challenge**, whose top `g`
bits must be zero (`powOK`: `int(c) < 2^(192 − g)`), before the positions. The PoW challenge and
the positions are one group: its escape is `2^-g` times the positions' (`LvmWhirGrind`:
`escRet_powCheck_le`, `escRet_queryFragG_le_ud`, `escRet_queryFragG_le_finViol`). -/

/-- The proof of work holds on the challenge `c`: its top `g` bits (of `192`) are zero. -/
def powOK (g : ℕ) (c : E) : Prop := eToNat c < 2 ^ (192 - g)

instance (g : ℕ) (c : E) : Decidable (powOK g c) := by unfold powOK; infer_instance

/-- Before the proof of work: the separating challenge and the nonce (nothing at `g = 0`). -/
def grindPre (g : ℕ) : VerifierProgram Unit :=
  if g = 0 then pure () else
    VerifierProgram.sampleChallenge.bind fun _ ↦ VerifierProgram.readScalar.bind fun _ ↦ pure ()

/-- The proof of work: the PoW challenge, its top `g` bits zero (nothing at `g = 0`). -/
def powCheck (g : ℕ) : VerifierProgram Unit :=
  if g = 0 then pure () else
    VerifierProgram.sampleChallenge.bind fun c ↦ VerifierProgram.require (powOK g c)

/-- **The level loop** (leanVM `whirLevelsT` without the out-of-domain step; the proof of work of `g`
bits as `grindPre g`, `powCheck g`): level `index` of the levels, from the state `s`. -/
def whirLevelsUd (logN laneFolds per c₀ n₀ g : ℕ) (direct : Bool) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirStateT → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsT level.fold s []
    let messageLog := logN - s.folds.length
    let residual ← match rest with
      | [] => VerifierProgram.readScalars (2 ^ messageLog)
      | next :: _ => do
        VerifierProgram.readCommitment (messageLog - next.fold + next.logInvRate)
          (3 * 2 ^ next.fold)
        pure []
    grindPre g
    powCheck g
    let queries ← samplePositions per (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings (cidx c₀ n₀ index) queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let s := glueT lam s [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    match rest with
    | [] =>
      (if direct then VerifierProgram.require
          (directOK messageLog level.logInvRate residual queries rows levelFolds)
        else pure ()).bind fun _ ↦ do
      let (tailFolds, target) ← tailRoundsT messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      VerifierProgram.require (terminal = target)
    | _ :: _ => whirLevelsUd logN laneFolds per c₀ n₀ g direct evaluateBasis (index + 1) rest s

/-- **The unique-decoding WHIR opening** of the claim `(evaluateBasis, target)` on the stack whose
root is commitment `cfg.c₀`. -/
def verifyWhirUd (cfg : UdConfig) (target : E) (evaluateBasis : List E → E) :
    VerifierProgram Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsUd cfg.μ ((cfg.levels.head?.map (·.fold)).getD 0) cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct
    evaluateBasis 0 cfg.levels ⟨target, quad, [], []⟩

/-- **The stacked opening**: the claims batched with powers of one challenge (leanVM
`verify_stacked_opening`, `lib.rs:122-139`). -/
def verifyStackedUd (cfg : UdConfig) (claims : List StackClaim) : VerifierProgram Unit := do
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhirUd cfg (dot scales (claims.map (·.2))) fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- The root commitment of a configuration: `2^(μ − ℓ₀ + R₀)` leaves of `2^ℓ₀` words (leanVM
`commitStack`). -/
def commitRootUd (cfg : UdConfig) : VerifierProgram Unit :=
  match cfg.levels with
  | [] => VerifierProgram.fail
  | level :: _ => VerifierProgram.readCommitment (cfg.μ - level.fold + level.logInvRate)
      (2 ^ level.fold)

/-! ## The opening's view of the commitments -/

/-- The empty commitment (height `0`), the view's filler when the root is missing. -/
def noCommit : ℕ × ℕ × Word := (0, 0, fun _ ↦ [])

/-- **The opening's view** of the commitments `cs`: its root `cs[c₀]`, then the commitments after
the first `n₀` (empty if fewer than `n₀`). Level `j` of the opening reads entry `j` of the view. -/
def viewC (c₀ n₀ : ℕ) (cs : List (ℕ × ℕ × Word)) : List (ℕ × ℕ × Word) :=
  if n₀ ≤ cs.length then ((cs.take n₀)[c₀]?.getD noCommit) :: cs.drop n₀ else []

theorem viewC_append {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)} (h : n₀ ≤ cs.length)
    (l : List (ℕ × ℕ × Word)) : viewC c₀ n₀ (cs ++ l) = viewC c₀ n₀ cs ++ l := by
  have h' : n₀ ≤ (cs ++ l).length := by simp; omega
  simp only [viewC, h, h', ↓reduceIte, List.cons_append, List.take_append_of_le_length h,
    List.drop_append_of_le_length h]

/-- The view's level-0 word is the root's, once the `n₀` commitments are present. -/
theorem wordOf_viewC_zero {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)} (hc : c₀ < n₀)
    (hn : n₀ ≤ cs.length) :
    ((viewC c₀ n₀ cs)[0]?.map fun c ↦ c.2.2) = (cs[c₀]?.map fun c ↦ c.2.2) := by
  have hlt : c₀ < (cs.take n₀).length := by simp; omega
  simp only [viewC, hn, ↓reduceIte, List.getElem?_cons_zero, List.getElem?_eq_getElem hlt,
    Option.getD_some, Option.map_some, List.getElem_take, List.getElem?_eq_getElem (show c₀ < cs.length by omega)]

theorem le_length_of_viewC {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : (viewC c₀ n₀ cs) ≠ []) : n₀ ≤ cs.length := by
  by_contra hn
  exact h (by simp [viewC, hn])

theorem length_viewC {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)} (h : n₀ ≤ cs.length) :
    (viewC c₀ n₀ cs).length = cs.length - n₀ + 1 := by
  simp [viewC, h]

/-- **The view reads the commitment level `j` opens.** -/
theorem getElem?_viewC {c₀ n₀ j : ℕ} {cs : List (ℕ × ℕ × Word)} {x : ℕ × ℕ × Word}
    (hc : c₀ < n₀) (h : (viewC c₀ n₀ cs)[j]? = some x) :
    cs[cidx c₀ n₀ j]? = some x := by
  have hne : viewC c₀ n₀ cs ≠ [] := by
    intro he; rw [he] at h; simp at h
  have hn := le_length_of_viewC hne
  cases j with
  | zero =>
    simp only [viewC, hn, ↓reduceIte, List.getElem?_cons_zero, Option.some.injEq] at h
    have hlt : c₀ < (cs.take n₀).length := by simp; omega
    rw [List.getElem?_eq_getElem hlt, Option.getD_some] at h
    simp only [cidx]
    rw [← h, List.getElem?_eq_getElem (by omega)]
    simp
  | succ j =>
    simp only [viewC, hn, ↓reduceIte, List.getElem?_cons_succ, List.getElem?_drop] at h
    simpa [cidx] using h

end

end LeanVM.Protocol.Verifier
