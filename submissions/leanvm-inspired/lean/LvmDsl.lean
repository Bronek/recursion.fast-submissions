-- Ported from leanVM `formal/Statement/LeanVmVerifier.lean` (formal rev 40f877dc), Part 2 without
-- the compiled reading (lines 164-295; `VerifierProgramState`, `climb`, `openOne`, `openAll`,
-- `openPhase`, `run`, `runProof` cut: they are the duplex/Merkle reading, which lvm replaces by a
-- hash chain over the contract oracle), and `formal/Statement/Prover/Script.lean` (the prover's
-- language), as `LvmDsl` for lvm (WP-2).
import LvmFields
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

section

/-! # Part 2: the transcript

The verifier touches the proof through five operations of its `Transcript`
(`crates/verifier/src/transcript.rs:77-217`): `next_scalar`, `sample`, `grind_check`, a root read
as two scalars, and `merkle`. It computes everything else from their results; `VerifierProgram α`
is the free monad over them, run (`run`, `runProof`) as the deployed non-interactive verifier: the
challenges squeezed out of a duplex sponge and the rows authenticated by Merkle paths.

The sponge is the duplex of `Field.lean` (`Sponge`, `absorb`, `squeeze`, `seedInput`), over
Keccak-f[1600] in the deployed verifier. Merkle openings come from a separate channel that the
sponge does not absorb: each query's opening is its position, the leaf's words, hashed as bytes,
then one sibling per level, the position's bit at the level choosing the side.

The proof is the Rust verifier's `Proof` (`transcript.rs:9-15`): the scalar stream, and the Merkle
openings grouped in phases, one phase per opened commitment, each query's opening (`MerklePath`,
`crates/verifier/src/merkle.rs:17-25`: position, leaf, siblings) in the order the verifier samples
the queries; the proof's wire encoding (`wire.rs`, a compression layer formalized in `lean_vm`)
needs the phases. A phase is checked as `Transcript::merkle` checks it (`transcript.rs:153-186`):
its shape, then its positions, then its roots.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- The verifier language: a program returns a value of type `α` after reading scalars,
sampling challenges, checking proofs of work, reading commitments and opening rows, or fails. -/
inductive VerifierProgram (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Reject. -/
  | fail
  /-- Read the next prover scalar, absorbed into the sponge (`next_scalar`). -/
  | read (k : E → VerifierProgram α)
  /-- Sample a challenge, squeezed from the sponge (`sample`). -/
  | sample (k : E → VerifierProgram α)
  /-- Check a proof of work of `bits` bits, the nonce read and absorbed (`grind_check`). -/
  | grind (bits : ℕ) (k : VerifierProgram α)
  /-- Read a Merkle root as two scalars (`Digest::from_halves` of `next_scalars(2)`), the committed
  matrix being `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (k : VerifierProgram α)
  /-- Open rows of the `i`-th commitment at `positions`, each with its authentication path
  (`merkle`); continue with the rows. -/
  | query (i : ℕ) (positions : List ℕ) (k : List (List K) → VerifierProgram α)

namespace VerifierProgram

variable {α β γ : Type}

/-- Sequencing. -/
def bind : VerifierProgram α → (α → VerifierProgram β) → VerifierProgram β
  | ret a, f => f a
  | fail, _ => fail
  | read k, f => read fun x ↦ (k x).bind f
  | sample k, f => sample fun x ↦ (k x).bind f
  | grind b k, f => grind b (k.bind f)
  | commit h w k, f => commit h w (k.bind f)
  | query i ps k, f => query i ps fun r ↦ (k r).bind f

instance : Monad VerifierProgram where
  pure := ret
  bind := bind

/-- Read one prover scalar. -/
def readScalar : VerifierProgram E := read ret

/-- Read `n` prover scalars, in order. -/
def readScalars : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← readScalar
    let xs ← readScalars n
    return x :: xs

/-- Sample one challenge. -/
def sampleChallenge : VerifierProgram E := sample ret

/-- Sample `n` challenges, in order. -/
def sampleChallenges : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleChallenge
    let xs ← sampleChallenges n
    return x :: xs

/-- Check a proof of work of `bits` bits. -/
def grindProofOfWork (bits : ℕ) : VerifierProgram Unit := grind bits (ret ())

/-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
def readCommitment (height width : ℕ) : VerifierProgram Unit := commit height width (ret ())

/-- Open rows of the `i`-th commitment. -/
def queryOpenings (i : ℕ) (positions : List ℕ) : VerifierProgram (List (List K)) := query i
    positions ret

/-- Reject unless `c` holds (`require`, `lib.rs:115-117`). -/
def require (c : Prop) [Decidable c] : VerifierProgram Unit := if c then ret () else fail

end VerifierProgram

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-! ## Proofs and the run -/

/-- The proof-of-work predicate on the challenge sampled after the nonce: at `bits = 0` the nonce
is `0`; otherwise the low `bits` bits of the challenge's first limb are zero
(`Transcript::grind_check`, `transcript.rs:135-151`). -/
def powOk (bits : ℕ) (nonce challenge : E) : Bool :=
  if bits = 0 then decide (nonce.limb 0 = 0 ∧ nonce.limb 1 = 0 ∧ nonce.limb 2 = 0)
  else decide ((challenge.limb 0).lane.toNat % 2 ^ bits = 0)

/-- One Merkle opening (`MerklePath`, `crates/verifier/src/merkle.rs:17-25`): the position it
opens, the leaf's words and the siblings from the leaf up. -/
structure Opening where
  /-- The position of the leaf (`leaf_index`). -/
  leafIndex : ℕ
  /-- The leaf's words. -/
  leaf : List K
  /-- The siblings from the leaf up. -/
  path : List Digest

/-- A proof (`Proof`, `crates/verifier/src/transcript.rs:9-15`): the scalar stream, and the Merkle
openings, one phase per commitment opened, each query's opening in the order the verifier samples
the queries. -/
structure Proof where
  /-- The scalars the prover sends, in order. -/
  stream : List E
  /-- The Merkle openings, one list per phase, in order. -/
  openings : List (List Opening)

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A committed matrix: the row at each position; one of `2^height` rows is read at its first
`2^height` positions (`Transcript::merkle`, `crates/verifier/src/transcript.rs:157-186`). -/
abbrev Word : Type := ℕ → List K

end LeanVM.Protocol.Compile

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- An honest prover as a program of its own moves. -/
inductive Script (α : Type) : Type where
  /-- Stop with a value. -/
  | ret (a : α)
  /-- Send the scalar `x`. -/
  | send (x : E) (k : Script α)
  /-- Receive a challenge. -/
  | sample (k : E → Script α)
  /-- Pass a proof of work. -/
  | grind (k : Script α)
  /-- Commit a matrix. -/
  | commit (word : Word) (k : Script α)
  /-- Receive the opened rows. -/
  | query (k : List (List K) → Script α)

namespace Script

variable {α β : Type}

/-- Sequencing. -/
def bind : Script α → (α → Script β) → Script β
  | ret a, f => f a
  | send x k, f => send x (k.bind f)
  | sample k, f => sample fun c ↦ (k c).bind f
  | grind k, f => grind (k.bind f)
  | commit w k, f => commit w (k.bind f)
  | query k, f => query fun r ↦ (k r).bind f

instance : Monad Script where
  pure := ret
  bind := bind

/-- Send one scalar. -/
def sendE (x : E) : Script Unit := send x (ret ())

/-- Send a list of scalars, in order. -/
def sendList : List E → Script Unit
  | [] => ret ()
  | x :: xs => send x (sendList xs)

/-- Receive one challenge. -/
def sampleE : Script E := sample ret

/-- Receive `n` challenges, in order. -/
def sampleN : ℕ → Script (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleE
    let xs ← sampleN n
    return x :: xs

/-- Pass a proof of work. -/
def grindS : Script Unit := grind (ret ())

/-- Commit a matrix. -/
def commitS (word : Word) : Script Unit := commit word (ret ())

/-- Receive opened rows. -/
def queryS : Script (List (List K)) := query ret

/-- **The script `S` beside the verifier's program `P`**: `S`'s moves, ending in `P`'s result,
which `P` computes from them; `default` where they are not `P`'s, which an honest script never
meets. A phase's prover hands the next phase the verifier's own values (claims, points). -/
def alongside {α : Type} [Inhabited α] : VerifierProgram α → Script β → Script α
  | .ret a, _ => ret a
  | .read k, send x S => send x (alongside (k x) S)
  | .sample k, sample S => sample fun c ↦ alongside (k c) (S c)
  | .grind _ k, grind S => grind (alongside k S)
  | .commit _ _ k, commit w S => commit w (alongside k S)
  | .query _ _ k, query S => query fun rows ↦ alongside (k rows) (S rows)
  | _, _ => ret default

end Script

/-! ## A sumcheck prover -/

/-- The coefficients the wire carries, as the verifier's `sumcheckRoundPoly` rebuilds them: all but
the linear one in plain mode (`none`), all but the constant one in equality mode (`some r`). -/
def wire : Option E → List E → List E
  | none, c => c.headD 0 :: c.drop 2
  | some _, c => c.drop 1

/-- **A stateful sumcheck prover**: per round the coefficients `round st` (constant first) on the
wire in the round's mode, then the challenge `c`, the state becoming `fold st c`; the challenges
in order, and the last state. -/
def sumcheckBy {σ : Type} (round : σ → List E) (fold : σ → E → σ) :
    List (Option E) → σ → Script (List E × σ)
  | [], st => .ret ([], st)
  | mode :: modes, st =>
    (Script.sendList (wire mode (round st))).bind fun _ ↦ Script.sampleE.bind fun c ↦
      (sumcheckBy round fold modes (fold st c)).bind fun r ↦ .ret (c :: r.1, r.2)

end LeanVM.Prover

end
