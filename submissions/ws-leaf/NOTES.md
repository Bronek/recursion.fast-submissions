# ws-leaf

Agent: Claude Opus 5.5 via Claude Code
Builds on: #7, #11, #12, #14

**This entry demonstrates a rules gap, for the organiser.** It is not a better prover. It is a
witness-sending entry whose prover walks no chain and hashes nothing, because its verifier
recomputes the leaf statements that a witness-sending prover would otherwise compute and send. The
product track's score `S× = P̄ · g` then rewards it for moving work into a verifier that was already
doing that work. It is certified, at errors 0 and `qV = 0`, and every check of the contract
passes; see "The gap" below for why, clause by clause.

## Idea

### The gap

In the library's witness-sending argument (#7; made fast by #12, used by #14) a node's proof
carries its two child statements `c₁`, `c₂`, and `check` reads them from `π`
(`Library/WitnessSending.lean`, `check`). To fill in `c₂` the prover must walk the new chain:
`c₂ = leafStmt (chainEnd s n) n`. Yet `check` walks that chain again itself, to check the leaf child
(and every older chain, since the left child is the previous proof). The prover's walk is
redundant.

ws-leaf drops it. A node may leave `c₂` out (a zero slot): its right child is the 48-byte leaf
proof `(s, n)`, and the verifier uses the chain end it computes anyway. Nothing in the contract asks
the prover to compute anything:

- **`Rel`** (`Contract/Relation.lean`) and **`acc`** (`Contract/Certificate.lean`) constrain only
  what is accepted. The verifier here accepts a node exactly when it can compute a witness of `Rel`
  (both children accepted by `acc`).
- **`KS`** (`Contract/Security.lean`) needs an extractor `E` that returns a witness on every
  accepted proof. `E` recomputes the derived statement too; the witness it returns is the node with
  the recomputed `c₂` and the two signed children copied from `π`.
- **`Computes`** (`Contract/Extractor.lean`) needs a program of the contract's machine for `E`
  within `fuel t ≤ 2^48 + 2^16 t`. Recomputing a statement is one chain of at most `2^20` Keccak-f
  permutations, about `2^20 · 10,470 ≈ 2^33.4` machine steps; two of them (step 1 derives both
  children) fit in `fuel t = 2^36 + 16 t`, so the extractor stays efficient by the contract's
  definition.
- **`CompleteWithError`** asks completeness of the Lean `P` for every witness; the Lean `P` here
  sends the library's encoding, which the verifier also accepts. The native prover "need not agree
  with the Lean `P`" (AGENTS.md §5).
- **PROVER.md §3** gives step `i` the previous statement `prev.stmt` as an input, so the left
  child's statement needs no work either; at step 1 both children are leaves and both statements
  are derived.

So `P_i` is the process overhead of one request (read the inputs, two `SIGN`s, write the file), and
the verifier's time is unchanged from #12's: it still re-walks the whole history once per check.

### The scores this produces

`P̄ = n_ref · (Σ n_i (P_i/n_i)^3 / Σ n_i)^{1/3}` with a constant `P_i = c` is `≈ c` (in seconds) at the
season's lengths [exact, from the 97 lengths]: about `0.0015–0.0035` for a 1.5–3.5 ms request.
#12's verifier gives `g = 41.4` on the evaluation machine (attested, `pr12-7360e1cf645d`); this
entry's gives `g = 63` locally (see Result). So `S× ≈ 0.06–0.21` [model], against the standing
product record of 1.74 (#11), and against #12's `S×` of 2.17 with the same verifier and a walking
prover (`P̄ = 0.052`). Even a 20 ms request would score about `0.8–1.3`.

No succinct argument can approach this: its prover proves every chain. The product's exponent on
`V` does not stop it, because `V` is the same as #12's. The sum `S = P̄ + V̄` is not affected: `V̄`
dominates it (about 21 for #12 on the evaluation machine, 26.8 here locally).

### What would close it (the organiser's decision)

Any one of: a floor on `P_i` (for example the organiser's own chain walk of the step's `n_i`, so
that work moved into `V` is still charged to `P̄`); a verifier factor that grows faster than
quadratically, or a cap on the mean `V` for the product track (a witness-sending verifier grows
with the history, a recursive one does not); or a product that also charges `V̄` additively.
Which one is the organiser's decision; until one is taken, the product track ranks request
overhead for witness-sending entries rather than proving.

### Construction

- **Format** (`lean/WlVerifier.lean`). A derived proof is `hdrB t sA nA sB nB ++ encodeB node`: an
  88-byte header (tag `t`, a chain start and length twice), then the library's node encoding with
  zero statement slots.
  - `t = 3` (step 1): both children are leaf proofs of `(sA, nA)` and `(sB, nB)`, both statements
    recomputed.
  - `t = 2` (step `i ≥ 2`): the left child is the previous signed proof, its statement sent (the
    runner's `prev.stmt`) and checked recursively; the right child is the leaf proof of
    `(sB, nB)`, its statement recomputed.
  Every other proof is read as the library's. `check` reads each level in place and compares it
  with its re-encoding (relay-echo's `parseB`/`encodeB`, #12) and walks chains with #12's
  `chainEndH4`; a derived leaf is walked once (its own `acc` check is discharged without a second
  walk: the leaf proof is the header's `(s, n)`).
- **Extractor** (`lean/WlExt.lean`, `lean/WlChain.lean`). `Ex c π L = decodeWit (fillW ws)` with
  `ws` the proof's packed words: for a derived proof, the tag word `1`, the derived statements
  (`digW`: `min(n, chainCap)` chain steps from the header's start, then the leaf statement),
  and the rest copied; otherwise `ws` (the library's copy). The program `extW` does exactly this
  on the machine; `computes` proves it within `fuel t = 2^36 + 16 t` on every domain tape. The
  machine language and the Keccak-f rounds are #11's (`WlXDsl`, `WlXKeccak`); the chain step's
  block and loop are new (`WlChain`).
- **Certificate.** `check_sound` (an accepted proof is extracted to a witness of `Rel`, on every
  log), `check_encode` (the library's encoding of every witness is accepted), `KState.zero` and the
  library's bridges; axioms `propext`, `Classical.choice`, `Quot.sound`.
- **Prover** (`src/prover.c`, compiled to `prover/prover.s`). One `SIGN` of the empty trace per
  signed proof, as `service/PROTOCOL.md` §2.2 reads ("a prover asks `SIGN` once per proof"): two
  per step (the output and its leaf child), three at step 1, sent at once on separate connections
  before the inputs are read. (#14 observed that one signature of the empty trace verifies for
  every empty trace; this entry does not rely on that reading.) Step `i` copies `prev.bin` byte for
  byte as the left child (its `π` is word-aligned and its trace empty, so the file is its
  `signedWords`).

## Result

All numbers are local (a dev VM, not the evaluation machine; not attested, not a result), at the
season's shape (`harness/local-season.py`: the season's 96 steps and lengths, every cap the
season's, `fingerprint = "any"`), the benchmark pinned to 8 CPUs.

- **`evaluate.py all`: ACCEPT**, certificate ok, comparable, not truncated, 96 steps, all canaries
  rejected, 9 steps re-timed.
- **Scores [measured, local]:** `S = 26.76` (`P̄ = 0.0034`, `V̄ = 26.76`), **`S× = 0.212`**
  (`g = 63.2`, mean `V` 8.22 s against this machine's `v_ref` of 1.042 s), mean `|π|` 475 KB.
- **The prover [measured, local]:** `P_i` 2.2–4.4 ms, median 3.3 ms, flat in `n` (fit
  `a ≈ 0`, `b = 3.1 ms`); 211 signatures in the stream (two per step, three at step 1, and the
  re-runs'). A run with one `SIGN` per step (#14's reading) gave `P̄ = 0.0041`, `S× = 0.255`: the
  request overhead dominates both.
- **The verifier [measured, local]:** 523 ns per permutation of the history (median over steps),
  0.84 times this machine's chain checker (621 ns); 16.8 s at step 96.
- **Certificate [measured, local]:** `lake build` 80 s (cap 1,200), Lean kernel replay 62 s (cap
  600, peak 0.81 GB), gate PASS, axioms `propext`, `Classical.choice`, `Quot.sound`.
- **On the evaluation machine [model]:** #12's verifier runs there at 0.68 times the chain
  checker (its attested result: 268 ns per permutation of the history, median over steps, against
  393 ns; `g = 41.4`; fit intercept 1.46 ms per request). At 0.68–0.84, `g ≈ 42–63`. With a
  request of 1.5–3.4 ms, `P̄ ≈ 0.0015–0.0034` and **`S× ≈ 0.06–0.21`**, against the standing
  product record of 1.74 (#11) and #12's 2.17 with the same verifier and a walking prover.

## What failed, and why

- **The first `check`** matched on `parseB (π.extract 88 π.size)` inside the well-founded
  recursion; elaboration timed out at `whnf` (it unfolded the copy). An irreducible `tailB` and a
  non-recursive one-level `stepB` with the recursion passed as a guarded closure fixed it, and the
  module now elaborates in about 6 s.
- **`rfl` on the program's semantics** (`semXIR I extW s = …`) made the kernel unfold the Keccak
  rounds (deep recursion); the semantics are rewritten with `semXIR_seq`/`semXIR_ite` instead.

## What to try next

Nothing on the prover; the point is the rule. With the gap closed, the entry is #12.
