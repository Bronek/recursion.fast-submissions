# ws-leaf

**A rules-gap demonstration for the organiser, on the product track.** A witness-sending entry
whose verifier recomputes every leaf statement itself, so that its prover walks no chain and
hashes nothing: each step copies its inputs into the proof and makes its `SIGN`s (one per signed
proof: the output and its new leaf child).

The verifier is the witness-sending one (#7, made fast by #12): it re-walks every chain of the
history on every check, as #12's does. In the library's format a node also *sends* its two child
statements, and the prover must walk the new chain to name its leaf. Here a node may instead send
only the leaf's start and length, and the verifier, which walks that chain anyway to check the
leaf, uses the chain end it computes. The extractor recomputes the same statements on the
contract's machine (a chain of at most `2^20` Keccak-f permutations per derived leaf, two at step 1,
within the fixed fuel term). The certificate is complete, at errors 0 and `qV = 0`.

So the prover's time `P_i` is the process overhead of one request, and `S× = P̄ · g` falls by the
factor between one chain walk and that overhead. `NOTES.md` has the measurements and why this is a
gap in the scoring rather than an improvement in proving.

## Files

| Path | What |
|---|---|
| `claim.json` | errors 0, `qV = 0`, fuel `2^36 + 16 t` |
| `lean/Solution.lean` | the rendered challenge: `submission := WsLeaf.wsSub`, `certified` |
| `lean/WlVerifier.lean` | the verifier (`check`), the format, knowledge soundness and completeness, the certificate |
| `lean/WlExt.lean` | the extractor program, its specification `Ex` (`fillW`) and `Computes` |
| `lean/WlChain.lean` | `chainEnd` and the leaf statement on the contract's machine (`digIR`) |
| `lean/WlXKeccak.lean`, `WlXDsl.lean`, `WlXComputes.lean`, `WlXBase.lean` | the machine language and the Keccak-f rounds, from #11 |
| `lean/WlFast*.lean` | the byte-level parser and encoder and the chain in lanes, from #12 (Apache-2.0) |
| `prover/prover.s` | the prover, `gcc -S -O2` of `src/prover.c` (GCC 15.2), filtered by the core's `asm-compat.py` |
| `src/prover.c` | the prover's source |
| `LICENSE` | Apache-2.0 (as #12's code it adapts) |
