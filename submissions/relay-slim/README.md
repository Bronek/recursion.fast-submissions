# relay-slim

A recursive hash-based SNARK entry. It is leanvm-inspired (#11) at pr11-c65f417, the record of both
tracks when this entry was made, with two changes: each commitment's root leaves carry only the
lanes that hold data, and the prover schedules its work differently without changing a byte of
its proofs. Everything else is #11's: leanVM's proof system over binary fields, adapted to the
contract's signed random oracle and to its cheap-extractor fuel cap. `NOTES.md` has what changed,
the numbers and the dead ends; #11's own notes (in the notes journal, under pr11-c65f417) have the
full design.

## What this entry changes

- **Trimmed root leaves (Z2).** Both commitments are stacked WHIR codes. At level 0 a Merkle leaf
  is one row of the stack: 64 words, 512 B. Only the first 49 of `C_main`'s 64 lanes hold data at
  the production parameters (the chain digests, the sponge table and the recursion tables), and
  only 35 of `C_rec`'s (the child's trace and signature). The rest are zero. A leaf now carries the
  occupied words alone, 392 B and 280 B, and the verifier reads the absent lanes as zero.
  - The proof shrinks from 783,192 to 716,152 B, and the trace that the parent's circuit reads
    shrinks with it.
  - The prover encodes and hashes fewer words: 589,824 fewer Keccak permutations per proof.
  - The Lean side moves with it: the compiler's leaf rows, the circuit's level-0 fold, the
    extractor's reading of `C_rec`, the records and the generated node program. The certificate is
    proved with the axioms `propext`, `Classical.choice` and `Quot.sound` only.
- **Prover scheduling (P), the same proof bytes.**
  - The chain tape's GKR witness is generated behind the chain walk, block by block (P2).
  - The recursion tables are built from the start on a placeholder chain end, then patched when
    the walk ends: the chain end reaches four cells of the public header table (P1).
  - The digest block is written beside the tape witness, and `prover setup` picks 8 or 4 workers
    by timing a probe closer to a whole step.

## How it works (#11's design)

- **Fields.** `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` (CompPoly `BF64`, `BF64.Ext3`), as in leanVM.
- **One proof per step.** It proves `nodeStmt c_L (leafStmt h n)`: the right child is a
  witness-sending leaf checked natively, the left child the previous signed proof, verified in the
  circuit. Step 1's first proof is a leaf alone.
- **The chain.** A 2^20-row Keccak tape commits each row's 256-bit digest only; the inputs are
  virtual. leanVM's GKR proves the permutations, and a wiring sumcheck ties them to the digests.
- **The child's verifier in the circuit.** A sponge table, BITS tables and a LoopIR program
  (affine-address loop tables over leanVM's memory bus) recompute the child's verifier on its trace.
  A self-fold accumulator handles the program's own fixed columns.
- **Commitments.** `C_main` (2^24 words) at the Johnson radius and `C_rec` (2^19 words, the only
  one the extractor decodes) in unique decoding, both stacked WHIR with 14 bits of grinding per
  level. The transcript is a hash chain over the contract's oracle.
- **The certificate.** `certified` is `LvmFinCert.certificateFin`: knowledge error 2^-128,
  completeness error 0, `qV = 16,384`, fuel `2^46 + 8192·t`. Five static facts about the program
  are checked once when `V` starts (`staticOkB`); the certificate holds for either value.

## Layout and building

- `lean/`: `Solution.lean` and 566 flat modules, all `Lvm*`. Only `Solution`'s import closure is
  built; check it with the harness's `evaluate.py cert` on this root.
- `prover/`: the Rust prover (std only; leanVM's crates vendored under `src/lv/`, every edit in
  `src/lv/PATCHES.md`) and the submitted `prover-*.s`, three CPU variants behind `dispatch.s`'s
  cpuid stub. `prover/build-asm.sh --install` regenerates the `.s` (rustc 1.99.0, offline) and
  links them in the order the runner does.
- `tools/qasm/`: the record tool. It regenerates the node program's records and blobs from the
  Lean definitions, checks them byte for byte, and fails when a commitment's columns pass the lanes
  its root leaves carry.

## Credits and licences

- leanvm-inspired (#11): the whole design, its Lean proofs and its prover, which this entry copies
  and changes in the two places above. Through #11: [leanVM](https://github.com/leanEthereum/leanVM)
  (protocol, Rust crates, `formal/` proofs),
  [leanerVM](https://github.com/Verified-zkEVM/leanerVM), relay-echo (#12, the AVX-512VL chain
  kernel generator), leanvm-gkr-fast (#13, the v4 tier's Keccak GKR) and leanvm-fast-verify (#15,
  every-round storage), the earlier Flock-class entry, longfellow-zk's Johnson-bound proofs, and
  the organiser's core library.
- The repository's Apache-2.0 licence covers this root. `LICENSE-longfellow` is the licence and
  change list of the vendored longfellow-zk proofs (`lean/LvmJB*`, `lean/LvmLJ*`); vendored files
  keep their own headers.
