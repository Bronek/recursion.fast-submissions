# leanvm-inspired

A recursive hash-based SNARK entry. It uses leanVM's proof system over binary fields, adapted to the
contract's signed random oracle and to its cheap-extractor fuel cap. Each step is one proof: a new
Keccak-256 chain, plus the previous signed proof verified inside the circuit. `NOTES.md` has the design,
the numbers and the dead ends.

**Changes since pr11-2f57ce79224a** (the gated chain link; local S = 8.76, S× = 6.46):
- the chain is a digest-only Keccak tape: only lanes 0–3 of each row's output are committed, each row's input is
  `Pad43` of the previous digest (virtual), one GKR of depth 24 proves the permutations, and a 20-round wiring
  sumcheck ties the GKR's input claim to the committed digests, masked to the live rows `i < n`;
- `C_main` shrinks from 2^26 to 2^24 words, with three WHIR levels instead of four; `|π|` 1,181,488 → 1,094,248 B,
  `qS` 11,832 → 9,916;
- local season shape (dev VM): ACCEPT, S 8.76 → 6.26, S× 6.46 → 3.94; steps 2.8–8.9 s (were 4.9–11.7 s).

pr11-2f57ce79224a itself gated the chain link by `n`, sped up the prover plumbing and made the native verifier
faster (fast twins in `LvmVFast`, proved equal to the specified `VS20`).

## Trust surface

- **The certificate.** `certified : CertificateR declared submission` is `Lvm.Fin.certificateFin`
  (`LvmFinCert`). Its axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and no
  `native_decide`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel = 2^46 + 8192·t`.
- **Facts about the concrete program.** They are kernel `decide`s at the frozen record (`LvmQAsmFacts*`,
  `LvmFinDec`), except five that the kernel cannot reach within the caps: `Q.wf`, grouping,
  injectivity, no computed-address read in `Q_arith`, and claim-list well-formedness.
- **The runtime guard.** Those five facts form `staticOkB : Bool`, and `submission = subG staticOkB VS20F`
  rejects every SNARK proof when the guard is false. The certificate holds for both values
  (`certificateR_guard`, `certificateR_reject`), so the guard affects completeness only. The compiled V
  evaluates it once per process (1.5 s); it is `true`.
- **Soundness error.** The model is 2^-129.08. Lean proves `εFS ≤ 2^-129 + 2^-130 + 2^-139 ≤ 2^-128`:
  IOP, extractor luck, hash.

## The proof system in one list

- **Fields.** `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` (CompPoly `BF64`, `BF64.Ext3`), the same as leanVM.
- **Step statement.** `nodeStmt c_L (leafStmt h n)`.
  - Right child: a witness-sending leaf, checked natively.
  - Left child: the previous signed proof, verified in the circuit.
  - A flag `b = 0` gives step 1's first proof.
- **Chain.** A 2^20-row Keccak tape that commits only each row's 256-bit digest `D[i]`. Row `i`'s input is
  `Pad43(D[i−1])` (`Pad43(s)` at row 0, zero for rows `≥ n`), never committed. leanVM's GKR (RMFE), one segment
  of depth 24, proves the permutations; a wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ n − 1]`, a
  slot reduction and one ring switch tie its input claim to bit slices of `D`. `V` evaluates the kernel in closed
  form from `n`'s bits.
- **Child verification.**
  - A 2^15-row sponge table: the trace digest, one WOTS walk and the statements.
  - BITS tables.
  - A LoopIR program (affine-address loop tables) that recomputes the child's verifier on its trace.
- **Fixed columns.** A self-fold accumulator: each proof folds its incoming claim with its own fixed
  claims, `V` checks one evaluation, and the parent's circuit checks the child's fold.
- **Memory.** leanVM's `g`-power logup bus, a grand-product GKR and a table sumcheck.
- **Commitments**, both stacked WHIR in the unique-decoding regime, with no OOD sample and no grinding:
  - `C_main`: 2^24 words, 3 levels (folds 6/4/4, 311/191/156 queries), never decoded;
  - `C_rec`: 2^19 words holding the child's trace and signature; 1 level, decoded by the extractor.
- **Transcript.** A hash chain over the contract oracle. Merkle hashes are oracle queries, and queries are
  lane-aligned and classified by length.
- **Sizes (P20).** `qS = 9,916`, `|π| = 1,094,248 B`, 6.31 M committed table words (of 9.44 M free in `C_main`).

## Main theorem chain (modules in `lean/`)

| step | statement | module |
|---|---|---|
| certificate | `certificateFin`; guard `certificateR_guard`, `certificateR_reject`; `staticFacts` | `LvmFinCert`, `LvmFinGuard`, `LvmFinStatic` |
| assembly | `openFin`, `certificateR_open`, `sSound_of_openS` | `LvmFinCert`, `LvmSubmissionS` |
| FS compiler | `kstate_of_kcert`, `ks_of_kcert`: `KCert` (leanVM `Cert` + luck) ⇒ `KState` ⇒ `KS` | `LvmCompileKS` |
| IOP | `kcertS`; WHIR-UD `whirUdSpec`, `card_foldBad_le_ud`; tape and `KS` phases `kgSpecS`; wiring `wireChSpec`; Keccak `callerSpec`, `kgSpec`; bus `midBusTableSpecS`; accumulator | `LvmCertS*`, `LvmWhir*`, `LvmMcaUd`, `LvmWireSpec`, `LvmWireKernel`, `LvmKeccakCaller*`, `LvmM3Mid*`, `LvmAccSpec*` |
| tables ⇒ relation | `chain_of_tape`, `traceDigest_of_KS`, `loopir_sound`, `qlink_sound`, `qsig_sound`, `qacc_replays`, `tape_spec`, `wire_spec`, `harith_core`/`harith20`, `nodeSound_of` | `LvmTapeRel`, `LvmSpongeTable`, `LvmLoopSound`, `LvmQ*`, `LvmQAcc*`, `LvmQEqKeccakTape`, `LvmQWireSound`, `LvmQAsmHarMain`, `LvmFinHB`, `LvmNodeSound*` |
| verifier | `VS20F_eq` (compiled = specified); `refines_VSL` (native ⇒ compiled IOP); `Vwith`, `complete` | `LvmVFast`, `LvmVEqRefines`, `LvmVerifier` |
| extractor | `computesX` (cost at the declared fuel), `EX_node`, `decodeRec_of_ud` | `LvmXTop`, `LvmXSpec`, `LvmXDecUd` |

Completeness is the witness-sending kind (`P := encode`, error 0). The harness tests the native prover.

## Layout

`lean/` holds 496 flat modules, all prefixed `Lvm` (`Solution`'s import closure holds 470; it still imports pr11-983bdcfa21d6's
chain-table and shift-link modules, `LvmChainTable*`, `LvmShift`, `LvmQLinkArithCH*`, which the certificate no
longer uses):

| group | prefixes |
|---|---|
| fields, DSL, doom rules | `LvmField*`, `LvmDsl*`, `LvmSpec*`, `LvmProg`, `LvmVCore`, `LvmVParams` |
| FS compiler | `LvmCompile*`, `LvmLog`, `LvmForest`, `LvmPotential` |
| polynomials, Keccak GKR, tape | `LvmMl*`, `LvmCp*`, `LvmSumcheck*`, `LvmGrand*`, `LvmKeccak*`, `LvmK*`, `LvmTapeRel`, `LvmWire*`, `LvmChain*`, `LvmSponge*`, `LvmShift` |
| bus, M3, ring switching | `LvmBus*`, `LvmSpine*`, `LvmFront*`, `LvmM3*`, `LvmRing*`, `LvmLayout*` |
| WHIR-UD | `LvmWhir*`, `LvmRS`, `LvmUd*`, `LvmMcaUd`, `LvmNovelBasis` |
| LoopIR, circuit, program | `LvmLoop*`, `LvmQ*` (`LvmQAsm*` assembles the real `Q`), `LvmQAcc*`, `LvmBits*`, `LvmWots*`, `LvmSig*`, `LvmReplay*` |
| native verifier | `LvmParams`, `LvmSchedule`, `LvmDriver`, `LvmDecide*`, `LvmVerifierS`, `LvmVEq*`, `LvmVF*` |
| extractor | `LvmX*` |
| assembly | `LvmAcc*`, `LvmCertS*`, `LvmNodeSound*`, `LvmSubmission*`, `LvmFin*`, `Solution` |

`prover/` contains:
- `src/lv/`: the vendored leanVM crates, with every edit in `src/lv/PATCHES.md`;
- `src/lvm/`: the schedule, tables, links, bus, accumulator, LoopIR witness, recursion witness and stream,
  plus the embedded program blobs `q-p20.blob` and `q-p8.blob`;
- `src/{service,format,proc,alloc}.rs`: from the earlier Flock-class entry;
- `dispatch.s`: the cpuid stub;
- `build-asm.sh` and `tools/`.

## Building

- **Prover.** Run `prover/build-asm.sh --install`. It needs rustc 1.99.0 and builds offline, with no
  dependencies. It emits `prover-v2.s` (portable), `prover-v4.s` (Zen 4: VPCLMULQDQ, GFNI, VBMI) and
  `prover-v4p.s` (AVX-512 + PCLMUL), filtered for GNU as 2.42, with symbols suffixed per variant. The
  runner links them with `gcc -static -O2 -pthread *.s -lm`. The `.s` output is reproducible byte for
  byte.
- **Lean.** Use the harness `evaluate.py cert` on this root (submission guide §5). Only `Solution`'s import
  closure is built.

## Trust notes

- **Measured vs estimated.** Local timings come from a QEMU dev VM on which v4 cannot start. They use the
  dev variant v4p: 2.8–8.9 s per step (`≈ 2.04 + 7.06·n/2^20` s), 6.5 s for step 1, 6.86 GiB peak, and `V`
  ≈ 0.27 s per check. Zen 4 numbers come from the harness.
- **CPU safety.** `prover setup` self-tests each variant (KATs, a batch proof, a full P8 proof) against
  the portable reference's digest, and writes a cap that `dispatch.s` honours. v4 was byte-identical to
  v2 under Intel SDE.
- **No Rust verifier.** The Lean `V_S` is the test oracle. It accepts the shipped prover's P8 and P20
  streams (`b = 0`; `b = 1` over both child flags).

## Credits

- [leanVM](https://github.com/leanEthereum/leanVM): the protocol, the Rust crates and the `formal/` proofs.
- [leanerVM](https://github.com/Verified-zkEVM/leanerVM): the bus lookup lemma, the generator facts and
  reference formalisations.
- The earlier Flock-class recursive entry: the extractor framework, field kernels, the UD line lemma,
  the sponge layer, the W/S dispatch, the oracle client and the assembly pipeline.
- The organiser's core library: `WitnessSending`, `KState`/`KS` and the fast Keccak and signature twins.
