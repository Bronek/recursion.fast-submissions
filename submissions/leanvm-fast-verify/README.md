# leanvm-fast-verify

leanvm-gkr-fast (#13) with a faster compiled verifier `V_S` and a faster prover. The protocol, the proof format and the claim are #13's, unchanged; the prover emits the same proof bytes.

- **What changed.** Four Lean modules. Each new evaluator is proved equal to the one it replaces, so `VS20F_eq` and the certificate go through as before:
  - `LvmVFast`: `mleK`, the multilinear extension of a base-field array (the first fold as base × extension products, the rest over arrays, no closures), with `mleK_eq`. The node program's group closed forms read base-field coefficient tables built once per process (`kT`, `grpEvalGK_eq`). Every `BITS` table's address columns are cached powers evaluated by `mleK` (`adrColA`, `tabC_eq`). The bus leaf forms multiply by base-field constants with `smulBase` (`sideBlocksK_eq`).
  - `LvmDecideV0`: `contShift` takes the closed form of its three shift prefix sums (`preCFV`) when the shapes allow it, else the row sum, now `contShiftRef`.
  - `LvmQLinkArith`: `contShift_fast : contShift = contShiftRef`; `contShift_eq` keeps its statement.
  - `LvmVEqLinkArith`: `toExt3_contShift` rewrites by `contShift_fast` first.
- **Prover.** The Keccak GKR witness stores every round's state instead of every fourth (`keccak_gkr/witness.rs`, `every`), so the layer passes recompute none; the `.s` files are rebuilt with `build-asm.sh --install`. `src/lv/PATCHES.md` lists the edit.
- **What did not change.** `claim.json`, the rest of `prover/` and the other 472 modules of `lean/` are byte-identical to #13's. #11's README and NOTES describe the design, the certificate and its trust surface.
- **Axioms.** `certified` depends on `propext`, `Classical.choice` and `Quot.sound`, as before.

`NOTES.md` has the measurements.
