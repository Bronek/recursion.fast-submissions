-- New for lvm (WP-3): the extractor's step model (BLUEPRINT §6.3, amended by §11 A5).
import LvmXField
import LvmXLookup

/-!
# The step model of the decoder (§6.2 steps 4–6) on the contract's machine

The decoder's hot loops as `XIR` kernels with **exact syntactic costs** (`cost`, which bounds the
machine's steps by `steps_le_cost`), composed into the fixed term of the extractor's fuel at lvm's
parameters (`C_rec`: 64 rows of `k = 2^13` message words, `n₀ = 2^15` positions, rate `1/4`).
The kernels are cost models: their loop structure, loads, stores, field blocks and loop overhead
are those of a real implementation, but what they compute is not proved here (that is WP-13's
`LvmXDec`, which may reuse them). The loop bodies use the proved blocks of `LvmXField`.

* **`interpIR k C`** (FR's `FRXLag.lagIR` on `K`-valued rows): Lagrange interpolation of `C` rows
  from `k` agreeing positions `J` to the targets `s < k`, **one setup shared by all rows**: the
  weights `W_t = (Π_{m ≠ t} (J_t ⊕ J_m))⁻¹` (`k²` products, `k` inversions) once, `Y_c[t] = W_t ·
  w_c(J_t)`; per target the prefix products `P_t` and suffix products `Q`, then per row a lazy
  multiply-accumulate (`clmul`, `clmulh`, two `xor`s, no reduction; one reduction per row and
  target). `cost_interpIR`: `29 + 1116 k + 48 C k + 101 k² + 12 C k²`.
* **`blkMacIR m`**: an `m × m` block of the half-split back-substitution (FR's `k²/2` per row):
  per entry two loads, one `K` product for the coefficient and a lazy multiply-accumulate.
  `bsubRow k = Σ_ℓ 2^ℓ · cost (blkMacIR (k / 2^(ℓ+1)))`.
* **`encPosIR k`**: `Enc₀(f₁)[x]` at one position (`k` `E` coefficients): the tensor table
  `X_i(x)` (`k` `K` products) and `k` lazy `E × K` multiply-accumulates, three reductions.
* **`foldPosIR`**: the agreement test at one position: `Σ_u eq(α, u) w[u, x]` over the 64 rows
  (lazy `E × K`), three reductions, the comparison with `Enc₀(f₁)[x]`, the append to `A`.
* **`readPosIR`**: one position's column: 9 lookups (`lookIR4`, 64 halvings each) down the
  Merkle path and the copy of the 64 leaf words.

**`fixedModel`** sums them with the memory (`2^25`), the output and the FS replay (both bounded
above, [e]); `fixedModel_eq` (`≈ 2^37.1`), `fixedModel_le : fixedModel ≤ 2^38`, and `fuel_margin`:
`2^8 · fixedModel ≤ fuelBase`.
-/

namespace Lvm.X

open RecursionFast

/-! ## Registers of the model kernels (`64 … 102`; row accumulators `128 + 2c`, `c < 64`) -/

/-- Pointer. -/ def mA : ℕ := 64
/-- Pointer. -/ def mB : ℕ := 65
/-- `Y`'s pointer. -/ def mY : ℕ := 66
/-- Column pointer. -/ def mX : ℕ := 67
/-- `J_t`. -/ def mT : ℕ := 68
/-- `J_m`. -/ def mJ : ℕ := 69
/-- Difference. -/ def mD : ℕ := 70
/-- Flag. -/ def mZ : ℕ := 71
/-- Product. -/ def mP : ℕ := 72
/-- Product. -/ def mQ : ℕ := 73
/-- Multiplier. -/ def mE : ℕ := 74
/-- Value. -/ def mV : ℕ := 75
/-- Low word. -/ def mLo : ℕ := 76
/-- High word. -/ def mHi : ℕ := 77
/-- The target `s`. -/ def mS : ℕ := 78
/-- Output pointer. -/ def mO : ℕ := 79
/-- `k`. -/ def mKk : ℕ := 80
/-- Column stride. -/ def mStr : ℕ := 81
/-- `Y`'s row base. -/ def mW : ℕ := 82
/-- `C`. -/ def mCC : ℕ := 83
/-- Loop counter. -/ def mC1 : ℕ := 84
/-- Its count. -/ def mN1 : ℕ := 85
/-- Loop counter. -/ def mC2 : ℕ := 86
/-- Its count. -/ def mN2 : ℕ := 87
/-- `E` operand pointer. -/ def mF : ℕ := 90
/-- `E` operand (3 words). -/ def mF0 : ℕ := 91
/-- `E` accumulator (6 words: low, high per coefficient). -/ def mAcE : ℕ := 94
/-- `E` result (3 words). -/ def mR : ℕ := 100

/-- Row `c`'s accumulator (two words). -/
def acc (c : ℕ) : ℕ := 128 + 2 * c

/-! ## Interpolation with a shared setup (FR's `lagIR`, `K` rows) -/

/-- One factor of `W_t`: `P *= (J_t ⊕ J_m) ||| [J_t = J_m]`. -/
def wFac : XIR :=
  .seq (.load mJ mA) (.blk ([.op .xor mD mT mJ, .op .eq mZ mT mJ, .op .or mD mD mZ,
    .op .add mA mA cOne] ++ mulKC mP mP mD))

/-- One value `Y_c[t] := W_t · w_c(J_t)` (the column pointer walks the rows, stride `n₀`). -/
def yVal : XIR :=
  .seq (.load mV mX) (.seq (.blk ([.op .add mX mX mStr] ++ mulKC mV mV mQ))
    (.seq (.store mY mV) (.blk [.op .add mY mY cOne])))

/-- One position `t`: `W_t` (`k` factors, one inversion), then its `C` values. -/
def wyBody (k C jb cb : ℕ) : XIR :=
  .seq (.load mT mB) (.seq (.blk [.const mP 1, .const mA (toWord jb), .const mN2 (toWord k)])
    (.seq (.loopK mC2 mN2 (toWord k) wFac) (.seq (invK mQ mP)
      (.seq (.blk [.const mX (toWord cb), .op .add mX mX mT, .const mN2 (toWord C)])
        (.seq (.loopK mC2 mN2 (toWord C) yVal) (.blk [.op .add mB mB cOne]))))))

/-- The weighted values `Y_c[t]`, `t < k`, `c < C`. -/
def yTabIR (k C jb yb cb n₀ : ℕ) : XIR :=
  .seq (.blk [.const mB (toWord jb), .const mY (toWord yb), .const mStr (toWord n₀),
      .const mN1 (toWord k)])
    (.loopK mC1 mN1 (toWord k) (wyBody k C jb cb))

/-- The forward pass's step: `P_t := P`, `P *= s ⊕ J_t`. -/
def fwdL : XIR :=
  .seq (.load mJ mA) (.seq (.store mB mP)
    (.blk ([.op .xor mD mS mJ, .op .add mA mA cOne, .op .add mB mB cOne] ++ mulKC mP mP mD)))

/-- Row `c`'s lazy multiply-accumulate: `acc_c += e · Y_c[t]`, unreduced (128 bits). -/
def macRow (c : ℕ) : XIR :=
  .seq (.load mV mY) (.blk [.op .add mY mY cOne, .op .clmul mLo mV mE, .op .clmulh mHi mV mE,
    .op .xor (acc c) (acc c) mLo, .op .xor (acc c + 1) (acc c + 1) mHi])

/-- The rows `0 … C − 1`, unrolled. -/
def accIR : ℕ → XIR
  | 0 => .blk []
  | C + 1 => .seq (accIR C) (macRow C)

/-- The backward pass's step (`t` from `k − 1` down): `e := P_t · Q`, `Q *= s ⊕ J_t`, the rows. -/
def bwdL (C : ℕ) : XIR :=
  .seq (.blk [.op .sub mA mA cOne, .op .sub mB mB cOne, .op .sub mW mW mCC, .op .or mY mW mW])
    (.seq (.load mJ mA) (.seq (.load mE mB)
      (.seq (.blk ([.op .xor mD mS mJ] ++ mulKC mE mE mQ ++ mulKC mQ mQ mD)) (accIR C))))

/-- Row `c`'s output: reduce, store at `mO`, advance by `k`. -/
def stRow (c : ℕ) : XIR :=
  .seq (.blk (redC mV (acc c) (acc c + 1) mLo mHi)) (.seq (.store mO mV)
    (.blk [.op .add mO mO mKk]))

/-- The outputs of rows `0 … C − 1`, unrolled. -/
def stAcc : ℕ → XIR
  | 0 => .blk []
  | C + 1 => .seq (stAcc C) (stRow C)

/-- The accumulators' zeros. -/
def zeroPs (C : ℕ) : List Prim := (List.range (2 * C)).map fun i => .const (128 + i) 0

/-- One target `s`: forward pass, backward pass, the `C` outputs. -/
def tgBody (k C jb pb yb ob : ℕ) : XIR :=
  .seq (.blk [.const mP 1, .const mA (toWord jb), .const mB (toWord pb), .const mN2 (toWord k)])
    (.seq (.loopK mC2 mN2 (toWord k) fwdL)
      (.seq (.blk ([.const mQ 1, .const mW (toWord (yb + C * k)), .const mCC (toWord C),
          .const mN2 (toWord k)] ++ zeroPs C))
        (.seq (.loopK mC2 mN2 (toWord k) (bwdL C))
          (.seq (.blk [.const mKk (toWord k), .const mO (toWord ob), .op .add mO mO mS])
            (.seq (stAcc C) (.blk [.op .add mS mS cOne]))))))

/-- The targets `s < k`. -/
def tgIR (k C jb pb yb ob : ℕ) : XIR :=
  .seq (.blk [.const mS 0, .const mN1 (toWord k)]) (.loopK mC1 mN1 (toWord k) (tgBody k C jb pb yb ob))

/-- **The interpolation of `C` rows** from the `k` positions at `jb` to the targets `s < k`. -/
def interpIR (k C jb pb yb ob cb n₀ : ℕ) : XIR := .seq (yTabIR k C jb yb cb n₀) (tgIR k C jb pb yb ob)

theorem len_zeroPs (C : ℕ) : (zeroPs C).length = 2 * C := by simp [zeroPs]


theorem cost_accIR (t : ℕ) : ∀ C, cost (accIR C) t = 1 + 12 * C
  | 0 => by simp [accIR, cost, blkSteps]
  | C + 1 => by
    simp only [accIR, macRow, cost, cost_accIR t C, blkSteps, List.length_cons, List.length_nil]
    norm_num; ring

theorem cost_stAcc (t : ℕ) : ∀ C, cost (stAcc C) t = 1 + 17 * C
  | 0 => by simp [stAcc, cost, blkSteps]
  | C + 1 => by
    simp only [stAcc, stRow, redC, cost, cost_stAcc t C, blkSteps, List.length_cons,
      List.length_nil]
    norm_num; ring

/-- **The interpolation's cost**: `29 + 1116 k + 48 C k + 101 k² + 12 C k²` (`k, C < 2^64`):
the shared setup is `101 k²`, each row adds `12 k²`. -/
theorem cost_interpIR (k C jb pb yb ob cb n₀ t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (interpIR k C jb pb yb ob cb n₀) t =
      29 + 1116 * k + 48 * C * k + 101 * k ^ 2 + 12 * C * k ^ 2 := by
  simp only [interpIR, yTabIR, wyBody, wFac, yVal, tgIR, tgBody, fwdL, bwdL, cost, cost_invK,
    cost_accIR, cost_stAcc, mulKC, redC, List.length_append, List.length_cons,
    List.length_nil, len_zeroPs, toNat_toWord hk, toNat_toWord hC]
  simp only [blkSteps]
  norm_num
  rw [show 2 * (4 + 2 * C) - 1 = 7 + 4 * C by omega]
  ring

/-! ## A block of the half-split back-substitution -/

/-- One entry: `acc += a_j · (τ_j · c)`, the coefficient `τ_j · c` computed by one `K` product. -/
def macK2 : XIR :=
  .seq (.load mV mA) (.seq (.load mE mB) (.blk ([.op .add mA mA cOne, .op .add mB mB cOne] ++
    mulKC mE mE mT ++ [.op .clmul mLo mV mE, .op .clmulh mHi mV mE, .op .xor 128 128 mLo,
      .op .xor 129 129 mHi])))

/-- One output of an `m × m` block: `m` entries, a reduction, the store. -/
def blkRow (m : ℕ) : XIR :=
  .seq (.blk [.const 128 0, .const 129 0, .const mN2 (toWord m), .op .or mA mX mX])
    (.seq (.loopK mC2 mN2 (toWord m) macK2) (.seq (.blk (redC mV 128 129 mLo mHi))
      (.seq (.store mO mV) (.blk [.op .add mO mO cOne]))))

/-- **An `m × m` block.** -/
def blkMacIR (m : ℕ) : XIR := .seq (.blk [.const mN1 (toWord m)]) (.loopK mC1 mN1 (toWord m) (blkRow m))

theorem cost_blkMacIR (m t : ℕ) (hm : m < 2 ^ 64) :
    cost (blkMacIR m) t = 10 + 36 * m + 32 * m ^ 2 := by
  simp only [blkMacIR, blkRow, macK2, cost, blkSteps, mulKC, redC, List.length_append,
    List.length_cons, List.length_nil, toNat_toWord hm]
  norm_num; ring_nf

/-- **One row's back-substitution**: the half-split levels `ℓ < 13`, `2^ℓ` blocks of side
`2^(12 − ℓ)` (`Σ = k²/2 − …` entries at `k = 2^13`). -/
def bsubRow : ℕ := ∑ l ∈ Finset.range 13, 2 ^ l * cost (blkMacIR (2 ^ (12 - l))) 0

theorem bsubRow_eq : bsubRow = 1075609590 := by
  simp (disch := norm_num) only [bsubRow, Finset.sum_range_succ, Finset.sum_range_zero,
    cost_blkMacIR]
  norm_num

/-! ## `Enc₀(f₁)` at one position -/

/-- One tensor-table entry: `tab[i'] := tab[i] · W_b(x)`. -/
def tabStep : XIR :=
  .seq (.load mV mA) (.seq (.blk ([.op .add mA mA cOne] ++ mulKC mV mV mT))
    (.seq (.store mB mV) (.blk [.op .add mB mB cOne])))

/-- One lazy `E × K` multiply-accumulate: the `E` operand (3 loads), the `K` operand, three
carry-less products into the 6-word accumulator. -/
def macEK : XIR :=
  .seq (.load mF0 mF) (.seq (.blk [.op .add mF mF cOne]) (.seq (.load (mF0 + 1) mF)
    (.seq (.blk [.op .add mF mF cOne]) (.seq (.load (mF0 + 2) mF)
      (.seq (.load mV mB) (.blk [.op .add mF mF cOne, .op .add mB mB cOne,
        .op .clmul mLo mF0 mV, .op .clmulh mHi mF0 mV, .op .xor mAcE mAcE mLo,
        .op .xor (mAcE + 1) (mAcE + 1) mHi,
        .op .clmul mLo (mF0 + 1) mV, .op .clmulh mHi (mF0 + 1) mV,
        .op .xor (mAcE + 2) (mAcE + 2) mLo, .op .xor (mAcE + 3) (mAcE + 3) mHi,
        .op .clmul mLo (mF0 + 2) mV, .op .clmulh mHi (mF0 + 2) mV,
        .op .xor (mAcE + 4) (mAcE + 4) mLo, .op .xor (mAcE + 5) (mAcE + 5) mHi]))))))

/-- The three reductions of the `E` accumulator into `mR … mR + 2`. -/
def redEPs : List Prim :=
  redC mR mAcE (mAcE + 1) mLo mHi ++ redC (mR + 1) (mAcE + 2) (mAcE + 3) mLo mHi ++
    redC (mR + 2) (mAcE + 4) (mAcE + 5) mLo mHi

/-- The zeros of the `E` accumulator. -/
def zeroEPs : List Prim := (List.range 6).map fun i => .const (mAcE + i) 0

/-- **`Enc₀(f₁)[x]`** from `k` coefficients: the table (`k` products), `k` multiply-accumulates,
the reductions, three stores. -/
def encPosIR (k : ℕ) : XIR :=
  .seq (.blk [.const mN2 (toWord k)]) (.seq (.loopK mC2 mN2 (toWord k) tabStep)
    (.seq (.blk (zeroEPs ++ [.const mN2 (toWord k)])) (.seq (.loopK mC2 mN2 (toWord k) macEK)
      (.seq (.blk redEPs) (.seq (.store mO mR) (.seq (.blk [.op .add mO mO cOne])
        (.seq (.store mO (mR + 1)) (.seq (.blk [.op .add mO mO cOne])
          (.seq (.store mO (mR + 2)) (.blk [.op .add mO mO cOne]))))))))))

theorem cost_encPosIR (k t : ℕ) (hk : k < 2 ^ 64) : cost (encPosIR k) t = 84 + 69 * k := by
  simp only [encPosIR, tabStep, macEK, redEPs, zeroEPs, cost, blkSteps, mulKC, redC,
    List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    toNat_toWord hk]
  norm_num; ring_nf

/-! ## The agreement test at one position -/

/-- **One position's agreement**: `Σ_u eq(α, u) w[u, x]` over 64 rows, reduced, compared with
`Enc₀(f₁)[x]` (three words at `mX`), the position appended to `A` when equal. -/
def foldPosIR : XIR :=
  .seq (.blk (zeroEPs ++ [.const mN2 64])) (.seq (.loopK mC2 mN2 64 macEK)
    (.seq (.blk redEPs) (.seq (.load mV mX) (.seq (.blk [.op .eq mZ mV mR, .op .add mX mX cOne])
      (.seq (.load mV mX) (.seq (.blk [.op .eq mD mV (mR + 1), .op .and mZ mZ mD,
        .op .add mX mX cOne]) (.seq (.load mV mX) (.seq (.blk [.op .eq mD mV (mR + 2),
          .op .and mZ mZ mD, .op .add mX mX cOne])
            (.ite mZ (.seq (.store mY mS) (.blk [.op .add mY mY cOne])) (.blk []))))))))))

theorem cost_foldPosIR (t : ℕ) : cost foldPosIR t = 2770 := by
  simp only [foldPosIR, macEK, redEPs, zeroEPs, cost, blkSteps, mulKC, redC,
    List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]
  norm_num

/-! ## One position's column -/

/-- One step down the Merkle path after a lookup: the child's four answer words from the found
entry's query (`rX` its tape position, `mD` the child's offset) into the target `rQ0 … rQ3`. -/
def childIR : XIR :=
  .seq (.blk [.op .add mA rX mD]) (.seq (.input rQ0 mA) (.seq (.blk [.op .add mA mA cOne])
    (.seq (.input rQ1 mA) (.seq (.blk [.op .add mA mA cOne]) (.seq (.input rQ2 mA)
      (.seq (.blk [.op .add mA mA cOne]) (.input rQ3 mA)))))))

/-- One leaf word into the word `w`: tape to memory, the column's stride. -/
def leafStep : XIR :=
  .seq (.input mV mA) (.seq (.blk [.op .add mA mA cOne]) (.seq (.store mY mV)
    (.blk [.op .add mY mY mStr])))

/-- **One position's column**: 8 node lookups and steps down, the leaf lookup, the 64 leaf
words (`bX`, `pL`: the log index's base and `|L|`'s tape word). -/
def readPosIR (bX pL : ℕ) : XIR :=
  .seq (.blk [.const mN2 8]) (.seq (.loopK mC2 mN2 8 (.seq (lookIR4 bX pL) childIR))
    (.seq (lookIR4 bX pL) (.seq (.blk [.op .add mA rX mD, .const mN2 64])
      (.loopK mC2 mN2 64 leafStep))))

theorem cost_lookIR4 (bX pL t : ℕ) : cost (lookIR4 bX pL) t = 6486 := by
  simp only [lookIR4, bsBody4, foundIR4, ansLtIR, cmpTWord, eqTWord, aposIR, ceil8Ps, readAt, cost,
    blkSteps, List.length_append, List.length_cons, List.length_nil]
  norm_num

theorem cost_readPosIR (bX pL t : ℕ) : cost (readPosIR bX pL) t = 59382 := by
  simp only [readPosIR, childIR, leafStep, cost_lookIR4, cost, blkSteps, List.length_cons,
    List.length_nil]
  norm_num

/-! ## The fixed term -/

/-- `k`, the message words per row of `C_rec`. -/
def kRec : ℕ := 2 ^ 13
/-- The rows of `C_rec`. -/
def rowsRec : ℕ := 64
/-- The positions of `C_rec`'s codeword. -/
def nRec : ℕ := 2 ^ 15

/-- The output of `E` (≤ `2^20` words: π's `2^17`, the trace's `≈ 2^18`, the signatures), at most
16 steps a word [e]. -/
def outModel : ℕ := 2 ^ 24
/-- The FS replay off the log (≈ `2^12` reconstructed queries of ≤ `2^11` words, each a lookup)
[e]. -/
def fsModel : ℕ := 2 ^ 25

/-- **The extractor's fixed term at lvm's parameters**: the memory, the columns, the encoding,
the agreement, the interpolation of all 64 rows with one shared setup, the 64 rows'
back-substitution, the output and the FS replay. -/
def fixedModel : ℕ :=
  memX + nRec * cost (readPosIR memX 0) 0 + nRec * cost (encPosIR kRec) 0 + nRec * cost foldPosIR 0 +
    cost (interpIR kRec rowsRec 0 0 0 0 0 nRec) 0 + rowsRec * bsubRow + outModel + fsModel

theorem fixedModel_eq : fixedModel = 147836206493 := by
  rw [fixedModel, cost_readPosIR, cost_encPosIR _ _ (by decide), cost_foldPosIR,
    cost_interpIR _ _ _ _ _ _ _ _ _ (by decide) (by decide), bsubRow_eq]
  decide

/-- **The fixed term is below `2^38`** (`≈ 2^37.1`), far below WP-3's acceptance line `2^44`. -/
theorem fixedModel_le : fixedModel ≤ 2 ^ 38 := by rw [fixedModel_eq]; decide

/-- The declared `fuel_base = 2^46` covers the fixed term with a factor `2^8` (`≈ 476`). -/
theorem fuel_margin : 2 ^ 8 * fixedModel ≤ fuelBase := by
  rw [fixedModel_eq, fuelBase]; decide

end Lvm.X
