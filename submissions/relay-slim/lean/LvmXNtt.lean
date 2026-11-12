-- adapted from rf-k/submissions/flock-recursive/lean/FRXBaryDefs.lean@8bff272b (section
-- G6_FRXBflyDefs) and rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (sections
-- G6_FRXBfly: the pure pair lemmas; G6_FRXFwd: the forward programs, their costs, fwdLevel_lo/hi,
-- fwdTop).
-- New for lvm (WP-13b); namespace `FR.X` → `Lvm.X`. Re-targeted from FR's two-word
-- `F = GF(2^128)` to lvm's one-word `K = BF64`: `ldF`/`stF` → `.load`/`.store`, `mulF` → `mulK`,
-- `addF` → `addK`, `invF` → `invK`, element stride 2 → 1, table row stride 40 → 15, 20 bits → 15.
import LvmXDec
import LvmXLoop

/-!
# The additive NTTs on the machine: the programs

BLUEPRINT §6.2 steps 4–6 on `K = BF64` (one word per element, `rdK`). A row of `2^ℓ` elements
from cell `A` holds element `i` at `A + i`.

* **The basis table** (`wtabIR tb`): the rows `wRow ptK 15 v`, `v < 15`, at `tb + 15 v + i`.
  Row `0` is `ptK (2^i)`, the word `2^i`; row `v + 1` maps each entry `a` of row `v` to
  `a (a + 1) · (b (b + 1))⁻¹`, `b` entry `v + 1` of row `v` (LCH, `Lvm.Nb.wRow`): one `invK`
  per row.
* **`α`** (`alphaIR`): `wAt ptK 15 l base`, the sum over the set bits `i < 15` of `base` of the
  table entry `(l, i)`, branch-free (`mask = 0 − bit`).
* **One butterfly** (`pairBody`): pair `q < 2^(ℓ−1)` of level `l` (`P = 2^l`) has the positions
  `lo = ⌊q/P⌋·2P + q mod P` and `hi = lo + P`; with `u, w` their values,
  `lo := u + α (w + u)`, `hi := w + u` (characteristic 2: `bflyLevel`'s `u − α (w − u)`, `w − u`).
* **A level** (`levelIR ℓ`): the `2^(ℓ−1)` pairs; **the inverse NTT** (`bflyIR ℓ tb`): levels
  `0 … ℓ − 1` on the row at `rA0`.
* **The forward NTT** (`fwdIR ℓ tb`): levels `ℓ − 1 … 0`, one forward butterfly
  (`fpairBody`) `lo := u + α w`, `hi := u + α w + w` (`Lvm.Nb.fwdLevel`).

Registers `140 … 176`, `185`, `186`; the field blocks' scratch is `5 … 11`.

## Costs (exact, `cost_*`)

`alphaIR` 316, `pairBody` = `fpairBody` 364, `bflyIR ℓ` `14 + ℓ (367 · 2^(ℓ−1) + 23)`,
`fwdIR ℓ` `14 + ℓ (367 · 2^(ℓ−1) + 27)`, `wtabIR` 24,752. At lvm's sizes: `bflyIR 13`
19,542,329; `fwdIR 15` 90,194,339.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## Registers -/

/-- The pair index `q`. -/ def rQ : ℕ := 140
/-- The level `l`. -/ def rLv : ℕ := 141
/-- `2^l`. -/ def rP2 : ℕ := 142
/-- The block's base position. -/ def rBs : ℕ := 143
/-- `q mod 2^l`. -/ def uX : ℕ := 144
/-- Scratch. -/ def uT1 : ℕ := 145
/-- Scratch. -/ def uT2 : ℕ := 146
/-- The address of `lo`. -/ def rAL : ℕ := 147
/-- The address of `hi`. -/ def rAH : ℕ := 149
/-- A table address. -/ def rTa : ℕ := 151
/-- The bit mask. -/ def rBit : ℕ := 153
/-- The bit index. -/ def uI : ℕ := 154
/-- The row's first cell `A`. -/ def rA0 : ℕ := 155
/-- The table row's first cell. -/ def rTr : ℕ := 156
/-- Counter of the pair loop. -/ def rC1 : ℕ := 157
/-- Count of the pair loop. -/ def rN1 : ℕ := 158
/-- Counter of the bit loops. -/ def rC2 : ℕ := 159
/-- Count of the bit loops. -/ def rN2 : ℕ := 160
/-- Counter of the level loops. -/ def rC3 : ℕ := 161
/-- Count of the level loops. -/ def rN3 : ℕ := 162
/-- `α`. -/ def fAl : ℕ := 164
/-- `u`. -/ def fU : ℕ := 166
/-- `w`. -/ def fW : ℕ := 168
/-- `w + u`. -/ def fH : ℕ := 170
/-- `α (w + u)`. -/ def fT : ℕ := 172
/-- The new `lo`. -/ def fN : ℕ := 174
/-- A table entry. -/ def fG : ℕ := 176
/-- The levels left, `ℓ − j`. -/ def rKf : ℕ := 185
/-- The table's first cell. -/ def rTbf : ℕ := 186

/-! ## `α = wAt ptK 15 l base` -/

/-- One bit `i`: `α += [bit_i(base)] · T[l][i]`; `rTa += 1`, `i += 1`. -/
def alphaBody : XIR :=
  .seq (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0, .op .sub rBit uT1 rBit])
    (.seq (.load fG rTa)
      (.blk [.op .and fG fG rBit, .op .xor fAl fAl fG, .op .add rTa rTa cOne,
        .op .add uI uI cOne]))

/-- **`α`** for the block at `rBs`, from the table row at `rTr`. -/
def alphaIR : XIR :=
  .seq (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 15])
    (.loopK rC2 rN2 15 alphaBody)

/-! ## One butterfly, a level, the iteration -/

/-- The pair's addresses: `rBs := ⌊q/P⌋ · 2P`, `rAL := A + lo`, `rAH := A + hi`. -/
def pairPs : List Prim :=
  [.op .divu uT1 rQ rP2, .op .remu uX rQ rP2, .op .add uT2 rP2 rP2, .op .mul rBs uT1 uT2,
   .op .add uT1 rBs uX, .op .add rAL rA0 uT1, .op .add rAH rAL rP2]

/-- The butterfly's arithmetic: `u, w` from the heap, `fH := w + u`, `fN := u + α fH`. -/
def arithIR : XIR :=
  .seq (.load fU rAL) (.seq (.load fW rAH) (.seq (addK fH fW fU) (.seq (mulK fT fAl fH)
    (addK fN fU fT))))

/-- **One butterfly**: pair `q` of the level in `rLv`. -/
def pairBody : XIR :=
  .seq (.blk pairPs) (.seq alphaIR (.seq arithIR (.seq (.store rAL fN)
    (.seq (.store rAH fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A level**: the `2^(ℓ−1)` pairs, `P = 2^l`. -/
def levelIR (ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) pairBody)

/-- A level, then the next level and table row. -/
def lvlStep (ℓ : ℕ) : XIR :=
  .seq (levelIR ℓ) (.blk [.op .add rLv rLv cOne, .const uT1 15, .op .add rTr rTr uT1])

/-- **The inverse NTT**: levels `0 … ℓ − 1` on the row at `rA0`, the table at `tb`. -/
def bflyIR (ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (lvlStep ℓ))

/-! ## The basis table -/

/-- Row `0`, entry `i`: the word `2^i` (`ptK (2^i)`). -/
def row0Body : XIR :=
  .seq (.blk [.op .shl fG cOne uI]) (.seq (.store rTa fG)
    (.blk [.op .add rTa rTa cOne, .op .add uI uI cOne]))

/-- Row `0` at `rTr`. -/
def row0IR : XIR :=
  .seq (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) (.loopK rC2 rN2 15 row0Body)

/-- Row `v + 1`, entry at `rTa` (row `v`): `a (a + 1) · fAl`, stored 15 cells on. -/
def rowBody : XIR :=
  .seq (.load fU rTa) (.seq (.blk [.op .xor fW fU cOne])
    (.seq (mulK fH fU fW) (.seq (mulK fN fH fAl) (.seq (.blk [.const uT1 15, .op .add rAH rTa uT1])
      (.seq (.store rAH fN) (.blk [.op .add rTa rTa cOne]))))))

/-- Row `v + 1` from row `v` (at `rTr`, `v` in `rLv`): `fAl := (b (b + 1))⁻¹`, `b` entry `v + 1`;
then the 15 entries; `rLv += 1`, `rTr += 15`. -/
def rowIR : XIR :=
  .seq (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1])
    (.seq (.load fU rTa) (.seq (.blk [.op .xor fW fU cOne])
      (.seq (mulK fH fU fW) (.seq (invK fAl fH) (.seq (.blk [.op .or rTa rTr rTr, .const rN2 15])
        (.seq (.loopK rC2 rN2 15 rowBody)
          (.blk [.op .add rLv rLv cOne, .const uT1 15, .op .add rTr rTr uT1])))))))

/-- **The basis table** at `tb`: row `0`, then rows `1 … 14`. -/
def wtabIR (tb : ℕ) : XIR :=
  .seq (.blk [.const rTr (toWord tb)]) (.seq row0IR (.seq (.blk [.const rLv 0, .const rN3 14])
    (.loopK rC3 rN3 14 rowIR)))

/-! ## The forward NTT -/

/-- The forward arithmetic: `fT := α w`, `fN := u + fT`, `fH := fN + w`. -/
def farithIR : XIR :=
  .seq (.load fU rAL) (.seq (.load fW rAH) (.seq (mulK fT fAl fW) (.seq (addK fN fU fT)
    (addK fH fN fW))))

/-- **One forward butterfly**: pair `q` of the level in `rLv`. -/
def fpairBody : XIR :=
  .seq (.blk pairPs) (.seq alphaIR (.seq farithIR (.seq (.store rAL fN)
    (.seq (.store rAH fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A forward level**: the `2^(ℓ−1)` pairs, `P = 2^l`. -/
def flevelIR (ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) fpairBody)

/-- The level's registers: `rLv := rKf − 1`, `rTr := tb + 15 rLv`. -/
def fPre : List Prim :=
  [.op .sub rLv rKf cOne, .const uT1 15, .op .mul rTr rLv uT1, .op .add rTr rTr rTbf]

/-- One step: the level `rKf − 1`, then `rKf −= 1`. -/
def fStep (ℓ : ℕ) : XIR := .seq (.blk fPre) (.seq (flevelIR ℓ) (.blk [.op .sub rKf rKf cOne]))

/-- **The forward NTT**: levels `ℓ − 1 … 0` on the row at `rA0`, the table at `tb`. -/
def fwdIR (ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (fStep ℓ))

/-! ## `simp` forms of the field blocks' side conditions

The `WF`/`Writes`/`Lo`/`LoK` side conditions below never unfold `mulK`'s or `invK`'s primitives
(`invK` has 517). -/

theorem mulK_wf_iff {d a b : ℕ} (hd : 4 ≤ d) : WF (mulK d a b) ↔ True :=
  iff_true_intro (wf_mulK d a b hd)

theorem mulK_writes_iff {d a b c : ℕ} (hc : 9 ≤ c) (h0 : c ≠ d) :
    Writes (mulK d a b) c ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by rcases mulKC_dst d a b p hp with h | h <;> omega, False.elim⟩

theorem invK_writes_iff {d a c : ℕ} (hc : 12 ≤ c) (h0 : c ≠ d) :
    Writes (invK d a) c ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by rcases invKC_dst d a p hp with h | h <;> omega, False.elim⟩

theorem mulK_lo_iff {d a b : ℕ} (hd : d < 256) : Lo (mulK d a b) ↔ True :=
  iff_true_intro fun p hp => by have := mulKC_dst d a b p hp; simp only [regs] at *; omega

theorem mulK_loK_iff {d a b : ℕ} (hd : d < regs) : LoK (mulK d a b) ↔ True :=
  iff_true_intro fun p hp => by have := mulKC_dst d a b p hp; simp only [regs] at *; omega

theorem invK_loK_iff {d a : ℕ} (hd : d < regs) : LoK (invK d a) ↔ True :=
  iff_true_intro fun p hp => by have := invKC_dst d a p hp; simp only [regs] at *; omega

/-! ## Well formed, no tape loop, no output -/

theorem wf_alphaIR : WF alphaIR := by
  simp +decide only [alphaIR, alphaBody, WF, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
    rC2, cTmp, regs, or_false, and_true]

theorem wf_arithIR : WF arithIR := by
  simp +decide only [arithIR, addK, WF, Prim.dst, fU, fW, fH, fT, fN, mulK_wf_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false, and_true]

theorem wf_farithIR : WF farithIR := by
  simp +decide only [farithIR, addK, WF, Prim.dst, fU, fW, fH, fT, fN, mulK_wf_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false, and_true]

theorem wf_pairBody : WF pairBody := by
  simp +decide only [pairBody, pairPs, arithIR, alphaIR, alphaBody, addK, WF, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs,
    mulK_wf_iff, mulK_writes_iff, or_false, and_true]

theorem wf_fpairBody : WF fpairBody := by
  simp +decide only [fpairBody, pairPs, farithIR, alphaIR, alphaBody, addK, WF, Writes, Prim.dst,
    rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp,
    regs, mulK_wf_iff, mulK_writes_iff, or_false, and_true]

theorem wf_bflyIR (ℓ tb : ℕ) : WF (bflyIR ℓ tb) := by
  simp +decide only [bflyIR, lvlStep, levelIR, pairBody, pairPs, arithIR, alphaIR, alphaBody,
    addK, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAH, rTa, rBit, uI, rTr, rC1,
    rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs, mulK_wf_iff,
    mulK_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp,
    forall_eq, exists_eq_left, or_false, and_true]

theorem wf_fwdIR (ℓ tb : ℕ) : WF (fwdIR ℓ tb) := by
  simp +decide only [fwdIR, fStep, fPre, flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody,
    addK, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAH, rTa, rBit, uI, rTr, rC1,
    rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, rKf, rTbf, cTmp, regs, mulK_wf_iff,
    mulK_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp,
    forall_eq, exists_eq_left, or_false, and_true]

theorem wf_rowBody : WF rowBody := by
  simp +decide only [rowBody, WF, Prim.dst, fU, fW, fH, fN, uT1, rAH, rTa, cTmp, mulK_wf_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_rowIR : WF rowIR := by
  have m3 := wf_invK fAl fH (by decide)
  have n1 : ¬ Writes (mulK fH fU fW) rC2 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  have n2 : ¬ Writes (mulK fN fH fAl) rC2 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  simp only [rowIR, rowBody, WF, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, m3, n1, n2,
    mulK_wf_iff (show 4 ≤ fH by decide), mulK_wf_iff (show 4 ≤ fN by decide)]
  simp [rLv, uT1, rAH, rTa, rTr, rC2, rN2, fU, fW, cTmp, regs]

theorem wf_wtabIR (tb : ℕ) : WF (wtabIR tb) := by
  have n3 : ¬ Writes (mulK fH fU fW) rC3 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  have n4 : ¬ Writes (invK fAl fH) rC3 := by rw [invK_writes_iff (by decide) (by decide)]; simp
  have n5 : ¬ Writes (mulK fN fH fAl) rC3 := by rw [mulK_writes_iff (by decide) (by decide)]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, wf_rowIR⟩
  · simp [WF, Prim.dst, rTr]
  · simp +decide only [row0IR, row0Body, WF, Writes, Prim.dst, uI, rTa, rN2, rC2, fG, cTmp, regs,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true]
  · simp [WF, Prim.dst, rLv, rN3]
  · decide
  · decide
  · simp only [rowIR, rowBody, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, n3, n4, n5]
    simp [rLv, uT1, rAH, rTa, rTr, rC2, rN2, rC3, fU, fW, cTmp]

theorem noLoopT_bflyIR (ℓ tb : ℕ) : NoLoopT (bflyIR ℓ tb) := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, addK, mulK, NoLoopT]

theorem noLoopT_fwdIR (ℓ tb : ℕ) : NoLoopT (fwdIR ℓ tb) := by
  simp [fwdIR, fStep, flevelIR, fpairBody, farithIR, alphaIR, alphaBody, addK, mulK, NoLoopT]

theorem noLoopT_wtabIR (tb : ℕ) : NoLoopT (wtabIR tb) := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, mulK, invK, NoLoopT]

theorem outs_bflyIR (ℓ tb t : ℕ) : outs (bflyIR ℓ tb) t = 0 := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, addK, mulK, outs]

theorem outs_fwdIR (ℓ tb t : ℕ) : outs (fwdIR ℓ tb) t = 0 := by
  simp [fwdIR, fStep, flevelIR, fpairBody, farithIR, alphaIR, alphaBody, addK, mulK, outs]

theorem outs_wtabIR (tb t : ℕ) : outs (wtabIR tb) t = 0 := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, mulK, invK, outs]

/-! ## Costs -/

theorem cost_alphaIR (t : ℕ) : cost alphaIR t = 316 := by
  have a : (15 : Word).toNat = 15 := rfl
  simp only [alphaIR, alphaBody, cost, blkSteps, List.length_cons, List.length_nil, a]
  norm_num

theorem cost_pairBody (t : ℕ) : cost pairBody t = 364 := by
  simp only [pairBody, pairPs, arithIR, cost, cost_alphaIR, cost_addK, cost_mulK, blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_fpairBody (t : ℕ) : cost fpairBody t = 364 := by
  simp only [fpairBody, pairPs, farithIR, cost, cost_alphaIR, cost_addK, cost_mulK, blkSteps,
    List.length_cons, List.length_nil]
  norm_num

/-- **The inverse NTT's cost**: `ℓ` levels of `2^(ℓ−1)` pairs. -/
theorem cost_bflyIR (ℓ tb t : ℕ) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (bflyIR ℓ tb) t = 14 + ℓ * (367 * 2 ^ (ℓ - 1) + 23) := by
  have a1 : (toWord (2 ^ (ℓ - 1))).toNat = 2 ^ (ℓ - 1) := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [bflyIR, lvlStep, levelIR, cost, cost_pairBody, blkSteps, List.length_cons,
    List.length_nil, a1, a2]
  norm_num
  ring

/-- **The forward NTT's cost**: `ℓ` levels of `2^(ℓ−1)` pairs. -/
theorem cost_fwdIR (ℓ tb t : ℕ) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (fwdIR ℓ tb) t = 14 + ℓ * (367 * 2 ^ (ℓ - 1) + 27) := by
  have a1 : (toWord (2 ^ (ℓ - 1))).toNat = 2 ^ (ℓ - 1) := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [fwdIR, fStep, fPre, flevelIR, cost, cost_fpairBody, blkSteps, List.length_cons,
    List.length_nil, a1, a2]
  norm_num
  ring

/-- **The basis table's cost.** -/
theorem cost_wtabIR (tb t : ℕ) : cost (wtabIR tb) t = 24752 := by
  have a : (14 : Word).toNat = 14 := rfl
  have b : (15 : Word).toNat = 15 := rfl
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, cost, cost_mulK, cost_invK, blkSteps,
    List.length_cons, List.length_nil, a, b]
  norm_num

/-- **lvm's inverse NTT** (`ℓ = 13`, a row of `2^13` coefficients). -/
theorem cost_bflyIR_13 (tb t : ℕ) : cost (bflyIR 13 tb) t = 19542329 := by
  rw [cost_bflyIR 13 tb t (by norm_num) (by norm_num)]; norm_num

/-- **lvm's forward NTT** (`ℓ = 15`, a codeword row of `2^15` positions). -/
theorem cost_fwdIR_15 (tb t : ℕ) : cost (fwdIR 15 tb) t = 90194339 := by
  rw [cost_fwdIR 15 tb t (by norm_num) (by norm_num)]; norm_num

/-! ## The pairs of a level (pure) -/

/-- The block base of pair `q` at level `l`. -/
def baseP (l q : ℕ) : ℕ := q / 2 ^ l * 2 ^ (l + 1)

/-- The low position of pair `q`. -/
def loP (l q : ℕ) : ℕ := baseP l q + q % 2 ^ l

/-- The high position of pair `q`. -/
def hiP (l q : ℕ) : ℕ := loP l q + 2 ^ l

/-- The pair of position `i`. -/
def pairOf (l i : ℕ) : ℕ := i / 2 ^ (l + 1) * 2 ^ l + i % 2 ^ l

theorem divmod_lin {a x P : ℕ} (hx : x < P) : (a * P + x) / P = a ∧ (a * P + x) % P = x := by
  have hP : 0 < P := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hx, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem two_pow_succ_eq (l : ℕ) : 2 ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; ring

theorem loP_div (l q : ℕ) : loP l q / 2 ^ (l + 1) = q / 2 ^ l ∧
    loP l q % 2 ^ (l + 1) = q % 2 ^ l := by
  have h := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  exact divmod_lin (by rw [two_pow_succ_eq]; omega)

theorem hiP_div (l q : ℕ) : hiP l q / 2 ^ (l + 1) = q / 2 ^ l ∧
    hiP l q % 2 ^ (l + 1) = q % 2 ^ l + 2 ^ l := by
  have h := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  have := divmod_lin (a := q / 2 ^ l) (x := q % 2 ^ l + 2 ^ l) (P := 2 ^ (l + 1))
    (by rw [two_pow_succ_eq]; omega)
  simpa [hiP, loP, baseP, Nat.add_assoc] using this

theorem pairOf_loP (l q : ℕ) : pairOf l (loP l q) = q := by
  have hb : loP l q = q % 2 ^ l + q / 2 ^ l * 2 * 2 ^ l := by rw [loP, baseP, pow_succ]; ring
  rw [pairOf, (loP_div l q).1, show loP l q % 2 ^ l = q % 2 ^ l by
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_mod]]
  exact Nat.div_add_mod' q _

theorem pairOf_hiP (l q : ℕ) : pairOf l (hiP l q) = q := by
  have hb : hiP l q = q % 2 ^ l + (q / 2 ^ l * 2 + 1) * 2 ^ l := by
    rw [hiP, loP, baseP, pow_succ]; ring
  rw [pairOf, (hiP_div l q).1, show hiP l q % 2 ^ l = q % 2 ^ l by
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_mod]]
  exact Nat.div_add_mod' q _

/-- A position of pair `q` is its low or its high position. -/
theorem pair_cases {l i q : ℕ} (h : pairOf l i = q) : i = loP l q ∨ i = hiP l q := by
  subst h
  have hP : 0 < 2 ^ l := by positivity
  have hi := Nat.div_add_mod' i (2 ^ (l + 1))
  have hr := Nat.mod_lt i (show 0 < 2 ^ (l + 1) by positivity)
  rw [two_pow_succ_eq] at hr
  have hm : i % 2 ^ l = i % 2 ^ (l + 1) % 2 ^ l := by
    rw [pow_succ, Nat.mod_mul_right_mod]
  by_cases hx : i % 2 ^ (l + 1) < 2 ^ l
  · left
    have e : i % 2 ^ l = i % 2 ^ (l + 1) := by rw [hm, Nat.mod_eq_of_lt hx]
    obtain ⟨d1, d2⟩ := divmod_lin (a := i / 2 ^ (l + 1)) hx
    rw [loP, baseP, pairOf, e, d1, d2]
    omega
  · right
    have e : i % 2 ^ l = i % 2 ^ (l + 1) - 2 ^ l := by
      rw [hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    obtain ⟨d1, d2⟩ := divmod_lin (a := i / 2 ^ (l + 1)) (P := 2 ^ l)
      (x := i % 2 ^ (l + 1) - 2 ^ l) (by omega)
    rw [hiP, loP, baseP, pairOf, e, d1, d2]
    omega

/-- The positions of a pair lie in the row. -/
theorem hiP_lt {ℓ l q : ℕ} (hl : l < ℓ) (hq : q < 2 ^ (ℓ - 1)) : hiP l q < 2 ^ ℓ := by
  have hP : 0 < 2 ^ l := by positivity
  have e1 : 2 ^ (ℓ - 1) = 2 ^ (ℓ - 1 - l) * 2 ^ l := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ ℓ = 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) := by rw [← pow_add]; congr 1; omega
  have hd : q / 2 ^ l < 2 ^ (ℓ - 1 - l) := by rw [Nat.div_lt_iff_lt_mul hP, ← e1]; exact hq
  have hm := Nat.mod_lt q hP
  have h3 : (q / 2 ^ l + 1) * 2 ^ (l + 1) ≤ 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) :=
    Nat.mul_le_mul_right _ hd
  have h2 := two_pow_succ_eq l
  rw [hiP, loP, baseP, e2]
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

theorem loP_lt_hiP (l q : ℕ) : loP l q < hiP l q := by
  have : 0 < 2 ^ l := by positivity
  simp only [hiP]; omega

/-- Every position of the row is in a pair below `2^(ℓ−1)`. -/
theorem pairOf_lt {ℓ l i : ℕ} (hl : l < ℓ) (hi : i < 2 ^ ℓ) : pairOf l i < 2 ^ (ℓ - 1) := by
  have hP : 0 < 2 ^ l := by positivity
  have e1 : 2 ^ (ℓ - 1) = 2 ^ (ℓ - 1 - l) * 2 ^ l := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ ℓ = 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) := by rw [← pow_add]; congr 1; omega
  have hd : i / 2 ^ (l + 1) < 2 ^ (ℓ - 1 - l) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e2]; exact hi
  have h3 : (i / 2 ^ (l + 1) + 1) * 2 ^ l ≤ 2 ^ (ℓ - 1 - l) * 2 ^ l := Nat.mul_le_mul_right _ hd
  have hm := Nat.mod_lt i hP
  rw [pairOf, e1]
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

/-- **`bflyLevel` at a pair's positions** (characteristic 2: `u − α (w − u) = u + α (w + u)`). -/
theorem bflyLevel_lo (pt : ℕ → BF64) (N l q : ℕ) (Y : ℕ → BF64) :
    bflyLevel pt N 0 l Y (loP l q) =
      Y (loP l q) + wAt pt N l (baseP l q) * (Y (hiP l q) + Y (loP l q)) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := loP_div l q
  simp only [bflyLevel, d1, d2, Nat.mod_mod, if_pos hm, Nat.zero_add]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

theorem bflyLevel_hi (pt : ℕ → BF64) (N l q : ℕ) (Y : ℕ → BF64) :
    bflyLevel pt N 0 l Y (hiP l q) = Y (hiP l q) + Y (loP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := hiP_div l q
  simp only [bflyLevel, d1, d2, if_neg (show ¬ (q % 2 ^ l + 2 ^ l < 2 ^ l) by omega),
    Nat.add_mod_right, Nat.mod_mod]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

/-- **`fwdLevel` at a pair's positions.** -/
theorem fwdLevel_lo (pt : ℕ → BF64) (N l q : ℕ) (Y : ℕ → BF64) :
    fwdLevel pt N l Y (loP l q) = Y (loP l q) + wAt pt N l (baseP l q) * Y (hiP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := loP_div l q
  simp only [fwdLevel, d1, d2, Nat.mod_mod, if_pos hm]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

theorem fwdLevel_hi (pt : ℕ → BF64) (N l q : ℕ) (Y : ℕ → BF64) :
    fwdLevel pt N l Y (hiP l q) =
      Y (loP l q) + wAt pt N l (baseP l q) * Y (hiP l q) + Y (hiP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := hiP_div l q
  simp only [fwdLevel, d1, d2, if_neg (show ¬ (q % 2 ^ l + 2 ^ l < 2 ^ l) by omega),
    Nat.add_mod_right, Nat.mod_mod]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

/-- The first `j` forward levels, `ℓ − 1, …, ℓ − j`. -/
def fwdTop (ℓ : ℕ) : ℕ → (ℕ → BF64) → ℕ → BF64
  | 0, Y => Y
  | j + 1, Y => fwdLevel ptK nLog (ℓ - 1 - j) (fwdTop ℓ j Y)

theorem fwdRun_top (ℓ : ℕ) (Y : ℕ → BF64) :
    ∀ j ≤ ℓ, fwdRun ptK nLog ℓ Y = fwdRun ptK nLog (ℓ - j) (fwdTop ℓ j Y)
  | 0, _ => rfl
  | j + 1, hj => by
    rw [fwdRun_top ℓ Y j (by omega), show ℓ - j = (ℓ - (j + 1)) + 1 by omega, fwdRun, fwdTop,
      show ℓ - (j + 1) = ℓ - 1 - j by omega]

end Lvm.X
