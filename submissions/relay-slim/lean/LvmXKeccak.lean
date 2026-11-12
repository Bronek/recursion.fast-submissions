-- New for lvm (WP-13a, extractor): the leaf statement `leafStmt h n` on the extractor machine.
-- Bit lemmas adapted from `flock-recursive` `FRKeccakBits.lean` (`blockLane_bit`, rf-k kk/base) and
-- `FRKeccakLanes.lean` (`outBytes_getElem`, `toUInt8_shiftRight_getLsbD`, rf-k-LC kk/LC cb7f6fb);
-- `packBytes_append8` restated from `FRXChainFlock.lean` (rf-k kk/base) with a bit-level proof.
import LvmXLookup
import RecursionFast.Library.KeccakFast

/-!
# `leafStmtIR`: the leaf statement `Keccak-256(0x4C ‖ h ‖ enc64 n)` on the extractor machine

The program reads the four packed words of `h` (tape words `hW … hW+3`) and the word of `n` (tape word
`nW`), builds the one padded sponge block of the 41-byte message in the 25 lane registers `128 … 152`
(lane `j` of `0x4C ‖ h ‖ enc64 n ‖ 0x01 ‖ 0⁹³ ‖ 0x80` is `(P_{j−1} >> 56) | (P_j << 8)` of the packed
words `P`), runs the 24 rounds of `Keccak-f[1600]` (θ, ρπ, χ as one block, ι with the round constant;
rotations by constant shifts and `or`, `¬` as `⊕` all-ones, `RecursionFast.Keccak.roundF` lane for lane),
and outputs lanes `0 … 3`.

Registers: lanes `A` `128 … 152`, ρπ's `B` `160 … 184`, θ's `C` `192 … 196` and `D` `200 … 204`,
scratch `208`, `209`, all-ones `210`, the round constant `211`, the input words `212 … 216`, the 34
shift amounts at `217 … 250` (`KcKR`); `readAt`'s address `rA = 64`. No store, no loop; every other
cell is unchanged (`leafStmtIR_frame`).

* `kcEval`: a block on the register file as a function (`rd_runPrims_kcEval`), so one `simp` per
  phase evaluates it; `kc_theta_run`, `kc_rhoPi_run`, `kc_chi_run`, `kc_iota_run`: each phase is `KeccakFast`'s
  (`KcHoldsA`/`KcHoldsB`: the registers hold an `S25`); `kcRoundsIR_sem`: the rounds are `l.foldl roundF`.
* `kc_absorb_eq`: the block absorbed by `digestB` is `kcS0` of the packed words; `leafStmt_kc`:
  `leafStmt h n = outBytes (keccakFF (kcS0 …))` (through `digestB_eq`); `kc_packBytes_outBytes`.
* **`leafStmtIR_sem`**, `wf_leafStmtIR`, `noLoopT_leafStmtIR`, `outs_leafStmtIR`,
  `cost_leafStmtIR`, `sizeIR_leafStmtIR`.
-/

namespace Lvm.X

open RecursionFast RecursionFast.Keccak

/-! ## Blocks on the register file -/

/-- One statement on a register file. -/
def kcStep (R : ℕ → Word) : Prim → ℕ → Word
  | .op o d a b => upd R d (o.eval (R a) (R b))
  | .const d w => upd R d w

/-- A block on a register file. -/
def kcEval (ps : List Prim) (R : ℕ → Word) : ℕ → Word := ps.foldl kcStep R

theorem kc_upd_apply (R : ℕ → Word) (d : ℕ) (v : Word) (i : ℕ) :
    upd R d v i = if i = d then v else R i := rfl

theorem rd_run_kcStep (M : Mem) (p : Prim) (h : p.dst < M.size) : rd (p.run M) = kcStep (rd M) p := by
  funext i
  cases p with
  | op o d a b =>
    simp only [Prim.dst] at h
    simp only [Prim.run, kcStep, upd, rd_set]
    by_cases hi : i = d
    · subst hi; simp [h]
    · simp [hi, Ne.symm hi]
  | const d w =>
    simp only [Prim.dst] at h
    simp only [Prim.run, kcStep, upd, rd_set]
    by_cases hi : i = d
    · subst hi; simp [h]
    · simp [hi, Ne.symm hi]

theorem kc_size_run_prim (M : Mem) (p : Prim) : (p.run M).size = M.size := by
  cases p <;> simp [Prim.run]

/-- **A block is its register-file function** when every destination is a cell. -/
theorem rd_runPrims_kcEval : ∀ (ps : List Prim) (M : Mem), (∀ p ∈ ps, p.dst < M.size) →
    rd (runPrims ps M) = kcEval ps (rd M)
  | [], _, _ => rfl
  | p :: ps, M, h => by
    rw [runPrims_cons, rd_runPrims_kcEval ps (p.run M) (fun q hq => by
      rw [kc_size_run_prim]; exact h q (List.mem_cons_of_mem _ hq)),
      rd_run_kcStep M p (h p List.mem_cons_self)]
    rfl

theorem kcEval_append (ps qs : List Prim) (R : ℕ → Word) :
    kcEval (ps ++ qs) R = kcEval qs (kcEval ps R) := List.foldl_append

theorem kcEval_frame : ∀ (ps : List Prim) (R : ℕ → Word) {i : ℕ}, (∀ p ∈ ps, p.dst ≠ i) →
    kcEval ps R i = R i
  | [], _, _, _ => rfl
  | p :: ps, R, i, h => by
    show kcEval ps (kcStep R p) i = R i
    rw [kcEval_frame ps _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have := h p List.mem_cons_self
    cases p <;> simp only [kcStep, upd, Prim.dst] at this ⊢ <;> simp [Ne.symm this]

/-! ## Machine operations on constants -/

theorem kc_eval_shl (a : Word) (k : ℕ) :
    XOp.shl.eval a (BitVec.ofNat 64 k) = a <<< (k % 2 ^ 64 % 64) := by
  simp [XOp.eval]

theorem kc_eval_shr (a : Word) (k : ℕ) :
    XOp.shr.eval a (BitVec.ofNat 64 k) = a >>> (k % 2 ^ 64 % 64) := by
  simp [XOp.eval]

theorem kc_eval_and (a b : Word) : XOp.and.eval a b = a &&& b := rfl

/-! ## The program -/

/-- θ: the column parities `C`, `D[x] = C[x−1] ⊕ rot(C[x+1], 1)`, `A ⊕= D`. -/
def kcThetaPs : List Prim :=
  [.op .xor 192 128 133, .op .xor 192 192 138, .op .xor 192 192 143, .op .xor 192 192 148,
   .op .xor 193 129 134, .op .xor 193 193 139, .op .xor 193 193 144, .op .xor 193 193 149,
   .op .xor 194 130 135, .op .xor 194 194 140, .op .xor 194 194 145, .op .xor 194 194 150,
   .op .xor 195 131 136, .op .xor 195 195 141, .op .xor 195 195 146, .op .xor 195 195 151,
   .op .xor 196 132 137, .op .xor 196 196 142, .op .xor 196 196 147, .op .xor 196 196 152,
   .op .shl 208 193 217, .op .shr 209 193 250, .op .or 208 208 209, .op .xor 200 196 208,
   .op .shl 208 194 217, .op .shr 209 194 250, .op .or 208 208 209, .op .xor 201 192 208,
   .op .shl 208 195 217, .op .shr 209 195 250, .op .or 208 208 209, .op .xor 202 193 208,
   .op .shl 208 196 217, .op .shr 209 196 250, .op .or 208 208 209, .op .xor 203 194 208,
   .op .shl 208 192 217, .op .shr 209 192 250, .op .or 208 208 209, .op .xor 204 195 208,
   .op .xor 128 128 200, .op .xor 129 129 201, .op .xor 130 130 202, .op .xor 131 131 203,
   .op .xor 132 132 204, .op .xor 133 133 200, .op .xor 134 134 201, .op .xor 135 135 202,
   .op .xor 136 136 203, .op .xor 137 137 204, .op .xor 138 138 200, .op .xor 139 139 201,
   .op .xor 140 140 202, .op .xor 141 141 203, .op .xor 142 142 204, .op .xor 143 143 200,
   .op .xor 144 144 201, .op .xor 145 145 202, .op .xor 146 146 203, .op .xor 147 147 204,
   .op .xor 148 148 200, .op .xor 149 149 201, .op .xor 150 150 202, .op .xor 151 151 203,
   .op .xor 152 152 204]

/-- ρ and π: `B[j] := rot(A[π⁻¹ j], ρ[π⁻¹ j])`. -/
def kcRhoPiPs : List Prim :=
  [.op .or 160 128 128, .op .shl 208 134 239, .op .shr 209 134 228, .op .or 161 208 209,
   .op .shl 208 140 238, .op .shr 209 140 229, .op .or 162 208 209, .op .shl 208 146 229,
   .op .shr 209 146 238, .op .or 163 208 209, .op .shl 208 152 224, .op .shr 209 152 243,
   .op .or 164 208 209, .op .shl 208 131 233, .op .shr 209 131 234, .op .or 165 208 209,
   .op .shl 208 137 228, .op .shr 209 137 239, .op .or 166 208 209, .op .shl 208 138 219,
   .op .shr 209 138 248, .op .or 167 208 209, .op .shl 208 144 240, .op .shr 209 144 227,
   .op .or 168 208 209, .op .shl 208 150 248, .op .shr 209 150 219, .op .or 169 208 209,
   .op .shl 208 129 217, .op .shr 209 129 250, .op .or 170 208 209, .op .shl 208 135 220,
   .op .shr 209 135 247, .op .or 171 208 209, .op .shl 208 141 231, .op .shr 209 141 236,
   .op .or 172 208 209, .op .shl 208 147 221, .op .shr 209 147 246, .op .or 173 208 209,
   .op .shl 208 148 226, .op .shr 209 148 241, .op .or 174 208 209, .op .shl 208 132 232,
   .op .shr 209 132 235, .op .or 175 208 209, .op .shl 208 133 234, .op .shr 209 133 233,
   .op .or 176 208 209, .op .shl 208 139 223, .op .shr 209 139 244, .op .or 177 208 209,
   .op .shl 208 145 225, .op .shr 209 145 242, .op .or 178 208 209, .op .shl 208 151 246,
   .op .shr 209 151 221, .op .or 179 208 209, .op .shl 208 130 249, .op .shr 209 130 218,
   .op .or 180 208 209, .op .shl 208 136 245, .op .shr 209 136 222, .op .or 181 208 209,
   .op .shl 208 142 236, .op .shr 209 142 231, .op .or 182 208 209, .op .shl 208 143 237,
   .op .shr 209 143 230, .op .or 183 208 209, .op .shl 208 149 218, .op .shr 209 149 249,
   .op .or 184 208 209]

/-- χ: `A[i] := B[i] ⊕ (¬B[i+1] ∧ B[i+2])` within rows, `¬` as `⊕` all-ones. -/
def kcChiPs : List Prim :=
  [.op .xor 208 161 210, .op .and 208 208 162, .op .xor 128 160 208, .op .xor 208 162 210,
   .op .and 208 208 163, .op .xor 129 161 208, .op .xor 208 163 210, .op .and 208 208 164,
   .op .xor 130 162 208, .op .xor 208 164 210, .op .and 208 208 160, .op .xor 131 163 208,
   .op .xor 208 160 210, .op .and 208 208 161, .op .xor 132 164 208, .op .xor 208 166 210,
   .op .and 208 208 167, .op .xor 133 165 208, .op .xor 208 167 210, .op .and 208 208 168,
   .op .xor 134 166 208, .op .xor 208 168 210, .op .and 208 208 169, .op .xor 135 167 208,
   .op .xor 208 169 210, .op .and 208 208 165, .op .xor 136 168 208, .op .xor 208 165 210,
   .op .and 208 208 166, .op .xor 137 169 208, .op .xor 208 171 210, .op .and 208 208 172,
   .op .xor 138 170 208, .op .xor 208 172 210, .op .and 208 208 173, .op .xor 139 171 208,
   .op .xor 208 173 210, .op .and 208 208 174, .op .xor 140 172 208, .op .xor 208 174 210,
   .op .and 208 208 170, .op .xor 141 173 208, .op .xor 208 170 210, .op .and 208 208 171,
   .op .xor 142 174 208, .op .xor 208 176 210, .op .and 208 208 177, .op .xor 143 175 208,
   .op .xor 208 177 210, .op .and 208 208 178, .op .xor 144 176 208, .op .xor 208 178 210,
   .op .and 208 208 179, .op .xor 145 177 208, .op .xor 208 179 210, .op .and 208 208 175,
   .op .xor 146 178 208, .op .xor 208 175 210, .op .and 208 208 176, .op .xor 147 179 208,
   .op .xor 208 181 210, .op .and 208 208 182, .op .xor 148 180 208, .op .xor 208 182 210,
   .op .and 208 208 183, .op .xor 149 181 208, .op .xor 208 183 210, .op .and 208 208 184,
   .op .xor 150 182 208, .op .xor 208 184 210, .op .and 208 208 180, .op .xor 151 183 208,
   .op .xor 208 180 210, .op .and 208 208 181, .op .xor 152 184 208]

/-- θ, ρπ and χ of a round. -/
def kcRoundPs : List Prim := kcThetaPs ++ kcRhoPiPs ++ kcChiPs

/-- ι: the round constant into lane 0. -/
def kcIotaPs (c : UInt64) : List Prim := [.const 211 c.toBitVec, .op .xor 128 128 211]

/-- One round. -/
def kcRoundIR (c : UInt64) : XIR := .seq (.blk kcRoundPs) (.blk (kcIotaPs c))

/-- The rounds with the constants `l`. -/
def kcRoundsIR : List UInt64 → XIR
  | [] => .blk []
  | c :: l => .seq (kcRoundIR c) (kcRoundsIR l)

/-- The constants and the absorbed block. -/
def kcInitPs : List Prim :=
  [.const 217 (BitVec.ofNat 64 1), .const 218 (BitVec.ofNat 64 2),
   .const 219 (BitVec.ofNat 64 3), .const 220 (BitVec.ofNat 64 6),
   .const 221 (BitVec.ofNat 64 8), .const 222 (BitVec.ofNat 64 9),
   .const 223 (BitVec.ofNat 64 10), .const 224 (BitVec.ofNat 64 14),
   .const 225 (BitVec.ofNat 64 15), .const 226 (BitVec.ofNat 64 18),
   .const 227 (BitVec.ofNat 64 19), .const 228 (BitVec.ofNat 64 20),
   .const 229 (BitVec.ofNat 64 21), .const 230 (BitVec.ofNat 64 23),
   .const 231 (BitVec.ofNat 64 25), .const 232 (BitVec.ofNat 64 27),
   .const 233 (BitVec.ofNat 64 28), .const 234 (BitVec.ofNat 64 36),
   .const 235 (BitVec.ofNat 64 37), .const 236 (BitVec.ofNat 64 39),
   .const 237 (BitVec.ofNat 64 41), .const 238 (BitVec.ofNat 64 43),
   .const 239 (BitVec.ofNat 64 44), .const 240 (BitVec.ofNat 64 45),
   .const 241 (BitVec.ofNat 64 46), .const 242 (BitVec.ofNat 64 49),
   .const 243 (BitVec.ofNat 64 50), .const 244 (BitVec.ofNat 64 54),
   .const 245 (BitVec.ofNat 64 55), .const 246 (BitVec.ofNat 64 56),
   .const 247 (BitVec.ofNat 64 58), .const 248 (BitVec.ofNat 64 61),
   .const 249 (BitVec.ofNat 64 62), .const 250 (BitVec.ofNat 64 63),
   .const 210 (BitVec.allOnes 64), .const 128 0x4C, .op .shl 208 212 221, .op .or 128 128 208,
   .op .shr 208 212 246, .op .shl 209 213 221, .op .or 129 208 209, .op .shr 208 213 246,
   .op .shl 209 214 221, .op .or 130 208 209, .op .shr 208 214 246, .op .shl 209 215 221,
   .op .or 131 208 209, .op .shr 208 215 246, .op .shl 209 216 221, .op .or 132 208 209,
   .op .shr 208 216 246, .const 209 0x100, .op .or 133 208 209, .const 134 0, .const 135 0,
   .const 136 0, .const 137 0, .const 138 0, .const 139 0, .const 140 0, .const 141 0,
   .const 142 0, .const 143 0, .const 144 0x8000000000000000, .const 145 0, .const 146 0,
   .const 147 0, .const 148 0, .const 149 0, .const 150 0, .const 151 0, .const 152 0]

/-- **The leaf statement**: read `h` (tape words `hW … hW+3`) and `n` (tape word `nW`), absorb,
permute, output lanes `0 … 3`. -/
def leafStmtIR (hW nW : ℕ) : XIR :=
  .seq (readAt 212 hW) (.seq (readAt 213 (hW + 1)) (.seq (readAt 214 (hW + 2))
    (.seq (readAt 215 (hW + 3)) (.seq (readAt 216 nW) (.seq (.blk kcInitPs)
      (.seq (kcRoundsIR rc.toList) (.seq (.out 128) (.seq (.out 129) (.seq (.out 130) (.out 131))))))))))

/-! ## The phases against `KeccakFast` -/

/-- The lane registers `128 …` hold `s`. -/
def KcHoldsA (R : ℕ → Word) (s : S25) : Prop :=
  R 128 = s.a0.toBitVec ∧ R 129 = s.a1.toBitVec ∧ R 130 = s.a2.toBitVec ∧ R 131 = s.a3.toBitVec ∧
    R 132 = s.a4.toBitVec ∧ R 133 = s.a5.toBitVec ∧ R 134 = s.a6.toBitVec ∧
    R 135 = s.a7.toBitVec ∧ R 136 = s.a8.toBitVec ∧ R 137 = s.a9.toBitVec ∧
    R 138 = s.a10.toBitVec ∧ R 139 = s.a11.toBitVec ∧ R 140 = s.a12.toBitVec ∧
    R 141 = s.a13.toBitVec ∧ R 142 = s.a14.toBitVec ∧ R 143 = s.a15.toBitVec ∧
    R 144 = s.a16.toBitVec ∧ R 145 = s.a17.toBitVec ∧ R 146 = s.a18.toBitVec ∧
    R 147 = s.a19.toBitVec ∧ R 148 = s.a20.toBitVec ∧ R 149 = s.a21.toBitVec ∧
    R 150 = s.a22.toBitVec ∧ R 151 = s.a23.toBitVec ∧ R 152 = s.a24.toBitVec

/-- The registers `160 …` hold `s`. -/
def KcHoldsB (R : ℕ → Word) (s : S25) : Prop :=
  R 160 = s.a0.toBitVec ∧ R 161 = s.a1.toBitVec ∧ R 162 = s.a2.toBitVec ∧ R 163 = s.a3.toBitVec ∧
    R 164 = s.a4.toBitVec ∧ R 165 = s.a5.toBitVec ∧ R 166 = s.a6.toBitVec ∧
    R 167 = s.a7.toBitVec ∧ R 168 = s.a8.toBitVec ∧ R 169 = s.a9.toBitVec ∧
    R 170 = s.a10.toBitVec ∧ R 171 = s.a11.toBitVec ∧ R 172 = s.a12.toBitVec ∧
    R 173 = s.a13.toBitVec ∧ R 174 = s.a14.toBitVec ∧ R 175 = s.a15.toBitVec ∧
    R 176 = s.a16.toBitVec ∧ R 177 = s.a17.toBitVec ∧ R 178 = s.a18.toBitVec ∧
    R 179 = s.a19.toBitVec ∧ R 180 = s.a20.toBitVec ∧ R 181 = s.a21.toBitVec ∧
    R 182 = s.a22.toBitVec ∧ R 183 = s.a23.toBitVec ∧ R 184 = s.a24.toBitVec

/-- The constant registers: the shift amounts and all-ones. -/
def KcKR (R : ℕ → Word) : Prop :=
  R 217 = BitVec.ofNat 64 1 ∧ R 218 = BitVec.ofNat 64 2 ∧ R 219 = BitVec.ofNat 64 3 ∧
    R 220 = BitVec.ofNat 64 6 ∧ R 221 = BitVec.ofNat 64 8 ∧ R 222 = BitVec.ofNat 64 9 ∧
    R 223 = BitVec.ofNat 64 10 ∧ R 224 = BitVec.ofNat 64 14 ∧ R 225 = BitVec.ofNat 64 15 ∧
    R 226 = BitVec.ofNat 64 18 ∧ R 227 = BitVec.ofNat 64 19 ∧ R 228 = BitVec.ofNat 64 20 ∧
    R 229 = BitVec.ofNat 64 21 ∧ R 230 = BitVec.ofNat 64 23 ∧ R 231 = BitVec.ofNat 64 25 ∧
    R 232 = BitVec.ofNat 64 27 ∧ R 233 = BitVec.ofNat 64 28 ∧ R 234 = BitVec.ofNat 64 36 ∧
    R 235 = BitVec.ofNat 64 37 ∧ R 236 = BitVec.ofNat 64 39 ∧ R 237 = BitVec.ofNat 64 41 ∧
    R 238 = BitVec.ofNat 64 43 ∧ R 239 = BitVec.ofNat 64 44 ∧ R 240 = BitVec.ofNat 64 45 ∧
    R 241 = BitVec.ofNat 64 46 ∧ R 242 = BitVec.ofNat 64 49 ∧ R 243 = BitVec.ofNat 64 50 ∧
    R 244 = BitVec.ofNat 64 54 ∧ R 245 = BitVec.ofNat 64 55 ∧ R 246 = BitVec.ofNat 64 56 ∧
    R 247 = BitVec.ofNat 64 58 ∧ R 248 = BitVec.ofNat 64 61 ∧ R 249 = BitVec.ofNat 64 62 ∧
    R 250 = BitVec.ofNat 64 63 ∧ R 210 = BitVec.allOnes 64

theorem kc_kr_frame {R R' : ℕ → Word} (h : ∀ i, i = 210 ∨ 217 ≤ i → R' i = R i) (hK : KcKR R) :
    KcKR R' := by
  simp only [KcKR] at hK ⊢
  simp (disch := omega) only [h]
  exact hK

theorem kc_kr_kcEval {ps : List Prim} (hps : ∀ p ∈ ps, p.dst < 210 ∨ p.dst = 211) {R : ℕ → Word}
    (hK : KcKR R) : KcKR (kcEval ps R) :=
  kc_kr_frame (fun _ hi => kcEval_frame ps R fun p hp he => by have := hps p hp; omega) hK

theorem kc_theta_run (R : ℕ → Word) (s : S25) (hA : KcHoldsA R s) (hK : KcKR R) :
    KcHoldsA (kcEval kcThetaPs R) (thetaF s) := by
  simp only [KcHoldsA, KcKR] at hA hK
  simp only [KcHoldsA, kcThetaPs, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_xor, eval_or, kc_eval_shl,
    kc_eval_shr, hA, hK, Nat.reduceMod, Nat.reducePow]
  simp only [thetaF, rotK, UInt64.reduceSub, UInt64.toBitVec_xor, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, and_self]

theorem kc_rhoPi_run (R : ℕ → Word) (s : S25) (hA : KcHoldsA R s) (hK : KcKR R) :
    KcHoldsB (kcEval kcRhoPiPs R) (piF (rhoF s)) := by
  simp only [KcHoldsA, KcKR] at hA hK
  simp only [KcHoldsB, kcRhoPiPs, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_or, kc_eval_shl,
    kc_eval_shr, hA, hK, Nat.reduceMod, Nat.reducePow]
  simp only [piF, rhoF, rotK, UInt64.reduceSub, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.umod_self, Nat.zero_mod,
    BitVec.ushiftRight_zero, BitVec.or_self, UInt64.shiftLeft_zero,
    UInt64.sub_zero, and_self]

theorem kc_chi_run (R : ℕ → Word) (s : S25) (hB : KcHoldsB R s) (hK : KcKR R) :
    KcHoldsA (kcEval kcChiPs R) (chiF s) := by
  simp only [KcHoldsB, KcKR] at hB hK
  simp only [KcHoldsA, kcChiPs, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_xor, kc_eval_and, hB, hK,
    BitVec.xor_allOnes]
  simp only [chiF, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not, and_self]

theorem kc_iota_run (R : ℕ → Word) (s : S25) (c : UInt64) (hA : KcHoldsA R s) :
    KcHoldsA (kcEval (kcIotaPs c) R) (iotaF s c) := by
  simp only [KcHoldsA] at hA
  simp only [KcHoldsA, kcIotaPs, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_xor, hA]
  simp only [iotaF, UInt64.toBitVec_xor, and_self]

theorem kcThetaPs_dst : ∀ p ∈ kcThetaPs, 128 ≤ p.dst ∧ (p.dst < 210 ∨ p.dst = 211) := by decide
theorem kcRhoPiPs_dst : ∀ p ∈ kcRhoPiPs, 128 ≤ p.dst ∧ (p.dst < 210 ∨ p.dst = 211) := by decide
theorem kcChiPs_dst : ∀ p ∈ kcChiPs, 128 ≤ p.dst ∧ (p.dst < 210 ∨ p.dst = 211) := by decide

theorem kcRoundPs_dst : ∀ p ∈ kcRoundPs, 128 ≤ p.dst ∧ (p.dst < 210 ∨ p.dst = 211) := by
  simp only [kcRoundPs, List.mem_append]
  rintro p ((h | h) | h)
  · exact kcThetaPs_dst p h
  · exact kcRhoPiPs_dst p h
  · exact kcChiPs_dst p h

theorem kcIotaPs_dst (c : UInt64) : ∀ p ∈ kcIotaPs c, 128 ≤ p.dst ∧ (p.dst < 210 ∨ p.dst = 211) := by
  simp [kcIotaPs, Prim.dst]

/-- **A round** on the register file is `roundF`. -/
theorem kc_round_run (R : ℕ → Word) (s : S25) (c : UInt64) (hA : KcHoldsA R s) (hK : KcKR R) :
    KcHoldsA (kcEval (kcIotaPs c) (kcEval kcRoundPs R)) (roundF s c) ∧
      KcKR (kcEval (kcIotaPs c) (kcEval kcRoundPs R)) := by
  have k1 := kc_kr_kcEval (fun p hp => (kcThetaPs_dst p hp).2) hK
  have k2 := kc_kr_kcEval (fun p hp => (kcRhoPiPs_dst p hp).2) k1
  have k3 := kc_kr_kcEval (fun p hp => (kcChiPs_dst p hp).2) k2
  rw [kcRoundPs, kcEval_append, kcEval_append]
  exact ⟨kc_iota_run _ _ c (kc_chi_run _ _ (kc_rhoPi_run _ _ (kc_theta_run R s hA hK) k1) k2),
    kc_kr_kcEval (fun p hp => (kcIotaPs_dst c p hp).2) k3⟩

/-! ## The rounds on the machine -/

theorem kc_blk_rd {ps : List Prim} (hps : ∀ p ∈ ps, p.dst < 256) (I : Array Word) (st : St)
    (hs : regs ≤ st.M.size) : rd (semXIR I (.blk ps) st).M = kcEval ps (rd st.M) :=
  rd_runPrims_kcEval ps st.M fun p hp => by have := hps p hp; simp only [regs] at hs; omega

theorem kc_blk_o (ps : List Prim) (I : Array Word) (st : St) : (semXIR I (.blk ps) st).o = st.o :=
  rfl

/-- **The rounds** run `l.foldl roundF` on the lanes, keep the constants and output nothing. -/
theorem kcRoundsIR_sem (I : Array Word) : ∀ (l : List UInt64) (st : St) (S : S25),
    regs ≤ st.M.size → KcHoldsA (rd st.M) S → KcKR (rd st.M) →
    KcHoldsA (rd (semXIR I (kcRoundsIR l) st).M) (l.foldl roundF S) ∧
      (semXIR I (kcRoundsIR l) st).o = st.o
  | [], st, S, _, hA, _ => by
    refine ⟨?_, rfl⟩
    have e : rd (semXIR I (kcRoundsIR []) st).M = rd st.M := rfl
    rw [e]; exact hA
  | c :: l, st, S, hs, hA, hK => by
    have e1 : semXIR I (kcRoundsIR (c :: l)) st =
        semXIR I (kcRoundsIR l) (semXIR I (.blk (kcIotaPs c)) (semXIR I (.blk kcRoundPs) st)) := rfl
    have hs1 : regs ≤ (semXIR I (.blk kcRoundPs) st).M.size := by rw [size_sem]; exact hs
    have e2 : rd (semXIR I (.blk (kcIotaPs c)) (semXIR I (.blk kcRoundPs) st)).M =
        kcEval (kcIotaPs c) (kcEval kcRoundPs (rd st.M)) := by
      rw [kc_blk_rd (fun p hp => by have := kcIotaPs_dst c p hp; omega) I _ hs1,
        kc_blk_rd (fun p hp => by have := kcRoundPs_dst p hp; omega) I _ hs]
    have hr := kc_round_run (rd st.M) S c hA hK
    rw [← e2] at hr
    have ih := kcRoundsIR_sem I l _ (roundF S c) (by rw [size_sem, size_sem]; exact hs) hr.1 hr.2
    rw [e1, List.foldl_cons, ih.2, kc_blk_o, kc_blk_o]
    exact ⟨ih.1, rfl⟩

/-! ## The absorbed block -/

/-- The absorbed block of `0x4C ‖ h ‖ enc64 n` from the packed words `w₀ … w₃` of `h` and the word
`wn` of `n`: lane `j < 17` is `(P_{j−1} >> 56) | (P_j << 8)` of the packed words `P` of the padded
message after its first byte. -/
def kcS0 (w0 w1 w2 w3 wn : Word) : S25 :=
  ⟨.ofBitVec (0x4C ||| w0 <<< 8), .ofBitVec (w0 >>> 56 ||| w1 <<< 8), .ofBitVec (w1 >>> 56 ||| w2 <<< 8),
   .ofBitVec (w2 >>> 56 ||| w3 <<< 8), .ofBitVec (w3 >>> 56 ||| wn <<< 8),
   .ofBitVec (wn >>> 56 ||| 0x100), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, .ofBitVec 0x8000000000000000,
   0, 0, 0, 0, 0, 0, 0, 0⟩

theorem kcInitPs_dst : ∀ p ∈ kcInitPs, 128 ≤ p.dst ∧ p.dst < 251 := by decide

/-- **The init block** sets the constants and absorbs the block of the input registers. -/
theorem kc_init_run (R : ℕ → Word) :
    KcHoldsA (kcEval kcInitPs R) (kcS0 (R 212) (R 213) (R 214) (R 215) (R 216)) ∧
      KcKR (kcEval kcInitPs R) := by
  simp only [KcHoldsA, KcKR, kcS0, kcInitPs, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_or, kc_eval_shl, kc_eval_shr,
    Nat.reduceMod, Nat.reducePow]
  simp

/-! ## Packed words bit by bit -/

/-- Bit `z` of packed word `j` is bit `z % 8` of byte `8 j + z / 8`. -/
theorem kc_getLsbD_packBytes (l : List UInt8) (j : ℕ) {z : ℕ} (hz : z < 64) :
    ((packBytes l).getD j 0).getLsbD z = (l.getD (8 * j + z / 8) 0).toBitVec.getLsbD (z % 8) := by
  rw [← wordByte_packBytes l (8 * j + z / 8), wordByte, show (8 * j + z / 8) / 8 = j by omega,
    show (8 * j + z / 8) % 8 = z / 8 by omega]
  generalize (packBytes l).getD j 0 = W
  rw [Nat.toUInt8_eq, UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat,
    show (256 : ℕ) ^ (z / 8) = 2 ^ (8 * (z / 8)) by rw [pow_mul]; norm_num, Nat.testBit_div_two_pow,
    show z % 8 + 8 * (z / 8) = z by omega, BitVec.testBit_toNat]
  simp [show z % 8 < 8 by omega]

theorem kc_getLsbD_byte (t : UInt8) (z : ℕ) : t.toBitVec.getLsbD z = t.toNat.testBit z := by
  rw [← UInt8.toNat_toBitVec, BitVec.testBit_toNat]

/-- **Packed words after one leading byte**: word `j` of `t :: s` is `t` or the top byte of word
`j − 1` of `s`, then word `j` of `s` shifted by one byte. -/
theorem kc_packBytes_cons1 (t : UInt8) (s : List UInt8) (j : ℕ) :
    (packBytes (t :: s)).getD j 0 =
      (if j = 0 then BitVec.ofNat 64 t.toNat else (packBytes s).getD (j - 1) 0 >>> 56) |||
        (packBytes s).getD j 0 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [kc_getLsbD_packBytes _ _ hz, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases hz8 : z < 8
  · simp only [hz, hz8, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
    split_ifs with hj
    · subst hj
      rw [show 8 * 0 + z / 8 = 0 by omega, List.getD_cons_zero, BitVec.getLsbD_ofNat, kc_getLsbD_byte,
        Nat.mod_eq_of_lt hz8]
      simp [hz]
    · rw [BitVec.getLsbD_ushiftRight, kc_getLsbD_packBytes _ _ (by omega),
        show 8 * j + z / 8 = (8 * (j - 1) + (56 + z) / 8) + 1 by omega, List.getD_cons_succ,
        show (56 + z) % 8 = z % 8 by omega]
  · simp only [hz, hz8, decide_true, decide_false, Bool.not_false, Bool.true_and]
    rw [kc_getLsbD_packBytes _ _ (by omega), show 8 * j + z / 8 = (8 * j + (z - 8) / 8) + 1 by omega,
      List.getD_cons_succ, show (z - 8) % 8 = z % 8 by omega]
    split_ifs with hj
    · rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow
        (lt_of_lt_of_le t.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
    · rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ (56 + z) (by omega), Bool.false_or]

/-- Packed words of `a ++ b` with `|a| = 8k`: `a`'s, then `b`'s (restated from `FRXChainFlock`). -/
theorem kc_packBytes_append_getD (a b : List UInt8) {k : ℕ} (ha : a.length = 8 * k) (j : ℕ) :
    (packBytes (a ++ b)).getD j 0 =
      if j < k then (packBytes a).getD j 0 else (packBytes b).getD (j - k) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  split_ifs with hj
  · rw [kc_getLsbD_packBytes _ _ hz, kc_getLsbD_packBytes _ _ hz, List.getD_append _ _ _ _ (by omega)]
  · rw [kc_getLsbD_packBytes _ _ hz, kc_getLsbD_packBytes _ _ hz,
      List.getD_append_right _ _ _ _ (by omega), ha,
      show 8 * j + z / 8 - 8 * k = 8 * (j - k) + z / 8 by omega]

/-- Bit `z` of lane `i` of a block is bit `z % 8` of its byte `8 i + z / 8` (`FRKeccakBits`). -/
theorem kc_blockLane_bit (arr : Array UInt8) (i : ℕ) {z : ℕ} (hz : z < 64) :
    (blockLane arr i).toBitVec.getLsbD z = (arr.getD (8 * i + z / 8) 0).toBitVec.getLsbD (z % 8) := by
  rw [blockLane_unfold]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    BitVec.getLsbD_or, BitVec.getLsbD_zero, BitVec.ofNat_eq_ofNat,
    BitVec.zero_umod, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    BitVec.shiftLeft_zero, UInt64.toBitVec_ofNat, BitVec.reduceMod, Bool.false_or]
  interval_cases z <;> simp only [Nat.reduceLT, BitVec.getLsbD_eq_getElem,
    BitVec.getElem_setWidth, Nat.reduceLeDiff, BitVec.getLsbD_of_ge, Bool.or_self,
    Nat.reduceMod, BitVec.getElem_shiftLeft, decide_false, Bool.not_false, Nat.reduceSub,
    Bool.true_and, Bool.false_or, decide_true, Bool.not_true, Nat.sub_eq_zero_of_le, Nat.ofNat_pos,
    Bool.false_and, Bool.or_false, Nat.reduceDiv, Nat.add_zero]

/-- **A rate lane of a byte array is its packed word.** -/
theorem kc_laneAt_eq (p : ByteArray) (o : ℕ) (h8 : o % 8 = 0) (ho : o < 136) :
    laneAt p o = .ofBitVec ((packBytes p.data.toList).getD (o / 8) 0) := by
  have e := blockLane_eq p 0 (o / 8) (by omega)
  rw [show 0 + 8 * (o / 8) = o by omega] at e
  rw [← e]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [kc_blockLane_bit _ _ hz]
  show _ = ((packBytes p.data.toList).getD (o / 8) 0).getLsbD z
  rw [kc_getLsbD_packBytes _ _ hz]
  congr 2
  have hk : 8 * (o / 8) + z / 8 < rate := by simp only [rate]; omega
  simp only [List.drop_zero, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_take, hk, ite_true, List.getD_eq_getElem?_getD]

/-! ## The sponge of the leaf message -/

/-- The padding of a 41-byte message: `0x01`, 93 zeros, `0x80`. -/
def kcPad2 : List UInt8 := 0x01 :: (List.replicate 93 0 ++ [0x80])

theorem kc_packBytes_kcPad2 (k : ℕ) :
    (packBytes kcPad2).getD k 0 = if k = 0 then 1 else if k = 11 then 0x0080000000000000 else 0 := by
  have e : packBytes kcPad2 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x0080000000000000] := by decide
  rw [e]
  by_cases hk : k < 12
  · interval_cases k <;> rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp only [show k ≠ 0 by omega, show k ≠ 11 by omega, ↓reduceIte]

theorem kc_packBytes_enc64 (n : ℕ) : (packBytes (enc64 n)).getD 0 0 = toWord n := by
  have e := RecursionFast.packBytes_append8 [] (enc64_length n)
  rw [List.append_nil] at e
  rw [e, ofLE_enc64]
  apply BitVec.eq_of_toNat_eq
  simp [toWord]

/-- The leaf message padded: `0x4C`, then `h ‖ enc64 n ‖ 0x01 ‖ 0⁹³ ‖ 0x80`. -/
theorem kc_pad_leaf (h : Digest) (n : ℕ) :
    pad (tagLeaf :: h.toList ++ enc64 n) = tagLeaf :: (h.toList ++ (enc64 n ++ kcPad2)) := by
  have hl : (tagLeaf :: h.toList ++ enc64 n).length = 41 := by simp [enc64_length]
  simp only [pad, hl, rate, kcPad2]
  simp

/-- The packed words of the padded message after its first byte. -/
theorem kc_packBytes_tail (h : Digest) (n : ℕ) (k : ℕ) :
    (packBytes (h.toList ++ (enc64 n ++ kcPad2))).getD k 0 =
      if k < 4 then (packBytes h.toList).getD k 0 else if k = 4 then toWord n else
        if k = 5 then 1 else if k = 16 then 0x0080000000000000 else 0 := by
  rw [kc_packBytes_append_getD _ _ (k := 4) (by simp), kc_packBytes_append_getD _ _ (k := 1) (enc64_length n),
    kc_packBytes_kcPad2]
  by_cases h4 : k < 4
  · simp [h4]
  · simp only [h4, ↓reduceIte]
    by_cases h5 : k = 4
    · subst h5
      simp only [show 4 - 4 < 1 by omega, ↓reduceIte, Nat.sub_self]
      exact kc_packBytes_enc64 n
    · simp only [h5, ↓reduceIte, show ¬ k - 4 < 1 by omega]
      by_cases h6 : k = 5
      · subst h6; simp
      · by_cases h7 : k = 16
        · subst h7; simp
        · simp only [h6, h7, ↓reduceIte, show k - 4 - 1 ≠ 0 by omega, show k - 4 - 1 ≠ 11 by omega]

theorem kc_ofBitVec_zero : UInt64.ofBitVec 0 = 0 := rfl

/-- **The absorbed block** of the leaf message is `kcS0` of the packed words. -/
theorem kc_absorb_eq (h : Digest) (n : ℕ) :
    xorBlock zeroS (padB ⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩) 0 =
      kcS0 ((packBytes h.toList).getD 0 0) ((packBytes h.toList).getD 1 0)
        ((packBytes h.toList).getD 2 0) ((packBytes h.toList).getD 3 0) (toWord n) := by
  have hd : (padB ⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩).data.toList =
      tagLeaf :: (h.toList ++ (enc64 n ++ kcPad2)) := by
    rw [padB_data, ← kc_pad_leaf]
  have hL := kc_laneAt_eq (padB ⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩)
  rw [hd] at hL
  simp only [xorBlock, zeroS, kcS0, UInt64.zero_xor]
  simp (disch := decide) only [hL, Nat.reduceMul, Nat.zero_add, Nat.reduceDiv, kc_packBytes_cons1,
    kc_packBytes_tail, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceSub]
  simp [tagLeaf]

/-! ## The output words -/

/-- Byte `e` of the output of a state (`FRKeccakLanes`). -/
theorem kc_outBytes_getElem (s : S25) (e : ℕ) (he : e < 32) :
    (outBytes s)[e] = (s.toVec[e / 8]'(by omega) >>> (8 * (e % 8)).toUInt64).toUInt8 := by
  interval_cases e <;> rfl

/-- Byte `q` of a lane, bit `b` (`FRKeccakLanes`). -/
theorem kc_toUInt8_shiftRight_getLsbD (u : UInt64) {q b : ℕ} (hq : q < 8) (hb : b < 8) :
    ((u >>> (8 * q).toUInt64).toUInt8).toBitVec.getLsbD b = u.toBitVec.getLsbD (8 * q + b) := by
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, decide_eq_true hb, Bool.true_and,
    UInt64.toBitVec_shiftRight]
  interval_cases q <;> simp

/-- **The packed digest of a state is its lanes `0 … 3`.** -/
theorem kc_packBytes_outBytes (S : S25) :
    packBytes (outBytes S).toList = [S.a0.toBitVec, S.a1.toBitVec, S.a2.toBitVec, S.a3.toBitVec] := by
  apply List.ext_getElem (by simp [packBytes_length])
  intro j h1 h2
  have hj : j < 4 := by simpa using h2
  rw [← List.getD_eq_getElem _ 0 h1]
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [kc_getLsbD_packBytes _ _ hz, List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList,
    kc_outBytes_getElem _ _ (by omega), kc_toUInt8_shiftRight_getLsbD _ (by omega) (by omega)]
  simp only [show (8 * j + z / 8) / 8 = j by omega, show 8 * ((8 * j + z / 8) % 8) + z % 8 = z by omega]
  interval_cases j <;> rfl

/-- **The leaf statement** is the permuted `kcS0` (through `KeccakFast.digestB_eq`). -/
theorem leafStmt_kc (h : Digest) (n : ℕ) :
    leafStmt h n = outBytes (keccakFF (kcS0 ((packBytes h.toList).getD 0 0)
      ((packBytes h.toList).getD 1 0) ((packBytes h.toList).getD 2 0)
      ((packBytes h.toList).getD 3 0) (toWord n))) := by
  have hb : (⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩ : ByteArray).data.toList =
      tagLeaf :: h.toList ++ enc64 n := rfl
  rw [leafStmt, ← hb, ← digestB_eq]
  have hs : (padB ⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩).size / rate = 1 := by
    have e := congrArg List.length (padB_data ⟨(tagLeaf :: h.toList ++ enc64 n).toArray⟩)
    rw [hb, kc_pad_leaf] at e
    simp only [Array.length_toList, ByteArray.size_data, List.length_cons, List.length_append,
      Vector.length_toList, enc64_length, kcPad2, List.length_replicate] at e
    rw [e]; rfl
  show outBytes (loopB _ zeroS 0 ((padB _).size / rate)) = _
  rw [hs, loopB.eq_2, loopB.eq_1, kc_absorb_eq]

/-! ## The program's shape -/

theorem lo_kcRoundsIR : ∀ l, Lo (kcRoundsIR l)
  | [] => by simp [kcRoundsIR, Lo]
  | c :: l => by
    simp only [kcRoundsIR, kcRoundIR, Lo]
    exact ⟨⟨fun p hp => by have := kcRoundPs_dst p hp; simp only [regs]; omega,
      fun p hp => by have := kcIotaPs_dst c p hp; simp only [regs]; omega⟩, lo_kcRoundsIR l⟩

theorem wf_kcRoundsIR : ∀ l, WF (kcRoundsIR l)
  | [] => by simp [kcRoundsIR, WF]
  | c :: l => by
    simp only [kcRoundsIR, kcRoundIR, WF]
    exact ⟨⟨fun p hp => by have := (kcRoundPs_dst p hp).1; omega,
      fun p hp => by have := (kcIotaPs_dst c p hp).1; omega⟩, wf_kcRoundsIR l⟩

theorem noLoopT_kcRoundsIR : ∀ l, NoLoopT (kcRoundsIR l)
  | [] => trivial
  | _ :: l => ⟨⟨trivial, trivial⟩, noLoopT_kcRoundsIR l⟩

theorem outs_kcRoundsIR (t : ℕ) : ∀ l, outs (kcRoundsIR l) t = 0
  | [] => rfl
  | _ :: l => by simp only [kcRoundsIR, kcRoundIR, outs, outs_kcRoundsIR t l]

theorem kcRoundPs_length : kcRoundPs.length = 213 := by
  simp only [kcRoundPs, List.length_append]
  rfl

theorem cost_kcRoundsIR (t : ℕ) : ∀ l, cost (kcRoundsIR l) t = 430 * l.length + 1
  | [] => rfl
  | c :: l => by
    simp only [kcRoundsIR, kcRoundIR, cost, cost_kcRoundsIR t l, kcRoundPs_length, kcIotaPs,
      List.length_cons, List.length_nil, blkSteps]
    simp
    omega

theorem sizeIR_kcRoundsIR : ∀ l, sizeIR (kcRoundsIR l) = 430 * l.length + 1
  | [] => rfl
  | c :: l => by
    simp only [kcRoundsIR, kcRoundIR, sizeIR, sizeIR_kcRoundsIR l, kcRoundPs_length, kcIotaPs,
      List.length_cons, List.length_nil, blkSteps]
    simp
    omega

theorem kcInitPs_length : kcInitPs.length = 72 := rfl

theorem rc_toList_length : rc.toList.length = 24 := rfl

theorem lo_leafStmtIR (hW nW : ℕ) : Lo (leafStmtIR hW nW) := by
  simp only [leafStmtIR, readAt, Lo, List.mem_singleton, forall_eq, Prim.dst, rA, regs,
    lo_kcRoundsIR, and_true]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    fun p hp => by have := kcInitPs_dst p hp; show p.dst < 256; omega⟩

theorem wf_leafStmtIR (hW nW : ℕ) : WF (leafStmtIR hW nW) := by
  simp only [leafStmtIR, readAt, WF, List.mem_singleton, forall_eq, Prim.dst, rA,
    wf_kcRoundsIR, and_true]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    fun p hp => by have := (kcInitPs_dst p hp).1; show 4 ≤ p.dst; omega⟩

theorem noLoopT_leafStmtIR (hW nW : ℕ) : NoLoopT (leafStmtIR hW nW) := by
  simp only [leafStmtIR, readAt, NoLoopT, noLoopT_kcRoundsIR, and_self]

theorem outs_leafStmtIR (hW nW : ℕ) : ∀ t, outs (leafStmtIR hW nW) t = 4 := by
  intro t
  simp only [leafStmtIR, readAt, outs, outs_kcRoundsIR]

theorem cost_leafStmtIR (hW nW : ℕ) : ∀ t, cost (leafStmtIR hW nW) t = 10493 := by
  intro t
  simp only [leafStmtIR, readAt, cost, cost_kcRoundsIR, rc_toList_length, kcInitPs_length,
    List.length_singleton, blkSteps]
  simp

theorem sizeIR_leafStmtIR (hW nW : ℕ) : sizeIR (leafStmtIR hW nW) = 10493 := by
  simp only [leafStmtIR, readAt, sizeIR, sizeIR_kcRoundsIR, rc_toList_length, kcInitPs_length,
    List.length_singleton, blkSteps]
  simp

/-! ## The headline -/

/-- `readAt d pos` on the register file. -/
theorem kc_readAt (I : Array Word) (st : St) (hs : regs ≤ st.M.size) {d pos : ℕ} (hd : d < regs)
    (hp : pos < 2 ^ 64) :
    rd (semXIR I (readAt d pos) st).M = upd (upd (rd st.M) rA (BitVec.ofNat 64 pos)) d (I.getD pos 0) ∧
      (semXIR I (readAt d pos) st).o = st.o ∧ regs ≤ (semXIR I (readAt d pos) st).M.size := by
  refine ⟨?_, rfl, by rw [size_sem]; exact hs⟩
  have hA : rA < st.M.size := by simp only [rA, regs] at hs ⊢; omega
  have e1 : rd (runPrims [.const rA (BitVec.ofNat 64 pos)] st.M) =
      upd (rd st.M) rA (BitVec.ofNat 64 pos) :=
    rd_run_kcStep st.M (.const rA (BitVec.ofNat 64 pos)) hA
  have e2 : rd (runPrims [.const rA (BitVec.ofNat 64 pos)] st.M) rA = BitVec.ofNat 64 pos := by
    rw [e1]; simp [upd]
  show rd (Prim.run (runPrims [.const rA (BitVec.ofNat 64 pos)] st.M) (.const d
    (I.getD (rd (runPrims [.const rA (BitVec.ofNat 64 pos)] st.M) rA).toNat 0))) = _
  rw [rd_run_kcStep _ _ (by simp only [size_runPrims, Prim.dst]; simp only [regs] at hs hd; omega),
    e2, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rfl

-- Not a `rfl` lemma on purpose: as a definitional `simp` step the kernel would re-check the whole
-- program's unfolding (deep recursion through the 24 rounds).
theorem kc_sem_seq (I : Array Word) (p q : XIR) (st : St) :
    semXIR I (.seq p q) st = semXIR I q (semXIR I p st) := by
  simp only [semXIR]

theorem kc_sem_out (I : Array Word) (v : ℕ) (st : St) :
    semXIR I (.out v) st = ⟨st.M, st.o.push (rd st.M v)⟩ := rfl

theorem kc_outs4 (I : Array Word) (st : St) (a b c d : ℕ) :
    (semXIR I (.seq (.out a) (.seq (.out b) (.seq (.out c) (.out d)))) st).o.toList =
      st.o.toList ++ [rd st.M a, rd st.M b, rd st.M c, rd st.M d] := by
  simp [semXIR]

/-- **The leaf statement on the machine**: from tape words `hW … hW+3` holding the packed `h` and
tape word `nW` holding `n`, `leafStmtIR` outputs the four packed words of `leafStmt h n`, and leaves
every heap cell alone. -/
theorem leafStmtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {hW nW : ℕ} (h : Digest) (n : ℕ)
    (hh : ∀ i < 4, I.getD (hW + i) 0 = (packBytes h.toList).getD i 0) (hn : I.getD nW 0 = toWord n)
    (hn64 : n < 2 ^ 64) (hb : hW + 4 < 2^64) (hb' : nW < 2^64) :
    (semXIR I (leafStmtIR hW nW) s).o.toList = s.o.toList ++ packBytes (leafStmt h n).toList ∧
    ∀ y, regs ≤ y → rd (semXIR I (leafStmtIR hW nW) s).M y = rd s.M y := by
  refine ⟨?_, hframe I _ s (lo_leafStmtIR hW nW)⟩
  have hr : (212 : ℕ) < regs ∧ (213 : ℕ) < regs ∧ (214 : ℕ) < regs ∧ (215 : ℕ) < regs ∧
      (216 : ℕ) < regs := by decide
  obtain ⟨e1, o1, z1⟩ := kc_readAt I s hM.1 hr.1 (pos := hW) (by omega)
  obtain ⟨e2, o2, z2⟩ := kc_readAt I _ z1 hr.2.1 (pos := hW + 1) (by omega)
  obtain ⟨e3, o3, z3⟩ := kc_readAt I _ z2 hr.2.2.1 (pos := hW + 2) (by omega)
  obtain ⟨e4, o4, z4⟩ := kc_readAt I _ z3 hr.2.2.2.1 (pos := hW + 3) (by omega)
  obtain ⟨e5, o5, z5⟩ := kc_readAt I _ z4 hr.2.2.2.2 (pos := nW) hb'
  generalize hs5 : semXIR I (readAt 216 nW) (semXIR I (readAt 215 (hW + 3))
    (semXIR I (readAt 214 (hW + 2)) (semXIR I (readAt 213 (hW + 1))
      (semXIR I (readAt 212 hW) s)))) = s5 at e5 o5 z5
  have w : ∀ i, i = 212 ∨ i = 213 ∨ i = 214 ∨ i = 215 ∨ i = 216 →
      rd s5.M i = upd (upd (upd (upd (upd (rd s.M) 212 (I.getD hW 0)) 213 (I.getD (hW + 1) 0)) 214
        (I.getD (hW + 2) 0)) 215 (I.getD (hW + 3) 0)) 216 (I.getD nW 0) i := by
    intro i hi
    rw [e5, e4, e3, e2, e1]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [upd, rA]
  have w0 : rd s5.M 212 = (packBytes h.toList).getD 0 0 := by
    rw [w 212 (by omega), ← hh 0 (by omega)]; simp [upd]
  have w1 : rd s5.M 213 = (packBytes h.toList).getD 1 0 := by
    rw [w 213 (by omega), ← hh 1 (by omega)]; simp [upd]
  have w2 : rd s5.M 214 = (packBytes h.toList).getD 2 0 := by
    rw [w 214 (by omega), ← hh 2 (by omega)]; simp [upd]
  have w3 : rd s5.M 215 = (packBytes h.toList).getD 3 0 := by
    rw [w 215 (by omega), ← hh 3 (by omega)]; simp [upd]
  have wn : rd s5.M 216 = toWord n := by
    rw [w 216 (by omega), ← hn]; simp [upd]
  have hi := kc_init_run (rd s5.M)
  rw [← kc_blk_rd (fun p hp => by have := kcInitPs_dst p hp; omega) I s5 z5, w0, w1, w2, w3, wn]
    at hi
  have z6 : regs ≤ (semXIR I (.blk kcInitPs) s5).M.size := by rw [size_sem]; exact z5
  have hR := kcRoundsIR_sem I rc.toList _ _ z6 hi.1 hi.2
  rw [Vector.foldl_toList, ← keccakFF] at hR
  simp only [leafStmtIR, kc_sem_seq]
  rw [hs5]
  simp only [kc_sem_out, Array.toList_push, hR.2, kc_blk_o, o5, o4, o3, o2, o1, leafStmt_kc,
    kc_packBytes_outBytes, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨a0, a1, a2, a3, -⟩ := hR.1
  rw [a0, a1, a2, a3]

/-- The registers the program writes: `rA = 64` and `128 … 250`. -/
theorem writes_kcRoundsIR : ∀ (l : List UInt64) {y : ℕ}, Writes (kcRoundsIR l) y → 128 ≤ y ∧ y < 251
  | [], _, h => by simp [kcRoundsIR, Writes] at h
  | c :: l, y, h => by
    simp only [kcRoundsIR, kcRoundIR, Writes] at h
    rcases h with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | h
    · have := kcRoundPs_dst p hp; omega
    · have := kcIotaPs_dst c p hp; omega
    · exact writes_kcRoundsIR l h

theorem not_writes_leafStmtIR {hW nW y : ℕ} (h64 : y ≠ 64) (hy : y < 128 ∨ 251 ≤ y) :
    ¬ Writes (leafStmtIR hW nW) y := by
  have hI : ¬ ∃ p ∈ kcInitPs, p.dst = y := fun ⟨p, hp, he⟩ => by
    have := kcInitPs_dst p hp; omega
  have hR : ¬ Writes (kcRoundsIR rc.toList) y := fun h => by
    have := writes_kcRoundsIR _ h; omega
  have hc : ∀ (d : ℕ) (w : Word), (Prim.const d w).dst = d := fun _ _ => rfl
  simp only [leafStmtIR, readAt, Writes, List.mem_singleton, exists_eq_left, hc, rA, hI, hR,
    or_false, not_or]
  omega

/-- **Register frame**: every cell but `rA = 64` and the registers `128 … 250` is unchanged (the
parse, walk, sort and lookup registers `65 … 127` included). -/
theorem leafStmtIR_frame (I : Array Word) (s : St) (hM : Inv s.M) (hW nW : ℕ) :
    ∀ y, y ≠ 64 → (y < 128 ∨ 251 ≤ y) → rd (semXIR I (leafStmtIR hW nW) s).M y = rd s.M y := by
  intro y h64 hy
  by_cases hr : y < regs
  · exact frame I _ s (wf_leafStmtIR hW nW) hM y hr (not_writes_leafStmtIR h64 hy)
  · exact hframe I _ s (lo_leafStmtIR hW nW) y (by omega)

end Lvm.X
