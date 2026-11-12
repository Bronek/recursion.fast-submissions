-- WP-13b: the `eq` table of the fold challenges on the machine (BLUEPRINT §6.2 step 5, the fold's weights).
-- adapted from rf-k/submissions/flock-recursive/lean/FRXEqT.lean@8bff272b (`omPs`, `bitPs`, `eqBody`, `entPre`,
-- `entAd`, `eqEnt`, `eqtIR`, `bit_word`, `rdK_one_sub` and their `*_sem`, `wf_eqtIR`, `noLoopT_eqtIR`,
-- `outs_eqtIR`, `cost_eqtIR`, `eqBits_ctl`; renamed `eqt*`/`et*`): FR's 4-word `K` becomes lvm's 3-word
-- `E = Ext3`, FR's challenges at stride 8 in the chain's answers (`sAt_words`, dropped) a plain table at
-- stride 3, FR's 2-word `ldF`/`stF` the 3-word `eqtLdE`/`eqtStE` (new).
import LvmXDec
import LvmXLoop

/-!
# The `eq` table of the fold challenges on the machine

The fold weighs lane `l` by `eqA α l = eqBits α 6 l` (`LvmXDec`). `eqtIR ℓ aB qB` reads the
challenges `α_v` (`E`, three words) at `aB + 3v`, `v < ℓ`, and writes
`E[x] = eqBits α ℓ x = ∏_{v<ℓ} (bit_v x ? α_v : 1 − α_v)` at `qB + 3x` for `x < 2^ℓ` (`rdE`), the
layout `LvmXAgree`'s fold reads (`qB + 3l + c`). Each entry is computed directly by its definition:
`ℓ` `E` products per entry, `384` in all at `ℓ = 6`.

* `eqtBody_sem`: one factor;
* `eqtEnt_sem`: one entry (the product over `v`, in `range` order);
* **`eqtIR_sem`**: the table, and the heap outside it kept; **`eqtIR_eqA`**: `ℓ = 6`, `eqA`;
* `cost_eqtIR`: `12 + 2^ℓ · (54 + 125ℓ)` steps, `51,468` at `ℓ = 6` (`cost_eqtIR_six`).

Registers: `E` values in `25 … 33` (the accumulator `25 … 27`, `α_v` `28 … 30`, `1 − α_v`
`31 … 33`; `mulE`'s scratch is `5 … 24`), scalars in `206 … 214`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-! ## Registers and the program -/

/-- The accumulator (`E`, `25 … 27`). -/ def etA : ℕ := 25
/-- The challenge `α_v` (`E`, `28 … 30`). -/ def etS : ℕ := 28
/-- `1 − α_v` (`E`, `31 … 33`). -/ def etO : ℕ := 31
/-- The entry `x`. -/ def etX : ℕ := 206
/-- The factor `v`. -/ def etV : ℕ := 207
/-- An address. -/ def etAd : ℕ := 208
/-- Bit `v` of `x`. -/ def etBit : ℕ := 209
/-- Constant scratch. -/ def etK : ℕ := 210
/-- Counter of the entry loop. -/ def etC1 : ℕ := 211
/-- Its count. -/ def etN1 : ℕ := 212
/-- Counter of the factor loop. -/ def etC2 : ℕ := 213
/-- Its count. -/ def etN2 : ℕ := 214

/-- `etO := 1 + etS` (`1 − α` in characteristic 2): coordinate 0 xor `1`, the others copied. -/
def eqtOm : List Prim :=
  [.op .xor etO etS cOne, .op .or (etO + 1) (etS + 1) (etS + 1), .op .or (etO + 2) (etS + 2) (etS + 2)]

/-- `etBit := bit_v x`, `v += 1`. -/
def eqtBitPs : List Prim :=
  [.op .shr etBit etX etV, .op .and etBit etBit cOne, .op .add etV etV cOne]

/-- `M[d] := M[M[p]]`, `M[p] += 1`. -/
def eqtLd1 (d p : ℕ) : XIR := .seq (.load d p) (.blk [.op .add p p cOne])

/-- **An `E` load** `M[d … d+2] := M[M[p] … M[p]+2]`, `M[p] += 3`. -/
def eqtLdE (d p : ℕ) : XIR := .seq (eqtLd1 d p) (.seq (eqtLd1 (d + 1) p) (eqtLd1 (d + 2) p))

/-- `M[M[p]] := M[v]`, `M[p] += 1`. -/
def eqtSt1 (p v : ℕ) : XIR := .seq (.store p v) (.blk [.op .add p p cOne])

/-- **An `E` store** `M[M[p] … M[p]+2] := M[v … v+2]`, `M[p] += 3`. -/
def eqtStE (p v : ℕ) : XIR := .seq (eqtSt1 p v) (.seq (eqtSt1 p (v + 1)) (eqtSt1 p (v + 2)))

/-- **One factor**: `acc *= (bit_v x ? α_v : 1 − α_v)`, `α_v` at `M[etAd]`; `etAd += 3`, `v += 1`. -/
def eqtBody : XIR :=
  .seq (eqtLdE etS etAd) (.seq (.blk eqtOm) (.seq (.blk eqtBitPs)
    (.ite etBit (mulE etA etA etS) (mulE etA etA etO))))

/-- `acc := 1`, `v := 0`, `etAd := aB`, `etN2 := ℓ`. -/
def eqtPre (ℓ aB : ℕ) : List Prim :=
  [.const etA 1, .const (etA + 1) 0, .const (etA + 2) 0, .const etV 0, .const etAd (toWord aB),
   .const etN2 (toWord ℓ)]

/-- `etAd := qB + 3x`. -/
def eqtAd (qB : ℕ) : List Prim :=
  [.op .add etAd etX etX, .op .add etAd etAd etX, .const etK (toWord qB), .op .add etAd etAd etK]

/-- **One entry** `E[x] := ∏_{v<ℓ} …`, stored at `qB + 3x`; `x += 1`. -/
def eqtEnt (ℓ aB qB : ℕ) : XIR :=
  .seq (.blk (eqtPre ℓ aB)) (.seq (.loopK etC2 etN2 (toWord ℓ) eqtBody) (.seq (.blk (eqtAd qB))
    (.seq (eqtStE etAd etA) (.blk [.op .add etX etX cOne]))))

/-- **The table** `E[x] = eqBits α ℓ x` at `qB + 3x`, `x < 2^ℓ`, from `α_v` at `aB + 3v`. -/
def eqtIR (ℓ aB qB : ℕ) : XIR :=
  .seq (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))])
    (.loopK etC1 etN1 (toWord (2 ^ ℓ)) (eqtEnt ℓ aB qB))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_eqtIR (ℓ aB qB : ℕ) : WF (eqtIR ℓ aB qB) := by
  simp +decide [eqtIR, eqtEnt, eqtBody, eqtLdE, eqtLd1, eqtStE, eqtSt1, eqtOm, eqtBitPs, eqtPre,
    eqtAd, mulE, mulEC, redC, WF, Writes, Prim.dst, etA, etS, etO, etX, etV, etAd, etBit, etK, etC1,
    etN1, etC2, etN2, cOne]

theorem noLoopT_eqtIR (ℓ aB qB : ℕ) : NoLoopT (eqtIR ℓ aB qB) := by
  simp [eqtIR, eqtEnt, eqtBody, eqtLdE, eqtLd1, eqtStE, eqtSt1, mulE, NoLoopT]

theorem outs_eqtIR (ℓ aB qB t : ℕ) : outs (eqtIR ℓ aB qB) t = 0 := by
  simp [eqtIR, eqtEnt, eqtBody, eqtLdE, eqtLd1, eqtStE, eqtSt1, mulE, outs]

/-- **The table's cost**: `2^ℓ` entries of `ℓ` factors. -/
theorem cost_eqtIR (ℓ aB qB t : ℕ) (hℓ : ℓ < 64) :
    cost (eqtIR ℓ aB qB) t = 12 + 2 ^ ℓ * (54 + 125 * ℓ) := by
  have a1 : (toWord (2 ^ ℓ)).toNat = 2 ^ ℓ := toNat_toWord (Nat.pow_lt_pow_right (by norm_num) hℓ)
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord (by omega)
  simp only [eqtIR, eqtEnt, eqtPre, eqtAd, eqtBody, eqtOm, eqtBitPs, eqtLdE, eqtLd1, eqtStE, eqtSt1,
    cost, cost_mulE, blkSteps, List.length_cons, List.length_nil, a1, a2, max_self]
  norm_num
  ring

/-- The lvm instance: `ℓ = 6`, **51,468 steps**. -/
theorem cost_eqtIR_six (aB qB t : ℕ) : cost (eqtIR 6 aB qB) t = 51468 := by
  rw [cost_eqtIR 6 aB qB t (by norm_num)]
  norm_num

/-! ## Field and word helpers -/

theorem eqt_wK_one : wK 1 = 1 := rfl
theorem eqt_wK_zero : wK 0 = 0 := rfl

/-- `1 − α` on coordinates: coordinate 0 plus `1` (characteristic 2). -/
theorem eqt_one_sub (c₀ c₁ c₂ : BF64) : mkE (c₀ + 1) c₁ c₂ = 1 - mkE c₀ c₁ c₂ := by
  rw [CharTwo.sub_eq_add, ← mkE_one, mkE_add, add_comm (1 : BF64) c₀, zero_add, zero_add]

/-- The bit word: `(x >> v) & 1` is `1` or `0` with bit `v` of `x`. -/
theorem eqt_bit_word {x v : ℕ} (hx : x < 2 ^ 64) (hv : v < 64) :
    XOp.and.eval (XOp.shr.eval (toWord x) (toWord v)) 1 = toWord (if x.testBit v then 1 else 0) := by
  rw [shr_toWord hx hv, and_one_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hx), bit_eq]

/-- Three equal words, one `E` element. -/
theorem eqt_rdE_eq {M M' : Mem} {a b : ℕ} (h0 : rd M' a = rd M b) (h1 : rd M' (a + 1) = rd M (b + 1))
    (h2 : rd M' (a + 2) = rd M (b + 2)) : rdE M' a = rdE M b := by
  simp only [rdE, rdK, h0, h1, h2]

theorem eqt_rdE_decS {c a : ℕ} (s : St) (h : c < a ∨ a + 3 ≤ c) : rdE (decS c s).M a = rdE s.M a :=
  eqt_rdE_eq (rd_decS (by omega) s) (rd_decS (by omega) s) (rd_decS (by omega) s)

/-- A block keeps every cell it does not name as a destination. -/
theorem eqt_rd_blk {I : Array Word} {ps : List Prim} {s : St} {r : ℕ} (h : ∀ p ∈ ps, p.dst ≠ r) :
    rd (semXIR I (.blk ps) s).M r = rd s.M r := rd_runPrims_of_not_writes h s.M

/-- `mulE etA etA b` writes `mulE`'s scratch and the accumulator, nothing else. -/
theorem eqt_mulE_frame {I : Array Word} {b : ℕ} {s : St} {i : ℕ} (hi : i < 5 ∨ etS ≤ i) :
    rd (semXIR I (mulE etA etA b) s).M i = rd s.M i := by
  rw [mulE, sem_blk]
  refine rd_runPrims_of_not_writes (fun p hp => ?_) s.M
  have := mulEC_dst etA etA b p hp
  simp only [etA, etS] at this hi
  omega

/-! ## `E` loads and stores -/

/-- `M[d] := M[x]`, `M[p] := x + 1` (`M[p] = x`). -/
theorem eqtLd1_sem (I : Array Word) (s : St) (hM : Inv s.M) {d p x : ℕ} (hd : 4 ≤ d)
    (hdr : d < regs) (hp : 4 ≤ p) (hpr : p < regs) (hdp : d ≠ p) (hP : rd s.M p = toWord x)
    (hx2 : x < 2 ^ 64) :
    rd (semXIR I (eqtLd1 d p) s).M d = rd s.M x ∧
    rd (semXIR I (eqtLd1 d p) s).M p = toWord (x + 1) ∧
    (∀ i, i ≠ d → i ≠ p → rd (semXIR I (eqtLd1 d p) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtLd1 d p) s).M := by
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM hd hdr hP hx2
  have hp1 : rd (semXIR I (.load d p) s).M p = toWord x := (l2 p (Ne.symm hdp)).trans hP
  rw [eqtLd1, semXIR_seq]
  generalize semXIR I (.load d p) s = s1 at l1 l2 hM1 hp1
  have hs1 := hM1.1
  have h1 : rd s1.M cOne = 1 := hM1.2 0 (by decide)
  simp only [regs] at hs1 hpr
  refine ⟨?_, ?_, fun i i1 i2 => ?_, inv_sem I (P := .blk [.op .add p p cOne])
    (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact hp) hM1⟩
  · rw [sem_blk, rd_runPrims_of_not_writes (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact Ne.symm hdp), l1]
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by omega), hp1, h1, add_one_toWord]
  · rw [sem_blk, rd_runPrims_of_not_writes (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact Ne.symm i2), l2 i i1]

/-- **An `E` load**: `M[d … d+2] := M[x … x+2]` (`M[p] = x`, a heap address), `M[p] := x + 3`. -/
theorem eqtLdE_sem (I : Array Word) (s : St) (hM : Inv s.M) {d p x : ℕ} (hd : 4 ≤ d)
    (hdr : d + 3 ≤ regs) (hp : 4 ≤ p) (hpr : p < regs) (hdp : p < d ∨ d + 3 ≤ p)
    (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x + 3 < 2 ^ 64) :
    rdE (semXIR I (eqtLdE d p) s).M d = rdE s.M x ∧
    rd (semXIR I (eqtLdE d p) s).M p = toWord (x + 3) ∧
    (∀ i, (i < d ∨ d + 3 ≤ i) → i ≠ p → rd (semXIR I (eqtLdE d p) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtLdE d p) s).M := by
  simp only [regs] at hdr hpr hx
  rw [eqtLdE, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := eqtLd1_sem I s hM (d := d) (p := p) hd (by simp only [regs]; omega)
    hp (by simp only [regs]; omega) (by omega) hP (by omega)
  generalize semXIR I (eqtLd1 d p) s = s1 at a1 a2 a3 hM1
  rw [semXIR_seq]
  obtain ⟨b1, b2, b3, hM2⟩ := eqtLd1_sem I s1 hM1 (d := d + 1) (p := p) (by omega)
    (by simp only [regs]; omega) hp (by simp only [regs]; omega) (by omega) a2 (by omega)
  generalize semXIR I (eqtLd1 (d + 1) p) s1 = s2 at b1 b2 b3 hM2
  obtain ⟨c1, c2, c3, hM3⟩ := eqtLd1_sem I s2 hM2 (d := d + 2) (p := p) (x := x + 2) (by omega)
    (by simp only [regs]; omega) hp (by simp only [regs]; omega) (by omega) b2 (by omega)
  generalize semXIR I (eqtLd1 (d + 2) p) s2 = s3 at c1 c2 c3 hM3
  refine ⟨eqt_rdE_eq ?_ ?_ ?_, c2, fun i i1 i2 => ?_, hM3⟩
  · rw [c3 d (by omega) (by omega), b3 d (by omega) (by omega), a1]
  · rw [c3 (d + 1) (by omega) (by omega), b1, a3 (x + 1) (by omega) (by omega)]
  · rw [c1, b3 (x + 2) (by omega) (by omega), a3 (x + 2) (by omega) (by omega)]
  · rw [c3 i (by omega) i2, b3 i (by omega) i2, a3 i (by omega) i2]

/-- `M[x] := M[v]`, `M[p] := x + 1` (`M[p] = x`, a heap address). -/
theorem eqtSt1_sem (I : Array Word) (s : St) (hM : Inv s.M) {p v x : ℕ} (hp : 4 < p)
    (hpr : p < regs) (hv : v ≠ cTmp) (hP : rd s.M p = toWord x) (hx : regs ≤ x)
    (hx2 : x < 2 ^ 64) (hxs : x < s.M.size) :
    rd (semXIR I (eqtSt1 p v) s).M x = rd s.M v ∧
    rd (semXIR I (eqtSt1 p v) s).M p = toWord (x + 1) ∧
    (∀ i, i ≠ x → i ≠ cTmp → i ≠ p → rd (semXIR I (eqtSt1 p v) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtSt1 p v) s).M := by
  have hpT : p ≠ cTmp := by simp only [cTmp]; omega
  have hpx : p ≠ x := by simp only [regs] at hpr hx; omega
  obtain ⟨t1, t2, hM1⟩ := store_sem I s hM hpT hv hP hx hx2 hxs
  have hp1 : rd (semXIR I (.store p v) s).M p = toWord x := (t2 p hpx hpT).trans hP
  rw [eqtSt1, semXIR_seq]
  generalize semXIR I (.store p v) s = s1 at t1 t2 hM1 hp1
  have hs1 := hM1.1
  have h1 : rd s1.M cOne = 1 := hM1.2 0 (by decide)
  simp only [regs] at hs1 hpr
  refine ⟨?_, ?_, fun i i1 i2 i3 => ?_, inv_sem I (P := .blk [.op .add p p cOne])
    (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact Nat.le_of_lt hp) hM1⟩
  · rw [sem_blk, rd_runPrims_of_not_writes (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact hpx), t1]
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by omega), hp1, h1, add_one_toWord]
  · rw [sem_blk, rd_runPrims_of_not_writes (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact Ne.symm i3), t2 i i1 i2]

/-- **An `E` store**: `M[x … x+2] := M[v … v+2]` (`M[p] = x`, a heap address), `M[p] := x + 3`. -/
theorem eqtStE_sem (I : Array Word) (s : St) (hM : Inv s.M) {p v x : ℕ} (hp : 4 < p)
    (hpr : p < regs) (hv : 4 < v) (hvr : v + 3 ≤ regs) (hpv : p < v ∨ v + 3 ≤ p)
    (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x + 3 < 2 ^ 64) (hxs : x + 3 ≤ s.M.size) :
    rdE (semXIR I (eqtStE p v) s).M x = rdE s.M v ∧
    rd (semXIR I (eqtStE p v) s).M p = toWord (x + 3) ∧
    (∀ i, (i < x ∨ x + 3 ≤ i) → i ≠ cTmp → i ≠ p → rd (semXIR I (eqtStE p v) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtStE p v) s).M := by
  simp only [regs] at hpr hvr hx
  rw [eqtStE, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := eqtSt1_sem I s hM (p := p) (v := v) hp (by simp only [regs]; omega)
    (by simp only [cTmp]; omega) hP (by simp only [regs]; omega) (by omega) (by omega)
  have z1 := size_sem I (eqtSt1 p v) s
  generalize semXIR I (eqtSt1 p v) s = s1 at a1 a2 a3 hM1 z1
  rw [semXIR_seq]
  obtain ⟨b1, b2, b3, hM2⟩ := eqtSt1_sem I s1 hM1 (p := p) (v := v + 1) (x := x + 1) hp
    (by simp only [regs]; omega) (by simp only [cTmp]; omega) a2 (by simp only [regs]; omega)
    (by omega) (by omega)
  have z2 := size_sem I (eqtSt1 p (v + 1)) s1
  generalize semXIR I (eqtSt1 p (v + 1)) s1 = s2 at b1 b2 b3 hM2 z2
  obtain ⟨c1, c2, c3, hM3⟩ := eqtSt1_sem I s2 hM2 (p := p) (v := v + 2) (x := x + 2) hp
    (by simp only [regs]; omega) (by simp only [cTmp]; omega) b2 (by simp only [regs]; omega)
    (by omega) (by omega)
  generalize semXIR I (eqtSt1 p (v + 2)) s2 = s3 at c1 c2 c3 hM3
  refine ⟨eqt_rdE_eq ?_ ?_ ?_, c2, fun i i1 i2 i3 => ?_, hM3⟩
  · rw [c3 x (by omega) (by simp only [cTmp]; omega) (by omega),
      b3 x (by omega) (by simp only [cTmp]; omega) (by omega), a1]
  · rw [c3 (x + 1) (by omega) (by simp only [cTmp]; omega) (by omega), b1,
      a3 (v + 1) (by omega) (by simp only [cTmp]; omega) (by omega)]
  · rw [c1, b3 (v + 2) (by omega) (by simp only [cTmp]; omega) (by omega),
      a3 (v + 2) (by omega) (by simp only [cTmp]; omega) (by omega)]
  · rw [c3 i (by omega) i2 i3, b3 i (by omega) i2 i3, a3 i (by omega) i2 i3]

/-! ## One factor -/

/-- `1 − α_v`: `etO := 1 + etS`. -/
theorem eqtOm_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdE (semXIR I (.blk eqtOm) s).M etO = 1 - rdE s.M etS ∧
    (∀ i, (i < etO ∨ etO + 3 ≤ i) → rd (semXIR I (.blk eqtOm) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk eqtOm) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  refine ⟨?_, fun i hi => eqt_rd_blk (fun q hq => ?_),
    inv_sem I (by simp +decide [WF]) hM⟩
  · simp only [rdE, rdK, sem_blk, eqtOm, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, etO, etS]; omega)) only
      [rd_set_self, rd_set_ne]
    simp only [h1, eval_xor, eval_or, BitVec.or_self, wK_xor, eqt_wK_one]
    exact eqt_one_sub _ _ _
  · simp only [eqtOm, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [Prim.dst] <;> omega

/-- The bit block: `etBit := bit_v x`, `v += 1`. -/
theorem eqtBitPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {x v : ℕ} (hx : x < 2 ^ 64)
    (hv : v < 64) (hX : rd s.M etX = toWord x) (hV : rd s.M etV = toWord v) :
    rd (semXIR I (.blk eqtBitPs) s).M etBit = toWord (if x.testBit v then 1 else 0) ∧
    rd (semXIR I (.blk eqtBitPs) s).M etV = toWord (v + 1) ∧
    (∀ i, i ≠ etBit → i ≠ etV → rd (semXIR I (.blk eqtBitPs) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk eqtBitPs) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  refine ⟨?_, ?_, fun i i1 i2 => eqt_rd_blk (fun q hq => ?_),
    inv_sem I (by simp +decide [WF]) hM⟩
  · simp only [sem_blk, eqtBitPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, etBit, etV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hX, hV, h1, eqt_bit_word hx hv]
  · simp only [sem_blk, eqtBitPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, etBit, etV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hV, h1, add_one_toWord]
  · simp only [eqtBitPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [Prim.dst] <;> omega

/-- **One factor**: with `x` in `etX`, `v` in `etV` and `α_v` at `a = M[etAd]`,
`acc *= (bit_v x ? α_v : 1 − α_v)`; `v += 1`, `etAd += 3`; the cells outside the body's
registers are kept. -/
theorem eqtBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {x v a : ℕ} {S : Ext3}
    (hx : x < 2 ^ 64) (hv : v < 64) (ha : regs ≤ a) (ha2 : a + 3 < 2 ^ 64)
    (hX : rd s.M etX = toWord x) (hV : rd s.M etV = toWord v) (hA : rd s.M etAd = toWord a)
    (hS : rdE s.M a = S) :
    rdE (semXIR I eqtBody s).M etA = rdE s.M etA * (if x.testBit v then S else 1 - S) ∧
    rd (semXIR I eqtBody s).M etV = toWord (v + 1) ∧
    rd (semXIR I eqtBody s).M etAd = toWord (a + 3) ∧
    (∀ i, ((34 ≤ i ∧ i ≤ etX) ∨ etC1 ≤ i) → rd (semXIR I eqtBody s).M i = rd s.M i) ∧
    Inv (semXIR I eqtBody s).M := by
  have hs := hM.1
  simp only [regs] at hs ha
  -- `α_v`
  rw [eqtBody, semXIR_seq]
  obtain ⟨l1, l2, l3, hM1⟩ := eqtLdE_sem I s hM (d := etS) (p := etAd) (x := a) (by decide)
    (by decide) (by decide) (by decide) (by decide) hA (by simp only [regs]; omega) ha2
  generalize semXIR I (eqtLdE etS etAd) s = s1 at l1 l2 l3 hM1
  -- `1 − α_v`
  rw [semXIR_seq]
  obtain ⟨o1, o2, hM2⟩ := eqtOm_sem I s1 hM1
  generalize semXIR I (.blk eqtOm) s1 = s2 at o1 o2 hM2
  -- the bit, `v`
  rw [semXIR_seq]
  have x2 : rd s2.M etX = toWord x := by
    rw [o2 _ (by decide), l3 _ (by decide) (by decide), hX]
  have v2 : rd s2.M etV = toWord v := by
    rw [o2 _ (by decide), l3 _ (by decide) (by decide), hV]
  obtain ⟨b1, b2, b3, hM3⟩ := eqtBitPs_sem I s2 hM2 hx hv x2 v2
  generalize semXIR I (.blk eqtBitPs) s2 = s3 at b1 b2 b3 hM3
  -- the operands of the product and the kept cells
  have kS : rdE s3.M etS = S := by
    rw [← hS, ← l1]
    exact eqt_rdE_eq (by rw [b3 _ (by decide) (by decide), o2 _ (by decide)])
      (by rw [b3 _ (by decide) (by decide), o2 _ (by decide)])
      (by rw [b3 _ (by decide) (by decide), o2 _ (by decide)])
  have kO : rdE s3.M etO = 1 - S := by
    rw [← hS, ← l1, ← o1]
    exact eqt_rdE_eq (b3 _ (by decide) (by decide)) (b3 _ (by decide) (by decide))
      (b3 _ (by decide) (by decide))
  have kA : rdE s3.M etA = rdE s.M etA := eqt_rdE_eq
    (by rw [b3 _ (by decide) (by decide), o2 _ (by decide), l3 _ (by decide) (by decide)])
    (by rw [b3 _ (by decide) (by decide), o2 _ (by decide), l3 _ (by decide) (by decide)])
    (by rw [b3 _ (by decide) (by decide), o2 _ (by decide), l3 _ (by decide) (by decide)])
  have keep3 : ∀ i, ((34 ≤ i ∧ i ≤ etX) ∨ etC1 ≤ i) → rd s3.M i = rd s.M i := fun i hi => by
    simp only [etX, etC1] at hi
    rw [b3 i (by simp only [etBit]; omega) (by simp only [etV]; omega),
      o2 i (by simp only [etO]; omega), l3 i (by simp only [etS]; omega) (by simp only [etAd]; omega)]
  have hb0 : (toWord (if x.testBit v then 1 else 0) = 0) ↔ ¬ x.testBit v := by
    by_cases h : x.testBit v
    · rw [ite_eq_left h]; exact ⟨fun e => absurd e (by decide), fun h' => absurd h h'⟩
    · rw [ite_eq_right h]; exact ⟨fun _ => h, fun _ => rfl⟩
  -- the product
  rw [semXIR_ite, b1]
  by_cases hbit : x.testBit v
  · rw [ite_eq_right (by rw [hb0]; exact not_not_intro hbit), ite_eq_left hbit]
    refine ⟨?_, ?_, ?_, fun i hi => ?_, inv_sem I (wf_mulE etA etA etS (by decide)) hM3⟩
    · rw [mulE_sem hM3 (by decide) (by decide) (by decide) (by decide), kA, kS]
    · rw [eqt_mulE_frame (by decide), b2]
    · rw [eqt_mulE_frame (by decide), b3 _ (by decide) (by decide), o2 _ (by decide), l2]
    · rw [eqt_mulE_frame (.inr (by simp only [etS, etX, etC1] at hi ⊢; omega)), keep3 i hi]
  · rw [ite_eq_left (by rw [hb0]; exact hbit), ite_eq_right hbit]
    refine ⟨?_, ?_, ?_, fun i hi => ?_, inv_sem I (wf_mulE etA etA etO (by decide)) hM3⟩
    · rw [mulE_sem hM3 (by decide) (by decide) (by decide) (by decide), kA, kO]
    · rw [eqt_mulE_frame (by decide), b2]
    · rw [eqt_mulE_frame (by decide), b3 _ (by decide) (by decide), o2 _ (by decide), l2]
    · rw [eqt_mulE_frame (.inr (by simp only [etS, etX, etC1] at hi ⊢; omega)), keep3 i hi]

/-! ## One entry -/

theorem eqtPre_sem (I : Array Word) (s : St) (hM : Inv s.M) (ℓ aB : ℕ) :
    rdE (semXIR I (.blk (eqtPre ℓ aB)) s).M etA = 1 ∧
    rd (semXIR I (.blk (eqtPre ℓ aB)) s).M etV = toWord 0 ∧
    rd (semXIR I (.blk (eqtPre ℓ aB)) s).M etAd = toWord (aB + 3 * 0) ∧
    rd (semXIR I (.blk (eqtPre ℓ aB)) s).M etN2 = toWord ℓ ∧
    (∀ i, (i < etA ∨ etA + 3 ≤ i) → i ≠ etV → i ≠ etAd → i ≠ etN2 →
      rd (semXIR I (.blk (eqtPre ℓ aB)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (eqtPre ℓ aB)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 => eqt_rd_blk (fun q hq => by
      simp only [eqtPre, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;> omega),
    inv_sem I (by simp +decide [eqtPre, WF, Prim.dst, etA, etV, etAd, etN2]) hM⟩
  · simp only [rdE, rdK, sem_blk, eqtPre, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, etA, etV, etAd, etN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [eqt_wK_one, eqt_wK_zero, mkE_one]
  all_goals simp only [sem_blk, eqtPre, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, etA, etV, etAd, etN2]; omega))
    only [rd_set_self, rd_set_ne] <;> rfl

theorem eqtAd_sem (I : Array Word) (s : St) (hM : Inv s.M) {x qB : ℕ}
    (hX : rd s.M etX = toWord x) :
    rd (semXIR I (.blk (eqtAd qB)) s).M etAd = toWord (qB + 3 * x) ∧
    (∀ i, i ≠ etAd → i ≠ etK → rd (semXIR I (.blk (eqtAd qB)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (eqtAd qB)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun i h1 h2 => eqt_rd_blk (fun q hq => by
      simp only [eqtAd, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;> omega),
    inv_sem I (by simp +decide [eqtAd, WF, Prim.dst, etAd, etK]) hM⟩
  simp only [sem_blk, eqtAd, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, etAd, etK]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hX, add_toWord, add_toWord, add_toWord]
  congr 1
  ring

/-- **One entry**: with `x` in `etX` and the challenges `S v` at `aB + 3v`, `eqtEnt` stores
`eqBits S ℓ x` at `qB + 3x`; `x += 1`; the cells outside the entry and the program's registers,
and the entry loop's registers, are kept. -/
theorem eqtEnt_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ aB qB x : ℕ} {S : ℕ → Ext3}
    (hℓ : ℓ < 64) (hx : x < 2 ^ 64) (haB : regs ≤ aB) (haB2 : aB + 3 * ℓ < 2 ^ 64)
    (hqB : regs ≤ qB) (hqB2 : qB + 3 * x + 3 < 2 ^ 64) (hsz : qB + 3 * x + 3 ≤ s.M.size)
    (hX : rd s.M etX = toWord x) (hS : ∀ v < ℓ, rdE s.M (aB + 3 * v) = S v) :
    rdE (semXIR I (eqtEnt ℓ aB qB) s).M (qB + 3 * x) = eqBits S ℓ x ∧
    rd (semXIR I (eqtEnt ℓ aB qB) s).M etX = toWord (x + 1) ∧
    (∀ i, (((34 ≤ i ∧ i < etX) ∨ etN2 < i) ∧ (i < qB + 3 * x ∨ qB + 3 * x + 3 ≤ i) ∨ i = etC1 ∨
      i = etN1) → rd (semXIR I (eqtEnt ℓ aB qB) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtEnt ℓ aB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs haB hqB
  obtain ⟨p1, p2, p3, p4, p5, hM1⟩ := eqtPre_sem I s hM ℓ aB
  have z1 := size_sem I (.blk (eqtPre ℓ aB)) s
  rw [eqtEnt, semXIR_seq]
  generalize semXIR I (.blk (eqtPre ℓ aB)) s = s1 at p1 p2 p3 p4 p5 hM1 z1
  -- the factor loop
  rw [semXIR_seq]
  let Q : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rdE s'.M etA = ∏ v ∈ range j, (if x.testBit v then S v else 1 - S v) ∧
    rd s'.M etV = toWord j ∧ rd s'.M etAd = toWord (aB + 3 * j) ∧
    ∀ i, ((34 ≤ i ∧ i ≤ etX) ∨ i = etC1 ∨ i = etN1 ∨ etN2 < i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ etC2 → i ≠ cTmp → rd (entryK etC2 etN2 (toWord ℓ) s1.M) i = rd s1.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have q0 : Q 0 ⟨entryK etC2 etN2 (toWord ℓ) s1.M, s1.o⟩ := by
    refine ⟨inv_entryK hM1 (by decide), by simp only [size_entryK, z1], ?_, ?_, ?_,
      fun i hi => ?_⟩
    · dsimp only
      rw [prod_range_zero, ← p1]
      exact eqt_rdE_eq (hE _ (by decide) (by decide)) (hE _ (by decide) (by decide))
        (hE _ (by decide) (by decide))
    · dsimp only; rw [hE _ (by decide) (by decide), p2]
    · dsimp only; rw [hE _ (by decide) (by decide), p3]
    · dsimp only
      simp only [etX, etC1, etN1, etN2] at hi
      rw [hE _ (by simp only [etC2]; omega) (by simp only [cTmp]; omega),
        p5 i (by simp only [etA]; omega) (by simp only [etV]; omega) (by simp only [etAd]; omega)
          (by simp only [etN2]; omega)]
  have qstep : ∀ j s', j < ℓ → Q j s' → Q (j + 1) (decS etC2 (semXIR I eqtBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hS' : rdE s'.M (aB + 3 * j) = S j := by
      rw [← hS j hj]
      exact eqt_rdE_eq (i6 _ (.inr (.inr (.inr (by simp only [etN2]; omega)))))
        (i6 _ (.inr (.inr (.inr (by simp only [etN2]; omega)))))
        (i6 _ (.inr (.inr (.inr (by simp only [etN2]; omega)))))
    obtain ⟨e1, e2, e3, e4, e5⟩ := eqtBody_sem I s' i1 (x := x) (v := j) (a := aB + 3 * j) hx
      (by omega) (by simp only [regs]; omega) (by omega) ((i6 _ (.inl (by decide))).trans hX)
      i4 i5 hS'
    have hd : ∀ i, i ≠ etC2 → rd (decS etC2 (semXIR I eqtBody s')).M i =
        rd (semXIR I eqtBody s').M i := fun i h => rd_decS (Ne.symm h) _
    refine ⟨inv_decS e5 (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [eqt_rdE_decS _ (by decide), e1, i3, prod_range_succ]
    · rw [hd _ (by decide), e2]
    · rw [hd _ (by decide), e3, show aB + 3 * j + 3 = aB + 3 * (j + 1) by ring]
    · have hi' : i ≠ etC2 := by simp only [etX, etC1, etN1, etN2, etC2] at hi ⊢; omega
      rw [hd _ hi', e4 i (by simp only [etX, etC1, etN1, etN2] at hi ⊢; omega), i6 i hi]
  have hq := loopK_run I eqtBody Q s1 hM1 (c := etC2) (n := etN2) (K := ℓ) (by decide)
    (by decide) (by decide) p4 (by omega) q0 qstep
  generalize semXIR I (.loopK etC2 etN2 (toWord ℓ) eqtBody) s1 = s2 at hq
  obtain ⟨j1, j2, j3, -, -, j6⟩ := hq
  have hX2 : rd s2.M etX = toWord x := (j6 _ (.inl (by decide))).trans hX
  -- the address, the store
  rw [semXIR_seq]
  obtain ⟨a1, a2, hM3⟩ := eqtAd_sem (qB := qB) I s2 j1 hX2
  have z3 := size_sem I (.blk (eqtAd qB)) s2
  generalize semXIR I (.blk (eqtAd qB)) s2 = s3 at a1 a2 hM3 z3
  rw [j2] at z3
  have hk3 : rdE s3.M etA = eqBits S ℓ x := by
    rw [show eqBits S ℓ x = ∏ v ∈ range ℓ, (if x.testBit v then S v else 1 - S v) from rfl, ← j3]
    exact eqt_rdE_eq (a2 _ (by decide) (by decide)) (a2 _ (by decide) (by decide))
      (a2 _ (by decide) (by decide))
  rw [semXIR_seq]
  obtain ⟨c1, c2, c3, hM4⟩ := eqtStE_sem I s3 hM3 (p := etAd) (v := etA) (x := qB + 3 * x)
    (by decide) (by decide) (by decide) (by decide) (by decide) a1 (by simp only [regs]; omega)
    (by omega) (by omega)
  generalize semXIR I (eqtStE etAd etA) s3 = s4 at c1 c2 c3 hM4
  have x4 : rd s4.M etX = toWord x := by
    rw [c3 _ (by simp only [etX]; omega) (by decide) (by decide), a2 _ (by decide) (by decide), hX2]
  -- `x += 1`
  have hs4 := hM4.1
  simp only [regs] at hs4
  have f5 : ∀ i, i ≠ etX → rd (semXIR I (.blk [.op .add etX etX cOne]) s4).M i = rd s4.M i :=
    fun i hi => eqt_rd_blk (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact Ne.symm hi)
  have g5 : rd (semXIR I (.blk [.op .add etX etX cOne]) s4).M etX = toWord (x + 1) := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [etX]; omega), x4, show rd s4.M cOne = 1 from hM4.2 0 (by decide),
      add_one_toWord]
  refine ⟨?_, g5, fun i hi => ?_, inv_sem I (P := .blk [.op .add etX etX cOne])
    (by simp +decide [WF]) hM4⟩
  · rw [← hk3, ← c1]
    exact eqt_rdE_eq (f5 _ (by simp only [etX]; omega)) (f5 _ (by simp only [etX]; omega))
      (f5 _ (by simp only [etX]; omega))
  · have hne : i ≠ etX ∧ (i < qB + 3 * x ∨ qB + 3 * x + 3 ≤ i) ∧ i ≠ cTmp ∧ i ≠ etAd ∧ i ≠ etK ∧
        ((34 ≤ i ∧ i ≤ etX) ∨ i = etC1 ∨ i = etN1 ∨ etN2 < i) := by
      simp only [etX, etAd, etK, cTmp, etC1, etN1, etN2] at hi ⊢; omega
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
    rw [f5 _ h1, c3 _ h2 h3 h4, a2 _ h4 h5, j6 i h6]

/-! ## The table -/

/-- **The `eq` table** on the machine, for any challenges `S v` (`E`, `rdE`) at `aB + 3v`,
`v < ℓ`: `eqtIR ℓ aB qB` leaves `eqBits S ℓ x` at `qB + 3x` for every `x < 2^ℓ`, and keeps every
cell outside `[qB, qB + 3·2^ℓ)` but its own registers (`cTmp`, `5 … 33`, `206 … 214`). -/
theorem eqtIR_sem_of (I : Array Word) (s : St) (hM : Inv s.M) {ℓ aB qB : ℕ} {S : ℕ → Ext3}
    (hℓ : ℓ < 64) (haB : regs ≤ aB) (haB2 : aB + 3 * ℓ < 2 ^ 64) (hqB : regs ≤ qB)
    (hqB2 : qB + 3 * 2 ^ ℓ < 2 ^ 64) (hsz : qB + 3 * 2 ^ ℓ ≤ s.M.size)
    (hdisj : aB + 3 * ℓ ≤ qB ∨ qB + 3 * 2 ^ ℓ ≤ aB)
    (hS : ∀ v < ℓ, rdE s.M (aB + 3 * v) = S v) :
    (∀ x < 2 ^ ℓ, rdE (semXIR I (eqtIR ℓ aB qB) s).M (qB + 3 * x) = eqBits S ℓ x) ∧
    (∀ i, ((34 ≤ i ∧ i < etX) ∨ etN2 < i) → (i < qB ∨ qB + 3 * 2 ^ ℓ ≤ i) →
      rd (semXIR I (eqtIR ℓ aB qB) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtIR ℓ aB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs haB hqB
  have hP : 2 ^ ℓ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hℓ
  have r0 : rd (semXIR I (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))]) s).M etX = toWord 0 ∧
      rd (semXIR I (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))]) s).M etN1 =
        toWord (2 ^ ℓ) := by
    simp only [sem_blk, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩
    · simp (disch := first | decide | (simp only [size_set, etX, etN1]; omega)) only
        [rd_set_self, rd_set_ne]
      rfl
    · simp (disch := first | decide | (simp only [size_set, etX, etN1]; omega)) only [rd_set_self]
  have k0 : ∀ i, i ≠ etX → i ≠ etN1 →
      rd (semXIR I (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))]) s).M i = rd s.M i :=
    fun i h1 h2 => eqt_rd_blk (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> simp only [Prim.dst] <;> omega)
  have hM0 := inv_sem I (P := .blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))])
    (by simp +decide [WF, Prim.dst, etX, etN1]) hM
  have z0 := size_sem I (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))]) s
  rw [eqtIR, semXIR_seq]
  generalize semXIR I (.blk [.const etX 0, .const etN1 (toWord (2 ^ ℓ))]) s = s0 at r0 k0 hM0 z0
  obtain ⟨x0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M etX = toWord j ∧
    (∀ x < j, rdE s'.M (qB + 3 * x) = eqBits S ℓ x) ∧
    ∀ i, ((34 ≤ i ∧ i < etX) ∨ etN2 < i) → (i < qB ∨ qB + 3 * j ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ etC1 → i ≠ cTmp →
      rd (entryK etC1 etN1 (toWord (2 ^ ℓ)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK etC1 etN1 (toWord (2 ^ ℓ)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun x hx => absurd hx (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), x0]
    · dsimp only
      simp only [etX, etN2] at hi
      rw [hE _ (by simp only [etC1]; omega) (by simp only [cTmp]; omega),
        k0 _ (by simp only [etX]; omega) (by simp only [etN1]; omega)]
  have step : ∀ j s', j < 2 ^ ℓ → P j s' →
      P (j + 1) (decS etC1 (semXIR I (eqtEnt ℓ aB qB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hS' : ∀ v < ℓ, rdE s'.M (aB + 3 * v) = S v := fun v hv => by
      rw [← hS v hv]
      exact eqt_rdE_eq (i5 _ (.inr (by simp only [etN2]; omega)) (by omega))
        (i5 _ (.inr (by simp only [etN2]; omega)) (by omega))
        (i5 _ (.inr (by simp only [etN2]; omega)) (by omega))
    obtain ⟨e1, e2, e3, e4⟩ := eqtEnt_sem I s' i1 (ℓ := ℓ) (aB := aB) (qB := qB) (x := j) (S := S)
      hℓ (by omega) (by simp only [regs]; omega) haB2 (by simp only [regs]; omega) (by omega)
      (by rw [i2]; omega) i3 hS'
    have hd : ∀ i, i ≠ etC1 → rd (decS etC1 (semXIR I (eqtEnt ℓ aB qB) s')).M i =
        rd (semXIR I (eqtEnt ℓ aB qB) s').M i := fun i h => rd_decS (Ne.symm h) _
    refine ⟨inv_decS e4 (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), e2],
      fun x hx => ?_, fun i hi hi2 => ?_⟩
    · rw [eqt_rdE_decS _ (by simp only [etC1]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | rfl
      · rw [← i4 x h]
        exact eqt_rdE_eq (e3 _ (.inl ⟨.inr (by simp only [etN2]; omega), by omega⟩))
          (e3 _ (.inl ⟨.inr (by simp only [etN2]; omega), by omega⟩))
          (e3 _ (.inl ⟨.inr (by simp only [etN2]; omega), by omega⟩))
      · exact e1
    · rw [hd _ (by simp only [etC1, etX, etN2] at hi ⊢; omega), e3 _ (.inl ⟨hi, by omega⟩),
        i5 i hi (by omega)]
  have := loopK_run I (eqtEnt ℓ aB qB) P s0 hM0 (c := etC1) (n := etN1) (K := 2 ^ ℓ) (by decide)
    (by decide) (by decide) n0 hP p0 step
  exact ⟨this.2.2.2.1, fun i hi hi2 => this.2.2.2.2 i hi hi2, this.1⟩

/-- **The `eq` table of the challenges on the heap**: from `α_v = rdE s.M (aB + 3v)`, `v < ℓ`
(three words each), `eqtIR ℓ aB qB` leaves `E[x] = eqBits α ℓ x = ∏_{v<ℓ} (bit_v x ? α_v : 1 − α_v)`
at `qB + 3x` for every `x < 2^ℓ` (three words, `rdE`); the heap outside `[qB, qB + 3·2^ℓ)` and the
registers outside `eqtIR`'s (`cTmp`, `5 … 33`, `206 … 214`) are kept; `Inv` holds. -/
theorem eqtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ aB qB : ℕ}
    (hℓ : ℓ < 64) (haB : regs ≤ aB) (haB2 : aB + 3 * ℓ < 2 ^ 64) (hqB : regs ≤ qB)
    (hqB2 : qB + 3 * 2 ^ ℓ < 2 ^ 64) (hsz : qB + 3 * 2 ^ ℓ ≤ s.M.size)
    (hdisj : aB + 3 * ℓ ≤ qB ∨ qB + 3 * 2 ^ ℓ ≤ aB) :
    (∀ x < 2 ^ ℓ, rdE (semXIR I (eqtIR ℓ aB qB) s).M (qB + 3 * x) =
      eqBits (fun v => rdE s.M (aB + 3 * v)) ℓ x) ∧
    (∀ i, ((34 ≤ i ∧ i < etX) ∨ etN2 < i) → (i < qB ∨ qB + 3 * 2 ^ ℓ ≤ i) →
      rd (semXIR I (eqtIR ℓ aB qB) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtIR ℓ aB qB) s).M :=
  eqtIR_sem_of I s hM hℓ haB haB2 hqB hqB2 hsz hdisj fun _ _ => rfl

/-- **The lvm instance** (`ℓ = 6`): with the fold challenges `α_v = rdE s.M (aB + 3v)`, `v < 6`,
`eqtIR 6 aB qB` leaves `eqA α l` at `qB + 3l` for every lane `l < 64`; the heap outside
`[qB, qB + 192)` is kept. -/
theorem eqtIR_eqA (I : Array Word) (s : St) (hM : Inv s.M) {aB qB : ℕ} (haB : regs ≤ aB)
    (haB2 : aB + 18 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (hsz : qB + 192 ≤ s.M.size) (hdisj : aB + 18 ≤ qB ∨ qB + 192 ≤ aB) :
    (∀ l < 64, rdE (semXIR I (eqtIR 6 aB qB) s).M (qB + 3 * l) =
      eqA (fun v => rdE s.M (aB + 3 * v)) l) ∧
    (∀ i, regs ≤ i → (i < qB ∨ qB + 192 ≤ i) → rd (semXIR I (eqtIR 6 aB qB) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtIR 6 aB qB) s).M := by
  obtain ⟨h1, h2, h3⟩ := eqtIR_sem I s hM (ℓ := 6) (aB := aB) (qB := qB) (by norm_num) haB
    (by omega) hqB (by omega) (by omega) (by omega)
  exact ⟨fun l hl => h1 l (by omega), fun i hi hi2 =>
    h2 i (.inr (lt_of_lt_of_le (by decide) hi)) (by omega), h3⟩

/-! ## Controls -/

/-- **Bit order control**: `eqBits` weighs bit `v` of the entry by `α_v`, so entry `1` of a
two-variable table is `α₀ (1 − α₁)` and entry `2` is `(1 − α₀) α₁`; the table is not symmetric in
the challenges. -/
theorem eqt_bits_ctl (S : ℕ → Ext3) :
    eqBits S 2 1 = S 0 * (1 - S 1) ∧ eqBits S 2 2 = (1 - S 0) * S 1 := by
  have b1 : Nat.testBit 1 0 = true := rfl
  have b2 : Nat.testBit 1 1 = false := rfl
  have b3 : Nat.testBit 2 0 = false := rfl
  have b4 : Nat.testBit 2 1 = true := rfl
  constructor <;> simp [eqBits, bitSel, prod_range_succ, b1, b2, b3, b4]

end Lvm.X
