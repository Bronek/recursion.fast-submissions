-- new for lvm (WP-12b): `Q_sig`'s `BITS` rows (WP-12's `SigBits`) as six `BITS` tables of the lvm
-- M3 instance, and `SigBitsOk`: the `SigBits` hypothesis of `qsig_sound` from the bus (WP-9b).
-- Searched for reuse: none of FR/leanerVM/leanVM has a bus-read bit table (see `LvmBitsTab`).
import LvmBitsTab
import LvmQSigDefs

/-!
# `SigBitsOk`: `Q_sig`'s `BITS` outputs from the tables

**The tables** (`sigSpecs I o bpl`, one `BSpec` per output class; `bpl k` places class `k`'s
committed columns):

| k | class | rows (`2^τ`) | word cell of row `x` | outputs, cells |
|---|---|---|---|---|
| 0 | `idx` | 1 (1) | `σ'.idx` = `I.sg` | `shl 8`, `bit 0..15`, `shr 16` at `I.bi + j` |
| 1 | `md` | 4 (4) | `I.md + x` | `bit 0..63` at `I.bd + 64x + j` |
| 2 | `cs` | 1 (1) | none (free word) | `bit 0..9` at `I.bc + j` |
| 3 | step inputs | 1,596 (2^11) | `xin I o i s l`, `x = 4(3i+s)+l` | `shl 24`, `shr 40` at `I.bx + 2x + j` |
| 4 | byte shifts | 672 (2^10) | chain ends 532, path halves 128, `h'`, `c_L'`, `leafStmt` 4 each | `shl 8`, `shr 56` at `I.be`/`I.bp`/`I.bh`/`I.bcl`/`I.bls` `+ 2x' + j` |
| 5 | `n'` | 1 (1) | `I.hd + 13` | `shl 8`, `shr 56`, `bit 0..I.ln`, `shr (I.ln+1)`, `shl (64-I.ln)` at `I.bn + j` |

2,275 real rows, 3,079 table rows; Q_link's position fields (A20, `BOut.fld`) are further `BSpec`s
of QL's.

**`SigBitsOk`** (the hypothesis `NodeSound` hands to `qsig_sound`): `SigBits I o` holds for the
interpreter's `K` memory on the inputs read off the stack. **`sigBitsOk`** proves it from WP-9b's
`AuxHyps` (`loopir_sound`'s hypotheses), the six tables being auxiliary tables of the instance
(`SigTabsIn`), and their cells lying below `Q.cells .K` (`SigCellsLt`).
-/

set_option autoImplicit false

namespace Lvm.SigBits

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig

/-! ## The six classes -/

section Specs

variable (I : SigIn) (o : SigOut) (pl : Nat → Bool × Nat)

/-- `σ'.idx`: its low byte shift, its 16 bits, its high part. -/
def sIdx : BSpec :=
  ⟨0, 1, .shl 8 :: ((List.range 16).map .bit ++ [.shr 16]), true, fun _ => I.sg,
    fun j _ => I.bi + j, pl⟩

/-- The message digest's 256 bits. -/
def sMd : BSpec :=
  ⟨2, 4, (List.range 64).map .bit, true, fun x => I.md + x, fun j x => I.bd + 64 * x + j, pl⟩

/-- The checksum's ten bits, of a free word. -/
def sCs : BSpec := ⟨0, 1, (List.range 10).map .bit, false, fun _ => 0, fun j _ => I.bc + j, pl⟩

/-- The chain step inputs (11-byte prefix): `shl 24`, `shr 40`. -/
def s24 : BSpec :=
  ⟨11, 1596, [.shl 24, .shr 40], true, fun x => xin I o (x / 12) (x / 4 % 3) (x % 4),
    fun j x => I.bx + 2 * x + j, pl⟩

/-- The one-byte shifts: chain ends, path halves, `h'`, `c_L'`, `leafStmt` lanes. -/
def s8 : BSpec :=
  ⟨10, 672, [.shl 8, .shr 56], true,
    fun x => if x < 532 then endc o (x / 4) (x % 4)
      else if x < 660 then (o.pa.cell (4 + 4 * ((x - 532) / 4 % 2) + (x - 532) % 4) ((x - 532) / 8)).n
      else if x < 664 then I.hd + 14 + (x - 660)
      else if x < 668 then I.hd + 5 + (x - 664) else I.yls + (x - 668),
    fun j x => if x < 532 then I.be + 2 * x + j
      else if x < 660 then I.bp + 2 * (x - 532) + j
      else if x < 664 then I.bh + 2 * (x - 660) + j
      else if x < 668 then I.bcl + 2 * (x - 664) + j else I.bls + 2 * (x - 668) + j, pl⟩

/-- `n'`: its byte shifts, its low `I.ln + 1` bits, its range parts. -/
def sN : BSpec :=
  ⟨0, 1, .shl 8 :: .shr 56 :: ((List.range (I.ln + 1)).map .bit ++ [.shr (I.ln + 1), .shl (64 - I.ln)]),
    true, fun _ => I.hd + 13, fun j _ => I.bn + j, pl⟩

/-- **`Q_sig`'s `BITS` tables**, class `k` placed by `bpl k`. -/
def sigSpecs (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  [sIdx I (bpl 0), sMd I (bpl 1), sCs I (bpl 2), s24 I o (bpl 3), s8 I o (bpl 4), sN I (bpl 5)]

end Specs

/-- The six tables are auxiliary tables of the instance. -/
def SigTabsIn (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (aux : List Tab) : Prop :=
  ∀ S ∈ sigSpecs I o bpl, S.tab ∈ aux

/-- The cells the six tables name at their real rows are cells of `Q`. -/
def SigCellsLt (Q : Program) (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) : Prop :=
  ∀ S ∈ sigSpecs I o bpl, ∀ x < S.n,
    (S.rd = true → S.wc x < Q.cells .K) ∧ ∀ j < S.outs.length, S.oc j x < Q.cells .K

theorem fixOk_sig (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) :
    FixOk ((sigSpecs I o bpl).map BSpec.tab) := BSpec.fixOk_tabs _

/-! ## `SigBitsOk` -/

section Ok

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **`SigBitsOk`**: `Q_sig`'s `BITS` outputs hold in the interpreter's memory on the inputs read
off the stack `q` (the `hbits` of `qsig_sound`, with `M := Q.interpMem (inKOf q) (inEOf q)`). -/
def SigBitsOk (q : Column L.μ) (I : SigIn) (o : SigOut) : Prop :=
  SigBits I o (memK Q pl groups arrs aux L hτ q)

/-- One output of a read word (`out_sound` at a row and an output, with the cells named). -/
theorem out1_at (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) (hn : S.n ≤ 2 ^ S.τ) (hrd : S.rd = true) (x j : Nat) (hx : x < S.n)
    (hj : j < S.outs.length) (hc : (S.rd = true → S.wc x < Q.cells .K) ∧
      ∀ j < S.outs.length, S.oc j x < Q.cells .K)
    {A B : Nat} {b : BOut} (hA : S.wc x = A) (hB : S.oc j x = B) (hb : S.out j = b) (hv : b.Valid) :
    Out1 (memK Q pl groups arrs aux L hτ q) A b B := by
  obtain ⟨w, h1, h2⟩ := out_sound Q pl groups arrs aux L hτ q H S hS hx hn hc.1 hc.2
  have := h2 j hj (hb ▸ hv)
  rw [hA, hB, hb] at *
  unfold Out1; rw [this, h1 hrd]

theorem getD_idx {z : Nat} (hz : z < 16) :
    (BOut.shl 8 :: ((List.range 16).map BOut.bit ++ [BOut.shr 16])).getD (1 + z) (.bit 0) = .bit z := by
  rw [show 1 + z = z + 1 by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : z < ((List.range 16).map BOut.bit).length), hz]

theorem getD_n {ln z : Nat} (hz : z ≤ ln) :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (2 + z) (.bit 0) = .bit z := by
  rw [show 2 + z = z + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega : z < ((List.range (ln + 1)).map BOut.bit).length),
    show z < ln + 1 by omega]

theorem getD_n_top {ln : Nat} :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (ln + 3) (.bit 0) = .shr (ln + 1) := by
  rw [show ln + 3 = (ln + 1) + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD]

theorem getD_n_low {ln : Nat} :
    (BOut.shl 8 :: BOut.shr 56 :: ((List.range (ln + 1)).map BOut.bit ++
      [BOut.shr (ln + 1), BOut.shl (64 - ln)])).getD (ln + 4) (.bit 0) = .shl (64 - ln) := by
  rw [show ln + 4 = ((ln + 1) + 1) + 1 + 1 by omega]
  simp [List.getD_eq_getElem?_getD]

theorem getD_bit {n z : Nat} (hz : z < n) : ((List.range n).map BOut.bit).getD z (.bit 0) = .bit z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hz]; rfl

/-- **`SigBitsOk` from the bus**: the six `BITS` tables in the instance, their cells inside `Q`,
and `loopir_sound`'s hypotheses (`AuxHyps`) give `Q_sig`'s `BITS` outputs. -/
theorem sigBitsOk (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (I : SigIn) (o : SigOut)
    (bpl : Nat → Nat → Bool × Nat) (hT : SigTabsIn I o bpl aux) (hC : SigCellsLt Q I o bpl)
    (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) :
    SigBitsOk Q pl groups arrs aux L hτ q I o := by
  have mem := fun S (hS : S ∈ sigSpecs I o bpl) => And.intro (hT S hS) (hC S hS)
  obtain ⟨tI, cI⟩ := mem (sIdx I (bpl 0)) (by simp [sigSpecs])
  obtain ⟨tM, cM⟩ := mem (sMd I (bpl 1)) (by simp [sigSpecs])
  obtain ⟨tC, cC⟩ := mem (sCs I (bpl 2)) (by simp [sigSpecs])
  obtain ⟨t24, c24⟩ := mem (s24 I o (bpl 3)) (by simp [sigSpecs])
  obtain ⟨t8, c8⟩ := mem (s8 I o (bpl 4)) (by simp [sigSpecs])
  obtain ⟨tN, cN⟩ := mem (sN I (bpl 5)) (by simp [sigSpecs])
  have o1 := out1_at Q pl groups arrs aux L hτ q H
  have nI : (sIdx I (bpl 0)).n ≤ 2 ^ (sIdx I (bpl 0)).τ := by simp [sIdx]
  have nM : (sMd I (bpl 1)).n ≤ 2 ^ (sMd I (bpl 1)).τ := by simp [sMd]
  have n24 : (s24 I o (bpl 3)).n ≤ 2 ^ (s24 I o (bpl 3)).τ := by simp only [s24]; norm_num
  have n8 : (s8 I o (bpl 4)).n ≤ 2 ^ (s8 I o (bpl 4)).τ := by simp only [s8]; norm_num
  have nN : (sN I (bpl 5)).n ≤ 2 ^ (sN I (bpl 5)).τ := by simp [sN]
  have x0 : ∀ {S : BSpec}, S.n = 1 → 0 < S.n := fun h => by omega
  refine ⟨?_, fun z hz => ?_, ?_, fun r hr => ?_, ?_, fun i hi s hs l hl => ⟨?_, ?_⟩,
    fun i hi l hl => ⟨?_, ?_⟩, fun t ht u hu l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩, ?_, ?_,
    fun z hz => ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩⟩
  -- idx: `shl 8`, bits, `shr 16`
  · exact o1 _ tI nI rfl 0 0 (x0 rfl) (by simp [sIdx]) (cI 0 (x0 rfl)) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tI nI rfl 0 (1 + z) (x0 rfl) (by simp [sIdx] <;> omega) (cI 0 (x0 rfl)) rfl
      (by simp [sIdx] <;> omega) (getD_idx hz) (show z < 64 by omega)
  · exact o1 _ tI nI rfl 0 17 (x0 rfl) (by simp [sIdx]) (cI 0 (x0 rfl)) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  -- md: 256 bits
  · exact o1 _ tM nM rfl (r / 64) (r % 64) (by simp [sMd] <;> omega) (by simp [sMd] <;> omega)
      (cM (r / 64) (by simp [sMd] <;> omega)) rfl (by simp only [sMd] <;> omega)
      (getD_bit (Nat.mod_lt _ (by norm_num))) (Nat.mod_lt _ (by norm_num))
  -- cs: ten bits of a free word
  · obtain ⟨w, -, h2⟩ := out_sound Q pl groups arrs aux L hτ q H _ tC (x := 0) (x0 rfl)
      (by simp [sCs]) (cC 0 (x0 rfl)).1 (cC 0 (x0 rfl)).2
    refine ⟨w.val, fun k hk => ?_⟩
    have hb : (sCs I (bpl 2)).out k = .bit k := getD_bit hk
    have := h2 k (by simp [sCs, hk]) (by rw [hb]; show k < 64; omega)
    rw [hb] at this
    exact this
  -- step inputs: `shl 24`, `shr 40`
  · exact o1 _ t24 n24 rfl (4 * (3 * i + s) + l) 0 (by simp only [s24] <;> omega) (by simp [s24])
      (c24 _ (by simp only [s24] <;> omega))
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t24 n24 rfl (4 * (3 * i + s) + l) 1 (by simp only [s24] <;> omega) (by simp [s24])
      (c24 _ (by simp only [s24] <;> omega))
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  -- chain ends
  · exact o1 _ t8 n8 rfl (4 * i + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (4 * i + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- path node halves
  · exact o1 _ t8 n8 rfl (532 + (8 * t + 4 * u + l)) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (532 + (8 * t + 4 * u + l)) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- h'
  · exact o1 _ t8 n8 rfl (660 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (660 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- n': `shl 8`, `shr 56`, bits, top, low
  · exact o1 _ tN nN rfl 0 0 (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN nN rfl 0 1 (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN nN rfl 0 (2 + z) (x0 rfl) (by simp [sN] <;> omega) (cN 0 (x0 rfl)) rfl
      (by simp [sN] <;> omega) (getD_n hz) (show z < 64 by omega)
  · exact o1 _ tN nN rfl 0 (I.ln + 3) (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl
      (by simp only [sN] <;> omega) getD_n_top (by simp only [BOut.Valid]; omega)
  · exact o1 _ tN nN rfl 0 (I.ln + 4) (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl
      (by simp only [sN] <;> omega) getD_n_low (by simp only [BOut.Valid]; omega)
  -- c_L'
  · exact o1 _ t8 n8 rfl (664 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (664 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- leafStmt lanes
  · exact o1 _ t8 n8 rfl (668 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (668 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])

end Ok

/-! ## Non-vacuity: honest tables -/

/-- The honest rows of a small word list satisfy every `Q_sig` `BITS` table's constraints, and its
output reads carry the word functions (`honest_tab`, for every word). -/
theorem honest_sig (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) :
    ∀ S ∈ sigSpecs I o bpl, ∀ w ∈ [(⟨0x0123456789abcdef⟩ : FK), ⟨0xffffffffffffffff⟩, 0, 1],
      (∀ C ∈ S.tab.cons, CPoly.evalB (fun i => FK.toBF64 (honest w i)) C = 0) ∧
        ∀ j < S.outs.length, (S.out j).Valid →
          CPoly.evalB (fun i => FK.toBF64 (honest w i)) (outPoly (S.out j)) =
            FK.toBF64 ⟨(S.out j).word w.val⟩ :=
  fun S _ w _ => honest_tab S w

/-- A computed check of the coefficients (independent of the proofs): the `shl 24`, `shr 40`
and `bit 5` polynomials on the honest row of `0x0123456789abcdef`. -/
theorem honest_check :
    evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.shl 24)) = ⟨0x6789abcdef000000⟩ ∧
      evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.shr 40)) = ⟨0x0000000000012345⟩ ∧
      evalK (honest ⟨0x0123456789abcdef⟩) (outPoly (.bit 5)) = ⟨1⟩ ∧
      ∀ C ∈ cons, evalK (honest ⟨0x0123456789abcdef⟩) C = 0 := by
  decide +kernel

end Lvm.SigBits
