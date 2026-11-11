-- New for lvm (WP-16a): the node program's tables (BLUEPRINT A19; WP-9's `lvmTabs`, INT-2's `lvmTabsC`)
-- from a placement record: everything of the assembly that does not depend on Q_arith (split from
-- LvmQAsmProg so that Q_arith's table phase can read the table shapes, HAR).
import LvmQAsmLay
import LvmLoopMleFast
import LvmQSig

/-!
# The node program's tables

* `p1C`, `sigOut`, `p2C`: Q_sig's pointer and output cells (after Q_link).
* `QData` (placement record, dumped by the assembler), `plOf`, `bplOf`.
* `arrs C D pub`: the input arrays of `LvmQAsmLay`'s table (aliased, public, written); `aux C D`:
  Q_sig's six `BITS` tables, then the position classes.
* **`tabs C G D pub = lvmTabsC G (plOf D) D.groups (arrs C D pub) (aux C D)`**, `G = cacheG (Q C)`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.SigBits

/-- Q_sig's pointer (after Q_link). -/
def p1C (C : QCfg) : Ptr := (⟨nK C, 0⟩ : Ptr).adv (qlink C.p (lay C) ⟨nK C, 0⟩).2

/-- Q_sig's output cells. -/
def sigOut (C : QCfg) : SigOut := (qsig (sigIn C) (p1C C)).1

/-- Q_arith's pointer (after Q_sig). -/
def p2C (C : QCfg) : Ptr := (p1C C).adv (qsig (sigIn C) (p1C C)).2

/-! ## Placement record (dumped by the assembler) -/

/-- Where the committed columns are: the groups and their columns' offsets, every input array's
finalize-count offset (in `arrs` order), the written array's value offset, the `BITS` classes'
committed columns (Q_sig's six, then the position classes). All in `C_main` unless aliased. -/
structure QData where
  groups : List Grp
  gpl : List (List Nat)
  afin : List Nat
  aval : Nat
  bpl : List (List Nat)

/-- Group `i`'s placement. -/
def plOf (D : QData) (i : Nat) (u : Var) : Bool × Nat :=
  (false, (D.gpl.getD i []).getD ((D.groups.getD i default).σ.committed.idxOf u) 0)

/-- `BITS` class `k`'s committed column `c` (`w`, `β_0..63`, the word count, the output counts). -/
def bplOf (D : QData) (k c : Nat) : Bool × Nat :=
  (false, (D.bpl.getD k []).getD (if c ≤ 65 then c else 66 + (c - 67) / 2) 0)

/-! ## Arrays and aux tables -/

/-- Where `KS`'s `X` columns of rows `≥ R` start, and `KS`'s output lane `l` (from the prover's
`Layout`: `tables.rs`; the shared `Lvm.CMain` numbers, `LvmLayout`; `KS`'s `Y` lane `l < 14` at `KS` slot `50 + l`; `KS` has `2^(rl + 1)` rows, `tables.rs`). -/
def xOff (C : QCfg) : Nat := if C.rl = 14 then CMain.xOff20 else CMain.xOff8
def ksY (C : QCfg) (l : Nat) : Nat :=
  if C.rl = 14 then CMain.ksOff20 + (50 + l) * 2 ^ 15 else CMain.ksOff8 + (50 + l) * 2 ^ (C.rl + 1)

/-- The header's lanes from the public values (`Pub.hdrLanes`, A23: 702 = 615 + `acc_in`'s 87;
`LvmNodeSoundIn.hdrLanes`' order). -/
def hdrOfPub (P : Pub) : List FK := P.hdrLanes

/-- The finalize offset of array `i`. -/
def fin (D : QData) (i : Nat) : Bool × Nat := (false, D.afin.getD i 0)

/-- **The input arrays** (`LvmQAsmLay`'s table, in this order). -/
def arrs (C : QCfg) (D : QData) (P : Pub) : List InArr :=
  let R := 2 ^ C.rl
  (List.range 17).map (fun l => ⟨.K, C.rl, l, 17, [(true, l * R)], fin D l, none⟩) ++
  [⟨.K, 10, sgB C, 1, [(true, 17 * R)], fin D 17, none⟩] ++
  (List.range 17).map (fun l => ⟨.K, 9, xsB C + l, 17, [(false, xOff C + l * R)], fin D (18 + l), none⟩) ++
  (List.range 4).map (fun l => ⟨.K, 9, ysB C + l, 4, [(false, ksY C l + R)], fin D (35 + l), none⟩) ++
  (List.range 4).map (fun l =>
    ⟨.K, 0, mdB C + l, 4, [(false, ksY C l + (spongeBlocks C.p - 1))], fin D (39 + l), none⟩) ++
  [pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P),
   pubArr C.aQT (qtB C) 1 (false, 0) (fin D 44) (qltData C.p (lay C)),
   ⟨.K, C.bo, obB C, 1, [(false, D.aval)], fin D 45, none⟩]

/-- The `BITS` classes: Q_sig's six, the position classes, the `s'` byte shifts (`sSpec`). -/
def bspecs (C : QCfg) (D : QData) : List BSpec :=
  sigSpecs (sigIn C) (sigOut C) (bplOf D) ++ posSpecs C (fun c => bplOf D (6 + c)) ++
    [sSpec C (bplOf D (6 + nPosCls C))]

/-- **The aux tables.** -/
def aux (C : QCfg) (D : QData) : List Tab := (bspecs C D).map BSpec.tab

/-- **The node program's tables**, `G` its cache (`cacheG (Q C)`). -/
def tabs (C : QCfg) (G : PG) (D : QData) (P : Pub) : List Tab :=
  lvmTabsC G (plOf D) D.groups (arrs C D P) (aux C D)

end Lvm.QAsm
