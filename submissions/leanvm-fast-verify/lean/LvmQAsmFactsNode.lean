-- New for lvm (WP-16a2, FIN-TF): the table-level static facts of the `P20` node program in their
-- consumers' forms: WP-16b's `MidHyp M3.tabsP20` (`LvmCertSMid3`) and the static fields of
-- `NodeBase` at `nodeHyp20`'s instance (`LvmCertSFinal`), and INB's `PosCellsLt`.
-- adapted from rf-lvm-QFX/submissions/leanvm-inspired/lean/LvmQAsmFacts{Sk,Static}.lean (uncommitted,
-- WP-16a-QFX); the program-level facts (`wf`, `grp`, `inj`) come from A24's `Lvm.Fin.StaticFacts`.
import LvmQAsmFactsDec
import LvmCertSMid3
import LvmFinStatic
import LvmPubOk

/-!
# The node program's table facts

For the instance `lay cfg20, sigIn cfg20, qarith cfg20, nK cfg20, 0, plOf data20, data20.groups,
arrs20, aux cfg20 data20` (`arrs20 x = arrs cfg20 data20 (pubX x)`):

* **`midHyp20 S : MidHyp M3.tabsP20`**: `fit` from `fitsR_P20` (`LvmQAsmFactsDec`, at `default`) and
  skeleton invariance; `keys`, `width`, `cons` from `chkB_P20`;
  `fix` from `fixOk_lvmTabs` with A24's `GrpOk` (`S.grp`).
* `NodeBase`'s static fields: **`hT20`**, **`hst20 S`** (`wf`, `grp`, `inj` from `S`; `inOk`,
  `auxSeeds`, `cnt`, `len` from the decisions), **`hlay20`**, **`hτT20`**, **`hqlt20`**.
* **`posCellsLt20 : PosCellsLt Q20n cfg20`** (`nodeHyp20`'s `hpc`).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits
open Lvm.NS Lvm.VEq Lvm.ASM

/-- The input arrays of a statement. -/
abbrev arrs20 (x : List UInt8) : List InArr := arrs cfg20 data20 (pubX x)

/-! ## The tables' checks at every public input -/

theorem chk20 (P : Pub) : chkB lay26 (M3.tabsP20 P) = true := chk20_of chkB_P20 P

theorem sumcheck20 (P : Pub) : sumcheckTabs (M3.tabsP20 P) = M3.tabsP20 P := chkB_sumcheck (chk20 P)

/-- **`NodeBase.hT`**: the sumcheck tables of a statement are WP-9's tables of the node program. -/
theorem hT20 : ∀ x, TS M3.tabsP20 x =
    lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20) := fun x => by
  unfold TS
  rw [sumcheck20, tabsP20_eq]

/-- `AuxStatic.cnt`. -/
theorem cnt20 (x : List UInt8) :
    ∀ t ∈ lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20), ∀ r ∈ t.reads, r.2 < t.w := by
  rw [← tabsP20_eq]; exact chkB_cnt (chk20 _)

/-- `AuxStatic.len`. -/
theorem len20 (x : List UInt8) :
    nReads (lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20)) < 2 ^ 64 - 1 := by
  rw [← tabsP20_eq]; exact chkB_len (chk20 _)

/-- **`NodeBase.hlay`.** -/
theorem hlay20 : ∀ x, LayOk lay26 (lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20)) :=
  fun x => by rw [← tabsP20_eq]; exact chkB_lay (chk20 _)

/-- `MidHyp.keys`. -/
theorem keys20 : ∀ x, KeysOk (TS M3.tabsP20 x) := fun x => by
  unfold TS; rw [sumcheck20]; exact chkB_keys (chk20 _)

/-- `MidHyp.width`. -/
theorem width20 : ∀ x, ∀ t ∈ TS M3.tabsP20 x, 0 < t.w := fun x => by
  unfold TS; rw [sumcheck20]; exact chkB_width (chk20 _)

/-- `MidHyp.cons`. -/
theorem cons20 : ∀ x, ((TS M3.tabsP20 x).map fun t => t.cons.length).sum ≤ 2 ^ 60 := fun x => by
  unfold TS; rw [sumcheck20]; exact chkB_cons (chk20 _)

/-- **`MidHyp.fix`**: every fixed column's closed form is its cells' extension (WP-9b's
`fixOk_lvmTabs` with A24's `GrpOk`, INT-2's `pubOk_of`, the `BITS` tables' `fixOk_tabs`). -/
theorem fix20 (S : Lvm.Fin.StaticFacts) : ∀ x, FixOk (TS M3.tabsP20 x) := fun x => by
  rw [hT20]
  exact fixOk_lvmTabs S.grp (pubOk_of _ (arrs_pub _ _ _)) (BitsTab.BSpec.fixOk_tabs _)

/-- **`MidHyp M3.tabsP20`** from `fitsR` at `default` (`fitsR_P20`) and A24's facts. -/
theorem midHyp20 (S : Lvm.Fin.StaticFacts) : MidHyp M3.tabsP20 :=
  ⟨fit20_of fitsR_P20, keys20, width20, fix20 S, cons20⟩

/-- **`NodeBase.hτT`** (`MidHyp.hτ` without A24's facts). -/
theorem hτT20 : ∀ x, ∀ t ∈ TS M3.tabsP20 x, t.τ ≤ lay26.μ :=
  fun x => (fit_of P20 _ (fit20_of fitsR_P20 (pubX x))).hτ

/-! ## `AuxStatic` -/

/-- **`AuxStatic.inOk`**: the input arrays tile the input cells. -/
theorem inOk20 (x : List UInt8) : InOk Q20n (arrs20 x) :=
  inOk_congr (arrs_arrSk cfg20 data20 default (pubX x)) (inOk_of_B inOkB_P20)

/-- **`NodeBase.hst`** for the `P20` node program, with A24's program facts. -/
theorem hst20 (S : Lvm.Fin.StaticFacts) : ∀ x,
    AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups
      (aux cfg20 data20) (arrs20 x) :=
  fun x => ⟨S.wf, S.grp, inOk20 x, auxSeeds20, cnt20 x, len20 x, S.inj⟩

/-! ## Q_link's `QLT` cells (`NodeBase.hqlt`) -/

theorem qltLen20 : (qltData P20 (lay cfg20)).length = 3 * 2 ^ 11 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ20.qlen]; rfl

/-- Q_link's `QLT` cells hold the static table `qltData` on the memory of any pair of any statement
(the `QLT` array is public: `inKOf_pub`; no `inb`, `Program.interpMem_inK`). -/
theorem qltMem20 {hτ' : ∀ x, ∀ t ∈ lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20),
      t.τ ≤ lay26.μ} (x : List UInt8) (qm : LeanVM.Protocol.Column 26) (qr : LeanVM.Protocol.Column 19) :
    ∀ y < (qltData P20 (lay cfg20)).length,
      (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups arrs20
        (aux cfg20 data20) hτ' x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0 := by
  intro y hy
  have hl := qltLen20
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem (mem_arrs_qlt (pubX x))
  have hx : y < 2 ^ (arrs20 x)[k].τ := by rw [he]; show y < 2 ^ 13; omega
  have hv := inKOf_pub Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20) lay26 (hτ' x)
    (inOk20 x) (stackOf lay26 qm qr) hk (by rw [he]; rfl) (by rw [he]; rfl) hx
  simp only [he, pubArr, Nat.one_mul] at hv
  have hlt : (lay cfg20).qt + y < (inKOf Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20)
      lay26 (hτ' x) (stackOf lay26 qm qr)).size := by
    rw [inKOf_size]; have := qlt_le_nK20 hQ20; show _ < nK cfg20; omega
  show (Q20n.interpMem _ _).k _ = _
  rw [Q20n.interpMem_inK _ _ hlt, show (lay cfg20).qt = qtB cfg20 from rfl, hv]
  rfl

/-- **`NodeBase.hqlt`** (any `hτ'`, any `hτT`: the cells are public input cells). -/
theorem hqlt20 {hτ' : ∀ x, ∀ t ∈ lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20),
      t.τ ≤ lay26.μ} {hτT : ∀ x, ∀ t ∈ TS M3.tabsP20 x, t.τ ≤ lay26.μ} :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups arrs20
          (aux cfg20 data20) hτ' x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0 :=
  fun _ _ x qm qr _ _ _ => qltMem20 x qm qr

/-! ## The position classes' cells -/

/-- **INB's `PosCellsLt` for the `P20` node program** (`nodeHyp20`'s `hpc`). -/
theorem posCellsLt20 : PosCellsLt Q20n cfg20 :=
  posCellsLt_of (C := cfg20) posCellsB_P20 (hS20 : StreamOk cfg20.p) hashedLen_nK20 (nK_le_cells _ _ _)

end Lvm.QAsm
