-- New for lvm (WP-14a, H0): the IOP verifier `P_S` (LvmCertS `PSWith`) with the middle phases `midS`
-- follows the whole schedule at P20 (`Fol`, LvmVEqShape): the roots, the middle phases (LvmVEqFolMid),
-- and the two WHIR openings against `openRecI`, `openMainI` (LvmVEqFol's `fol_verifyStackedUd`; lvm2 JB-VQP J1:
-- `C_main`'s with OOD samples, `fol_verifyStackedJ`).
import LvmVEqFolMid
import LvmCertS
import LvmReplay

/-!
# `P_S` follows the schedule

* `lvMatch_rec`, `lvMatch_main`: `cfgRec20G`'s and `cfgMain24J 3`'s levels are P20's (`LvMatch`,
  `LvMatchJ` with the OOD samples' `κ`, at `capS`, `shpS`, `idxS`), by evaluation on `P20L`
  (LvmReplay's `P20_eq`: the levels written out);
* `fol_openRec`, `fol_openMain`: the openings against `openRecI P20`, `openMainI P20`;
* `folP_commit`: the two roots against `commitI P20`;
* **`fol_PS`**: `PSWith (midS tabs) x` against `atomsOf P20 (schedule P20)` from no pending
  positions.

A `Fol` at concrete atoms is applied with `@` (the default application elaborator would unfold it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgRec20G cfgMain24J)
open Lvm.Replay (P20_eq)

theorem lvMatch_rec : LvMatch P20 capS shpS idxS .crec cfgRec20G.μ cfgRec20G.c₀ cfgRec20G.n₀ P20.recFinalLog
    0 0 cfgRec20G.levels P20.recLevels := by
  rw [P20_eq]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem lvMatch_main : LvMatchJ P20 capS shpS idxS .main (cfgMain24J 3).μ (cfgMain24J 3).c₀
    (cfgMain24J 3).n₀ P20.mainFinalLog 0 0 (cfgMain24J 3).levels P20.mainLevels := by
  rw [P20_eq]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩⟩⟩

theorem openMainI_P20 : openMainI P20 = smp 1 ++ whirIJ .main P20.mainLevels P20.mainFinalLog P20.grind := by
  rw [openMainI, if_pos (by rw [P20_eq]; rfl)]

/-- **`C_rec`'s opening** against `openRecI P20`. -/
theorem fol_openRec (claims : List Verifier.StackClaim) (pp : List ℕ) :
    Fol capS shpS idxS (Verifier.verifyStackedUd cfgRec20G claims) (atomsOf P20 (openRecI P20)) pp
      fun _ _ ↦ True :=
  @fol_verifyStackedUd P20 capS shpS idxS cfgRec20G rfl .crec P20.recLevels P20.recFinalLog lvMatch_rec claims pp

/-- **`C_main`'s opening** (J1: with OOD samples) against `openMainI P20`. -/
theorem fol_openMain (claims : List Verifier.StackClaim) (pp : List ℕ) :
    Fol capS shpS idxS (Verifier.verifyStackedJ (cfgMain24J 3) claims) (atomsOf P20 (openMainI P20)) pp
      fun _ _ ↦ True := by
  rw [openMainI_P20]
  exact @fol_verifyStackedJ P20 capS shpS idxS (cfgMain24J 3) rfl rfl .main P20.mainLevels P20.mainFinalLog
    lvMatch_main claims pp

theorem cap_main0 : capS (cfgMain24G.μ - 6 + 1) (2 ^ 6) = (P20.level ⟨.main, 0⟩).cap := by
  rw [P20_eq]; rfl

theorem cap_rec0 : capS (cfgRec20G.μ - 6 + 2) (2 ^ 6) = (P20.level ⟨.crec, 0⟩).cap := by
  rw [P20_eq]; rfl

theorem atomsOf_commitI : atomsOf P20 (commitI P20) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++ [.cap (P20.level ⟨.crec, 0⟩).cap ⟨.crec, 0⟩] := rfl

/-- **The roots** against `commitI P20`. -/
theorem folP_commit : FolP capS shpS idxS
    ((Verifier.commitRootUd cfgMain24G).bind fun _ ↦ Verifier.commitRootUd cfgRec20G)
    (atomsOf P20 (commitI P20)) fun _ ↦ True := by
  rw [atomsOf_commitI]
  exact (folP_commitRootUd cfgMain24G rfl cap_main0 rfl).bind fun _ _ ↦
    folP_commitRootUd cfgRec20G rfl cap_rec0 rfl

theorem atomsOf_schedule : atomsOf P20 (schedule P20) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++ ([.cap (P20.level ⟨.crec, 0⟩).cap ⟨.crec, 0⟩] ++
      (atomsOf P20 Lvm.ASM.midItems ++ (atomsOf P20 (openRecI P20) ++ (atomsOf P20 (openMainI P20) ++ [])))) := by
  rw [schedule_eq, midItems_eq]
  simp only [atomsOf_append, List.append_assoc, List.append_nil, atomsOf_commitI]

/-- **`P_S` follows the schedule** at P20. -/
theorem fol_PS (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWith (midS tabs) x) (atomsOf P20 (schedule P20)) [] fun _ _ ↦ True := by
  rw [atomsOf_schedule]
  unfold Lvm.ASM.PSWith
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (folP_commitRootUd cfgRec20G rfl cap_rec0 rfl) fun _ _ ↦ ?_
  refine Fol.bindP (folP_midS tabs hfit x) fun cl _ ↦ ?_
  refine @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openRecI P20)) _ [] _ _ (@fol_openRec cl.1 []) fun _ pp' _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] pp' _ _ (@fol_openMain cl.2 pp')
    fun _ _ _ ↦ trivial

end Lvm.VEq
