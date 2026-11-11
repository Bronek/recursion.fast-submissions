-- New for lvm (HAR): the interface between Q_arith's phase gadgets and `F`'s phases: the claims as
-- circuit cells (`CClaim`), the phase-replay statement (`Replays`), table shapes (`TShape`), and the
-- binding of the node program's stream cells to `Σ` (`streamed_sigma`).
import LvmQAsmHarRun
import LvmQLinkMain
import LvmQSumcheckCore
import LvmLoopMleFast
import LvmQSigHdr

/-!
# Q_arith's phase interface

* **`Replays c M sig F g p P P' R`**: wherever the gadget `g`'s rows hold and assert (`Ok`, the gate
  on), `F` run from any state at position `P` (`pos s = s.ent + s.msg`) with `ok` keeps `ok`, ends at
  position `P'`, and its result is related by `R` to the gadget's output. Every phase family proves
  its phase in this form (soundness direction, BLUEPRINT §4.6 `Q_arith_eq`); `harith` composes them.
* **`CClaim`**: a claim of phase 8 as cells: its commitment, its weight's form (a point claim, a
  ring-switch claim, a sum of point claims) with the point/coefficient cells, its value cell.
  `CClaim.val M` is the `F`-side claim (`BlockClaim.point`, the ring weight closure of `ringSwitch`/
  `chLink0`, `sumClaim`) with the cells' values: a phase proves `claims.map (CClaim.val M) = F's claims`.
* **`TShape`**: what a table contributes to the table phase other than its fixed columns' closed
  forms (height, constraints, keys, column kinds); the circuit is built from shapes (`Tab.shape`).
* **`streamed_sigma`**: the node program's stream cells (`InMapN.stream`) are `Σ`'s lanes.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.M3 Lvm.Replay Lvm.Q1 DM

/-! ## Replaying a phase -/

/-- **A gadget replays a phase of `F`** (soundness direction). -/
def Replays {α β : Type} (c : Ctx) (M : Mem) (sig : ByteArray) (F : DM α) (g : BM β) (p : Ptr)
    (P P' : Nat) (R : α → β → Prop) : Prop :=
  Lvm.QSig.Ok c M g p → ∀ s : RS, pos s = P → s.ok = true →
    (F sig s).2.ok = true ∧ pos (F sig s).2 = P' ∧ R (F sig s).1 (g p).1

/-! ## Claims as cells -/

/-- The weight form of a claim. -/
inductive CW where
  /-- `BlockClaim.point blk z v`: the block's extension at the point `z`. -/
  | point (blk : Placement) (z : List Cell)
  /-- A ring-switch claim `⟨blk, fun x => ringWeight pt x cs, v⟩` (`ringSwitch`, `chLink0`). -/
  | ring (blk : Placement) (pt cs : List Cell)
  /-- `sumClaim nu parts v` (`ksLink0`): coefficient, block, point per part. -/
  | sum (nu : Nat) (parts : List (Cell × Placement × List Cell))

/-- A claim of phase 8 as cells. -/
structure CClaim where
  /-- The commitment. -/
  com : Com
  /-- The weight. -/
  cw : CW
  /-- The value. -/
  value : Cell

/-- The values of a list of cells. -/
def vs (M : Mem) (l : List Cell) : List FE := l.map (Cell.val M)

/-- **The claim a `CClaim` stands for** in memory `M`. -/
def CClaim.val (M : Mem) (cc : CClaim) : Com × BlockClaim :=
  (cc.com, match cc.cw with
    | .point blk z => BlockClaim.point blk (vs M z) (cc.value.val M)
    | .ring blk pt cs => ⟨blk, fun x => ringWeight (vs M pt) x (vs M cs), cc.value.val M⟩
    | .sum nu parts => sumClaim nu (parts.map fun (k, blk, z) => (k.val M, blk, vs M z)) (cc.value.val M))

/-! ## Table shapes -/

/-- A table without its fixed columns' contents. -/
structure TShape where
  /-- Log-height. -/
  τ : Nat
  /-- Column kinds: a committed column's placement, `none` for a fixed column. -/
  cols : List (Option (Bool × Nat))
  /-- Constraints. -/
  cons : List CPoly
  /-- Reads. -/
  reads : List (Key × Nat)
  /-- Seeds. -/
  seeds : List (Key × Nat)

/-- A column's kind. -/
def colKind : ColSrc → Option (Bool × Nat)
  | .com rec off => some (rec, off)
  | .fix _ _ => none

/-- The shape of a table. -/
def _root_.Lvm.M3.Tab.shape (t : Tab) : TShape := ⟨t.τ, t.cols.map colKind, t.cons, t.reads, t.seeds⟩

/-! ## The stream -/

/-- `Σ`'s lane `j` is the stream's lane `j` (inside the hashed bytes). -/
theorem kAt_sigma (p : Params) (ws : List Word) (j : Nat) (hj : 8 * j + 8 ≤ hashedLen p)
    (hl : j < ws.length) : kAt (sigma p ws) (8 * j) = laneK ws j := by
  have hb : ∀ i < 8, (sigma p ws).get! (8 * j + i) = (wordsBytes ws).getD (8 * j + i) 0 := by
    intro i hi
    rw [get!_bl, sigma, bl_mk, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, if_pos (by omega)]
  have e : (List.range 8).map (fun i => (sigma p ws).get! (8 * j + i)) = wordBytes (ws.getD j 0) := by
    have hwb := wordsBytes_slice ws j 1
    rw [List.take_one, show (ws.drop j).head? = some (ws.getD j 0) by
      simp [List.getD_eq_getElem?_getD, List.head?_drop, List.getElem?_eq_getElem hl]] at hwb
    simp only [Option.toList_some] at hwb
    rw [show wordsBytes [ws.getD j 0] = wordBytes (ws.getD j 0) by simp [wordsBytes]] at hwb
    rw [← hwb]
    refine List.ext_getElem (by simp [wordsBytes_length]; omega) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, hb i h1, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    · rfl
  have hu : (laneAt (sigma p ws) (8 * j)).toNat = (ws.getD j 0).toNat := by
    show u64At (sigma p ws) (8 * j) = _
    rw [u64At_eq, e, ofLE_wordBytes]
  unfold kAt laneK
  congr 1
  apply UInt64.toNat.inj
  rw [hu]
  rfl

/-- **The stream cells are `Σ`'s lanes** (the node program's stream region at cell `0`). -/
theorem streamed_sigma {M : Mem} (p : Params) (ws : List Word) {N T : Nat}
    (hst : ∀ j < N, M.k j = laneK ws j) (hTN : T ≤ N) (hT : 8 * T ≤ hashedLen p) (hl : T ≤ ws.length) :
    Streamed M (sigma p ws) T := fun j hj =>
  (hst j (by omega)).trans (kAt_sigma p ws j (by omega) (by omega)).symm

end Lvm.Har
