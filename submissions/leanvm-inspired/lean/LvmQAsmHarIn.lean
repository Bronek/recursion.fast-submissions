-- New for lvm (HAR): `harith`'s inputs: the node program's stream cells bind `Σ'` (the child's trace bytes),
-- the gate, and Q_arith's segments split into phases 4–7 and the rest.
import LvmQAsmProg
import LvmQAsmHarBase

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.Q1 Lvm.Replay

/-- **`Σ'` is the stream cells' bytes**: with Q_link's `LaneLink`, the child's trace bytes are `sigma`,
whose lanes the node program's stream cells hold (`InMapN.stream`). -/
theorem streamed_child (C : QCfg) {M : Mem} {ws : List Word} (hS : StreamOk C.p) (hL : LaneLink C.p ws)
    (hst : ∀ j < 2 ^ (lay C).m, M.k ((lay C).sb + j) = laneK ws j) {T : Nat} (hTm : T ≤ 2 ^ (lay C).m)
    (hT : 8 * T ≤ hashedLen C.p) (hl : T ≤ ws.length) :
    Streamed M (traceBytesB (decode C.p ws)) T := by
  rw [traceBytesB_decode hS hL]
  exact streamed_sigma C.p ws (N := 2 ^ (lay C).m) (fun j hj => by simpa [lay] using hst j hj) hTm hT hl

/-- The gate: `PUB` lane 0 holds the flag. -/
theorem gate_val {M : Mem} (C : QCfg) (h : M.k (pbB C) = 1) : (kc (pbB C)).val M = 1 := by
  simp [h, ofK_one]

/-- **Q_arith's segments split** into phases 4–7 and the rest. -/
theorem qarith_split (C : QCfg) {c : Ctx} {M : Mem} {p : Ptr} (h : Lvm.QSig.Ok c M (qarith C) p) :
    Lvm.QSig.Ok c M (phases47 C) p ∧
      Lvm.QSig.Ok c M (qarithRest C (phases47 C p).1) (p.adv (phases47 C p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [show qarith C = (phases47 C >>= qarithRest C) from rfl, hold_bind] at h1
  rw [show qarith C = (phases47 C >>= qarithRest C) from rfl, assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

end Lvm.Har
