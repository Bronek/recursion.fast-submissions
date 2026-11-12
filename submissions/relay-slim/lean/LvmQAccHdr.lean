-- New for lvm (AC-Q): the child's `PUB` lanes (`Pub.hdrLanes` of `pubOf`, A23) as stream lanes, and
-- phase 3b (`accFold`, AC-V) as a function of the reader position. Searched: LvmNodeSoundIn's
-- `hdrLanes`/`pub_cells` (the parent's header from bytes, not `pubOf`), HAR's `*_run` lemmas (other phases).
import LvmQAccParts
import LvmDecideM3Real
import LvmQLinkArithRead
import LvmQEqKeccakRead

/-!
# The child's header and phase 3b

* **`pubOf_hdrLanes`**: `(pubOf vk c Σ).hdrLanes` lane `i < 702` is `Σ`'s lane `11 + i` (the header
  from byte 8 is in the seed query), except the key lanes `1 … 4`, which are `digestLanes vk`.
* **`pubEval_child`**: hence `pubEval` of the child's `PUB` lanes is `qpub`'s sum on streamed cells.
* **`accFold_run`**: phase 3b from position `P`: `κ` at `P + 40 + 72 i`, `h` at `P + 72 dk + 40 + 24 j`,
  `t` after them, the zero scalar in the next entry; the four checks; the position after.
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM

/-! ## The child's `PUB` lanes -/

/-- The child's `PUB` lane `i` from its stream and `V`'s key argument. -/
def hdrLaneS (vk : Vector UInt8 32) (sig : ByteArray) (i : Nat) : FK :=
  if 1 ≤ i ∧ i < 5 then (digestLanes vk).getD (i - 1) 0 else kAt sig (8 * (11 + i))

theorem list_eq_range_getD (l : List FK) : l = (List.range l.length).map fun i => l.getD i 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h1]

theorem flatMap_feAt (sig : ByteArray) (b : Nat) : ∀ n : Nat,
    ((List.range n).map fun j => feAt sig (8 * (b + 3 * j))).flatMap FE.lanes =
      (List.range (3 * n)).map fun x => kAt sig (8 * (b + x))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_feAt sig b n,
      show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.append_assoc, feAt, FE.lanes, List.cons_append, List.nil_append]
    rw [show 8 * (b + 3 * n) + 8 = 8 * (b + (3 * n + 1)) by ring,
      show 8 * (b + 3 * n) + 16 = 8 * (b + (3 * n + 1 + 1)) by ring, show 8 * (b + 3 * n) = 8 * (b + 3 * n) from rfl]

theorem map_range_add (f : Nat → FK) (a b : Nat) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map fun i => f (a + i) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

theorem range_split (F : Nat → FK) :
    (List.range pubLanes).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range 597).map fun i => F (18 + i)) ++
      ((List.range 87).map fun i => F (615 + i)) := by
  rw [show pubLanes = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 87 from rfl]
  simp only [map_range_add, List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.zero_add, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

/-- **The child's `PUB` lanes** are its stream's lanes from `11`, the key from `V`'s argument. -/
theorem pubOf_hdrLanes (vk c : Vector UInt8 32) (sig : ByteArray) :
    (pubOf vk c sig).hdrLanes = (List.range pubLanes).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(pubOf vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by omega)]
    simp only [pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (pubOf vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by omega]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e2 : (pubOf vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by omega) rfl
  have e3 : (pubOf vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by omega) rfl
  have e4 : (⟨(pubOf vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by omega)]
    simp only [pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e5 : (pubOf vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by omega) rfl
  have e6 : (pubOf vk c sig).sigLeaf = (List.range 597).map fun i => hdrLaneS vk sig (18 + i) := by
    simp only [pubOf]
    rw [show sigBytes / 8 = 597 from rfl]
    exact seg 152 18 597 (by omega) rfl
  have hpos : ∀ i, headerAt (offAcc + eBytes * i) = 8 * (626 + 3 * i) := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes]; omega
  have e7 : ((pubOf vk c sig).accIn.pt ++ [(pubOf vk c sig).accIn.y]).flatMap FE.lanes =
      (List.range 87).map fun i => hdrLaneS vk sig (615 + i) := by
    have : (pubOf vk c sig).accIn.pt ++ [(pubOf vk c sig).accIn.y] =
        (List.range 29).map fun j => feAt sig (8 * (626 + 3 * j)) := by
      simp only [pubOf, hpos]
      rw [show (29 : Nat) = accVars + 1 from rfl, List.range_succ, List.map_append, List.map_singleton]
    rw [this, flatMap_feAt sig 626 29]
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), show 11 + (615 + i) = 626 + i by omega]
  rw [range_split]
  simp only [Pub.hdrLanes, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

/-- **The child's `PUB` evaluation on streamed cells**: with the stream's lanes `< T` and the key
cells `vkc …` holding `digestLanes vk`, `pubEval` of the child's lanes at a point of `τp` coordinates
is `qpub`'s sum. -/
theorem pubEval_child {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hT : 11 + pubLanes ≤ T) {vk : Vector UInt8 32} (c : Vector UInt8 32) {vkc : Nat}
    (hvk : ∀ i < 4, M.k (vkc + i) = (digestLanes vk).getD i 0) (pt : List FE)
    (hn : pubLanes ≤ 2 ^ pt.length) :
    M3.pubEval (pubOf vk c sig).hdrLanes pt =
      ∑ i ∈ Finset.range pubLanes, eqW pt i * FE.ofK (pubLane M 11 vkc i) := by
  rw [M3.pubEval_eq, mle_eq_sum, pubOf_hdrLanes]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ pt.length = pubLanes + m := ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, eqW pt (pubLanes + x) *
      FE.ofK (M3.pubCell ((List.range pubLanes).map (hdrLaneS vk sig)) (pubLanes + x)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    simp [M3.pubCell, List.getD_eq_getElem?_getD, ofK_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  refine congrArg (fun x => eqW pt i * FE.ofK x) ?_
  simp only [M3.pubCell, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hdrLaneS, pubLane]
  split_ifs with h
  · rw [hvk _ (by omega), List.getD_eq_getElem?_getD]
  · rw [hS _ (by omega)]

/-! ## Phase 3b as a function of the position -/

/-- Phase 3b's positions from its start `P` (`dk` batching challenges). -/
def phH (P dk : Nat) : Nat := P + 72 * dk
def phZ (P dk : Nat) : Nat := phH P dk + 24 * (accVars + 1) + 72

/-- **Phase 3b from position `P`** (`accFold`, BLUEPRINT §12.4): `κ`, `h`, `t`, the zero scalar read at
fixed offsets; the four checks on `ok`; the folded claim. -/
theorem accFold_run (P : Params) (m : M3) (pub : Pub) (evals : List (List FE × List FE))
    (sig : ByteArray) (s : RS) (hdk : 1 ≤ P.accLog) :
    accFold P m pub evals sig s =
      let v := feAt sig
      let kap := samplesAt v (s.ent + s.msg) P.accLog
      let h := scalarsAt v (phH (s.ent + s.msg) P.accLog + 40) (accVars + 1)
      let t := v (phH (s.ent + s.msg) P.accLog + 24 * (accVars + 1) + 40)
      (⟨accLine pub.accIn.pt (tablePoint evals ++ kap) t, polyEval h t⟩,
        ⟨phZ (s.ent + s.msg) P.accLog, 24,
          (v (phZ (s.ent + s.msg) P.accLog + 40) == 0) &&
            ((sumE h == dot (eqKernel kap) (m.fixSent pub evals)) &&
              ((h.headD 0 == pub.accIn.y) && (m.pubCheck pub evals && s.ok)))⟩) := by
  unfold accFold
  rw [bind_run, require_run, bind_run, samples_run sig _ _ hdk, bind_run, readEs_run, bind_run,
    sampleE_run, bind_run, readE_run, bind_run, require_run, bind_run, require_run, bind_run,
    require_run, pure_run]
  simp only [samplesAt, phH, phZ]
  rw [show s.ent + s.msg + 72 * P.accLog + 40 + (0 + 24 * (accVars + 1)) =
      s.ent + s.msg + 72 * P.accLog + 24 * (accVars + 1) + 40 by omega,
    show s.ent + s.msg + 72 * P.accLog + 0 + 40 = s.ent + s.msg + 72 * P.accLog + 40 by omega,
    show s.ent + s.msg + 72 * P.accLog + 72 + (0 + 24 * (accVars + 1)) =
      s.ent + s.msg + 72 * P.accLog + 24 * (accVars + 1) + 72 by omega, Nat.add_zero, Nat.zero_add]

end Lvm.QAcc
