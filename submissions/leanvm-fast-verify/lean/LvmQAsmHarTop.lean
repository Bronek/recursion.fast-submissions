-- New for lvm (HAR): the composition of the phase facts into `decideCore` and `accOutOf` (BLUEPRINT
-- §12.6's node-level `harith`): if every phase of `decideProgH`, run from its start position with the
-- flag `ok`, keeps `ok`, reaches the next start position and yields fixed values, then `F`'s run
-- accepts (`decideCore`) and folds to the given accumulator (`accOutOf`).
import LvmQAsmHarRun

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

theorem bind_run' {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := rfl

theorem pure_run' {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) := rfl

theorem require_run' (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := rfl

theorem skip_run' (n : Nat) (sig : ByteArray) (s : RS) : skip n sig s = ((), { s with msg := s.msg + n }) := rfl

theorem read_run' (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) := rfl

/-- A phase from position `P` (with `ok`) yields `v`, keeps `ok`, and ends at `P'`. -/
def PhaseAt {α : Type} (F : DM α) (sig : ByteArray) (P P' : Nat) (v : α) : Prop :=
  ∀ s : RS, pos s = P → s.ok = true → (F sig s).1 = v ∧ (F sig s).2.ok = true ∧ pos (F sig s).2 = P'

/-- **`decideCore` and `accOutOf` from the phases** (generic in the parameters and the instance). -/
theorem core_of_phases (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb Pt P3 P4 P5 P6 P7 P8 : Nat}
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    {evals : List (List FE × List FE)} {acc : Acc}
    {r v : List FE} {ko : KeccakOut} {ring : FE × (List FE → FE)} {okL : Bool} {linkClaims : List (Com × BlockClaim)}
    {rk vks : List FE} {kko : KeccakOut} {kring : FE × (List FE → FE)} {okK : Bool}
    {kLinkClaims : List (Com × BlockClaim)}
    (h0 : RS.start.ent + (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap + nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap) = Pb)
    (hbus : PhaseAt (busPh p) sig Pb Pt (alphas, beta, countRoot, point, values, leafdec))
    (hbusOk : (m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pubOf vk c sig⟩).ok = true)
    (htab : PhaseAt (tabPh p m (pubOf vk c sig)
      (m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pubOf vk c sig⟩) point) sig Pt P3 evals)
    (hacc : PhaseAt (accFold p m (pubOf vk c sig) evals) sig P3 P4 acc)
    (hch : PhaseAt (chPh p) sig P4 P5 (r, v, ko, ring))
    (hchl : PhaseAt (chLinkPh p m r v (pubOf vk c sig)) sig P5 P6 (okL, linkClaims)) (hokL : okL = true)
    (hks : PhaseAt (ksPh p) sig P6 P7 (rk, vks, kko, kring))
    (hksl : PhaseAt (ksLinkPh p m rk (pubOf vk c sig)) sig P7 P8 (okK, kLinkClaims)) (hokK : okK = true)
    (hopen : ∀ s : RS, pos s = P8 → s.ok = true →
      let o := openPh p (claimsOf p m (pubOf vk c sig)
        (m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pubOf vk c sig⟩) evals r v ko ring
        linkClaims rk vks kko kring kLinkClaims) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    decideCore p m vk c sig = true ∧ accOutOf p m vk c sig = acc := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = ⟨RS.start.ent, nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap +
    nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap, true⟩ := ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← h0, hs1]; rfl
  obtain ⟨b1, b2, b3⟩ := hbus s1 e1 (by rw [hs1])
  generalize hB : busPh p sig s1 = B at b1 b2 b3
  obtain ⟨bv, s2⟩ := B
  simp only at b1 b2 b3
  rw [b1] at hB
  -- after `require bus.ok`
  obtain ⟨s2', hs2'⟩ : ∃ s2' : RS, s2' = { s2 with ok := (m.busFinal ⟨alphas, beta, countRoot, point, values,
    leafdec, pubOf vk c sig⟩).ok && s2.ok } := ⟨_, rfl⟩
  have e2 : pos s2' = Pt := by rw [hs2']; exact b3
  have o2 : s2'.ok = true := by rw [hs2']; simp [hbusOk, b2]
  obtain ⟨t1, t2, t3⟩ := htab s2' e2 o2
  generalize hT : tabPh p m (pubOf vk c sig) (m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pubOf vk c sig⟩) point sig s2' = TT
    at t1 t2 t3
  obtain ⟨tv, s3⟩ := TT
  simp only at t1 t2 t3
  rw [t1] at hT
  obtain ⟨a1, a2, a3⟩ := hacc s3 t3 t2
  generalize hA : accFold p m (pubOf vk c sig) evals sig s3 = AA at a1 a2 a3
  obtain ⟨av, s4⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨c1, c2, c3⟩ := hch s4 a3 a2
  generalize hC : chPh p sig s4 = CC at c1 c2 c3
  obtain ⟨cv, s5⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨l1, l2, l3⟩ := hchl s5 c3 c2
  generalize hL : chLinkPh p m r v (pubOf vk c sig) sig s5 = LL at l1 l2 l3
  obtain ⟨lv, s6⟩ := LL
  simp only at l1 l2 l3
  rw [l1] at hL
  obtain ⟨s6', hs6'⟩ : ∃ s6' : RS, s6' = { s6 with ok := okL && s6.ok } := ⟨_, rfl⟩
  have e6 : pos s6' = P6 := by rw [hs6']; exact l3
  have o6 : s6'.ok = true := by rw [hs6']; simp [hokL, l2]
  obtain ⟨k1, k2, k3⟩ := hks s6' e6 o6
  generalize hK : ksPh p sig s6' = KK at k1 k2 k3
  obtain ⟨kv, s7⟩ := KK
  simp only at k1 k2 k3
  rw [k1] at hK
  obtain ⟨m1, m2, m3⟩ := hksl s7 k3 k2
  generalize hM : ksLinkPh p m rk (pubOf vk c sig) sig s7 = MM at m1 m2 m3
  obtain ⟨mv, s8⟩ := MM
  simp only at m1 m2 m3
  rw [m1] at hM
  obtain ⟨s8', hs8'⟩ : ∃ s8' : RS, s8' = { s8 with ok := okK && s8.ok } := ⟨_, rfl⟩
  have e8 : pos s8' = P8 := by rw [hs8']; exact m3
  have o8 : s8'.ok = true := by rw [hs8']; simp [hokK, m2]
  obtain ⟨o1, o2', o3⟩ := hopen s8' e8 o8
  generalize hO : openPh p (claimsOf p m (pubOf vk c sig) (m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec,
    pubOf vk c sig⟩)
    evals r v ko ring linkClaims rk vks kko kring kLinkClaims) sig s8' = OO at o1 o2' o3
  obtain ⟨ov, s9⟩ := OO
  simp only at o1 o2' o3
  have run : decideProgH p m vk c sig RS.start = (acc, s9) := by
    unfold decideProgH
    simp only [bind_run', read_run', skip_run', pure_run', require_run']
    have hs1' : ({ RS.start with msg := RS.start.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap +
        nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap } : RS) = s1 := by simp [hs1, RS.start]
    rw [hs1', hB]
    simp only
    rw [← hs2', hT, hA]
    simp only
    rw [hC]
    simp only
    rw [hL]
    simp only
    rw [← hs6', hK]
    simp only
    rw [hM]
    simp only
    rw [← hs8', hO]
  unfold decideCore accOutOf DM.runOn
  rw [decideProg_eq]
  simp only [StateT.run, run, o1, o2', o3, Bool.true_and, beq_self_eq_true, and_self]

end Lvm.Har
