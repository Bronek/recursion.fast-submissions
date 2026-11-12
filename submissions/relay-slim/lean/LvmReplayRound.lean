-- New for lvm (WP-11b-QL): the round trip of `reassemble` (BLUEPRINT §2.2), part 2: the statements.
import LvmReplayBack

/-!
# Round trip: `reassemble (trace of an accepting V_S run on π) = π`

**`VS_roundtrip`**: if `V_S` accepts `π` on the trace `tr` (`(VS p m vk c π).runSeq tr = some true`),
then `tr` meets its plan (`LinkOk p tr`: the honest trace satisfies what Q_link asserts) and the
proof it carries is `π` (`reassemble p tr = π`): `V_S` uses every proof byte in exactly one query.

Hypotheses: the plan's static checks (`PlanOk`, as for `VS_replay`) and **`PlanBytes`**: the plan's
entries carry `piSize p − 8` bytes (`pOff (plan p) (plan p).length = piSize p`), so that the
header's size check bounds every read of the driver. Both are decided at `P20` and `P8`.

The proof (`LvmReplayBack`) runs the driver forward from the header: every query it asks is the
trace's entry, the bytes it reads are the entries' contributions, and the accepting continuation
says the body was used up (`off = |π|`).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## The header bytes -/

theorem zeroBytes_spec (b : ByteArray) : ∀ (n o : Nat), zeroBytes b o n = true → ∀ x < n, b.get! (o + x) = 0
  | 0, _, _, x, hx => absurd hx (by omega)
  | n + 1, o, h, x, hx => by
    simp only [zeroBytes, Bool.and_eq_true, beq_iff_eq] at h
    rcases x with _ | x
    · simpa using h.1
    · rw [show o + (x + 1) = o + 1 + x by omega]; exact zeroBytes_spec b n (o + 1) h.2 x (by omega)

/-- The first eight bytes of a proof that passes the header check are `'S'` and seven zeros. -/
theorem take8_of_parse {π : ByteArray} (h8 : 8 ≤ π.size) (h0 : π.get! 0 = 0x53) (hz : zeroBytes π 1 7 = true) :
    (bl π).take 8 = hdr8 := by
  have hz' := zeroBytes_spec π 7 1 hz
  have hl : 8 ≤ (bl π).length := by rw [← size_bl]; exact h8
  apply List.ext_getElem (by simp only [List.length_take, hdr8, List.length_cons, List.length_nil]; omega)
  intro n h1 h2
  have hn8 : n < 8 := by simpa [hdr8] using h2
  have hnl : n < (bl π).length := by omega
  simp only [List.getElem_take]
  have hn : (bl π)[n] = π.get! n := by
    rw [get!_bl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnl, Option.getD_some]
  rw [hn]
  rcases n with _ | n
  · simpa [hdr8] using h0
  · have := hz' n (by omega)
    rw [Nat.add_comm 1 n] at this
    rw [this]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | rfl | omega

/-! ## The driver -/

/-- **The driver forward**: an accepting run of the driver on `π` (whose first 8 bytes are the
header's constant ones, and which holds the plan's bytes) asks a trace of the schedule, and that
trace reassembles to `π`. -/
theorem drive_fwd (p : Params) (hP : PlanOk p) (π : ByteArray) (tr : Trace) (F : ByteArray → Bool)
    (hsz : pOff (plan p) (plan p).length ≤ π.size) (h8 : (bl π).take 8 = hdr8)
    (h : (drive p π F).runSeq tr = some true) :
    reassemble p tr = π ∧ LinkOk p tr := by
  have h0 : (drive p π F).runSeq (tr.drop 0) = some true := h
  obtain ⟨hi0, hq0, h1⟩ := query_fwd h0
  obtain ⟨hi1, hq1, h2⟩ := query_fwd h1
  simp only [Nat.zero_add] at hq1 h2 hi1
  have hPl : 2 ≤ (plan p).length := by simp [plan]
  have hP0 : (plan p).getD 0 default = ⟨.q0, 7⟩ := rfl
  have hP1 : (plan p).getD 1 default = ⟨.fs 0, seedLen⟩ := rfl
  have hH : pOff (plan p) 2 = headerBytes := by
    rw [show 2 = 0 + 1 + 1 from rfl, pOff_succ (by omega), pOff_succ (by omega), hP0, hP1]
    simp [pOff, clen, seedLen, headerBytes, sigBytes, eBytes, accVars]
  have hHle : headerBytes ≤ π.size := hH ▸ le_trans (pOff_mono _ (by omega)) hsz
  have hbl1 : bl (qOf tr 1) = (aOf tr 0).toList ++ ((bl π).drop 8).take (headerBytes - 8) := by
    rw [hq1, seedQuery, bl_append, bl_digestBytes, bl_extract]
  have hcl : (((bl π).drop 8).take (headerBytes - 8)).length = headerBytes - 8 :=
    length_take_drop (by rw [← size_bl]; simp [headerBytes, sigBytes, eBytes, accVars] at hHle ⊢; omega)
  have hR0 : RInv p tr π ⟨headerBytes, headerBytes, aOf tr 1,
      [(seedQuery π (aOf tr 0), aOf tr 1), (q0Query, aOf tr 0)], [], []⟩ w0 := by
    refine ⟨by simp [w0]; omega, ?_, rfl, rfl, ?_, hH.symm, List.Forall₂.nil, ?_⟩
    · show _ = (tr.take 2).reverse
      rw [← hq1, ← hq0]
      have e0 := entry_eq tr (i := 0) (by omega)
      have e1 := entry_eq tr (i := 1) (by omega)
      rw [show 2 = 0 + 1 + 1 from rfl, List.take_add_one, List.take_add_one, List.take_zero,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), ← e0, ← e1]
      rfl
    · show (bl π).take headerBytes = hdr8 ++ bodyTo tr (plan p) 2
      rw [show headerBytes = 8 + (headerBytes - 8) by decide, List.take_add, h8,
        show (2 : Nat) = 0 + 1 + 1 from rfl, bodyTo_succ, bodyTo_succ, hP0, hP1]
      show _ = hdr8 ++ (bodyTo tr (plan p) 0 ++ [] ++ (bl (qOf tr 1)).drop 32)
      rw [hbl1, List.drop_left' (by simp)]
      simp [bodyTo]
    · intro x hx
      simp only [w0] at hx
      rcases x with _ | x
      · rw [hP0]; simp only [Good]; rw [hq0]; exact ⟨by rfl, rfl⟩
      · rw [show x = 0 by omega, hP1]
        simp only [Good]
        refine ⟨?_, ?_⟩
        · rw [size_bl, hbl1, List.length_append, hcl]
          have : 8 ≤ headerBytes := by decide
          simp [seedLen]; omega
        · rw [hbl1, List.take_left' (by simp)]
  have hal : Al (plan p) w0.i (planAll p).1 := by
    refine ⟨by simp only [w0, plan_length]; omega, fun x hx => ?_⟩
    simp only [w0, plan, List.getD_eq_getElem?_getD]
    rw [show 2 + x = x + 1 + 1 by omega]
    simp
  obtain ⟨hok, hpend, -⟩ := hP
  obtain ⟨s', hR', hrun⟩ := items_fwd hsz _ (schedule p) w0 _ hR0 (fun _ h => by simp [w0] at h) hok hal h2
  rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl] at hR' hrun
  have hend : (planAll p).2.i = (plan p).length := by
    rw [planAll, planItems_i, plan_length]; simp [w0, planAll]
  obtain ⟨hnil, hb⟩ := ret_fwd hrun
  rw [hend, List.drop_eq_nil_iff] at hnil
  have htl : tr.length = (plan p).length := by have := hR'.len; rw [hend] at this; omega
  have hoff : s'.off = π.size := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hb; exact hb.1
  have hpend' : s'.pend = π.size := by have := hR'.off; rw [hpend] at this; omega
  have hpre := hR'.pre
  rw [hpend', size_bl, List.take_length, hend, bodyTo_length] at hpre
  refine ⟨ba_ext (by rw [bl_reassemble]; exact hpre.symm), htl, fun i hi => hR'.good i (by rw [hend]; omega)⟩

/-! ## `V_S` -/

/-- **The plan's entries hold the proof's body**: `8 + Σ clen = piSize p` (decided per parameter set). -/
def PlanBytes (p : Params) : Prop := pOff (plan p) (plan p).length = piSize p

/-- **Round trip** (BLUEPRINT §2.2): if `V_S` accepts `π` on the trace `tr`, then `tr` is a trace of
the schedule and it carries `π`. -/
theorem VS_roundtrip (p : Params) (m : M3) (vk c : Digest) (hP : PlanOk p) (hB : PlanBytes p)
    (π : ByteArray) (tr : Trace) (h : (VS p m vk c π).runSeq tr = some true) :
    reassemble p tr = π ∧ LinkOk p tr := by
  cases hp : parseOk p vk c π with
  | false => simp only [VS, hp] at h; exact absurd (ret_fwd h).2 (by simp)
  | true =>
    simp only [VS, hp, ite_true] at h
    have hp' := hp
    simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
    obtain ⟨⟨⟨hsize, h0⟩, hz⟩, -⟩ := hp'
    have hsz : pOff (plan p) (plan p).length ≤ π.size := by rw [hB, hsize]
    have h8 : 8 ≤ π.size := le_trans (by simp [pOff]) hsz
    exact drive_fwd p hP π tr _ hsz (take8_of_parse h8 h0 hz) h

/-! ## The production and test sets -/

set_option maxRecDepth 200000 in
theorem planBytes_P20 : PlanBytes P20 := by unfold PlanBytes; rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
theorem planBytes_P8 : PlanBytes P8 := by unfold PlanBytes; rw [P8_eq]; decide +kernel

theorem VS20_roundtrip (tabs : Pub → List M3.Tab) (vk c : Digest) (π : ByteArray) (tr : Trace)
    (h : (VSL P20 tabs vk c π).runSeq tr = some true) :
    reassemble P20 tr = π ∧ LinkOk P20 tr :=
  VS_roundtrip P20 (M3.real P20 tabs) vk c planOk_P20 planBytes_P20 π tr h

theorem VS8_roundtrip (tabs : Pub → List M3.Tab) (vk c : Digest) (π : ByteArray) (tr : Trace)
    (h : (VSL P8 tabs vk c π).runSeq tr = some true) :
    reassemble P8 tr = π ∧ LinkOk P8 tr :=
  VS_roundtrip P8 (M3.real P8 tabs) vk c planOk_P8 planBytes_P8 π tr h

end Lvm.Replay
