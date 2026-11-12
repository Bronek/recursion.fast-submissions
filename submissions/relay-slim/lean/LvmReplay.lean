-- New for lvm (WP-11b-QL): the replay theorem of BLUEPRINT §4.6 for lvm's driver. The statement's
-- shape is FR's (`FRVIRSpecCore.runSeq_runIR`, `FRNodeReadCore.readTrace_of_stream`; rf-k@8bff272b).
import LvmReplayDrive
import LvmVerifierS

/-!
# Replay (BLUEPRINT §4.6)

**`VS_replay`**: for every parameter set whose plan passes its static checks (`PlanOk`), every
trace `tr` that is a trace of the schedule (`LinkOk p tr`: the plan's length, and at every entry
the plan's query length and link, which is what Q_link asserts on the stream), and a header that
`V_S` accepts natively,

  `(V_S vk c (reassemble p tr)).runSeq tr = some (F vk c (traceBytesB tr))`,

where `F = decideF p m vk c` is `V_S`'s decision on the stream `Σ = tagTrace ‖ traceBytes tr`.
`drive_replay` is the driver alone (no header check), for any decision `F`.

The proof (`LvmReplayDrive`) runs the driver item by item against the walk that defines the plan:
every query the driver forms from `π = reassemble p tr` and the answers so far is the trace's
entry, because `π` is the concatenation of the entries' contributions and every entry starts with
the state, holds the current node in the half its position bit selects, and ends each path on the
cap node. At the end every body byte has been read (`off = |π|`) and the log is `tr`.

`PlanOk P20`, `PlanOk P8` are decided; `plan_P20`/`plan_P8` check the plan against
WP-11a's schedule tallies (`qS`, `piSize`, the query lengths of `queryList`).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

theorem items_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (k : DSt → OProg Bool) :
    ∀ (its : List Item) (w : WS) (s : DSt), Inv p tr π s w → PosInv p tr s w →
    (planItems p w its).2.ok = true → Al (plan p) w.i (planItems p w its).1 →
    ∃ s', Inv p tr π s' (planItems p w its).2 ∧ PosInv p tr s' (planItems p w its).2 ∧
      (driveItems p π its s k).runSeq (tr.drop w.i) = (k s').runSeq (tr.drop (planItems p w its).2.i)
  | [], w, s, hI, hPo, _, _ => ⟨s, hI, hPo, by simp only [planItems, driveItems]⟩
  | it :: its, w, s, hI, hPo, hok, hal => by
    obtain ⟨hal1, hal2⟩ := Al_planItems p hal
    have hok1 : (planItem p w it).2.ok = true := planItems_ok p _ its hok
    obtain ⟨s1, hI1, hPo1, hrun1⟩ := item_step hn hG k its it w s hI hPo hok1 hal1
    obtain ⟨s', hI', hPo', hrun'⟩ := items_run hn hG k its _ s1 hI1 hPo1 hok hal2
    exact ⟨s', hI', hPo', by rw [hrun1, hrun']; rfl⟩

theorem plan_length (p : Params) : (plan p).length = 2 + (planAll p).1.length := by
  simp [plan]; omega

theorem bl_reassemble (p : Params) (tr : Trace) : bl (reassemble p tr) = hdr8 ++ bodyFrom tr (plan p) 0 :=
  bl_mk _

/-- **Replay of the driver**: on a trace of the schedule, the driver on the reassembled proof asks
exactly the trace and returns `F` of its stream. -/
theorem drive_replay (p : Params) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr) (F : ByteArray → Bool) :
    (drive p (reassemble p tr) F).runSeq tr = some (F (traceBytesB tr)) := by
  obtain ⟨hn, hG⟩ := hL
  have hlen2 : 2 ≤ tr.length := by rw [hn, plan_length]; omega
  set π := reassemble p tr with hπ
  set P := plan p with hPdef
  -- the first two entries
  have hP0 : P.getD 0 default = ⟨.q0, 7⟩ := rfl
  have hP1 : P.getD 1 default = ⟨.fs 0, seedLen⟩ := rfl
  obtain ⟨-, hq0⟩ := (show Good tr 0 ⟨.q0, 7⟩ by rw [← hP0]; exact hG 0 (by omega))
  obtain ⟨hs1, hq1⟩ := (show Good tr 1 ⟨.fs 0, seedLen⟩ by rw [← hP1]; exact hG 1 (by omega))
  simp only at hq0 hq1 hs1
  have hPl : 2 ≤ (plan p).length := by rw [← hPdef, ← hn]; exact hlen2
  have hbody0 : (bl π).drop 8 = (bl (qOf tr 1)).drop 32 ++ bodyFrom tr P 2 := by
    rw [hπ, bl_reassemble, List.drop_left' (by rfl : hdr8.length = 8), bodyFrom_cons _ _ (by omega),
      bodyFrom_cons _ _ (by omega), hP0, hP1]
    rfl
  have hcl1 : ((bl (qOf tr 1)).drop 32).length = headerBytes - 8 := by
    rw [List.length_drop, ← size_bl, hs1]; rfl
  have hseed : seedQuery π (aOf tr 0) = qOf tr 1 := by
    apply ba_ext
    rw [seedQuery, bl_append, bl_digestBytes, ← hq1,
      show headerBytes = 8 + (headerBytes - 8) by decide, bl_extract_body hbody0 hcl1, List.take_append_drop]
  have hle8 : 8 ≤ π.size := by rw [size_bl, hπ, bl_reassemble]; simp [hdr8]
  have hbodyH : (bl π).drop headerBytes = bodyFrom tr P 2 := by
    rw [show headerBytes = 8 + ((bl (qOf tr 1)).drop 32).length by rw [hcl1]; decide, ← List.drop_drop,
      hbody0, List.drop_left]
  have hleH : headerBytes ≤ π.size := by
    have := le_of_body hbody0 hle8; rw [hcl1] at this; have h8 : 8 + (headerBytes - 8) = headerBytes := by decide
    omega
  -- the walk from entry 2
  have hI0 : Inv p tr π ⟨headerBytes, headerBytes, aOf tr 1,
      [(seedQuery π (aOf tr 0), aOf tr 1), (q0Query, aOf tr 0)], [], []⟩ w0 := by
    refine ⟨?_, rfl, rfl, hbodyH, hleH, List.Forall₂.nil⟩
    show _ = (tr.take 2).reverse
    rw [hseed, ← hq0]
    have e0 := entry_eq tr (i := 0) (by omega)
    have e1 := entry_eq tr (i := 1) (by omega)
    rw [show 2 = 0 + 1 + 1 from rfl, List.take_add_one, List.take_add_one, List.take_zero,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), ← e0, ← e1]
    rfl
  have hal : Al P w0.i (planAll p).1 := by
    refine ⟨by simp only [w0, hPdef, plan_length]; omega, fun x hx => ?_⟩
    simp only [w0, hPdef, plan, List.getD_eq_getElem?_getD]
    rw [show 2 + x = x + 1 + 1 by omega]
    simp
  obtain ⟨hok, hpend, -⟩ := hP
  obtain ⟨s', hI', -, hrun⟩ := items_run (π := π) hn hG
    (fun s => .ret (s.off == π.size && F (streamOf s.log))) (schedule p) w0 _ hI0
    (fun _ h => by simp [w0] at h) hok hal
  have hend : (planAll p).2.i = tr.length := by
    rw [planAll, planItems_i, hn, plan_length]; simp [w0, planAll]
  have hoff : s'.off = π.size := by
    have h1 := hI'.off
    have h2 := hI'.body
    have h3 := hI'.le
    rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl] at h1 h2
    rw [hpend] at h1
    rw [hend, hn, bodyFrom_end _ _ le_rfl, List.drop_eq_nil_iff, ← size_bl] at h2
    omega
  have hlog : s'.log = tr.reverse := by
    rw [hI'.log, show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.take_length]
  -- run
  have htr : tr = (qOf tr 0, aOf tr 0) :: (qOf tr 1, aOf tr 1) :: tr.drop 2 := by
    rw [← drop_cons_getD tr (i := 1) (by omega), ← drop_cons_getD tr (i := 0) (by omega)]; rfl
  have hrun' := hrun
  rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.drop_length] at hrun'
  conv_lhs => rw [htr]
  simp only [drive, OProg.runSeq, hq0, ite_true, hseed]
  simp only [w0, hseed] at hrun'
  rw [hrun']
  simp [OProg.runSeq, hoff, hlog, streamOf]

/-- **Replay** (BLUEPRINT §4.6, generic over the schedule): on a trace of the schedule whose
reassembled proof passes `V_S`'s native header checks, `V_S` asks exactly the trace and returns its
decision `F vk c Σ` on the trace's stream. -/
theorem VS_replay (p : Params) (m : M3) (vk c : Digest) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (hparse : parseOk p vk c (reassemble p tr) = true) :
    (VS p m vk c (reassemble p tr)).runSeq tr = some (decideF p m vk c (traceBytesB tr)) := by
  simp only [VS, hparse, ite_true]
  exact drive_replay p hP tr hL _

/-! ## The production and test sets -/

/-- `P20` with its WHIR levels written out (`levels_P20`, `t_P20`), so that the kernel does not
recompute the query counts at every use. -/
def P20L : Params := { P20 with
  mainLevels := [⟨0, 6, 18, 1, 19, 8, 11, 230, 512⟩, ⟨1, 4, 14, 2, 16, 7, 9, 115, 384⟩,
    ⟨2, 4, 10, 3, 13, 7, 6, 77, 384⟩]
  recLevels := [⟨0, 6, 13, 2, 15, 7, 8, 170, 512⟩, ⟨1, 4, 9, 3, 12, 7, 5, 139, 384⟩] }

/-- `P8` with its WHIR levels written out. -/
def P8L : Params := { P8 with
  mainLevels := [⟨0, 6, 17, 1, 18, 4, 14, 33, 512⟩, ⟨1, 4, 13, 2, 15, 4, 11, 17, 384⟩,
    ⟨2, 4, 9, 3, 12, 4, 8, 11, 384⟩]
  recLevels := [⟨0, 6, 12, 2, 14, 4, 10, 24, 512⟩, ⟨1, 4, 8, 3, 11, 4, 7, 20, 384⟩] }

theorem P20_eq : P20 = P20L := by
  have h1 : P20.mainLevels = P20L.mainLevels := by decide +kernel
  have h2 : P20.recLevels = P20L.recLevels := by decide +kernel
  show P20 = { P20 with mainLevels := P20L.mainLevels, recLevels := P20L.recLevels }
  rw [← h1, ← h2]

theorem P8_eq : P8 = P8L := by
  have h1 : P8.mainLevels = P8L.mainLevels := by decide +kernel
  have h2 : P8.recLevels = P8L.recLevels := by decide +kernel
  show P8 = { P8 with mainLevels := P8L.mainLevels, recLevels := P8L.recLevels }
  rw [← h1, ← h2]

set_option maxRecDepth 200000 in
/-- `PlanOk P20` and the walk's last entry (WP-16b: one decision; the plan's length from it by
`plan_length`, `planItems_i`, without evaluating the entries). -/
theorem planSt_P20 : PlanOk P20 ∧ (planAll P20).2.i = 8295 := by rw [P20_eq]; decide +kernel

theorem planOk_P20 : PlanOk P20 := planSt_P20.1

set_option maxRecDepth 200000 in
theorem planOk_P8 : PlanOk P8 := by rw [P8_eq]; decide +kernel

/-- The plan has `qS` entries (8,295 at `P20`; WP-0's frozen count). -/
theorem plan_P20 : (plan P20).length = 8295 := by
  have h := planItems_i P20 w0 (schedule P20)
  have h2 : (planItems P20 w0 (schedule P20)).2.i = 8295 := planSt_P20.2
  have hw : w0.i = 2 := rfl
  rw [plan_length, planAll]
  omega

set_option maxRecDepth 200000 in
theorem plan_P8 : (plan P8).length = 2321 := by rw [P8_eq]; decide +kernel

theorem VS20_replay (tabs : Pub → List M3.Tab) (vk c : Digest) (tr : Trace) (hL : LinkOk P20 tr)
    (hparse : parseOk P20 vk c (reassemble P20 tr) = true) :
    (VSL P20 tabs vk c (reassemble P20 tr)).runSeq tr = some (decideF P20 (M3.real P20 tabs) vk c (traceBytesB tr)) :=
  VS_replay P20 (M3.real P20 tabs) vk c planOk_P20 tr hL hparse

theorem VS8_replay (tabs : Pub → List M3.Tab) (vk c : Digest) (tr : Trace) (hL : LinkOk P8 tr)
    (hparse : parseOk P8 vk c (reassemble P8 tr) = true) :
    (VSL P8 tabs vk c (reassemble P8 tr)).runSeq tr = some (decideF P8 (M3.real P8 tabs) vk c (traceBytesB tr)) :=
  VS_replay P8 (M3.real P8 tabs) vk c planOk_P8 tr hL hparse

end Lvm.Replay
