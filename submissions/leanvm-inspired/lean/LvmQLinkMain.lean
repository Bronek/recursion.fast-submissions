-- New for lvm (WP-11b-QL): Q_link end to end — its static checks as one Boolean, replay from Q_link's
-- rows, the bridge to WP-8's sponge hypotheses, and the instances at P20 and P8.
import LvmQLinkSound
import LvmQBuildWf
import LvmReplay
import LvmSpongeTable
import LvmPlanP20

/-!
# Q_link end to end

* `qOk_of`: Q_link's static conditions `QOk` from one decidable Boolean `qOkB` (the bounds of the
  QLT entries are proved, not checked).
* **`qlink_replay`**: where Q_link's rows and assertions hold (any memory: the committed one by
  `loopir_sound`, or the interpreter's), with its inputs in place, `V_S` on the proof the stream's
  trace reassembles runs exactly that trace and returns `V_S`'s decision `F` on the hashed bytes `Σ`
  of the stream; and the padding of `Σ`'s last sponge block is pinned.
  `qlink_interp_replay`: the same from `interp (Q_link) = ok` (BLUEPRINT §4.6's `replay`).
* **`padOk_KS`, `streamOf_KS`**: WP-8's `traceDigest_of_KS` hypotheses `PadOk (msgBytes msg) L` and
  `streamOf (msgBytes msg) L = tagTrace :: traceBytes tr`, for `KS` message lanes holding the stream
  (`msg i l` = lane `17 i + l`).
* At `P20`/`P8`: the layouts `lay20`/`lay8`, `StreamOk`, `QOk` and the program check (`segsOk`, hence
  `wf`) decided; `ksLog = recRowsLog + 1`.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## The static conditions as one Boolean -/

/-- Q_link's static conditions, decidable (the QLT bounds follow from `StreamOk`). -/
def qOkB (p : Params) (lay : Layout) : Bool :=
  decide ((qltEntries p lay).length ≤ 2 ^ lay.aQ) && decide (hashedLen p / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) && decide (hashedLen p < 2 ^ 64) &&
    ((opens p).all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide (((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa)

theorem lane1C_lt : lane1C < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp [q0Bytes])

theorem padLane_lt (L q : Nat) : padLane L q < 2 ^ 64 := lt_of_lt_of_le (ofLE_lt _) (by simp)

section
variable {p : Params} {lay : Layout}

theorem hashedLen_mod (hS : StreamOk p) : hashedLen p % 8 = 0 := by
  have := bOff_mod hS.1 (plan p).length (by have := plan_length_ge p; omega) le_rfl
  rw [bOff_end, ← hS.2] at this; exact this

/-- **The QLT entries' bounds**, from the plan's stream facts. -/
theorem qbound_of (hS : StreamOk p) (hT2 : 17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) (h64 : hashedLen p < 2 ^ 64) :
    ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
      e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64 := by
  have hL8 := hashedLen_mod hS
  have hL48 := hashedLen_ge hS
  have hLb : hashedLen p / 8 + 5 ≤ 2 ^ lay.m := by simp only [nBlk] at hT2; omega
  intro e he
  simp only [qltEntries, List.mem_append] at he
  rcases he with (h01 | hmid) | hpad
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h01
    rcases h01 with rfl | rfl <;> dsimp only
    · exact ⟨le_rfl, by omega, by omega, by omega, by simp [lane0C]⟩
    · exact ⟨by omega, by omega, by omega, by omega, lane1C_lt⟩
  · obtain ⟨⟨pe, i⟩, hx, hf⟩ := List.mem_filterMap.mp hmid
    have hgi := List.mem_zipIdx_iff_getElem?.mp hx
    simp only at hgi hf
    have hi : i < (plan p).length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hgi; cases hgi
    have hpe : (plan p).getD i default = pe := by
      rw [List.getD_eq_getElem?_getD, hgi, Option.getD_some]
    split at hf
    · next st hk =>
      cases hf
      have hok := streamOk_entry hS.1 hi
      rw [hpe] at hok
      simp only [entryOk, hk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨h32, hst⟩, h1⟩ := hok
      have hin := lanes_in hS h1 hi
      rw [hpe] at hin
      have h8 := streamOk_len hS.1 h1 hi
      rw [hpe] at h8
      have hans : ansLane p st + 4 ≤ hashedLen p / 8 := by
        by_cases h0 : st = 0
        · subst h0; simp only [ansLane, ite_true]; omega
        · have := lanes_in hS (i := st) (by omega) (by omega)
          simp only [ansLane, h0, ite_false]; omega
      dsimp only
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases hf
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hpad
    rw [List.mem_range] at hk
    simp only [nBlk] at hT2 hk ⊢
    exact ⟨by omega, by omega, by omega, by omega, padLane_lt _ _⟩

theorem qOk_of (hS : StreamOk p) (h : qOkB p lay = true) : QOk p lay := by
  simp only [qOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, qbound_of hS h3 h4, h2, fun o ho => ?_, h6⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h5 o ho
  exact ⟨a1, a2, a3, a4, a5⟩

end

/-! ## Replay from Q_link's rows -/

/-- **`Σ`**: the hashed bytes of the stream (the bytes `V_S`'s decision `F` reads). -/
def sigma (p : Params) (ws : List Word) : ByteArray := ⟨((wordsBytes ws).take (hashedLen p)).toArray⟩

theorem traceBytesB_decode {p : Params} {ws : List Word} (hS : StreamOk p) (hL : LaneLink p ws) :
    traceBytesB (decode p ws) = sigma p ws := by
  apply ba_ext
  rw [sigma, bl_mk, stream_of_laneLink hS hL]
  exact traceBytesB_data _

theorem ctxOf_cells (Q : Program) : (ctxOf Q).cells = Q.cells := rfl

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Replay** (BLUEPRINT §4.6), from Q_link's rows and assertions: `V_S` on the proof that the
stream's trace reassembles asks exactly that trace and answers `F` on `Σ`; `Σ`'s padding is pinned. -/
theorem qlink_replay (m : M3) (vk cd : Digest) (hP : PlanOk p) (hS : StreamOk p) (hQ : QOk p lay)
    (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink p lay pt).2) (hA : SegsAssert M pt (qlink p lay pt).2)
    (hparse : parseOk p vk cd (reassemble p (decode p ws)) = true) :
    (VS p m vk cd (reassemble p (decode p ws))).runSeq (decode p ws) = some (decideF p m vk cd (sigma p ws)) ∧
      LinkOk p (decode p ws) ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  obtain ⟨hL, hpad⟩ := qlink_sound hS hQ hin hws hinj hN hNs h hA
  refine ⟨?_, linkOk_of_laneLink hS hL, hpad⟩
  rw [VS_replay p m vk cd hP _ (linkOk_of_laneLink hS hL) hparse, traceBytesB_decode hS hL]

/-- **Replay from the interpreter** (BLUEPRINT §4.6's `interp Q_link Σ = true → …`): Q_link alone as a
LoopIR program on `nK` input cells. -/
theorem qlink_interp_replay (m : M3) (vk cd : Digest) (hP : PlanOk p) (hS : StreamOk p) (hQ : QOk p lay)
    (nK : Nat) (hseg : segsOk ⟨nK, 0⟩ (qlink p lay ⟨nK, 0⟩).2 = true) (inK : Array FK) (hsz : inK.size = nK)
    (hinj : GInj (max ((toProgram nK 0 (qlink p lay)).cells .K) ((toProgram nK 0 (qlink p lay)).cells .E)))
    (hNs : lay.sb + 2 ^ lay.m ≤ (toProgram nK 0 (qlink p lay)).cells .K)
    (hinb : ((toProgram nK 0 (qlink p lay)).interp inK #[]).inb = true)
    (hok : ((toProgram nK 0 (qlink p lay)).interp inK #[]).ok = true)
    (hin : QIn p lay ws ((toProgram nK 0 (qlink p lay)).interpMem inK #[])) (hws : 2 ^ lay.m ≤ ws.length)
    (hparse : parseOk p vk cd (reassemble p (decode p ws)) = true) :
    (VS p m vk cd (reassemble p (decode p ws))).runSeq (decode p ws) = some (decideF p m vk cd (sigma p ws)) ∧
      LinkOk p (decode p ws) ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  obtain ⟨hH, hOk, -⟩ := toProgram_interp nK 0 (qlink p lay) (toProgram_wf _ _ _ hseg) inK #[] ⟨hsz, rfl⟩
    hinj hinb
  have hc := ctxOf_cells (toProgram nK 0 (qlink p lay))
  exact qlink_replay m vk cd hP hS hQ hin hws hinj (by rw [hc]; exact le_max_left _ _)
    (le_trans hNs (le_max_left _ _)) hH (hOk.mp hok) hparse

end

/-! ## WP-8's sponge hypotheses (`traceDigest_of_KS`) -/

theorem u64_byte (x : UInt64) (b : Nat) (hb : b < 8) :
    (x >>> (8 * b).toUInt64).toUInt8 = (x.toNat / 256 ^ b % 256).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h1 : ((8 * b).toUInt64).toNat % 64 = 8 * b := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h1, Nat.shiftRight_eq_div_pow,
    show (256 : Nat) ^ b = 2 ^ (8 * b) by rw [Nat.pow_mul]]
  simp [Nat.toUInt8]

section
variable {ws : List Word} {msg : ℕ → ℕ → LeanVM.Parameters.K}

/-- A `KS` message byte is the stream's byte, when `KS`'s message lanes hold the stream
(`msg i l` = lane `17 i + l`, rows `i < B`). -/
theorem msgBytes_eq {B : Nat} (hmsg : ∀ i < B, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    {n : Nat} (hn : n < 136 * B) : KG.msgBytes msg (n / 136) (n % 136) = (wordsBytes ws).getD n 0 := by
  have hn : n = 8 * (n / 8) + n % 8 := by omega
  conv_rhs => rw [hn]
  rw [byte_of_lane ws _ _ (Nat.mod_lt _ (by decide)), KG.msgBytes, show n % 136 % 8 = n % 8 by omega,
    u64_byte _ _ (Nat.mod_lt _ (by decide)), hmsg _ (by omega) _ (by omega), show 17 * (n / 136) + n % 136 / 8 = n / 8 by omega]

/-- **The bytes `KS`'s first rows absorb are the stream's.** -/
theorem streamOf_KS (L : Nat)
    (hmsg : ∀ i < nBlk L, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    (hL : L ≤ 8 * ws.length) : KSponge.streamOf (KG.msgBytes msg) L = (wordsBytes ws).take L := by
  apply List.ext_getElem
  · rw [KSponge.streamOf_length, List.length_take, wordsBytes_length]; omega
  · intro n h1 h2
    rw [KSponge.streamOf_length] at h1
    have e := KSponge.streamOf_getD (KG.msgBytes msg) L h1
    rw [List.getD_eq_getElem _ _ (by rw [KSponge.streamOf_length]; exact h1)] at e
    rw [e, List.getElem_take, ← List.getD_eq_getElem _ 0 (by rw [List.length_take] at h2; omega)]
    exact msgBytes_eq hmsg (by simp only [nBlk]; omega)

/-- **WP-8's `PadOk`** for the `KS` rows that hold the stream, from Q_link's `PadOkB`. -/
theorem padOk_KS (L : Nat)
    (hmsg : ∀ i < nBlk L, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    (h : PadOkB (wordsBytes ws) L) : KSponge.PadOk (KG.msgBytes msg) L := by
  intro q h1 h2
  exact (msgBytes_eq hmsg h2).trans (h q h1 h2)

/-- **WP-8's stream hypothesis**: the `KS` rows that hold the stream absorb `tagTrace ‖ traceBytes`
of the trace the stream encodes. -/
theorem streamOf_KS_trace {p : Params} (hS : StreamOk p) (hL : LaneLink p ws)
    (hmsg : ∀ i < nBlk (hashedLen p), ∀ l < 17,
      (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l)) :
    KSponge.streamOf (KG.msgBytes msg) (hashedLen p) = tagTrace :: traceBytes (decode p ws) := by
  rw [streamOf_KS _ hmsg hL.size, stream_of_laneLink hS hL]

end

/-! ## The instances at `P20` and `P8` -/

/-- Q_link's standalone layout: the stream at cells `0 …` (the `17 · 2^rec` stream lanes, or the
`readd` region's `2^m` if larger: `P8`), then the QLT table, the gate cell, the position bits, the positions' BITS fields (low, then high). -/
def layOf (p : Params) (aQ K m pa : Nat) : Layout :=
  let qt := max (17 * 2 ^ p.recRowsLog) (2 ^ m)
  let fg := qt + 3 * 2 ^ aQ
  ⟨0, fg, qt, fg + 1, m, K, aQ, fg + 1 + ((opens p).map fun o => padT o.L.t * o.L.height).sum, pa⟩

/-- The input cells of the standalone layout. -/
def nInKOf (lay : Layout) : Nat := lay.fl + 2 * 2 ^ lay.pa

/-- At `P20`: 2^11 QLT iterations (1,500 entries), step array 2^8, `readd` region 2^18 lanes, 2^10
position cells (991 positions). -/
def lay20 : Layout := layOf P20 11 8 18 10

/-- At `P8`: 2^10 QLT iterations (914 entries), step array 2^5, `readd` region 2^17 lanes (the
stream's 55,185 lanes pass 2^16; as `LvmQAsmLay.cfg8`), 2^8 position cells (156 positions). -/
def lay8 : Layout := layOf P8 11 5 17 8

theorem ksLog_P20 : P20.ksLog = P20.recRowsLog + 1 := by decide

theorem ksLog_P8 : P8.ksLog = P8.recRowsLog + 1 := by decide

/-- WP-16b: from the plan's one-pass decision (`LvmPlanP20`) and `sizes_P20`'s hashed length. -/
theorem streamOk_P20 : StreamOk P20 :=
  ⟨Lvm.PlanChk.streamOkL_P20, by rw [sizes_P20.2.2.2.2.2.1, Lvm.PlanChk.slen_P20]⟩

set_option maxRecDepth 200000 in
theorem streamOk_P8 : StreamOk P8 := by rw [P8_eq]; exact ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 200000 in
theorem qOk_P20 : QOk P20 lay20 :=
  qOk_of streamOk_P20 (by show qOkB P20 (layOf P20 11 8 18 10) = true; rw [P20_eq]; decide +kernel)

set_option maxRecDepth 200000 in
theorem qOk_P8 : QOk P8 lay8 :=
  qOk_of streamOk_P8 (by show qOkB P8 (layOf P8 11 5 17 8) = true; rw [P8_eq]; decide +kernel)

set_option maxRecDepth 200000 in
/-- Q_link's program check at `P20` (so `(toProgram …).wf`, by `toProgram_wf`). -/
theorem segsOk_P20 : segsOk ⟨nInKOf lay20, 0⟩ (qlink P20 lay20 ⟨nInKOf lay20, 0⟩).2 = true := by
  show segsOk ⟨nInKOf (layOf P20 11 8 18 10), 0⟩
    (qlink P20 (layOf P20 11 8 18 10) ⟨nInKOf (layOf P20 11 8 18 10), 0⟩).2 = true
  rw [P20_eq]; decide +kernel

set_option maxRecDepth 200000 in
theorem segsOk_P8 : segsOk ⟨nInKOf lay8, 0⟩ (qlink P8 lay8 ⟨nInKOf lay8, 0⟩).2 = true := by
  show segsOk ⟨nInKOf (layOf P8 11 5 17 8), 0⟩
    (qlink P8 (layOf P8 11 5 17 8) ⟨nInKOf (layOf P8 11 5 17 8), 0⟩).2 = true
  rw [P8_eq]; decide +kernel

section
variable {ws : List Word} {c : Ctx} {M : Mem}

/-- **Replay at `P20`** from Q_link's rows (`V_S` = `VSL P20 tabs`, any tables). -/
theorem qlink20_replay (tabs : Pub → List M3.Tab) (vk cd : Digest) (hin : QIn P20 lay20 ws M) (hws : 2 ^ 18 ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : 2 ^ 18 ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink P20 lay20 pt).2) (hA : SegsAssert M pt (qlink P20 lay20 pt).2)
    (hparse : parseOk P20 vk cd (reassemble P20 (decode P20 ws)) = true) :
    (VSL P20 tabs vk cd (reassemble P20 (decode P20 ws))).runSeq (decode P20 ws) =
        some (decideF P20 (M3.real P20 tabs) vk cd (sigma P20 ws)) ∧
      LinkOk P20 (decode P20 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P20) :=
  qlink_replay (M3.real P20 tabs) vk cd planOk_P20 streamOk_P20 qOk_P20 hin hws hinj hN
    (by simp only [lay20, layOf]; omega) h hA hparse

/-- **Replay at `P8`** from Q_link's rows. -/
theorem qlink8_replay (tabs : Pub → List M3.Tab) (vk cd : Digest) (hin : QIn P8 lay8 ws M) (hws : 2 ^ 17 ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : 2 ^ 17 ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink P8 lay8 pt).2) (hA : SegsAssert M pt (qlink P8 lay8 pt).2)
    (hparse : parseOk P8 vk cd (reassemble P8 (decode P8 ws)) = true) :
    (VSL P8 tabs vk cd (reassemble P8 (decode P8 ws))).runSeq (decode P8 ws) =
        some (decideF P8 (M3.real P8 tabs) vk cd (sigma P8 ws)) ∧
      LinkOk P8 (decode P8 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P8) :=
  qlink_replay (M3.real P8 tabs) vk cd planOk_P8 streamOk_P8 qOk_P8 hin hws hinj hN
    (by simp only [lay8, layOf]; omega) h hA hparse

end

end Lvm.QLink
