-- New for lvm (WP-11b-QL): Q_link's soundness, from its gadgets' specifications.
import LvmQLink

/-!
# Q_link is sound: its rows and assertions give `LaneLink` and the padding

`qlink_sound`: in any memory where Q_link's rows hold and its assertions hold (the committed memory
by `loopir_sound`, or the interpreter's), with the inputs where `Layout` says (`QIn`: the stream lanes,
the QLT table, the position bits from BITS, the flag `1`), the plan's static checks (`QOk`) and
`g`-powers injective below the cell counts, the stream meets every lane condition of the schedule
(`LaneLink`) and its last sponge block is padded (`PadOkB`, WP-8's `PadOk`).
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## Lanes as cells -/

/-- Stream lane `j` as a `K` value. -/
def laneK (ws : List Word) (j : Nat) : FK := ⟨UInt64.ofBitVec (ws.getD j 0)⟩

theorem laneK_val (ws : List Word) (j : Nat) : (laneK ws j).val.toNat = lw ws j := rfl

theorem lw_of_laneK {ws : List Word} {j j' : Nat} (h : laneK ws j = laneK ws j') : lw ws j = lw ws j' := by
  rw [← laneK_val, h, laneK_val]

theorem kOf_toNat {v : Nat} (hv : v < 2 ^ 64) : (kOf v).val.toNat = v := by
  have : v < 18446744073709551616 := lt_of_lt_of_eq hv (by norm_num)
  simp [kOf, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt this]

theorem lw_of_kOf {ws : List Word} {j v : Nat} (hv : v < 2 ^ 64) (h : laneK ws j = kOf v) : lw ws j = v := by
  rw [← laneK_val, h, kOf_toNat hv]

/-! ## Extracting a gadget's rows from a program -/

theorem seqAll_both {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)) (p : Ptr), SegsHold c M p (seqAll ms p).2 → SegsAssert M p (seqAll ms p).2 →
      ∀ m ∈ ms, ∃ q, SegsHold c M q (m q).2 ∧ SegsAssert M q (m q).2
  | [], _, _, _, _, h => by simp at h
  | m :: ms, p, h, hA, m', hm => by
    simp only [seqAll] at h hA
    rw [hold_bind] at h; rw [assert_bind] at hA
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨p, h.1, hA.1⟩
    · rw [hold_bind] at h; rw [assert_bind] at hA
      exact seqAll_both ms _ h.2.1 hA.2.1 m' hm

/-! ## The step array -/

theorem stepArr_apply (K : Nat) (g : Cell) (p : Ptr) :
    (stepArr K g p).1 = p.k := rfl

theorem stepArr_spec {c : Ctx} {M : Mem} {p : Ptr} {K g : Nat} (h : SegsHold c M p (stepArr K (kc g) p).2) :
    (∀ x < 2 ^ K, M.k (p.k + x) = M.k g) ∧ (∀ x < 2 ^ K, M.k (p.k + 2 ^ K + x) = 0) := by
  simp only [stepArr] at h
  rw [hold_bind] at h
  obtain ⟨-, h⟩ := h
  simp only [getPtr, Ptr.adv_nil] at h
  rw [hold_bind] at h
  obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨h2, -⟩ := h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have e := lrel_lin (t := 0) rfl (loop_rel h1 (jf := x) (by simpa using hx) (by simp))
    simp only [List.getD_cons_zero, List.getD_cons_succ, Cell.val_opd, Cell.val_K, ofK_zero, zero_mul,
      add_zero, LoopOut.cell_val] at e
    simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
      List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at] at e
    simpa [Mem.rd] using ofK_inj e
  · have e := lrel_lin (t := 0) rfl (loop_rel h2 (jf := x) (by simpa using hx) (by simp))
    simp only [List.getD_cons_zero, List.getD_cons_succ, Cell.val_opd, Cell.val_K, ofK_one, one_mul,
      ofK_zero, add_zero, LoopOut.cell_val] at e
    simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
      List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at, Ptr.adv, segsW, Seg.w, Block.tw,
      Block.size, Block.lsize, mkLoop] at e
    rw [← ofK_add, FK.add_self] at e
    simpa [Mem.rd, Nat.add_assoc] using ofK_inj e

/-! ## Inputs and static conditions -/

/-- **Where Q_link's inputs are**, and the flag. -/
structure QIn (p : Params) (lay : Layout) (ws : List Word) (M : Mem) : Prop where
  /-- The node flag is on. -/
  flag : M.k lay.fg = 1
  /-- The stream region holds the stream's lanes. -/
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK ws j
  /-- The QLT table. -/
  table : ∀ x < (qltData p lay).length, M.k (lay.qt + x) = (qltData p lay).getD x 0
  /-- The position bits (BITS): bit `z` of position `j` of opening `k`. -/
  bits : ∀ k < (opens p).length, ∀ j < ((opens p).getD k default).L.t,
    ∀ z < ((opens p).getD k default).L.height,
    M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) =
      if ansBit p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height + z)
      then 1 else 0

/-- **Q_link's static conditions** (decided per parameter set and layout). -/
structure QOk (p : Params) (lay : Layout) : Prop where
  qlen : (qltEntries p lay).length ≤ 2 ^ lay.aQ
  qbound : ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
    e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64
  hT : hashedLen p / 8 + 17 ≤ 2 ^ lay.m
  opens : ∀ o ∈ opens p, 1 ≤ o.L.path ∧ o.L.path < o.L.height ∧ (∀ c ∈ pchunks o.L.t, c.2 ≤ lay.K) ∧
    eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m ∧ o.L.row < 2 ^ 64
  /-- The position cells cover every position. -/
  pos : ((Lvm.QLink.opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa

theorem qltPadded_length (p : Params) (lay : Layout) (h : (qltEntries p lay).length ≤ 2 ^ lay.aQ) :
    (qltPadded p lay).length = 2 ^ lay.aQ := by
  simp [qltPadded]; omega

theorem tblOf_length : ∀ l : List (Nat × Nat × Nat), (tblOf l).length = 3 * l.length
  | [] => rfl
  | _ :: l => by simp [tblOf, tblOf_length l]; ring

theorem tblOf_getD : ∀ (l : List (Nat × Nat × Nat)) {k : Nat}, k < l.length →
      (tblOf l).getD (3 * k) 0 = Build.gpow (l.getD k (0, 0, 0)).1 ∧
      (tblOf l).getD (3 * k + 1) 0 = Build.gpow (l.getD k (0, 0, 0)).2.1 ∧
      (tblOf l).getD (3 * k + 2) 0 = kOf (l.getD k (0, 0, 0)).2.2
  | [], _, hk => by simp at hk
  | e :: l, 0, _ => by simp [tblOf]
  | e :: l, k + 1, hk => by
    have := tblOf_getD l (k := k) (by simpa using hk)
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, show 3 * k + 1 + 1 + 1 + 1 = 3 * k + 1 + 1 + 1 + 1 from rfl,
      show 3 * k + 1 + 1 + 1 + 2 = 3 * k + 2 + 1 + 1 + 1 by ring]
    simp only [tblOf, List.getD_cons_succ, Nat.add_assoc] at this ⊢
    exact this

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Every QLT entry's checks hold.** -/
theorem qlt_entry (hQ : QOk p lay) (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    (hA : SegsAssert M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    {e : Nat × Nat × Nat} (he : e ∈ qltEntries p lay) :
    M.k e.1 = kOf e.2.2 ∧ ∀ l < 4, M.k (e.1 + 1 + l) = M.k (e.2.1 + l) := by
  have hmem : e ∈ qltPadded p lay := List.mem_append_left _ he
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hmem
  rw [qltPadded_length p lay hQ.qlen] at hk
  have hkd : (qltPadded p lay).getD k (0, 0, 0) = e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [qltPadded_length p lay hQ.qlen]; exact hk)]
    simpa using hke
  have hd := tblOf_getD (qltPadded p lay) (k := k) (by rw [qltPadded_length p lay hQ.qlen]; exact hk)
  rw [hkd] at hd
  have hlenD : (qltData p lay).length = 3 * 2 ^ lay.aQ := by
    rw [qltData, tblOf_length, qltPadded_length p lay hQ.qlen]
  have t0 := hin.table (3 * k) (by omega)
  have t1 := hin.table (3 * k + 1) (by omega)
  have t2 := hin.table (3 * k + 2) (by omega)
  simp only [qltData] at t0 t1 t2
  rw [hd.1] at t0; rw [hd.2.1] at t1; rw [hd.2.2] at t2
  obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound e he
  have := qltLoop_spec h hA hin.flag hinj hN (jf := k) (e₁ := e.1) (e₂ := e.2.1) hk (by omega) (by omega)
    t0 (by rw [show lay.qt + 1 + 3 * k = lay.qt + (3 * k + 1) by ring]; exact t1)
  rw [show lay.qt + 2 + 3 * k = lay.qt + (3 * k + 2) by ring, t2] at this
  exact this

end

/-! ## Openings -/

theorem unflat_two' {dc dx c y : Nat} (hc : c < 2 ^ dc) (hy : y < 2 ^ dx) :
    unflat [dc, dx] (c + 2 ^ dc * y) = [c, y] := by
  have hm : (c + 2 ^ dc * y) % 2 ^ dc = c := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hdv : (c + 2 ^ dc * y) / 2 ^ dc = y := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hc, Nat.zero_add]
  simp [unflat, hm, hdv, Nat.mod_eq_of_lt hy]

theorem pchunks_cover {t j : Nat} (hj : j < t) :
    ∃ c ∈ pchunks t, c.1 ≤ j ∧ j - c.1 < realCount t c.1 c.2 ∧ j - c.1 < 2 ^ c.2 := by
  have ht : t ≠ 0 := by omega
  have h1 := Nat.log2_self_le ht
  have h2 := @Nat.lt_log2_self t
  unfold pchunks realCount
  split
  · next he => exact ⟨(0, t.log2), by simp, by omega, by simp; omega, by simp; omega⟩
  · next he =>
    by_cases hj2 : j < 2 ^ t.log2
    · exact ⟨(0, t.log2), by simp, by omega, by simp; omega, by simp; omega⟩
    · have h3 := @Nat.lt_log2_self (t - 2 ^ t.log2 - 1)
      refine ⟨(2 ^ t.log2, (t - 2 ^ t.log2 - 1).log2 + 1), by simp, by simp; omega, ?_, ?_⟩ <;> simp <;> omega

theorem realCount_le (t s a : Nat) : realCount t s a ≤ 2 ^ a := Nat.min_le_left _ _

theorem bitSum_congr (M : Mem) (bt bt' : Nat) (st st' J J' : List Nat) (n : Nat)
    (h : ∀ y < n, bt + y + Loop.dot st J = bt' + y + Loop.dot st' J') : bitSum M bt st J n = bitSum M bt' st' J' n := by
  simp only [bitSum]
  congr 1
  exact List.map_congr_left fun y hy => by rw [h y (by simpa using hy)]

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **An opening's checks hold at every position.** -/
theorem open_facts (hQ : QOk p lay) (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < (opens p).length) {o : OpenInfo} (hko : (opens p).getD k default = o) {q : Ptr}
    (h : SegsHold c M q (openLoops p lay zo (bitBase p lay k) o q).2)
    (hA : SegsAssert M q (openLoops p lay zo (bitBase p lay k) o q).2)
    {j : Nat} (hj : j < o.L.t) :
    M.k (lay.sb + eLane p o.i0 + posStride o.L * j) = kOf o.L.row ∧
    (∀ l < 4, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L o.L.path + 9 + l) =
      M.k (lay.sb + (eLane p o.ce + 1 + o.co / 8) +
        4 * bitSum M (bitBase p lay k + o.L.height * j + o.L.path) [] [] (o.L.height - o.L.path) + l)) ∧
    (∀ lvl < o.L.path, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1)) = kOf 64 ∧ ∀ l < 4,
      M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) - 4 + l) =
        if M.k (bitBase p lay k + o.L.height * j + lvl) = 1 then M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 5 + l)
        else M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 1 + l)) := by
  have ho : o ∈ opens p := by
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1, hph, hK, hcap, hrow⟩ := hQ.opens o ho
  have hbit : ∀ j' < o.L.t, ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * j' + z) = 0 ∨
      M.k (bitBase p lay k + o.L.height * j' + z) = 1 := by
    intro j' hj' z hz'
    have := hin.bits k hk j' (by rw [hko]; exact hj') z (by rw [hko]; exact hz')
    rw [hko] at this
    rw [this]; split <;> simp
  simp only [openLoops] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨cc, hcc, hc1, hc2, hc3⟩ := pchunks_cover hj
  obtain ⟨q1, h1, hA1⟩ := seqAll_both _ _ h.1 hA.1 _ (List.mem_map_of_mem hcc)
  rw [hold_bind] at h1; rw [assert_bind] at hA1
  have hgate : ∀ jj, jj < realCount o.L.t cc.1 cc.2 →
      M.k (zo + 2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj) = 1 := by
    intro jj hjj
    have hr := realCount_le o.L.t cc.1 cc.2
    have hKc : 2 ^ cc.2 ≤ 2 ^ lay.K := Nat.pow_le_pow_right (by omega) (hK cc hcc)
    rw [show zo + 2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj = zo + (2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj) by omega]
    exact hz _ (by omega)
  have hjs : j = cc.1 + (j - cc.1) := by omega
  have hHj : o.L.height * j = o.L.height * cc.1 + o.L.height * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  have hSj : posStride o.L * j = posStride o.L * cc.1 + posStride o.L * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  -- the cap loop
  have hc' := capLoop_spec h1.1 hA1.1 (jf := j - cc.1) (by simpa using hc3) (by omega)
    (by simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero, Nat.one_mul]
        exact hgate _ hc2)
    (fun y hy => by
      simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero]
      have := hbit j hj (o.L.path + y) (by omega)
      rwa [show bitBase p lay k + o.L.height * cc.1 + o.L.path + y + o.L.height * (j - cc.1) =
        bitBase p lay k + o.L.height * j + (o.L.path + y) by omega])
    hinj hN (by omega)
  simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero] at hc'
  have hbase : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + posStride o.L * (j - cc.1) = (lay.sb + eLane p o.i0 + posStride o.L * j) := by
    omega
  refine ⟨?_, fun l hl => ?_, fun lvl hlvl => ?_⟩
  · rw [← hbase]; exact hc'.1
  · have := hc'.2 l hl
    rw [show lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L o.L.path + 9 + l +
        posStride o.L * (j - cc.1) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L o.L.path + 9 + l by omega] at this
    rw [this, bitSum_congr M _ (bitBase p lay k + o.L.height * j + o.L.path) [o.L.height] [] [j - cc.1] []
      (o.L.height - o.L.path) (fun y _ => by simp only [Loop.dot]; omega)]
  · -- the node loop of the level chunk holding lvl
    obtain ⟨dd, hdd, hd1, hd2⟩ := chunks_cover hlvl
    have h1s := h1.2; have hA1s := hA1.2
    rw [hold_bind] at h1s; rw [assert_bind] at hA1s
    obtain ⟨q2, h2, hA2⟩ := seqAll_both _ _ h1s.1 hA1s.1 _ (List.mem_map_of_mem hdd)
    have hjf : lvl - dd.1 + 2 ^ dd.2 * (j - cc.1) < 2 ^ [dd.2, cc.2].sum := by
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_add]
      have := Nat.mul_le_mul_left (2 ^ dd.2) (show j - cc.1 + 1 ≤ 2 ^ cc.2 by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    have hu := unflat_two' (dc := dd.2) (dx := cc.2) (c := lvl - dd.1) (y := j - cc.1) (by omega) hc3
    have hn := nodeLoop_spec h2 hA2 hjf
      (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.zero_mul, Nat.zero_add, Nat.one_mul]; exact hgate _ hc2)
      (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.one_mul]
          have := hbit j hj lvl (by omega)
          rwa [show bitBase p lay k + o.L.height * cc.1 + dd.1 + (lvl - dd.1 + o.L.height * (j - cc.1)) =
            bitBase p lay k + o.L.height * j + lvl by omega])
    rw [hu] at hn
    simp only [Loop.dot, Nat.add_zero] at hn
    have hsl : slotOff o.L (dd.1 + 1) + 13 * (lvl - dd.1) = slotOff o.L (lvl + 1) := by
      simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]; omega
    have hb2 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) := by
      omega
    have hbit' : bitBase p lay k + o.L.height * cc.1 + dd.1 + (1 * (lvl - dd.1) + o.L.height * (j - cc.1)) =
        bitBase p lay k + o.L.height * j + lvl := by omega
    refine ⟨by rw [← hb2]; exact hn.1, fun l hl => ?_⟩
    have := hn.2 l hl
    have e1 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) - 4 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) - 4 + l := by
      have : 4 ≤ lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) := by
        simp only [slotOff, Nat.add_one_ne_zero, ite_false]; omega
      omega
    have e2 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) + 5 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 5 + l := by omega
    have e3 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) + 1 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 1 + l := by omega
    simp only [hbit', e1, e2, e3] at this
    exact this

end

/-! ## The theorem -/

theorem kOf_inj {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) (h : kOf v = kOf w) : v = w := by
  rw [← kOf_toNat hv, ← kOf_toNat hw, h]

theorem byte_of_lane (ws : List Word) (q b : Nat) (hb : b < 8) :
    (wordsBytes ws).getD (8 * q + b) 0 = ((lw ws q) / 256 ^ b % 256).toUInt8 := by
  rw [← wordByte_eq_getD, wordByte, show (8 * q + b) / 8 = q by omega, show (8 * q + b) % 8 = b by omega,
    ← toUInt8_mod]
  rfl

theorem padLane_byte (L q b : Nat) (hb : b < 8) : (padLane L q / 256 ^ b % 256).toUInt8 = padAt L (8 * q + b) := by
  rw [padLane, ofLE_div_mod]
  simp [List.getD_eq_getElem?_getD, hb]

theorem fk01 : ¬ ((0 : FK) = 1) := by decide

theorem posL_succ (p : Params) (ws : List Word) (e s h : Nat) :
    posL p ws e s (h + 1) = posL p ws e s h + (if ansBit p ws e (s + h) then 2 ^ h else 0) := by
  simp [posL, List.range_succ]

theorem posL_lt (p : Params) (ws : List Word) (e s : Nat) : ∀ h, posL p ws e s h < 2 ^ h
  | 0 => by simp [posL]
  | h + 1 => by
    rw [posL_succ, Nat.pow_succ]; have := posL_lt p ws e s h
    split <;> omega

theorem bitSum_posL {p : Params} {ws : List Word} {M : Mem} {bt e s n : Nat}
    (hb : ∀ y < n, M.k (bt + y) = if ansBit p ws e (s + y) then 1 else 0) :
    bitSum M bt [] [] n = posL p ws e s n := by
  simp only [bitSum, posL]
  congr 1
  apply List.map_congr_left
  intro y hy
  rw [show bt + y + Loop.dot [] [] = bt + y from rfl, hb y (List.mem_range.mp hy)]
  split <;> simp [fk01]

theorem lanes_in {p : Params} (hS : StreamOk p) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    eLane p i + 5 + ((plan p).getD i default).len / 8 ≤ hashedLen p / 8 := by
  have e := entry_end p hi
  rw [← hS.2, bOff_eq hS.1 h1 (by omega)] at e
  have := streamOk_len hS.1 h1 hi
  omega

/-- An opening entry: its opening, position and slot. -/
theorem open_pos {p : Params} {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpen = true) :
    ∃ k, k < (opens p).length ∧ ∃ o, (opens p).getD k default = o ∧ ∃ jj y, jj < o.L.t ∧ y < 1 + o.L.path ∧
      i = o.i0 + jj * (1 + o.L.path) + y ∧
      (plan p).getD i default = if y = 0 then ⟨.leaf, o.L.row⟩
        else ⟨.node o.pe o.L.height jj (y - 1) (if y = o.L.path then some (o.ce, o.co, o.L.path) else none), 64⟩ := by
  obtain ⟨o, ho, h1, h2, h3⟩ := open_of_entry p hi he
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  rw [openPlan_length] at h2
  have hP : 0 < 1 + o.L.path := by omega
  have hx : (i - o.i0) / (1 + o.L.path) * (1 + o.L.path) + (i - o.i0) % (1 + o.L.path) = i - o.i0 :=
    Nat.div_add_mod' _ _
  have hjt : (i - o.i0) / (1 + o.L.path) < o.L.t := by
    rw [Nat.div_lt_iff_lt_mul hP]; omega
  have e := openPlan_getD o.L o.pe o.ce o.co hjt (Nat.mod_lt (i - o.i0) hP)
  rw [hx] at e
  refine ⟨k, hk, o, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hko],
    (i - o.i0) / (1 + o.L.path), (i - o.i0) % (1 + o.L.path), hjt, Nat.mod_lt _ hP, by omega, ?_⟩
  rw [h3, e]

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- Q_link's checks after the position cells. -/
theorem qlinkCore_sound (hS : StreamOk p) (hQ : QOk p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlinkCore p lay pt).2) (hA : SegsAssert M pt (qlinkCore p lay pt).2) :
    LaneLink p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlinkCore] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨hz1, -⟩ := stepArr_spec h.1
  have hz : ∀ x < 2 ^ lay.K, M.k (pt.k + x) = 1 := fun x hx => by rw [hz1 x hx, hin.flag]
  have h2 := h.2; have hA2 := hA.2
  rw [stepArr_apply] at h2 hA2
  rw [hold_bind] at h2; rw [assert_bind] at hA2
  have QE : ∀ a b v, (a, b, v) ∈ qltEntries p lay → M.k a = kOf v ∧ ∀ l < 4, M.k (a + 1 + l) = M.k (b + l) :=
    fun a b v he => qlt_entry hQ hin hinj hN hNs h2.1 hA2.1 he
  have QB : ∀ a b v, (a, b, v) ∈ qltEntries p lay → lay.sb ≤ a ∧ lay.sb ≤ b ∧ a + 5 ≤ lay.sb + 2 ^ lay.m ∧
      b + 4 ≤ lay.sb + 2 ^ lay.m ∧ v < 2 ^ 64 := fun a b v he => hQ.qbound _ he
  have h3 := h2.2; have hA3 := hA2.2
  rw [hold_bind] at h3; rw [assert_bind] at hA3
  have hopk : ∀ k, k < (opens p).length → ∀ o, (opens p).getD k default = o →
      ∃ q, SegsHold c M q (openLoops p lay pt.k (bitBase p lay k) o q).2 ∧
        SegsAssert M q (openLoops p lay pt.k (bitBase p lay k) o q).2 := by
    intro k hk o hko
    obtain ⟨q, hq1, hq2⟩ := seqAll_both _ _ h3.1 hA3.1 _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    subst hko
    exact ⟨q, hq1, hq2⟩
  -- stream lanes
  have hT := hQ.hT
  have hL8 : hashedLen p % 8 = 0 := by
    have := bOff_mod hS.1 (plan p).length (by have := plan_length_ge p; omega) le_rfl
    rw [bOff_end, ← hS.2] at this; exact this
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  -- FS entries are QLT entries
  have FSM : ∀ i, i < (plan p).length → ∀ st, ((plan p).getD i default).k = .fs st →
      (lay.sb + eLane p i, lay.sb + ansLane p st, ((plan p).getD i default).len) ∈ qltEntries p lay := by
    intro i hi st hk
    have hgi : (plan p).getD i default = (plan p)[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [hgi] at hk ⊢
    apply List.mem_append_left; apply List.mem_append_right
    rw [List.mem_filterMap]
    exact ⟨((plan p)[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]),
      by simp only [hk]⟩
  -- opening entries
  have OE : ∀ i, i < (plan p).length → ((plan p).getD i default).k.isOpen = true →
      ∃ k o jj y, k < (opens p).length ∧ (opens p).getD k default = o ∧ jj < o.L.t ∧ y < 1 + o.L.path ∧
        (plan p).getD i default = (if y = 0 then ⟨.leaf, o.L.row⟩ else ⟨.node o.pe o.L.height jj (y - 1)
          (if y = o.L.path then some (o.ce, o.co, o.L.path) else none), 64⟩) ∧
        lw ws (eLane p i) = ((plan p).getD i default).len ∧
        (y ≠ 0 → ∀ l < 4, lw ws ((if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1))
          then eLane p i + 5 else eLane p i + 1) + l) = lw ws (eLane p i - 4 + l)) ∧
        (y = o.L.path → ∀ l < 4, lw ws (eLane p i + 9 + l) = lw ws (eLane p o.ce + 1 + o.co / 8 +
          4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) + l)) := by
    intro i hi he
    obtain ⟨k, hk, o, hko, jj, y, hjj, hy, hieq, hpe⟩ := open_pos hi he
    have ho : o ∈ opens p := by
      rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
    obtain ⟨q, hq1, hq2⟩ := hopk k hk o hko
    obtain ⟨f1, f2, f3⟩ := open_facts hQ hin hinj hN hNs hz hk hko hq1 hq2 hjj
    have hEL : eLane p i = eLane p o.i0 + posStride o.L * jj + slotOff o.L y := by
      rw [hieq, eLane_open hS ho hjj (by omega), Nat.mul_comm]
    have hi1 : 1 ≤ i := by have := opens_i0 p ho; omega
    have hin_ := lanes_in hS hi1 hi
    have hbits : ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * jj + z) =
        if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + z) then 1 else 0 := by
      intro z hz
      have := hin.bits k hk jj (by rw [hko]; exact hjj) z (by rw [hko]; exact hz)
      rw [hko] at this; exact this
    obtain ⟨hp1, hph, -, hcapb, hrow⟩ := hQ.opens o ho
    refine ⟨k, o, jj, y, hk, hko, hjj, hy, hpe, ?_, ?_, ?_⟩
    · by_cases hy0 : y = 0
      · subst hy0
        rw [hpe, if_pos rfl]
        rw [hpe, if_pos rfl] at hin_
        refine LV _ _ (by omega) hrow ?_
        rw [hEL, show lay.sb + (eLane p o.i0 + posStride o.L * jj + slotOff o.L 0) =
          lay.sb + eLane p o.i0 + posStride o.L * jj by simp [slotOff]; omega]
        exact f1
      · rw [hpe, if_neg hy0]
        rw [hpe, if_neg hy0] at hin_
        have := (f3 (y - 1) (by omega)).1
        rw [show y - 1 + 1 = y by omega] at this
        refine LV _ _ (by omega) (by norm_num) ?_
        rw [hEL, show lay.sb + (eLane p o.i0 + posStride o.L * jj + slotOff o.L y) =
          lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y by omega]
        exact this
    · intro hy0 l hl
      have e := (f3 (y - 1) (by omega)).2 l hl
      rw [show y - 1 + 1 = y by omega] at e
      have hs5 : 5 ≤ slotOff o.L y := by simp only [slotOff, if_neg hy0]; omega
      have hb := hbits (y - 1) (by omega)
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane p i + 13 ≤ hashedLen p / 8 := by simp only at hin_; omega
      by_cases hab : ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1)) = true
      · rw [if_pos hab] at hb ⊢; rw [if_pos hb] at e
        refine (LE _ _ (by omega) (by omega) ?_).symm
        rw [show lay.sb + (eLane p i - 4 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y - 4 + l
            by omega,
          show lay.sb + (eLane p i + 5 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y + 5 + l
            by omega]
        exact e
      · rw [if_neg hab] at hb ⊢; rw [hb, if_neg fk01] at e
        refine (LE _ _ (by omega) (by omega) ?_).symm
        rw [show lay.sb + (eLane p i - 4 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y - 4 + l
            by omega,
          show lay.sb + (eLane p i + 1 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y + 1 + l
            by omega]
        exact e
    · intro hyp l hl
      subst hyp
      have e := f2 l hl
      have hbs : bitSum M (bitBase p lay k + o.L.height * jj + o.L.path) [] [] (o.L.height - o.L.path) =
          posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) :=
        bitSum_posL fun z hz => by
          have := hbits (o.L.path + z) (by omega)
          simpa only [Nat.add_assoc] using this
      rw [hbs] at e
      have hpl := posL_lt p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path)
      have hy0 : o.L.path ≠ 0 := by omega
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane p i + 13 ≤ hashedLen p / 8 := by simp only at hin_; omega
      refine LE _ _ (by omega) (by omega) ?_
      rw [show lay.sb + (eLane p i + 9 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L o.L.path + 9 + l
          by omega,
        show lay.sb + (eLane p o.ce + 1 + o.co / 8 + 4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path)
          (o.L.height - o.L.path) + l) = lay.sb + (eLane p o.ce + 1 + o.co / 8) +
          4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) + l by omega]
      exact e
  -- the constant lanes
  have m0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  have m1 : (lay.sb + 1, lay.sb + 2, lane1C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m0
    exact LV 0 _ (by omega) b5 (by simpa using (QE _ _ _ m0).1)
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m1
    exact LV 1 _ (by omega) b5 (QE _ _ _ m1).1
  · intro i h1 hi
    cases hk : ((plan p).getD i default).k with
    | q0 =>
      have := streamOk_entry hS.1 hi
      simp only [entryOk, hk] at this
      simp at this; omega
    | fs st =>
      have hm := FSM i hi st hk
      obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
      exact LV _ _ (by omega) b5 (QE _ _ _ hm).1
    | leaf =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
    | node pe h j lvl cap =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
  · intro i hi st hk l hl
    have hm := FSM i hi st hk
    obtain ⟨-, -, b3, b4, -⟩ := QB _ _ _ hm
    have e := (QE _ _ _ hm).2 l hl
    refine LE _ _ (by omega) (by omega) ?_
    rw [show lay.sb + (eLane p i + 1 + l) = lay.sb + eLane p i + 1 + l by omega,
      show lay.sb + (ansLane p st + l) = lay.sb + ansLane p st + l by omega]
    exact e
  · intro i hi pe h j lvl cap hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, hnode, -⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hk
      exact hnode hy0 l hl
  · intro i hi pe h j lvl ce co path hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, -, hcap⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, hc⟩ := hk
      by_cases hyp : y = o.L.path
      · rw [if_pos hyp] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hcap hyp l hl
      · rw [if_neg hyp] at hc; cases hc
  · -- the padding
    intro q hq1 hq2
    have hk : q / 8 - hashedLen p / 8 < 17 * nBlk (hashedLen p) - hashedLen p / 8 := by omega
    have hm : (lay.sb + q / 8, lay.sb + q / 8 + 1, padLane (hashedLen p) (q / 8)) ∈ qltEntries p lay := by
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨q / 8 - hashedLen p / 8, List.mem_range.mpr hk, by
        simp only [show hashedLen p / 8 + (q / 8 - hashedLen p / 8) = q / 8 by omega]⟩
    obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
    have hv := LV _ _ (by omega) b5 (QE _ _ _ hm).1
    have hb := byte_of_lane ws (q / 8) (q % 8) (by omega)
    rw [show 8 * (q / 8) + q % 8 = q by omega, hv, padLane_byte _ _ _ (by omega),
      show 8 * (q / 8) + q % 8 = q by omega] at hb
    exact hb

/-- **Q_link is sound**: its rows and assertions, with its inputs where the layout says, make the
stream meet every lane condition of the schedule, and pin the trace sponge's padding. -/
theorem qlink_sound (hS : StreamOk p) (hQ : QOk p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink p lay pt).2) (hA : SegsAssert M pt (qlink p lay pt).2) :
    LaneLink p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlink] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  exact qlinkCore_sound hS hQ hin hws hinj hN hNs h.2 hA.2

/-! ## The position cells (A20) -/

theorem posLoop_spec {pt : Ptr} {a lo hi : Nat} (h : SegsHold c M pt (posLoop a lo hi pt).2) :
    ∀ g < 2 ^ a, M.k (pt.k + g) = M.k (lo + g) + M.k (hi + g) := by
  intro g hg
  have e := lrel_lin (t := 0) rfl (loop_rel h (jf := g) (by simpa using hg) (by simp))
  simp only [List.getD_cons_zero, List.getD_cons_succ, ofK_one, one_mul, ofK_zero, add_zero,
    Opd.val_absK, LoopOut.cell_val] at e
  simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at, unflat_one' (show g < 2 ^ [a].sum by simpa using hg),
    Loop.dot] at e
  rw [← ofK_add] at e
  simpa [Mem.rd] using ofK_inj e

theorem sum_take_add_lt (l : List Nat) {k : Nat} (hk : k < l.length) : (l.take k).sum + l[k] ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop k l, List.sum_append, List.drop_eq_getElem_cons hk, List.sum_cons]
  omega

theorem posIdx_lt (hQ : QOk p lay) {k j : Nat} (hk : k < (opens p).length)
    (hj : j < ((opens p).getD k default).L.t) : posIdx p k j < 2 ^ lay.pa := by
  have := sum_take_add_lt ((opens p).map fun o => o.L.t) (k := k) (by simpa using hk)
  rw [← List.map_take] at this
  simp only [List.getElem_map] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
  have := hQ.pos
  simp only [posIdx]; omega

/-- **The position cells** (A20): where Q_link's rows hold, the cell `pt.k + posIdx p k j` (position `j`
of opening `k`) is the sum of the position's two BITS fields. -/
theorem qlink_pos (hQ : QOk p lay) {pt : Ptr} (h : SegsHold c M pt (qlink p lay pt).2) {k j : Nat}
    (hk : k < (opens p).length) (hj : j < ((opens p).getD k default).L.t) :
    M.k (pt.k + posIdx p k j) = M.k (lay.fl + posIdx p k j) + M.k (lay.fl + 2 ^ lay.pa + posIdx p k j) := by
  simp only [qlink] at h
  rw [hold_bind] at h
  exact posLoop_spec h.1 _ (posIdx_lt hQ hk hj)

end

/-- `b·2^d + a = b·2^d ⊕ a` for `a < 2^d` (as `LvmXEnc.mul_two_pow_add_eq_xor`). -/
theorem mul_two_pow_add_xor {b d a : Nat} (ha : a < 2 ^ d) : b * 2 ^ d + a = b * 2 ^ d ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < d
  · simp [h, show ¬ (d ≤ i) by omega]
  · rw [if_neg h, Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [show d ≤ i by omega]

/-- **Two disjoint fields add to the position** (`K` addition is `xor`). -/
theorem kOf_add_fields {a b d : Nat} (ha : a < 2 ^ d) (h64 : b * 2 ^ d + a < 2 ^ 64) :
    kOf a + kOf (b * 2 ^ d) = kOf (b * 2 ^ d + a) := by
  have hb : b * 2 ^ d < 2 ^ 64 := by omega
  have ha' : a < 2 ^ 64 := by omega
  show FK.add _ _ = _
  simp only [FK.add, kOf]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor, Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using ha'),
    Nat.mod_eq_of_lt (by simpa using hb), Nat.mod_eq_of_lt (by simpa using h64), mul_two_pow_add_xor ha,
    Nat.xor_comm]

end Lvm.QLink
