-- New for lvm (INB): `hinb` for the assembled node programs `QAsm.Q cfg20` and `QAsm.Q cfg8`
-- (WP-16a's `LvmQAsmProg`): WP-16a's position classes cover the cap bits (`capCov_pos`), Q_sig and
-- Q_arith have no `readd` (decided), and `LvmQAsmInbNode.hinb_node`/`inb_of_m3` do the rest.
import LvmQAsmInbNode
import LvmQAsmProg

/-!
# `hinb` for `Q20` and `Q8`

* **`capCov_pos`**: the position classes `posSpecs C bpl` (one `BITS` row per 8 padded positions,
  `nRows`) put a `bit` output on every cap bit cell `bitBase k + H·j + z`, `j < padT t`, `z < H`,
  given that their cells lie inside `Q` (`PosCellsLt`, a static bound like Q_sig's `SigCellsLt`,
  independent of the placement).
* **`hinb20`**: `nodeSound_layout`'s `hinb` at WP-16a's `P20` node program (`lay cfg20`, `sigIn cfg20`,
  `qarith cfg20`, `nK cfg20`, `0`, `aux cfg20 D`), from `nodeSound_layout`'s `hT`, `hst`, `hQ`, `hqlt`
  and `PosCellsLt`. **`inb8`**: the same fact for `Q cfg8` on any stack with `M3Holds`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-! ## The position classes cover the cap bits -/

/-- The position classes' cells lie inside `Q` (as Q_sig's `SigCellsLt`): per opening `k`, lane
`l` and row `x < nRows`, the word cell (a stream lane) and every output cell (`posCell`). Independent of
the placement `bpl`. -/
def PosCellsLt (Q : Program) (C : QCfg) : Prop :=
  ∀ k < (opens C.p).length, ∀ l < nLanes ((opens C.p).getD k default).L.height,
    ∀ x < nRows ((opens C.p).getD k default),
    ansLane C.p (((opens C.p).getD k default).pe + x) + l < Q.cells .K ∧
    ∀ jo < (laneOuts ((opens C.p).getD k default).L.height l).length,
      posCell C k ((opens C.p).getD k default) x
        ((laneOuts ((opens C.p).getD k default).L.height l).getD jo (.bit 0, 0, 0)) < Q.cells .K

theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simp; omega
  · have := @Nat.lt_log2_self (n - 1); rw [Nat.pow_succ] at this ⊢; omega

theorem filter_range_lt : ∀ (n m : Nat),
    (List.range n).filter (fun z => decide (z < m)) = List.range (min n m)
  | 0, m => by simp
  | n + 1, m => by
    rw [List.range_succ, List.filter_append, filter_range_lt n m]
    by_cases h : n < m
    · rw [show min (n + 1) m = min n m + 1 by omega, List.range_succ, show min n m = n by omega]
      simp [h]
    · rw [show min (n + 1) m = min n m by omega]; simp [h]

/-- The first outputs of lane `l`'s row are its bits. -/
theorem laneOuts_bit {H l z : Nat} (hz : z < 64) (h : 64 * l + z < 8 * H) :
    z < (laneOuts H l).length ∧ (laneOuts H l).getD z (.bit 0, 0, 0) = (.bit z, 0, 64 * l + z) := by
  have hf : (List.range 64).filter (fun z => decide (64 * l + z < 8 * H)) = List.range (min 64 (8 * H - 64 * l)) := by
    rw [← filter_range_lt]
    congr 1; funext y; exact decide_eq_decide.mpr (by omega)
  unfold laneOuts
  rw [hf]
  have hl : z < ((List.range (min 64 (8 * H - 64 * l))).map fun z => ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat)).length := by
    simp; omega
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl]
  simp

theorem mem_posSpecs (C : QCfg) (bpl : Nat → Nat → Bool × Nat) {k l : Nat} (hk : k < (opens C.p).length)
    (hl : l < nLanes ((opens C.p).getD k default).L.height) :
    ∃ c, (⟨clog2 (nRows ((opens C.p).getD k default)), nRows ((opens C.p).getD k default),
      (laneOuts ((opens C.p).getD k default).L.height l).map (·.1), true,
      fun x => ansLane C.p (((opens C.p).getD k default).pe + x) + l,
      fun j x => posCell C k ((opens C.p).getD k default) x
        ((laneOuts ((opens C.p).getD k default).L.height l).getD j (.bit 0, 0, 0)), bpl c⟩ : BSpec) ∈
      posSpecs C bpl := by
  set cls := (List.range (opens C.p).length).flatMap fun k =>
    (List.range (nLanes ((opens C.p).getD k default).L.height)).map
      fun l => (k, (opens C.p).getD k default, l) with hcls
  have hm : (k, (opens C.p).getD k default, l) ∈ cls := by
    rw [hcls, List.mem_flatMap]
    exact ⟨k, List.mem_range.mpr hk, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, ?_⟩
  unfold posSpecs
  rw [← hcls]
  refine List.mem_map.mpr ⟨((k, (opens C.p).getD k default, l), i), ?_, rfl⟩
  have hi' : i < (cls.zipIdx).length := by simpa using hi
  have := List.getElem_mem hi'
  rw [List.getElem_zipIdx, he, Nat.zero_add] at this
  exact this

/-- **The position classes cover the cap bits.** -/
theorem capCov_pos (C : QCfg) (Q : Program) (aux : List Tab) (bpl : Nat → Nat → Bool × Nat)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) : CapCov C.p Q (lay C) aux := by
  intro k hk j hj z hz
  obtain ⟨n, hn⟩ : ∃ n, n = j % 8 * ((opens C.p).getD k default).L.height + z := ⟨_, rfl⟩
  have hl0 : n / 64 < nLanes ((opens C.p).getD k default).L.height := by
    have : j % 8 * ((opens C.p).getD k default).L.height ≤ 7 * ((opens C.p).getD k default).L.height :=
      Nat.mul_le_mul_right _ (by omega)
    unfold nLanes; omega
  obtain ⟨c, hS⟩ := mem_posSpecs C bpl hk hl0
  have hpc := hpc k hk (n / 64) hl0
  generalize (opens C.p).getD k default = o at hj hz hn hS hpc ⊢
  generalize hH : o.L.height = H at hz hn hS hpc ⊢
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hn8 : n < 8 * H := by
    have : j % 8 * H ≤ 7 * H := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnH : n / H = j % 8 := by
    rw [hn, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hz, Nat.zero_add]
  have hnm : n % H = z := by
    rw [hn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  have hdm := Nat.div_add_mod n 64
  obtain ⟨hlen, hget⟩ := laneOuts_bit (H := H) (l := n / 64) (z := n % 64) (Nat.mod_lt _ (by norm_num))
    (by omega)
  have hlen' : n % 64 < ((laneOuts H (n / 64)).map (·.1)).length := by rw [List.length_map]; exact hlen
  have hout : ((laneOuts H (n / 64)).map (·.1)).getD (n % 64) (.bit 0) = .bit (n % 64) := by
    rw [List.getD_eq_getElem _ _ hlen', List.getElem_map, ← List.getD_eq_getElem _ (.bit 0, 0, 0) hlen, hget]
  have hoc : posCell C k o (j / 8) ((laneOuts H (n / 64)).getD (n % 64) (.bit 0, 0, 0)) =
      bitBase C.p (lay C) k + H * j + z := by
    rw [hget, show 64 * (n / 64) + n % 64 = n by omega]
    have hjj : 8 * (j / 8) + n / H = j := by rw [hnH]; omega
    simp only [posCell, hH, hjj, if_pos hj, hnm]
  have hx : j / 8 < nRows o := by unfold nRows; omega
  exact ⟨_, haux _ hS, le_two_pow_clog2 _, j / 8, hx, fun _ => (hpc (j / 8) hx).1,
    fun jo hjo => (hpc (j / 8) hx).2 jo (by simpa using hjo), n % 64, hlen', n % 64, Nat.mod_lt _ (by norm_num),
    hout, hoc⟩

theorem posSpecs_aux (C : QCfg) (D : QData) {S : BSpec} (h : S ∈ posSpecs C fun c => bplOf D (6 + c)) :
    S.tab ∈ aux C D :=
  List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_right _ h))

/-! ## Decided: Q_sig reads no cell by address

Q_arith's fact `noReaddSegs (qarith C (p2C C)).2 = true` is a hypothesis (`hna`) of `hinb20`/`inb8`
(WP-16a2): with HAR's full Q_arith the kernel cannot evaluate it (`List.mergeSort` in the table phase
does not reduce; with a structural sort the table gadget alone exceeds 12 GB at `P8`). Natively it holds
(`P8`: 33,736 segments, no `readd`); a structural proof (no gadget of Q_arith emits a `readd`) is owed. -/

set_option maxRecDepth 100000 in
theorem noReadd_sig20 : noReaddSegs (qsig (sigIn cfg20) (p1C cfg20)).2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noReadd_sig8 : noReaddSegs (qsig (sigIn cfg8) (p1C cfg8)).2 = true := by decide +kernel

theorem qlt_le_nK20 (hQ : QOk P20 (lay cfg20)) : (lay cfg20).qt + (qltData P20 (lay cfg20)).length ≤ nK cfg20 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg20 + 3 * 2 ^ 11 ≤ qtB cfg20 + 2 ^ 13 + 2 ^ 15
  omega

theorem qlt_le_nK8 (hQ : QOk P8 (lay cfg8)) : (lay cfg8).qt + (qltData P8 (lay cfg8)).length ≤ nK cfg8 := by
  rw [qltData, tblOf_length, qltPadded_length _ _ hQ.qlen]
  show qtB cfg8 + 3 * 2 ^ 11 ≤ qtB cfg8 + 2 ^ 13 + 2 ^ 16
  omega

/-! ## `hinb` at `P20` (`nodeSound_layout`'s form) -/

section P20

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}

/-- **`hinb` for WP-16a's `P20` node program** (`NodeHyp.hinb`): from `nodeSound_layout`'s `hT`,
`hst`, `hQ`, `hqlt` and the position classes' cell bounds. -/
theorem hinb20 {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D) (arrsX x))
    (hQ : QOk P20 (lay cfg20))
    (hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
          ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : noReaddSegs (qarith cfg20 (p2C cfg20)).2 = true) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true :=
  hinb_node hT hst hQ (qlt_le_nK20 hQ)
    (capCov_pos cfg20 _ (aux cfg20 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc)
    noReadd_sig20 hna hqlt

end P20

/-! ## `inb` at `P8` (any stack with `M3Holds`) -/

section P8

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {D : QData} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Q cfg8) pl groups arrs (aux cfg8 D), t.τ ≤ L.μ}

/-- **Every `readd` of WP-16a's `P8` node program finds its cell** on a stack with `M3Holds` (in
`AuxH0`), with the program check, Q_link's static checks, the `QLT` inputs and the position classes'
cell bounds. -/
theorem inb8 {q : Column L.μ} (hwf : (Q cfg8).wf = true)
    (H0 : AuxH0 (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q) (hQ : QOk P8 (lay cfg8))
    (htab : ∀ y < (qltData P8 (lay cfg8)).length,
      (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q).getD ((lay cfg8).qt + y) 0 = (qltData P8 (lay cfg8)).getD y 0)
    (hpc : PosCellsLt (Q cfg8) cfg8) (hna : noReaddSegs (qarith cfg8 (p2C cfg8)).2 = true) :
    ((Q cfg8).interp (inKOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)
      (inEOf (Q cfg8) pl groups arrs (aux cfg8 D) L hτ q)).inb = true :=
  inb_of_m3 (p := P8) (lay := lay cfg8) (I := sigIn cfg8) (qa := qarith cfg8) hwf H0 hQ
    (fun y hy => ⟨by have := qlt_le_nK8 hQ; omega, htab y hy⟩)
    (capCov_pos cfg8 _ (aux cfg8 D) (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg8 D h) hpc)
    noReadd_sig8 hna

end P8

end Lvm.QAsm
