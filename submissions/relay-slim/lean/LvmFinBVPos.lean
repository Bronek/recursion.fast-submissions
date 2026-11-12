-- New for lvm (WP-16a2, FIN-BV): `harith_core`'s position facts `PosOk` at the `P20` node program.
-- Route (HAR §3): Q_link's position cells (QL's `qlink_pos`: the sum of the position's two `BITS`
-- fields, A20), the position classes' `fld` outputs (WP-12b's `out1_at`), the fields' sum is
-- Q_link's `posL` (new: `fields_posL`), and `F` reads the same number (HAR-POS's `qsAt_posL`).
import LvmFinBV

/-!
# The position cells hold `F`'s positions

* **`fields_posL`**: the two `fld` outputs of a position (`fields H i`: `lo` at bit 0, `hi` at bit
  `m₁`) add up (`xor`, disjoint) to Q_link's `posL` of the answer lanes.
* **`posVal_of`** (any configuration): in the interpreter's memory, a position's two field cells add
  up to `kOf (posL …)`.
* **`PosLanes p Ls V k0`** (a static fact of the schedule and `F`'s layout, decidable at the frozen
  `P20`): level `i` of `Ls` (positions lanes from `V`) is Q_link's opening `k0 + i`, of height at
  most 64, and `F` reads its positions answers at the answers' lanes.
* **`posOkR20`**, **`posOkM20`**: `harith_core`'s `hposr`, `hposm` at `cfg20`.
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

/-! ## Bits of a field and of a position -/

/-- Bit `i` of a `fld z₀ m d` output: bit `z₀ + (i − d)` of the word for `d ≤ i < d + m`. -/
theorem ubit_fld {z₀ m d : ℕ} (h : z₀ < 64 ∧ 1 ≤ m ∧ m + d ≤ 64) (w : UInt64) (i : ℕ) :
    ubit ((BOut.fld z₀ m d).word w) i =
      (decide (d ≤ i) && decide (i < d + m) && ubit w (z₀ + (i - d))) := by
  obtain ⟨h0, h1, h2⟩ := h
  by_cases hi : i < 64
  · simp only [BOut.word, ubit_shr _ (show 64 - m - d < 64 by omega), ubit_shl _ (show 64 - m < 64 by omega),
      ubit_shr _ h0]
    by_cases c1 : d ≤ i
    · by_cases c2 : i < d + m
      · rw [show z₀ + (64 - m - d + i - (64 - m)) = z₀ + (i - d) by omega]
        simp [c1, c2, show 64 - m - d + i < 64 by omega, show 64 - m ≤ 64 - m - d + i by omega]
      · simp [c2, show ¬ (64 - m - d + i < 64) by omega]
    · simp [c1, show ¬ (64 - m ≤ 64 - m - d + i) by omega]
  · rw [ubit_ge _ (by omega)]
    simp [show ¬ (i < d + m) by omega]

theorem ubit_laneK (ws : List Word) (j z : ℕ) : ubit (laneK ws j).val z = (lw ws j).testBit z := rfl

theorem ubit_toUInt64 (n : ℕ) {b : ℕ} (hb : b < 64) : ubit n.toUInt64 b = n.testBit b := by
  show (n.toUInt64).toNat.testBit b = _
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]
  simp [hb]

/-- Bit `b` of a position: bit `s + b` of the answer's lanes, for `b < h`. -/
theorem posL_testBit (p : Params) (ws : List Word) (e s h : ℕ) (hs : s + h ≤ 192) (b : ℕ) :
    (posL p ws e s h).testBit b =
      (decide (b < h) && (lw ws (ansLane p e + (s + b) / 64)).testBit ((s + b) % 64)) := by
  rw [posL_eq p ws (lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2))
    e s h (fun n _ h2 => by rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ n (by omega)]; rfl)]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < h
  · rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ (s + b) (by omega)]
  · simp [hb]

/-- **A position's two fields add up to `posL`** (A20: `lo` holds bits `[0, m₁)`, `hi` bits `[m₁, H)`;
`K` addition is `xor` of disjoint bit ranges). -/
theorem fields_posL (p : Params) (ws : List Word) (e : ℕ) {H i : ℕ} (hH2 : 2 ≤ H) (hH : H ≤ 64)
    (h192 : i * H + H ≤ 192) :
    w64 ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).1.1)).val) +
      w64 ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).2.1)).val) =
      kOf (posL p ws e (i * H) H) := by
  simp only [fields]
  generalize hs : i * H = s at h192 ⊢
  generalize hm : (if s / 64 = (s + H - 1) / 64 then H - 1 else 64 - s % 64) = m₁
  have hm' : (s / 64 = (s + H - 1) / 64 ∧ m₁ = H - 1) ∨ (s / 64 ≠ (s + H - 1) / 64 ∧ m₁ = 64 - s % 64) := by
    by_cases hc : s / 64 = (s + H - 1) / 64
    · rw [if_pos hc] at hm; exact Or.inl ⟨hc, hm.symm⟩
    · rw [if_neg hc] at hm; exact Or.inr ⟨hc, hm.symm⟩
  have hv1 : s % 64 < 64 ∧ 1 ≤ m₁ ∧ m₁ + 0 ≤ 64 := by omega
  have hv2 : (s + m₁) % 64 < 64 ∧ 1 ≤ H - m₁ ∧ H - m₁ + m₁ ≤ 64 := by omega
  show (⟨_ ^^^ _⟩ : FK) = ⟨(posL p ws e s H).toUInt64⟩
  congr 1
  apply u64_ext
  intro b hb
  rw [ubit_xor, ubit_fld hv1, ubit_fld hv2, ubit_toUInt64 _ hb, posL_testBit p ws e s H h192, ubit_laneK,
    ubit_laneK]
  by_cases b1 : b < m₁
  · rw [show (s + b) / 64 = s / 64 by omega, show (s + b) % 64 = s % 64 + (b - 0) by omega]
    simp [b1, show ¬ m₁ ≤ b by omega, show b < H by omega]
  · by_cases b2 : b < H
    · rw [show (s + b) / 64 = (s + m₁) / 64 by omega, show (s + b) % 64 = (s + m₁) % 64 + (b - m₁) by omega]
      simp [b1, b2, show m₁ ≤ b by omega, show b < m₁ + (H - m₁) by omega]
    · simp [b1, b2, show ¬ b < m₁ + (H - m₁) by omega]

/-! ## The position classes' field outputs -/

theorem lo_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2), 1, i) ∈
      laneOuts H (fields H i).1.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

theorem hi_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2), 2, i) ∈
      laneOuts H (fields H i).2.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

/-- An output of a position class's row, in `Out1` form: the output `e` of opening `k`'s lane-`l` row
(`laneOuts`), written by a row of lane class `l` (`posSpecs_hit`). -/
theorem out1_entry {Q : Program} {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr}
    {aux : List Tab} {L : Lay} {hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ} {q : Column L.μ}
    (H : AuxHyps Q pl groups arrs aux L hτ q) (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) {k l x : ℕ} {o : OpenInfo}
    (hk : k < (opens C.p).length) (ho : (opens C.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height)
    (hx : x < nRows o) {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hv : e.1.Valid) :
    Out1 (memK Q pl groups arrs aux L hτ q) (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e) := by
  subst ho
  obtain ⟨S, hS, hτS, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ := posSpecs_hit C bpl hk hl hx he
  exact out1_at Q pl groups arrs aux L hτ q H S (haux _ hS) hτS hrd y jo hy hjo
    (posCellsLt_spec hpc bpl hS hy) hwc hoc hout hv

/-- **A position's two field cells add up to `kOf (posL …)`** in the interpreter's memory (the position
classes' `fld` outputs on the answer lanes, the stream cells `hs`). -/
theorem posVal_of {Q : Program} {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr}
    {aux : List Tab} {L : Lay} {hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ} {q : Column L.μ}
    (H : AuxHyps Q pl groups arrs aux L hτ q) (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) (hS : StreamOk C.p)
    (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, memK Q pl groups arrs aux L hτ q ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    memK Q pl groups arrs aux L hτ q ((lay C).fl + posIdx C.p k j) +
        memK Q pl groups arrs aux L hτ q ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8) (j % 8 * ((opens C.p).getD k default).L.height)
        ((opens C.p).getD k default).L.height) := by
  generalize hoD : (opens C.p).getD k default = o at hH hj ⊢
  have ho : o ∈ opens C.p := by
    rw [← hoD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hj
  obtain ⟨hp1, hp2, -, -, -⟩ := hQ.opens _ ho
  have hin := lanes_in hS h1 hlt
  have hT := hQ.hT
  have hx : j / 8 < nRows o := by
    have := lt_padT hj; unfold nRows; omega
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hji : 8 * (j / 8) + j % 8 = j := by omega
  have hsH : j % 8 * o.L.height ≤ 7 * o.L.height := Nat.mul_le_mul_right _ (by omega)
  -- the two field entries, their lanes and validity
  have hl1 : (fields o.L.height (j % 8)).1.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; omega
  have hl2 : (fields o.L.height (j % 8)).2.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; split_ifs <;> omega
  have hv1 : (BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have hv2 : (BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have o1 := out1_entry H C bpl haux hpc hk hoD hl1 hx (lo_mem o.L.height hj8) hv1
  have o2 := out1_entry H C bpl haux hpc hk hoD hl2 hx (hi_mem o.L.height hj8) hv2
  have c1 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2), 1, j % 8) = (lay C).fl + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte, Nat.add_zero]; rfl
  have c2 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2), 2, j % 8) = (lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte]; rfl
  have hlane : ∀ l ≤ 2, ansLane C.p (o.pe + j / 8) + l < 2 ^ (lay C).m := by
    intro l hl
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by omega)]; omega
  have hl1' : (fields o.L.height (j % 8)).1.1 ≤ 2 := by
    simp only [fields]; omega
  have hl2' : (fields o.L.height (j % 8)).2.1 ≤ 2 := by
    simp only [fields]; split_ifs <;> omega
  have hs' : ∀ l < 2 ^ (lay C).m, memK Q pl groups arrs aux L hτ q l = laneK ws l := fun l hl => by
    have := hs l hl; rwa [show (lay C).sb = 0 from rfl, Nat.zero_add] at this
  unfold Out1 at o1 o2
  rw [← c1, ← c2, o1, o2, hs' _ (hlane _ hl1'), hs' _ (hlane _ hl2')]
  exact fields_posL C.p ws (o.pe + j / 8) (by omega) hH h192

/-! ## `PosOk` -/

/-- **`F`'s positions lanes and Q_link's openings** (a static fact of the schedule and `F`'s layout,
decidable on the frozen parameter set): level `i` of `Ls` (positions lanes from `V`) is opening `k0 + i`
of the plan, of height at most 64, and `F` reads that opening's positions answers (72 bytes each) at the
answers' lanes. -/
def PosLanes (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    ∀ x < nAns ((opens p).getD (k0 + i) default),
      8 * (posLanes g ood Ls V).getD i 0 + 72 * x + 40 = 8 * ansLane p (((opens p).getD (k0 + i) default).pe + x)

/-- **`PosOk` from the position cells' values** (`F`'s positions are `posL`, `qsAt_posL`). -/
theorem posOk_of (C : SCfg) (k0 : ℕ) (hpb : ∀ i, C.pb i = posBase cfg20 (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : PosLanes P20 C.g C.ood Ls V k0) {M : Mem} {ws : List Word} (hS : StreamOk P20) (hL : LaneLink P20 ws)
    (hQ : QOk P20 (lay cfg20))
    (hcell : ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t, M.k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 ws (((opens P20).getD k default).pe + j / 8) (j % 8 * ((opens P20).getD k default).L.height)
          ((opens P20).getD k default).L.height)) :
    PosOk C M (traceBytesB (decode P20 ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decode hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens P20).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens P20).getD (k0 + i) default ∈ opens P20 := by
    -- `Option.getD_some` by `rw`: left to defeq, the kernel evaluates `opens P20` (1.5 s)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hjt
  have hin := lanes_in hS h1 hlt
  have hab := ansLane_bound hS hL.size hlt
  have e1 : posBase cfg20 (k0 + i) + j = nK cfg20 + posIdx P20 (k0 + i) j := by
    have hp : cfg20.p = P20 := rfl
    simp only [posBase, posIdx, hp]; omega
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens P20).getD (k0 + i) default) := by unfold nAns; omega
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane P20 (((opens P20).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen P20 := by
    simp only [ansLane, if_neg (show ((opens P20).getD (k0 + i) default).pe + j / 8 ≠ 0 by omega)]; omega
  rw [qsAt_posL P20 ws _ _ _ j hj (hP _ hx) hb hlen (by omega), hLeq]
  rfl

section P20

theorem cfg20_p : cfg20.p = P20 := by unfold cfg20; rfl

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}
  {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}

/-- **The position cells of the `P20` node program** (Q_link's `posLoop`, `qlink_pos`) hold
`kOf (posL …)` of the child's stream, on a good pair with the input map. -/
theorem posCells20
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D)
      (arrsX x))
    (hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodN T hτ x qm qr)
    (mp : InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm
      qr) :
    ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t,
      (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
          (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height) ((opens P20).getD k default).L.height) := by
  intro k hk hH j hj
  have H := auxH20 hT hst hinb hok hb hG
  obtain ⟨hl, -, -⟩ := parts_of_aux H
  have hk' : k < (opens cfg20.p).length := by rw [cfg20_p]; exact hk
  have hH' : ((opens cfg20.p).getD k default).L.height ≤ 64 := by rw [cfg20_p]; exact hH
  have hj' : j < ((opens cfg20.p).getD k default).L.t := by rw [cfg20_p]; exact hj
  have hv := posVal_of H cfg20 (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc
    (by rw [cfg20_p]; exact hS) (by rw [cfg20_p]; exact hQ) mp.stream hk' hH' hj'
  rw [cfg20_p] at hv
  have hq := qlink_pos (pt := p0 (nK cfg20) 0) hQ hl.1 hk hj
  exact hq.trans hv

/-- **`harith_core`'s `hposr`**: `C_rec`'s position cells hold `F`'s positions. -/
theorem posOkR20
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D)
      (arrsX x))
    (hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hPL : PosLanes P20 P20.grind false P20.recLevels (openU P20 + 15) 0) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      PosOk (cfgRec P20 (posBase cfg20) (pwBase cfg20))
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr)
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) 0 P20.recLevels (openU P20 + 15) := by
  intro vk c x qm qr hok hb hG mp hL
  exact posOk_of _ 0 (fun i => by rw [Nat.zero_add]; rfl) hPL hS hL hQ
    (posCells20 hT hst hinb hS hQ hpc hok hb hG mp)

/-- **`harith_core`'s `hposm`**: `C_main`'s position cells (openings `1 + i`) hold `F`'s positions. -/
theorem posOkM20
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D)
      (arrsX x))
    (hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hPL : PosLanes P20 P20.grind P20.mainOod P20.mainLevels
      (stackEndL P20.grind false P20.recLevels (openU P20 + 15) + 15) 2) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20))
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr)
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) 0 P20.mainLevels
        (stackEndL P20.grind false P20.recLevels (openU P20 + 15) + 15) := by
  intro vk c x qm qr hok hb hG mp hL
  have h2 : P20.recLevels.length = 2 := by decide +kernel
  exact posOk_of _ 2 (fun i => by show posBase cfg20 (P20.recLevels.length + i) = _; rw [h2]) hPL hS hL hQ
    (posCells20 hT hst hinb hS hQ hpc hok hb hG mp)

end P20

end Lvm.Fin
