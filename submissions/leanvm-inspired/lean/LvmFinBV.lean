-- New for lvm (WP-16a2, FIN-BV): memory facts of WP-16a's `P20` node program that `NodeBase.hpos`
-- and HAR's `harith_core` (via the `harith` bridge) take, on the interpreter's memory of a good pair:
-- `AuxHyps` from `NodeBase`'s `hT`, `hst` and `NodeHyp.hinb` (as `nodeSound_main`), then WP-12b's
-- `out1_at`/`sigBitsOk`, WP-14c's `sig_of_aux` and QL's `qin_bits`. `posBits_of` is adapted from
-- INB's `capCov_pos` (LvmQAsmInb).
import LvmQAsmInb
import LvmQAsmFacts
import LvmQAsmHarPos
import LvmQLinkBits
import LvmQWireSound

/-!
# `BITS` facts of the `P20` node program

For `Q = Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0` on the tables
`lvmTabs Q pl groups (arrsX x) (aux cfg20 D)` (any placement, groups, arrays, record `D`) and any
tables `T` with `hT` (`T = TS M3.tabsP20` for `NodeBase`):

* **`auxH20`**: `loopir_sound`'s hypotheses (`AuxHyps`) on a good pair;
* **`sBits20`**: `SBitsS M.k hd (bsB cfg20)` from the `s'` bit class `sSpec` (its outputs are
  input cells: `bsB cfg20 + 256 ≤ nK cfg20`);
* **`nBits20`**: `NBits M.k ((sigIn cfg20).bn + 2) P20.logN` (`SigBits.n_bit`);
* **`n1_20`**, **`nN_20`**: `1 ≤ n' ≤ 2^logN` of the child's public values (Q_sig's `ChildOk`; `n'` is
  stream lane 24);
* **`posBits_of`**: QL's `PosBits` from the position classes (any configuration);
  **`hpos20`**: `NodeBase.hpos` (QL's `qin_bits`).
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

/-! ## The position classes' `bit` outputs (any configuration) -/

theorem lt_padT {t j : ℕ} (hj : j < t) : j < padT t := by
  obtain ⟨c, hc, h1, h2, h3⟩ := pchunks_cover hj
  have := pchunks_end c hc
  omega

/-- **QL's `PosBits` from the position classes** (adapted from INB's `capCov_pos`): every position bit
cell is the `bit` output of its class's row, in the interpreter's memory. -/
theorem posBits_of {Q : Program} {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr}
    {aux : List Tab} {L : Lay} {hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ} {q : Column L.μ}
    (H : AuxHyps Q pl groups arrs aux L hτ q) (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) :
    PosBits C.p (lay C) (memK Q pl groups arrs aux L hτ q) := by
  constructor
  intro k hk j hj z hz
  obtain ⟨n, hn⟩ : ∃ n, n = j % 8 * ((opens C.p).getD k default).L.height + z := ⟨_, rfl⟩
  have hl0 : n / 64 < nLanes ((opens C.p).getD k default).L.height := by
    have : j % 8 * ((opens C.p).getD k default).L.height ≤ 7 * ((opens C.p).getD k default).L.height :=
      Nat.mul_le_mul_right _ (by omega)
    unfold QAsm.nLanes; omega
  obtain ⟨c, hS⟩ := mem_posSpecs C bpl hk hl0
  have hpc := hpc k hk (n / 64) hl0
  have hjp := lt_padT hj
  rw [← hn]
  generalize (opens C.p).getD k default = o at hj hz hn hS hpc hjp ⊢
  generalize hH : o.L.height = Hh at hz hn hS hpc ⊢
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hn8 : n < 8 * Hh := by
    have : j % 8 * Hh ≤ 7 * Hh := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnH : n / Hh = j % 8 := by
    rw [hn, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hz, Nat.zero_add]
  have hnm : n % Hh = z := by
    rw [hn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  have hdm := Nat.div_add_mod n 64
  obtain ⟨hlen, hget⟩ := laneOuts_bit (H := Hh) (l := n / 64) (z := n % 64) (Nat.mod_lt _ (by norm_num))
    (by omega)
  have hlen' : n % 64 < ((laneOuts Hh (n / 64)).map (·.1)).length := by rw [List.length_map]; exact hlen
  have hout : ((laneOuts Hh (n / 64)).map (·.1)).getD (n % 64) (.bit 0) = .bit (n % 64) := by
    rw [List.getD_eq_getElem _ _ hlen', List.getElem_map, ← List.getD_eq_getElem _ (.bit 0, 0, 0) hlen, hget]
  have hoc : posCell C k o (j / 8) ((laneOuts Hh (n / 64)).getD (n % 64) (.bit 0, 0, 0)) =
      bitBase C.p (lay C) k + Hh * j + z := by
    rw [hget, show 64 * (n / 64) + n % 64 = n by omega]
    have hjj : 8 * (j / 8) + n / Hh = j := by rw [hnH]; omega
    simp only [posCell, hH, hjj, if_pos hjp, hnm]
  have hx : j / 8 < nRows o := by unfold nRows; omega
  have hA : ansLane C.p (o.pe + j / 8) + n / 64 = (lay C).sb + ansLane C.p (o.pe + j / 8) + n / 64 := by
    show _ = 0 + _ + _; rw [Nat.zero_add]
  exact out1_at Q pl groups arrs aux L hτ q H _ (haux _ hS) (le_two_pow_clog2 _) rfl (j / 8) (n % 64) hx
    hlen' ⟨fun _ => (hpc (j / 8) hx).1, fun jo hjo => (hpc (j / 8) hx).2 jo (by simpa using hjo)⟩ hA hoc
    hout (Nat.mod_lt _ (by norm_num))

/-! ## The `P20` node program -/

section P20

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}
  {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}

/-- **`loopir_sound`'s hypotheses on a good pair** (`nodeSound_main`'s `H`), from `NodeBase`'s `hT`,
`hst` and `NodeHyp.hinb`. -/
theorem auxH20
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
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodN T hτ x qm qr) :
    AuxHyps (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D) lay26
      (hτ' x) (stackOf lay26 qm qr) :=
  ⟨(hst x).wf, (hst x).grp, (hst x).inOk, (hst x).auxSeeds, (hst x).cnt, (hst x).len, (hst x).inj,
    m3Holds_congr (hT x) hG.1, hinb vk c x qm qr hok hb hG⟩

/-- **The bits of `s'`** (`harith_core`'s `hsb`, lvm2 S2): the class `sSpec` (last of `aux`) reads stream
lane `hd + 9 + l = 20 + l` and writes its 64 `bit` outputs at `bsB + 64 l + z`; they are input cells
(`hbs`, a static bound like `PosCellsLt`). -/
theorem sBits20
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
    (hbs : bsB cfg20 + 256 ≤ nK cfg20) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      Lvm.Q1.SBitsS (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ'
        x qm qr).k (sigIn cfg20).hd (bsB cfg20) := by
  intro vk c x qm qr hok hb hG l hl z hz
  have H := auxH20 hT hst hinb hok hb hG
  have hK : nK cfg20 ≤ (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K :=
    nK_le_cells _ _ _
  have h24 : 24 ≤ nK cfg20 := by decide
  have hS : (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).tab ∈ aux cfg20 D :=
    List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _))
  have hlen : (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).outs.length = 64 := by
    show ((List.range 64).map BOut.bit).length = 64; simp
  have hc : ((sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).rd = true →
      (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).wc l <
        (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) ∧
      ∀ j < (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).outs.length,
        (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).oc j l <
          (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K :=
    ⟨fun _ => show 11 + 9 + l < _ by omega, fun j hj => by
      rw [hlen] at hj
      show bsB cfg20 + 64 * l + j < _
      omega⟩
  have hn : (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).n ≤ 2 ^ (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).τ :=
    show 4 ≤ 2 ^ 2 by decide
  have hout : (sSpec cfg20 (bplOf D (6 + nPosCls cfg20))).out z = .bit z := by
    show ((List.range 64).map BOut.bit).getD z (.bit 0) = .bit z
    rw [List.getD_eq_getElem _ _ (by simpa using hz)]
    simp
  exact out1_at _ pl groups (arrsX x) (aux cfg20 D) lay26 (hτ' x) _ H _ hS hn rfl l z hl (by rw [hlen]; exact hz)
    hc rfl rfl hout (show z < 64 from hz)

/-- **The bits of the child's `n'`** (`harith_core`'s `hnb`): Q_sig's class `sN` (`SigBits.n_bit`). -/
theorem nBits20 {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab}
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
    (haux : aux cfg20 D = (sigSpecs (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl).map
      BitsTab.BSpec.tab ++ rest)
    (hR : SigRegLt ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) (sigIn cfg20))
    (hP : (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0).k ≤
      (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      NBits (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm
        qr).k ((sigIn cfg20).bn + 2) P20.logN := by
  intro vk c x qm qr hok hb hG j hj
  have H := auxH20 hT hst hinb hok hb hG
  have hTabs : SigTabsIn (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl (aux cfg20 D) := by
    rw [haux]; exact sigTabsIn_append _ _ bpl rest
  have hsb := sigBitsOk _ pl groups (arrsX x) (aux cfg20 D) lay26 (hτ' x) _ H (sigIn cfg20) _ bpl hTabs
    (sigCellsLt_qsig bpl hR hP) ⟨by decide, by decide⟩
  have hlog : P20.logN = 20 := rfl
  rw [hlog] at hj
  exact SigBits.n_bit hsb j (show j ≤ 20 by omega)

/-- `Σ` holds the seed query: `hashedLen ≥ 5,736` on every plan with `StreamOk`. -/
theorem hashedLen_ge {p : Params} (hS : StreamOk p) : 5736 ≤ hashedLen p := by
  have h := entry_end p (i := 1) (by have := plan_length_ge p; omega)
  have h1 : ((plan p).getD 1 default).len = 5648 := by rw [plan_one]; decide
  rw [bOff_one, h1, ← hS.2] at h
  omega

/-- **`1 ≤ n'`** (`harith_core`'s `hn1`): Q_sig's `ChildOk` on the child's header lane `n'` (stream
lane 24), which is `pubOf`'s `n` on `Σ' = sigma` (`traceBytesB_decode`, `kAt_sigma`). -/
theorem n1_20 {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab}
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
    (hS : StreamOk P20)
    (haux : aux cfg20 D = (sigSpecs (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl).map
      BitsTab.BSpec.tab ++ rest)
    (hR : SigRegLt ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) (sigIn cfg20))
    (hP : (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0).k ≤
      (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      1 ≤ (pubOf vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))))).n := by
  intro vk c x qm qr hok hb hG mp hL
  have H := auxH20 hT hst hinb hok hb hG
  have hTabs : SigTabsIn (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl (aux cfg20 D) := by
    rw [haux]; exact sigTabsIn_append _ _ bpl rest
  have hks := sigKSin_of_goodK hG.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨-, hch⟩ := sig_of_aux H mp.flag hks bpl hTabs (sigCellsLt_qsig bpl hR hP) rfl
  have h1 : 1 ≤ ((memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ'
      x qm qr).k ((sigIn cfg20).hd + 13)).val.toNat := hch.2.2.1
  rw [mp.hd 13 (by norm_num)] at h1
  have hlen := hashedLen_ge hS
  have hws : (wsOf (Lvm.X.laneOf (wOfCol qr))).length = 17 * 2 ^ 14 := by simp [wsOf]
  have hk := kAt_sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) 24 (by omega) (by omega)
  rw [traceBytesB_decode hS hL]
  show 1 ≤ (laneAt (sigma P20 _) (headerAt 112)).toNat
  rw [show headerAt 112 = 8 * 24 from rfl,
    show laneAt (sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) (8 * 24) =
      (kAt (sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) (8 * 24)).val from rfl, hk]
  exact h1

/-- **`n' ≤ 2^logN`** (`harith_core`'s `hnN`, T-V's `dRange`): `ChildOk`'s upper bound, as `n1_20`. -/
theorem nN_20 {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab}
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
    (hS : StreamOk P20)
    (haux : aux cfg20 D = (sigSpecs (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl).map
      BitsTab.BSpec.tab ++ rest)
    (hR : SigRegLt ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) (sigIn cfg20))
    (hP : (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0).k ≤
      (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).cells .K) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      (pubOf vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))))).n ≤ 2 ^ P20.logN := by
  intro vk c x qm qr hok hb hG mp hL
  have H := auxH20 hT hst hinb hok hb hG
  have hTabs : SigTabsIn (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 bpl (aux cfg20 D) := by
    rw [haux]; exact sigTabsIn_append _ _ bpl rest
  have hks := sigKSin_of_goodK hG.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨-, hch⟩ := sig_of_aux H mp.flag hks bpl hTabs (sigCellsLt_qsig bpl hR hP) rfl
  have h1 : ((memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ'
      x qm qr).k ((sigIn cfg20).hd + 13)).val.toNat ≤ 2 ^ P20.logN := hch.2.2.2.1
  rw [mp.hd 13 (by norm_num)] at h1
  have hlen := hashedLen_ge hS
  have hws : (wsOf (Lvm.X.laneOf (wOfCol qr))).length = 17 * 2 ^ 14 := by simp [wsOf]
  have hk := kAt_sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) 24 (by omega) (by omega)
  rw [traceBytesB_decode hS hL]
  show (laneAt (sigma P20 _) (headerAt 112)).toNat ≤ _
  rw [show headerAt 112 = 8 * 24 from rfl,
    show laneAt (sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) (8 * 24) =
      (kAt (sigma P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) (8 * 24)).val from rfl, hk]
  exact h1

/-- **`NodeBase.hpos`**: Q_link's position bit cells are the answers' bits (QL's `qin_bits`, from the
position classes' `bit` outputs `posBits_of` and the stream cells `stream_cells`). -/
theorem hpos20
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
    (hlay : ∀ x, LayOk lay26 (lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups
      (arrsX x) (aux cfg20 D)))
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hSt : ∀ x, Bundle (arrsX x) 17 14 (lay cfg20).sb true fun l => l * 2 ^ 14)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
            (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0 := by
  intro vk c x qm qr hok hb hG
  have H := auxH20 hT hst hinb hok hb hG
  have hs : ∀ L < 2 ^ (lay cfg20).m,
      (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
        ((lay cfg20).sb + L) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) L :=
    fun L hL => stream_cells H (hlay x) (hSt x) (lt_of_lt_of_le hL hws20)
  exact qin_bits hS hQ hs
    (posBits_of H cfg20 (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc)

end P20

end Lvm.Fin
