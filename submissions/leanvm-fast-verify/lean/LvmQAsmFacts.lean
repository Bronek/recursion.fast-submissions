-- New for lvm (WP-16a-QFX): the static layout facts of the assembled `P20` node program
-- (`LvmQAsmProg.Q cfg20`) in the form WP-14c's `nodeSound_layout` (LvmNodeSoundLayout) asks.
import LvmQAsmV
import LvmNodeSoundLayout
import LvmVEqMid

/-!
# The node program's layout facts

For `lay := lay cfg20`, `I := sigIn cfg20`, `qa := qarith cfg20`, `nK := nK cfg20`, `nE := 0`, the input
arrays `arrs cfg20 data20 (pubX x)` and `aux := aux cfg20 data20`:

* the program's cell counts from its segments (`cells_toProgram`: no `group` in the kernel), hence
  `nK ≤ cells .K` and Q_arith's pointer below it (`p2_le_cells`);
* the region facts `hfg20 … hslI20`, `hws20`, `hR20`, `hNs20`, `hP20`, Q_link's `hQ20`, `hS20`, `haux20`,
  `auxSeeds20` (rfl or small `decide`s on `cfg20`'s numbers);
* the placements of the input arrays (`hSt20 … hMd20`, A19) and the `PUB` array (`hPub20`): the
  header's lanes are the statement's public values (`hdrOfPub_pubX : hdrOfPub (pubX x) = hdrLanes x`).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits Lvm.NS
open Lvm.VEq

/-! ## The cell counts of a gadget's program -/

theorem advBs_nil (p : Ptr) : p.advBs [] = p := by simp [Ptr.advBs]

theorem advBs_glueB (p : Ptr) (rs : List Row) (bs : List Block) :
    p.advBs (glueB rs bs) = (p.adv (rs.map .row)).advBs bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    rw [Ptr.advBs_cons, advBs_glue]

/-- Grouping keeps the pointer. -/
theorem groupAux_adv : ∀ (p : Ptr) (δ : List Seg),
    (p.adv ((groupAux δ).1.map .row)).advBs (groupAux δ).2 = p.adv δ
  | p, [] => by simp [groupAux, advBs_nil]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [List.map_cons, List.map_nil]
      rw [advBs_glueB, groupAux_adv _ δ, ← Ptr.adv_cons]
    · simp only [List.map_cons]
      rw [Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), groupAux_adv _ δ, ← Ptr.adv_cons]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [List.map_nil, Ptr.adv_nil]
    rw [Ptr.advBs_cons, advBs_blk, advBs_glueB, groupAux_adv _ δ, ← Ptr.adv_cons]

theorem advBs_group (p : Ptr) (δ : List Seg) : p.advBs (group δ) = p.adv δ := by
  rw [group_eq, advBs_glueB, groupAux_adv]

/-- **A gadget's program's cell counts** are its pointer after its segments. -/
theorem cells_toProgram {α : Type} (nK nE : ℕ) (m : BM α) :
    (toProgram nK nE m).cells .K = ((⟨nK, nE⟩ : Ptr).adv (m ⟨nK, nE⟩).2).k ∧
      (toProgram nK nE m).cells .E = ((⟨nK, nE⟩ : Ptr).adv (m ⟨nK, nE⟩).2).e := by
  have h := start_ptr (toProgram nK nE m) (toProgram nK nE m).blocks.length
  rw [List.take_length] at h
  have hb : (toProgram nK nE m).blocks = group (m ⟨nK, nE⟩).2 := rfl
  have hp : ((⟨(toProgram nK nE m).nInK, (toProgram nK nE m).nInE⟩ : Ptr)) = ⟨nK, nE⟩ := rfl
  rw [hb, hp, advBs_group] at h
  exact ⟨congrArg Ptr.k h, congrArg Ptr.e h⟩

theorem nK_le_cells {α : Type} (nK nE : ℕ) (m : BM α) : nK ≤ (toProgram nK nE m).cells .K := by
  rw [(cells_toProgram nK nE m).1]
  exact Nat.le_add_right _ _

/-- **Q_arith's pointer lies inside the program.** -/
theorem p2_le_cells {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ) :
    (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K := by
  rw [(cells_toProgram nK nE _).1]
  have e : (qprog lay I qa ⟨nK, nE⟩).2 =
      (qlink P20 lay (p0 nK nE)).2 ++ ((qsig I (p1 lay nK nE)).2 ++ (qa (p2 lay I nK nE)).2) := rfl
  rw [e, Ptr.adv_append, Ptr.adv_append]
  exact Nat.le_add_right _ _

/-! ## The regions (`cfg20`) -/

theorem hfg20 : (lay cfg20).fg = (sigIn cfg20).flag := rfl
theorem hln20 : (sigIn cfg20).ln = 20 := rfl
theorem hhd20 : (sigIn cfg20).hd = (lay cfg20).sb + 11 := rfl
theorem hyc20 : (sigIn cfg20).yc = (sigIn cfg20).ys + 4 * 430 := rfl
theorem hyls20 : (sigIn cfg20).yls = (sigIn cfg20).ys + 4 * 447 := rfl
theorem hyns20 : (sigIn cfg20).yns = (sigIn cfg20).ys + 4 * 448 := rfl
theorem hfl20 : (sigIn cfg20).flag = pbB cfg20 := rfl
theorem hvkI20 : (sigIn cfg20).vk = pbB cfg20 + 1 := rfl
theorem hcLI20 : (sigIn cfg20).cL = pbB cfg20 + 5 := rfl
theorem hslI20 : (sigIn cfg20).sl = pbB cfg20 + 18 := rfl
theorem hws20 : 2 ^ (lay cfg20).m ≤ 17 * 2 ^ 14 := by decide

/-- The node program (`nodeSound_layout`'s `Qn`). -/
abbrev Q20n : Program := Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0

theorem Q20n_eq : Q20n = Q cfg20 := rfl

theorem sigRegLt_mono {C C' : ℕ} {I : SigIn} (h : SigRegLt C I) (hC : C ≤ C') : SigRegLt C' I :=
  ⟨by have := h.sg; omega, by have := h.bi; omega, by have := h.md; omega, by have := h.bd; omega,
    by have := h.bc; omega, by have := h.bx; omega, by have := h.be; omega, by have := h.bp; omega,
    by have := h.hd; omega, by have := h.bh; omega, by have := h.bcl; omega, by have := h.yls; omega,
    by have := h.bls; omega, by have := h.bn; omega⟩

/-- Q_sig's regions are input cells. -/
theorem sigRegLt_nK20 : SigRegLt (nK cfg20) (sigIn cfg20) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem hR20 : SigRegLt (Q20n.cells .K) (sigIn cfg20) := sigRegLt_mono sigRegLt_nK20 (nK_le_cells _ _ _)

theorem hNs20 : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ max (Q20n.cells .K) (Q20n.cells .E) :=
  le_trans (by decide : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ nK cfg20)
    (le_trans (nK_le_cells _ _ _) (le_max_left _ _))

theorem hP20 : (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0).k ≤ Q20n.cells .K := p2_le_cells _ _ _ _ _

/-- Q_link's stream facts (QL's `streamOk_P20`). -/
theorem hS20 : StreamOk P20 := Lvm.QLink.streamOk_P20

/-- `a + slenS (ls.take i)` in one walk of `ls` (`eLane p i = offAt (lens p) 1 i / 8`). -/
def offAt : List ℕ → ℕ → ℕ → ℕ
  | _, a, 0 => a
  | [], a, _ + 1 => a
  | l :: ls, a, i + 1 => offAt ls (a + (40 + l)) i

theorem offAt_eq : ∀ (ls : List ℕ) (a i : ℕ), offAt ls a i = a + slenS (ls.take i)
  | _, a, 0 => by simp [offAt, slenS]
  | [], a, _ + 1 => by simp [offAt, slenS]
  | l :: ls, a, i + 1 => by
    rw [offAt, offAt_eq ls _ i]
    simp only [slenS, List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- `qOkB` with the caps' lanes through `offAt` (one walk of the plan's lengths per opening instead of
`take`, `map`, `sum`). -/
def qOkF (p : Params) (lay : Layout) : Bool :=
  decide ((qltEntries p lay).length ≤ 2 ^ lay.aQ) && decide (hashedLen p / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) && decide (hashedLen p < 2 ^ 64) &&
    ((opens p).all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (offAt (lens p) 1 o.ce / 8 + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide (((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa)

theorem qOkF_eq (p : Params) (lay : Layout) : qOkF p lay = qOkB p lay := by
  have h : ∀ i, offAt (lens p) 1 i / 8 = eLane p i := fun i => by rw [offAt_eq]; rfl
  simp only [qOkF, qOkB, h]

set_option maxRecDepth 200000 in
/-- **Q_link's static checks** on the node program's layout (`qOkB` reads `sb`, `m`, `K`, `aQ`, `pa`;
decided as `qOkF`). -/
theorem hQ20 : QOk P20 (lay cfg20) :=
  qOk_of Lvm.QLink.streamOk_P20 (by rw [← qOkF_eq, P20_eq]; decide +kernel)

/-- **`aux` is Q_sig's six `BITS` tables, then the position classes and the `s'` byte shifts.** -/
theorem haux20 : aux cfg20 data20 =
    (sigSpecs (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (bplOf data20)).map
      BitsTab.BSpec.tab ++ ((posSpecs cfg20 fun c => bplOf data20 (6 + c)) ++
        [sSpec cfg20 (bplOf data20 (6 + nPosCls cfg20))]).map BitsTab.BSpec.tab := by
  unfold aux bspecs
  rw [List.append_assoc, List.map_append]
  rfl

theorem auxSeeds20 : ∀ t ∈ aux cfg20 data20, t.seeds = [] := fun t ht => by
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp ht
  rfl

/-! ## The statement's header lanes -/

theorem getB_rep (n m : ℕ) (x : List UInt8) :
    (⟨(List.replicate n 0 ++ x).toArray⟩ : ByteArray).get! (n + m) = x.getD m 0 := by
  show (List.replicate n 0 ++ x).toArray[n + m]! = _
  simp [List.getElem?_append_right, List.getD_eq_getElem?_getD]
  rfl

theorem laneAt_congr {b b' : ByteArray} {o o' : ℕ} (h : ∀ i, b.get! (o + i) = b'.get! (o' + i)) :
    laneAt b o = laneAt b' o' := by
  simp only [laneAt, h]

theorem kAt_sig (x : List UInt8) (m : ℕ) : kAt (sigOfX x) (88 + m) = kAt (hdrBytesX x) (8 + m) := by
  unfold kAt
  congr 1
  refine laneAt_congr fun i => ?_
  rw [Nat.add_assoc, Nat.add_assoc]
  exact (getB_rep 88 (m + i) x).trans (getB_rep 8 (m + i) x).symm

theorem hdrLane_eq (x : List UInt8) (k : ℕ) : hdrLane x k = kAt (hdrBytesX x) (8 + 8 * k) := by
  simp only [hdrLane, kAt]
  congr 1
  exact UInt64.ofNat_toNat

theorem digestAt_getD (b : ByteArray) (o n : ℕ) (h : n < 32) :
    (digestAt b o).toArray.getD n 0 = b.get! (o + n) := by
  simp [digestAt, Array.getD, h]

theorem digestLanes_digestAt (b : ByteArray) (o : ℕ) :
    digestLanes (digestAt b o) = (List.range 4).map fun i => kAt b (o + 8 * i) := by
  unfold digestLanes
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 4 := List.mem_range.mp hi
  simp only [kAt, laneAt]
  congr 1
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega),
    digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega),
    digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega)]
  simp only [UInt64.zero_or, Nat.add_assoc]

/-- **The `PUB` values are the header's lanes**: V_S's public values of a statement (`pubX`,
WP-14a) in `hdrOfPub`'s order are WP-14c's `hdrLanes` (the little-endian words from byte 8). -/
theorem hdrOfPub_pubX (x : List UInt8) : hdrOfPub (pubX x) = hdrLanes x := by
  have hk : ∀ j m, headerAt j + m = 88 + (j - 8 + m) := fun j m => by simp only [headerAt]; omega
  have hL : ∀ (a n : ℕ), (List.range n).map (fun i => kAt (sigOfX x) (headerAt (8 + 8 * a) + 8 * i)) =
      (List.range n).map fun i => hdrLane x (a + i) := fun a n => List.map_congr_left fun i _ => by
    rw [hk, kAt_sig, hdrLane_eq]; congr 1; omega
  have hD : ∀ (a : ℕ), (List.range 4).map (fun i => kAt (hdrBytesX x) (8 + 8 * a + 8 * i)) =
      (List.range 4).map fun i => hdrLane x (a + i) := fun a => List.map_congr_left fun i _ => by
    rw [hdrLane_eq]; congr 1; omega
  have h0 : ∀ a, (⟨laneAt (sigOfX x) (headerAt (8 + 8 * a))⟩ : FK) = hdrLane x a := fun a => by
    have := kAt_sig x (8 * a); simp only [kAt] at this
    rw [show headerAt (8 + 8 * a) = 88 + 8 * a by simp only [headerAt]; omega, this, hdrLane_eq]; rfl
  -- A23: `acc_in`'s 29 scalars are header lanes `615 + 3i + t`
  have hE0 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i)) = hdrLane x (615 + 3 * i) := fun i => by
    have h := hk (offAcc + eBytes * i) 0
    rw [Nat.add_zero] at h
    rw [h, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hE1 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i) + 8) = hdrLane x (615 + (3 * i + 1)) :=
    fun i => by rw [hk, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hE2 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i) + 16) = hdrLane x (615 + (3 * i + 2)) :=
    fun i => by rw [hk, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hA : ∀ n, ((List.range n).map fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))).flatMap FE.lanes =
      (List.range (3 * n)).map fun i => hdrLane x (615 + i) := fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatMap_append, ih,
        show 3 * (n + 1) = 3 * n + 3 by omega, List.range_add, List.map_append, List.map_map]
      congr 1
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, FE.lanes, feAt]
      rw [hE0, hE1, hE2]
      rfl
  unfold hdrLanes
  rw [show pubLanes = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accVars + 1) from rfl]
  simp only [List.range_add, List.map_append, List.map_map]
  unfold hdrOfPub pubX pubOf Pub.hdrLanes
  rw [show (List.range accVars).map (fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))) ++
      [feAt (sigOfX x) (headerAt (offAcc + eBytes * accVars))] =
      (List.range (accVars + 1)).map (fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))) from by
    rw [List.range_succ, List.map_append]; rfl, hA]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]
  rw [show (hdX x).vk = digestAt (hdrBytesX x) (8 + 8 * 1) from rfl, digestLanes_digestAt, hD 1,
    show headerAt 48 = headerAt (8 + 8 * 5) from rfl, hL 5, show headerAt 80 = headerAt (8 + 8 * 9) from rfl,
    hL 9, show headerAt 120 = headerAt (8 + 8 * 14) from rfl, hL 14,
    show headerAt 152 = headerAt (8 + 8 * 18) from rfl, hL 18,
    show headerAt 8 = headerAt (8 + 8 * 0) from rfl, h0 0, show headerAt 112 = headerAt (8 + 8 * 13) from rfl,
    h0 13]
  rfl

/-! ## The input arrays' placement (A19) -/

theorem bundle_of_mem {arrs : List InArr} {s τ base : ℕ} {rec : Bool} {off : ℕ → ℕ}
    (h : ∀ l < s, ∃ a ∈ arrs, a.ty = .K ∧ a.pub = none ∧ a.τ = τ ∧ a.base = base + l ∧ a.stride = s ∧
      a.val = [(rec, off l)]) : Bundle arrs s τ base rec off := fun l hl => by
  obtain ⟨a, ha, hr⟩ := h l hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  exact ⟨k, hk, hr⟩

section Arrs

variable (P : Pub)

theorem mem_arrs_st {l : ℕ} (hl : l < 17) :
    (⟨.K, cfg20.rl, l, 17, [(true, l * 2 ^ cfg20.rl)], fin data20 l, none⟩ : InArr) ∈ arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)))))

theorem mem_arrs_sg :
    (⟨.K, 10, sgB cfg20, 1, [(true, 17 * 2 ^ cfg20.rl)], fin data20 17, none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _)))))

theorem mem_arrs_xs {l : ℕ} (hl : l < 17) :
    (⟨.K, 9, xsB cfg20 + l, 17, [(false, xOff cfg20 + l * 2 ^ cfg20.rl)], fin data20 (18 + l), none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))))

theorem mem_arrs_ys {l : ℕ} (hl : l < 4) :
    (⟨.K, 9, ysB cfg20 + l, 4, [(false, ksY cfg20 l + 2 ^ cfg20.rl)], fin data20 (35 + l), none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)))

theorem mem_arrs_md {l : ℕ} (hl : l < 4) :
    (⟨.K, 0, mdB cfg20 + l, 4, [(false, ksY cfg20 l + (spongeBlocks cfg20.p - 1))], fin data20 (39 + l),
      none⟩ : InArr) ∈ arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))

theorem mem_arrs_pub :
    pubArr 10 (pbB cfg20) 1 (false, 0) (fin data20 43) (hdrOfPub P) ∈ arrs cfg20 data20 P :=
  List.mem_append_right _ List.mem_cons_self

end Arrs

theorem ksY20 (l : ℕ) : ksY cfg20 l = 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) := by
  simp only [ksY, cfg20, if_true]
  ring

/-- **The stream** (a 17-bundle on `C_rec`, column `l` at word `l·2^14`). -/
theorem hSt20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 17 14 (lay cfg20).sb true fun l => l * 2 ^ 14 :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_st _ hl, rfl, rfl, rfl, (Nat.zero_add l).symm, rfl, rfl⟩

/-- **`σ'`** (`C_rec` word `17·2^14`). -/
theorem hSg20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 1 10 (sigIn cfg20).sg true fun _ => 17 * 2 ^ 14 :=
  bundle_of_mem fun l hl => by
    obtain rfl : l = 0 := by omega
    exact ⟨_, mem_arrs_sg _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`KS`'s `X` message lanes** (a 17-bundle on `C_main`). -/
theorem hX20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 17 9 (sigIn cfg20).xs false fun l => ksY2 + 2 ^ 19 + l * 2 ^ 14 :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_xs _ hl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`KS`'s output lanes 0–3 of rows `[2^14, 2^14 + 2^9)`** (a 4-bundle). -/
theorem hY20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 4 9 (sigIn cfg20).ys false
      fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + 2 ^ 14 :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_ys _ hl, rfl, rfl, rfl, rfl, rfl, by rw [ksY20]; rfl⟩

/-- **The trace digest** (`KS` row `B − 1`, a 4-bundle of height 1). -/
theorem hMd20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 4 0 (sigIn cfg20).md false
      fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1) :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_md _ hl, rfl, rfl, rfl, rfl, rfl,
    by rw [ksY20, show cfg20.p = P20 from rfl]⟩

/-- **`PUB`**: the header's lanes at `pbB cfg20`. -/
theorem hPub20 (x : List UInt8) : PubAt (arrs cfg20 data20 (pubX x)) x (pbB cfg20) := by
  have h := mem_arrs_pub (pubX x)
  rw [hdrOfPub_pubX] at h
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem h
  exact ⟨k, hk, _, _, he⟩

end Lvm.QAsm
