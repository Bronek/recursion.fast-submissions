-- New for lvm (WP-11b-QL): the round trip of `reassemble`, part 1. The induction mirrors
-- `LvmReplayDrive` (new for lvm) in the forward direction; no FR or leanerVM source.
import LvmReplay

/-!
# Round trip, part 1: an accepting run of the driver on any `π`

`LvmReplayDrive` runs the driver on `reassemble tr` against a trace that meets its plan. Here the
direction is reversed: `π` is arbitrary and the trace is whatever the accepting run consumed. Every
query the driver asks is the trace's entry (`runSeq` checks it), so the entries meet their plan
(`Good`), and the bytes of `π` the driver reads are the entries' contributions (`contrib`), in order.

* `RInv`: the driver's state against the walk's: the log, the FS state, the cursor, the **prefix**
  `(bl π).take pend = hdr8 ++ bodyTo tr (plan p) i` (the contributions of the entries before `i`),
  the static offset `pend = pOff (plan p) i`, the caps (`CapsRel`), `Good` below `i`.
* The static offset `pOff` (content-free: the driver's cursor moves by fixed amounts) and the bound
  `pOff (plan p) (plan p).length ≤ π.size` (from the header check and `PlanBytes`) keep every read
  inside `π`, so no `extract` is cut short.
* `fs_fwd`, `posLoop_fwd`, `climb_fwd`, `openLoop_fwd`, `item_fwd`, `items_fwd`: one lemma per
  driver function, as in `LvmReplayDrive`.
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## Accepting runs -/

theorem query_fwd {q : ByteArray} {k : Digest → OProg Bool} {tr : Trace} {i : Nat}
    (h : (OProg.query q k).runSeq (tr.drop i) = some true) :
    i < tr.length ∧ qOf tr i = q ∧ (k (aOf tr i)).runSeq (tr.drop (i + 1)) = some true := by
  by_cases hi : i < tr.length
  · rw [drop_cons_getD tr hi] at h
    simp only [OProg.runSeq] at h
    split at h
    · next he => exact ⟨hi, he, h⟩
    · simp at h
  · rw [List.drop_eq_nil_of_le (by omega)] at h
    simp [OProg.runSeq] at h

theorem ask_fwd {q : ByteArray} {s : DSt} {k : DSt → Digest → OProg Bool} {tr : Trace} {i : Nat}
    (h : (ask q s k).runSeq (tr.drop i) = some true) :
    i < tr.length ∧ qOf tr i = q ∧
      (k { s with log := (q, aOf tr i) :: s.log } (aOf tr i)).runSeq (tr.drop (i + 1)) = some true :=
  query_fwd (k := fun a => k { s with log := (q, a) :: s.log } a) h

theorem ret_fwd {b : Bool} {l : Trace} (h : (OProg.ret b).runSeq l = some true) : l = [] ∧ b = true := by
  cases l with
  | nil => simp only [OProg.runSeq, Option.some.injEq] at h; exact ⟨rfl, h⟩
  | cons e l => simp [OProg.runSeq] at h

/-! ## Static offsets -/

/-- The proof bytes entry `e` carries (the length of `contrib` on an entry that meets its plan). -/
def clen (e : PE) : Nat :=
  match e.k with
  | .q0 => 0
  | .fs _ => e.len - 32
  | .leaf => e.len
  | .node .. => 32

/-- The `π` offset of entry `i`'s bytes: the 8 header bytes, then the entries before `i`. -/
def pOff (P : List PE) (i : Nat) : Nat := 8 + ((P.take i).map clen).sum

theorem pOff_succ {P : List PE} {i : Nat} (hi : i < P.length) :
    pOff P (i + 1) = pOff P i + clen (P.getD i default) := by
  simp only [pOff, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.getD_eq_getElem?_getD, Option.getD_some]
  omega

theorem pOff_mono (P : List PE) {i j : Nat} (h : i ≤ j) : pOff P i ≤ pOff P j := by
  simp only [pOff]
  rw [show j = i + (j - i) by omega, List.take_add, List.map_append, List.sum_append]
  omega

/-! ## The body as a prefix -/

/-- The contributions of the entries before `n`. -/
def bodyTo (tr : Trace) (P : List PE) (n : Nat) : List UInt8 :=
  (List.range n).flatMap fun k => contrib tr k (P.getD k default)

theorem bodyTo_succ (tr : Trace) (P : List PE) (n : Nat) :
    bodyTo tr P (n + 1) = bodyTo tr P n ++ contrib tr n (P.getD n default) := by
  simp [bodyTo, List.range_succ, List.flatMap_append]

theorem bodyTo_length (tr : Trace) (P : List PE) : bodyTo tr P P.length = bodyFrom tr P 0 := by
  simp [bodyTo, bodyFrom, List.range_eq_range']

theorem getD_take_drop (l : List UInt8) (a : Nat) {n y : Nat} (hy : y < n) :
    ((l.drop a).take n).getD y 0 = l.getD (a + y) 0 := by
  rw [← getD_drop' l a y]
  simp [List.getD_eq_getElem?_getD, hy]

theorem length_take_drop {l : List UInt8} {a n : Nat} (h : a + n ≤ l.length) : ((l.drop a).take n).length = n := by
  simp only [List.length_take, List.length_drop]; omega

/-! ## The invariant -/

/-- **The driver's state against the walk's** on an accepting run over `tr` on the proof `π`. -/
structure RInv (p : Params) (tr : Trace) (π : ByteArray) (s : DSt) (w : WS) : Prop where
  len : w.i ≤ tr.length
  log : s.log = (tr.take w.i).reverse
  st : s.st = aOf tr w.st
  off : s.off = s.pend + w.pend
  pre : (bl π).take s.pend = hdr8 ++ bodyTo tr (plan p) w.i
  pend : s.pend = pOff (plan p) w.i
  caps : CapsRel tr π s.pend w.pend w.pcaps s.caps w.caps
  good : ∀ x < w.i, Good tr x ((plan p).getD x default)

theorem RInv.congr {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w₁ w₂ : WS} (h : RInv p tr π s w₁)
    (hi : w₁.i = w₂.i) (hp : w₁.pend = w₂.pend) (hs : w₁.st = w₂.st) (hpc : w₁.pcaps = w₂.pcaps)
    (hc : w₁.caps = w₂.caps) : RInv p tr π s w₂ :=
  ⟨hi ▸ h.len, hi ▸ h.log, hs ▸ h.st, hp ▸ h.off, hi ▸ h.pre, hi ▸ h.pend, hp ▸ hpc ▸ hc ▸ h.caps, hi ▸ h.good⟩

/-! ## One Fiat–Shamir query -/

theorem fs_fwd {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w : WS} (hR : RInv p tr π s w)
    (hsz : pOff (plan p) (plan p).length ≤ π.size) (hiP : w.i < (plan p).length)
    (hP : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩) {k : DSt → Digest → OProg Bool}
    (h : (fsQuery π s k).runSeq (tr.drop w.i) = some true) :
    RInv p tr π (dStep tr w.i s) w.stepFS ∧
      (k (dStep tr w.i s) (aOf tr w.i)).runSeq (tr.drop (w.i + 1)) = some true := by
  unfold fsQuery at h
  obtain ⟨hi, hq, hrun⟩ := ask_fwd h
  have hoff1 : s.off = pOff (plan p) (w.i + 1) := by
    rw [pOff_succ hiP, hP, ← hR.pend, hR.off]; simp [clen]
  have hle : s.off ≤ π.size := hoff1 ▸ le_trans (pOff_mono _ (by omega)) hsz
  have hext : bl (π.extract s.pend s.off) = ((bl π).drop s.pend).take w.pend := by
    rw [bl_extract, hR.off, Nat.add_sub_cancel_left]
  have hcl : (((bl π).drop s.pend).take w.pend).length = w.pend :=
    length_take_drop (by rw [← size_bl]; have := hR.off; omega)
  have hblq : bl (qOf tr w.i) = (aOf tr w.st).toList ++ ((bl π).drop s.pend).take w.pend := by
    rw [hq, bl_append, bl_digestBytes, hR.st, hext]
  have hgood : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by
    simp only [Good]
    refine ⟨?_, ?_⟩
    · rw [size_bl, hblq, List.length_append, hcl]; simp
    · rw [hblq, List.take_left' (by simp)]
  refine ⟨⟨by simp [WS.stepFS, WS.settle]; omega, ?_, rfl, by simp [dStep, WS.stepFS, WS.settle], ?_, ?_, ?_, ?_⟩,
    by rw [← hq] at hrun; exact hrun⟩
  · simp only [dStep, WS.stepFS, WS.settle]; rw [take_succ_rev tr hi, hR.log]
  · simp only [dStep, WS.stepFS, WS.settle]
    rw [hR.off, List.take_add, hR.pre, bodyTo_succ, hP, List.append_assoc]
    congr 2
    show _ = (bl (qOf tr w.i)).drop 32
    rw [hblq, List.drop_left' (by simp)]
  · simp only [dStep, WS.stepFS, WS.settle]; exact hoff1
  · simp only [dStep, WS.stepFS, WS.settle]
    refine capsRel_settle (fun y hy => ?_) _ _ _ _ hR.caps
    rw [get!_bl, get!_bl, hblq, List.getD_append_right _ _ _ _ (by simp),
      show 32 + y - (aOf tr w.st).toList.length = y by simp, getD_take_drop _ _ hy]
  · intro x hx
    simp only [WS.stepFS, WS.settle] at hx
    rcases Nat.lt_or_ge x w.i with hx' | hx'
    · exact hR.good x hx'
    · rw [show x = w.i by omega, hP]; exact hgood

/-! ## The positions -/

theorem posLoop_fwd {p : Params} {tr : Trace} {π : ByteArray} (hsz : pOff (plan p) (plan p).length ≤ π.size)
    (h : Nat) (k : DSt → OProg Bool) :
    ∀ (n rem : Nat) (s : DSt) (w : WS), RInv p tr π s w → w.i + n ≤ (plan p).length →
    (∀ x < n, (plan p).getD (w.i + x) default =
      ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩) →
    (posLoop π h n rem s k).runSeq (tr.drop w.i) = some true →
    ∃ s', RInv p tr π s' (WS.stepFS^[n] w) ∧ s'.pos = s.pos ++ posOut tr h w.i n rem ∧
      (k s').runSeq (tr.drop (w.i + n)) = some true
  | 0, rem, s, w, hR, _, _, hrun => ⟨s, hR, by simp [posOut], by simpa [posLoop] using hrun⟩
  | n + 1, rem, s, w, hR, hl, hP, hrun => by
    have hP0 := hP 0 (by omega)
    simp only [ite_true, Nat.add_zero] at hP0
    simp only [posLoop] at hrun
    obtain ⟨hR1, hrun1⟩ := fs_fwd hR hsz (by omega) hP0 hrun
    have hR2 : RInv p tr π { (dStep tr w.i s) with
        pos := (dStep tr w.i s).pos ++ posBatch tr h w.i (min positionsPerAnswer rem) } w.stepFS :=
      ⟨hR1.len, hR1.log, hR1.st, hR1.off, hR1.pre, hR1.pend, hR1.caps, hR1.good⟩
    obtain ⟨s', hR3, hpos3, hrun3⟩ := posLoop_fwd hsz h k n (rem - min positionsPerAnswer rem) _ _ hR2
      (by simp [WS.stepFS, WS.settle]; omega) (fun x hx => by
        have := hP (x + 1) (by omega)
        rw [show w.i + (x + 1) = w.stepFS.i + x by simp [WS.stepFS, WS.settle]; omega] at this
        rw [this]
        rcases x with _ | x <;> simp [WS.stepFS, WS.settle] <;> omega) hrun1
    refine ⟨s', by rw [Function.iterate_succ_apply]; exact hR3, ?_, ?_⟩
    · rw [hpos3]; simp [dStep, posOut, posBatch, List.append_assoc, WS.stepFS, WS.settle]
    · rw [show w.i + (n + 1) = w.stepFS.i + n by simp [WS.stepFS, WS.settle]; omega]; exact hrun3

/-! ## Merkle paths and openings -/

/-- A node entry meets its plan, the cap aside. -/
def NodeOk (tr : Trace) (i pe h j lvl : Nat) : Prop :=
  (qOf tr i).size = 64 ∧
    (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).take 32 else (bl (qOf tr i)).drop 32) =
      (aOf tr (i - 1)).toList

theorem climb_fwd {p : Params} {tr : Trace} {π : ByteArray} (hsz : pOff (plan p) (plan p).length ≤ π.size)
    (pe h j : Nat) (k : DSt → Digest → OProg Bool) :
    ∀ (m lvl : Nat) (cur : Digest) (s : DSt) (i : Nat), i ≤ tr.length →
    s.log = (tr.take i).reverse → (bl π).take s.off = hdr8 ++ bodyTo tr (plan p) i →
    s.off = pOff (plan p) i → cur = aOf tr (i - 1) → i + m ≤ (plan p).length →
    (∀ x < m, ∃ cap, (plan p).getD (i + x) default = ⟨.node pe h j (lvl + x) cap, 64⟩) →
    (climb π (posVal tr pe h j) m lvl cur s k).runSeq (tr.drop i) = some true →
    i + m ≤ tr.length ∧ (∀ x < m, NodeOk tr (i + x) pe h j (lvl + x)) ∧
      (bl π).take (s.off + 32 * m) = hdr8 ++ bodyTo tr (plan p) (i + m) ∧
      s.off + 32 * m = pOff (plan p) (i + m) ∧
      (k { s with off := s.off + 32 * m, log := (tr.take (i + m)).reverse }
        (if m = 0 then cur else aOf tr (i + m - 1))).runSeq (tr.drop (i + m)) = some true
  | 0, lvl, cur, s, i, hi0, hlog, hpre, hoff, _, _, _, hrun => by
    refine ⟨by simpa using hi0, fun x hx => absurd hx (by omega), by simpa using hpre, by simpa using hoff, ?_⟩
    simp only [climb, Nat.mul_zero, Nat.add_zero, ite_true] at hrun ⊢
    rw [← hlog]; exact hrun
  | m + 1, lvl, cur, s, i, _, hlog, hpre, hoff, hcur, hl, hP, hrun => by
    obtain ⟨cap, hPi⟩ := hP 0 (by omega)
    simp only [Nat.add_zero] at hPi
    simp only [climb] at hrun
    obtain ⟨hi, hq, hrun1⟩ := ask_fwd hrun
    have hiP : i < (plan p).length := by omega
    have hoff1 : s.off + 32 = pOff (plan p) (i + 1) := by rw [pOff_succ hiP, hPi, hoff]; rfl
    have hle : s.off + 32 ≤ π.size := hoff1 ▸ le_trans (pOff_mono _ (by omega)) hsz
    have hsl : (((bl π).drop s.off).take 32).length = 32 := length_take_drop (by rw [← size_bl]; omega)
    have hbs : bl (π.extract s.off (s.off + 32)) = ((bl π).drop s.off).take 32 := by
      rw [bl_extract, Nat.add_sub_cancel_left]
    have hblq : bl (qOf tr i) = if (posVal tr pe h j >>> lvl) % 2 = 0 then cur.toList ++ ((bl π).drop s.off).take 32
        else ((bl π).drop s.off).take 32 ++ cur.toList := by
      rw [hq]; split <;> simp only [bl_append, bl_digestBytes, hbs]
    have hq64 : (bl (qOf tr i)).length = 64 := by rw [hblq]; split <;> simp [hsl]
    have hhalf : (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).take 32 else (bl (qOf tr i)).drop 32) =
        cur.toList := by
      rw [hblq]
      split
      · rw [List.take_left' (by simp)]
      · rw [List.drop_left' hsl]
    have hnode : NodeOk tr i pe h j lvl := ⟨by rw [size_bl]; exact hq64, by rw [← hcur]; exact hhalf⟩
    have hcon : contrib tr i ((plan p).getD i default) = ((bl π).drop s.off).take 32 := by
      rw [hPi]
      show (if (bl (qOf tr i)).take 32 = (aOf tr (i - 1)).toList then (bl (qOf tr i)).drop 32
        else (bl (qOf tr i)).take 32) = _
      rw [← hcur, compare_rule hq64 hhalf, hblq]
      split
      · rw [List.drop_left' (by simp)]
      · rw [List.take_left' hsl]
    have hpre1 : (bl π).take (s.off + 32) = hdr8 ++ bodyTo tr (plan p) (i + 1) := by
      rw [List.take_add, hpre, bodyTo_succ, hcon, List.append_assoc]
    rw [← hq] at hrun1
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := climb_fwd hsz pe h j k m (lvl + 1) (aOf tr i)
      { s with off := s.off + 32, log := (qOf tr i, aOf tr i) :: s.log } (i + 1) (by omega)
      (by simp only; rw [take_succ_rev tr hi, hlog]) hpre1 hoff1 (by simp) (by omega)
      (fun x hx => by
        obtain ⟨c, hc⟩ := hP (x + 1) (by omega)
        exact ⟨c, by rw [show i + 1 + x = i + (x + 1) by omega, hc]; congr 2; omega⟩) hrun1
    simp only at ih3 ih4 ih5
    have e1 : i + 1 + m = i + (m + 1) := by omega
    have e3 : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
    refine ⟨by omega, fun x hx => ?_, by rw [← e1, ← e3]; exact ih3, by rw [← e1, ← e3]; exact ih4, ?_⟩
    · rcases x with _ | x
      · simpa using hnode
      · have := ih2 x (by omega)
        rwa [show i + 1 + x = i + (x + 1) by omega, show lvl + 1 + x = lvl + (x + 1) by omega] at this
    · have e2 : (if m = 0 then aOf tr i else aOf tr (i + 1 + m - 1)) =
          (if m + 1 = 0 then cur else aOf tr (i + (m + 1) - 1)) := by
        rcases m with _ | m
        · simp
        · simp only [Nat.add_one_ne_zero, ite_false]; congr 1; omega
      rw [e2, e3, e1] at ih5
      exact ih5

theorem openLoop_fwd {p : Params} {tr : Trace} {π : ByteArray} (hsz : pOff (plan p) (plan p).length ≤ π.size)
    (L : Level) (capOff pe ce co nb : Nat)
    (hcap : ∀ x < nb, π.get! (capOff + x) = (qOf tr ce).get! (co + x))
    (hnb : nodeBytes * 2 ^ (L.height - L.path) ≤ nb) (hp1 : 1 ≤ L.path) (hph : L.path ≤ L.height)
    (k : DSt → OProg Bool) :
    ∀ (m j₀ : Nat) (s : DSt) (i : Nat), i ≤ tr.length → s.log = (tr.take i).reverse →
    (bl π).take s.off = hdr8 ++ bodyTo tr (plan p) i → s.off = pOff (plan p) i →
    Al (plan p) i (openPart L pe ce co j₀ m) →
    (openLoop π L capOff ((List.range' j₀ m).map (posVal tr pe L.height)) s k).runSeq (tr.drop i) = some true →
    i + m * (1 + L.path) ≤ tr.length ∧
      (∀ x < m * (1 + L.path), Good tr (i + x) ((plan p).getD (i + x) default)) ∧
      (bl π).take (s.off + m * (L.row + 32 * L.path)) = hdr8 ++ bodyTo tr (plan p) (i + m * (1 + L.path)) ∧
      s.off + m * (L.row + 32 * L.path) = pOff (plan p) (i + m * (1 + L.path)) ∧
      (k { s with off := s.off + m * (L.row + 32 * L.path),
                  log := (tr.take (i + m * (1 + L.path))).reverse }).runSeq
        (tr.drop (i + m * (1 + L.path))) = some true
  | 0, j₀, s, i, hi0, hlog, hpre, hoff, _, hrun => by
    refine ⟨by simpa using hi0, fun x hx => absurd hx (by simp), by simpa using hpre, by simpa using hoff, ?_⟩
    simp only [List.range'_zero, List.map_nil, openLoop, Nat.zero_mul, Nat.add_zero] at hrun ⊢
    rw [← hlog]; exact hrun
  | m + 1, j₀, s, i, _, hlog, hpre, hoff, hal, hrun => by
    have hsplit : openPart L pe ce co j₀ (m + 1) = (⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
        (⟨.node pe L.height j₀ lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩ : PE)) ++
        openPart L pe ce co (j₀ + 1) m := by
      simp [openPart, List.range'_succ]
    rw [hsplit, Al_append] at hal
    obtain ⟨hal1, hal2⟩ := hal
    obtain ⟨hiP, hPi⟩ := Al_head hal1
    have hal1' := Al_tail hal1
    simp only [List.length_cons, List.length_map, List.length_range] at hal2
    have hlt : i + 1 + L.path ≤ (plan p).length := by have := hal1.1; simp at this; omega
    rw [List.range'_succ, List.map_cons] at hrun
    simp only [openLoop] at hrun
    obtain ⟨hi, hq, hrun1⟩ := ask_fwd hrun
    -- the leaf
    have hoff1 : s.off + L.row = pOff (plan p) (i + 1) := by rw [pOff_succ hiP, hPi, hoff]; rfl
    have hle : s.off + L.row ≤ π.size := hoff1 ▸ le_trans (pOff_mono _ (by omega)) hsz
    have hbl : bl (qOf tr i) = ((bl π).drop s.off).take L.row := by
      rw [hq, bl_extract, Nat.add_sub_cancel_left]
    have hcl : (bl (qOf tr i)).length = L.row := by rw [hbl]; exact length_take_drop (by rw [← size_bl]; omega)
    have hgleaf : Good tr i ((plan p).getD i default) := by
      rw [hPi]; simp only [Good]; exact ⟨by rw [size_bl]; exact hcl, trivial⟩
    have hpre1 : (bl π).take (s.off + L.row) = hdr8 ++ bodyTo tr (plan p) (i + 1) := by
      rw [List.take_add, hpre, bodyTo_succ, hPi, List.append_assoc]
      congr 2
      show _ = bl (qOf tr i)
      rw [hbl]
    -- the path
    rw [← hq] at hrun1
    have hPn : ∀ x < L.path, (plan p).getD (i + 1 + x) default =
        ⟨.node pe L.height j₀ x (if x + 1 = L.path then some (ce, co, L.path) else none), 64⟩ := by
      intro x hx
      have := hal1'.2 x (by simpa using hx)
      rw [this]; simp [List.getD_eq_getElem?_getD, hx]
    obtain ⟨c1, c2, c3, c4, c5⟩ := climb_fwd hsz pe L.height j₀
      (fun s top => if top == digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) then
        openLoop π L capOff ((List.range' (j₀ + 1) m).map (posVal tr pe L.height)) s k else .ret false)
      L.path 0 (aOf tr i) { s with off := s.off + L.row, log := (qOf tr i, aOf tr i) :: s.log } (i + 1) (by omega)
      (by simp only; rw [take_succ_rev tr hi, hlog]) hpre1 hoff1 (by simp) hlt
      (fun x hx => ⟨_, by rw [hPn x hx, Nat.zero_add]⟩) hrun1
    simp only [show L.path ≠ 0 by omega, ite_false, show i + 1 + L.path - 1 = i + L.path by omega] at c3 c4 c5
    split at c5
    · next htop =>
      have htop' : aOf tr (i + L.path) = digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) :=
        beq_iff_eq.mp htop
      -- the cap entry meets its plan
      have hidx := shiftRight_lt_pow (posVal_lt tr pe L.height j₀) hph
      have hcapEq : aOf tr (i + L.path) = Vector.ofFn fun x =>
          (qOf tr ce).get! (co + nodeBytes * (posVal tr pe L.height j₀ >>> L.path) + x.val) := by
        rw [htop', digestAt]
        apply Vector.ext; intro x hx
        simp only [Vector.getElem_ofFn]
        have hb32 : nodeBytes * (posVal tr pe L.height j₀ >>> L.path) + nodeBytes ≤
            nodeBytes * 2 ^ (L.height - L.path) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hidx
        rw [Nat.add_assoc capOff, hcap _ (by simp only [nodeBytes] at hb32 hnb ⊢; omega), Nat.add_assoc]
      obtain ⟨d1, d2, d3, d4, d5⟩ := openLoop_fwd hsz L capOff pe ce co nb hcap hnb hp1 hph k m (j₀ + 1)
        { s with off := s.off + L.row + 32 * L.path, log := (tr.take (i + 1 + L.path)).reverse } (i + 1 + L.path)
        c1 rfl c3 c4 (by rw [show i + 1 + L.path = i + (L.path + 1) by omega]; exact hal2) c5
      simp only at d3 d4 d5
      have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) =
          s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      have e' : i + 1 + L.path + m * (1 + L.path) = i + (m + 1) * (1 + L.path) := by ring
      rw [e, e'] at d3 d4 d5
      rw [e'] at d1
      refine ⟨d1, fun x hx => ?_, d3, d4, d5⟩
      by_cases hx1 : x < 1 + L.path
      · rcases x with _ | y
        · exact hgleaf
        · have hy : y < L.path := by omega
          obtain ⟨hN1, hN2⟩ := c2 y hy
          simp only [Nat.zero_add] at hN2
          rw [show i + (y + 1) = i + 1 + y by omega, hPn y hy]
          by_cases hyl : y + 1 = L.path
          · rw [if_pos hyl]
            simp only [Good]
            refine ⟨hN1, hN2, ?_⟩
            rw [show i + 1 + y = i + L.path by omega]; exact hcapEq
          · rw [if_neg hyl]
            simp only [Good]
            exact ⟨hN1, hN2, trivial⟩
      · have := d2 (x - (1 + L.path)) (by rw [Nat.add_mul, Nat.one_mul] at hx; omega)
        rwa [show i + 1 + L.path + (x - (1 + L.path)) = i + x by omega] at this
    · next => exact absurd (ret_fwd c5).2 (by simp)

/-! ## The items -/

/-- **One item** of an accepting run: its entries meet their plan, the invariant goes on. -/
theorem item_fwd {p : Params} {tr : Trace} {π : ByteArray} (hsz : pOff (plan p) (plan p).length ≤ π.size)
    (k : DSt → OProg Bool) (its : List Item) (it : Item) (w : WS) (s : DSt)
    (hR : RInv p tr π s w) (hPo : PosInv p tr s w) (hok : (planItem p w it).2.ok = true)
    (hal : Al (plan p) w.i (planItem p w it).1)
    (hrun : (driveItems p π (it :: its) s k).runSeq (tr.drop w.i) = some true) :
    ∃ s1, RInv p tr π s1 (planItem p w it).2 ∧ PosInv p tr s1 (planItem p w it).2 ∧
      (driveItems p π its s1 k).runSeq (tr.drop (planItem p w it).2.i) = some true := by
  have hlen := hal.1
  cases it with
  | read m =>
    refine ⟨{ s with off := s.off + eBytes * m }, ⟨hR.len, hR.log, hR.st, ?_, hR.pre, hR.pend,
      capsRel_wpend (by simp [planItem]) _ _ _ hR.caps, hR.good⟩, hPo, hrun⟩
    simp only [planItem]; rw [hR.off]; omega
  | cap c r =>
    refine ⟨{ s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c },
      ⟨hR.len, hR.log, hR.st, ?_, hR.pre, hR.pend,
        ⟨rfl, hR.off, by simp [planItem], capsRel_wpend (by simp [planItem]) _ _ _ hR.caps⟩, hR.good⟩,
      hPo, hrun⟩
    simp only [planItem]; rw [hR.off]; omega
  | sample =>
    have hP0 : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩ := by
      simpa [planItem] using (Al_head (es := []) (by simpa [planItem] using hal)).2
    have hiP : w.i < (plan p).length := by simp [planItem] at hlen; omega
    obtain ⟨hR1, hrun1⟩ := fs_fwd hR hsz hiP hP0 (k := fun s _ => driveItems p π its s k) hrun
    exact ⟨dStep tr w.i s, hR1, fun r hr => hPo r hr, hrun1⟩
  | positions r =>
    have hn1 : 1 ≤ (p.level r).nPosQ := by
      simp only [planItem, WS.settle, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    have hPx : ∀ x < (p.level r).nPosQ, (plan p).getD (w.i + x) default =
        ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩ := by
      intro x hx
      rw [hal.2 x (by simpa [planItem] using hx)]
      simp only [planItem]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx]
      simp only [Option.map_some, Option.getD_some]
      split_ifs <;> rfl
    obtain ⟨s', hR', hpos', hrun'⟩ := posLoop_fwd (π := π) hsz (p.level r).height
      (fun s => driveItems p π its s k) (p.level r).nPosQ (p.level r).t { s with pos := [] } w
      ⟨hR.len, hR.log, hR.st, hR.off, hR.pre, hR.pend, hR.caps, hR.good⟩
      (by simp [planItem] at hlen; omega) hPx hrun
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w _ hn1
    refine ⟨s', hR'.congr (by simp [planItem, WS.settle, h1]) (by simp [planItem, WS.settle, h2])
      (by simp [planItem, WS.settle, h3]) (by simp [planItem, WS.settle, h4])
      (by simp [planItem, h5]), fun r' hr' => ?_, ?_⟩
    · simp only [planItem, WS.settle, Option.some.injEq] at hr'
      subst hr'
      rw [hpos', List.nil_append, posOut_eq _ _ _ _ _ (nPosQ_ge _)]
      simp [planItem, WS.settle, posVal]
    · have : (planItem p w (.positions r)).2.i = w.i + (p.level r).nPosQ := by simp [planItem, WS.settle]
      rw [this]; exact hrun'
  | opening r =>
    cases hf : w.caps.find? (·.1 == r) with
    | none => simp [planItem, hf] at hok
    | some c =>
      obtain ⟨r', ce, co, nb⟩ := c
      simp only [planItem, hf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.isEmpty_iff] at hok hal hlen ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hpend⟩, hpc⟩, hpr⟩, hp1⟩, hph⟩, hnb⟩, hrow⟩, -⟩, -⟩ := hok
      have hcr := hR.caps
      rw [hpc] at hcr
      obtain ⟨capOff, hco, hbytes⟩ := capsRel_find r _ _ hcr hf
      have hpos := hPo r hpr
      have hoff : s.off = s.pend := by rw [hR.off, hpend, Nat.add_zero]
      rw [driveItems] at hrun
      simp only [capOffset, hco, hrow, ite_true] at hrun
      rw [hpos, List.range_eq_range'] at hrun
      obtain ⟨o1, o2, o3, o4, o5⟩ := openLoop_fwd (π := π) hsz (p.level r) capOff w.pe ce co nb hbytes hnb hp1 hph
        (fun s => driveItems p π its { s with pend := s.off } k) (p.level r).t 0 s w.i hR.len hR.log
        (by rw [hoff]; exact hR.pre) (by rw [hoff]; exact hR.pend) (by rw [← openPlan_eq]; exact hal) hrun
      refine ⟨{ s with
            off := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path)
            log := (tr.take (w.i + (p.level r).t * (1 + (p.level r).path))).reverse
            pend := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path) },
        ⟨by simpa [Nat.mul_comm] using o1, by simp [Nat.mul_comm], hR.st, by simp [hpend],
          by simpa [Nat.mul_comm] using o3, by simpa [Nat.mul_comm] using o4,
          by show CapsRel tr π _ _ w.pcaps s.caps w.caps; rw [hpc]; exact hcr, fun x hx => ?_⟩,
        fun r' hr' => hPo r' hr', ?_⟩
      · simp only at hx
        rcases Nat.lt_or_ge x w.i with hx' | hx'
        · exact hR.good x hx'
        · have := o2 (x - w.i) (by omega)
          rwa [show w.i + (x - w.i) = x by omega] at this
      · simpa [Nat.mul_comm] using o5

theorem items_fwd {p : Params} {tr : Trace} {π : ByteArray} (hsz : pOff (plan p) (plan p).length ≤ π.size)
    (k : DSt → OProg Bool) :
    ∀ (its : List Item) (w : WS) (s : DSt), RInv p tr π s w → PosInv p tr s w →
    (planItems p w its).2.ok = true → Al (plan p) w.i (planItems p w its).1 →
    (driveItems p π its s k).runSeq (tr.drop w.i) = some true →
    ∃ s', RInv p tr π s' (planItems p w its).2 ∧ (k s').runSeq (tr.drop (planItems p w its).2.i) = some true
  | [], w, s, hR, _, _, _, hrun => ⟨s, hR, by simpa [planItems, driveItems] using hrun⟩
  | it :: its, w, s, hR, hPo, hok, hal, hrun => by
    obtain ⟨hal1, hal2⟩ := Al_planItems p hal
    have hok1 : (planItem p w it).2.ok = true := planItems_ok p _ its hok
    obtain ⟨s1, hR1, hPo1, hrun1⟩ := item_fwd hsz k its it w s hR hPo hok1 hal1 hrun
    exact items_fwd hsz k its _ s1 hR1 hPo1 hok hal2 hrun1

end Lvm.Replay
