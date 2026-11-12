-- New for lvm (WP-11b-QL). FR's replay (`FRVIRSpecCore.runSeq_runIR`, `exec_append`) is for its IR
-- interpreter, not for a CPS driver; the shape of the statement (`runSeq` of the program on the trace
-- = the semantics on the trace) is FR's, the induction over `driveItems` is new.
import LvmReplayBase

/-!
# Replay, part 2: the driver on `reassemble tr` asks exactly `tr`

`items_run`: if the trace meets its plan (`Good` at every entry), the proof `π` holds the trace's
contributions (`(bl π).drop pend = bodyFrom …`), and the driver's state matches the walk's (`Inv`,
`PosInv`), then `driveItems` over the schedule items consumes exactly the items' entries of the
trace and continues with a state that again matches. Proved by induction over the items, with one
lemma per driver function: `fs_step` (one Fiat–Shamir query), `posLoop_run` (the positions
queries), `climb_run` (a Merkle path), `openLoop_run` (an opening), and the cap check from the caps
relation `CapsRel`.
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## The invariant -/

/-- The driver's caps (π offsets) against the walk's: pending caps sit at `pend + P` with
`P + bytes ≤ wpend`; absorbed caps hold, byte for byte, the bytes of their FS query. -/
def CapsRel (tr : Trace) (π : ByteArray) (pend wpend : Nat) :
    List (Ref × Nat × Nat) → List (Ref × Nat) → List (Ref × Nat × Nat × Nat) → Prop
  | [], dc, wc => List.Forall₂ (fun d c => d.1 = c.1 ∧
      ∀ x < c.2.2.2, π.get! (d.2 + x) = (qOf tr c.2.1).get! (c.2.2.1 + x)) dc wc
  | c :: pc, d :: dc, wc => d.1 = c.1 ∧ d.2 = pend + c.2.1 ∧ c.2.1 + c.2.2 ≤ wpend ∧
      CapsRel tr π pend wpend pc dc wc
  | _ :: _, [], _ => False

/-- **The driver's state matches the walk's** on the trace `tr` and the proof `π`. -/
structure Inv (p : Params) (tr : Trace) (π : ByteArray) (s : DSt) (w : WS) : Prop where
  log : s.log = (tr.take w.i).reverse
  st : s.st = aOf tr w.st
  off : s.off = s.pend + w.pend
  body : (bl π).drop s.pend = bodyFrom tr (plan p) w.i
  le : s.pend ≤ π.size
  caps : CapsRel tr π s.pend w.pend w.pcaps s.caps w.caps

/-- The driver's positions are the walk's oracle's. -/
def PosInv (p : Params) (tr : Trace) (s : DSt) (w : WS) : Prop :=
  ∀ r, w.posRef = some r → s.pos = (List.range (p.level r).t).map (posVal tr w.pe (p.level r).height)

/-- The trace meets its plan at every entry. -/
def AllGood (p : Params) (tr : Trace) : Prop := ∀ i < tr.length, Good tr i ((plan p).getD i default)

/-! ## Small facts -/

theorem entry_eq (tr : Trace) {i : Nat} (hi : i < tr.length) : (qOf tr i, aOf tr i) = tr[i] := by
  simp [qOf, aOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem drop_cons_getD (tr : Trace) {i : Nat} (hi : i < tr.length) :
    tr.drop i = (qOf tr i, aOf tr i) :: tr.drop (i + 1) := by
  rw [entry_eq tr hi]; exact List.drop_eq_getElem_cons hi

theorem take_succ_rev (tr : Trace) {i : Nat} (hi : i < tr.length) :
    (tr.take (i + 1)).reverse = (qOf tr i, aOf tr i) :: (tr.take i).reverse := by
  rw [entry_eq tr hi, List.take_add_one, List.getElem?_eq_getElem hi]
  simp

theorem getD_drop' (l : List UInt8) (a b : Nat) : (l.drop a).getD b 0 = l.getD (a + b) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem ask_run (q : ByteArray) (s : DSt) (k : DSt → Digest → OProg Bool) (e : ByteArray × Digest)
    (rest : Trace) (h : e.1 = q) :
    (ask q s k).runSeq (e :: rest) = (k { s with log := (q, e.2) :: s.log } e.2).runSeq rest := by
  obtain ⟨q', a⟩ := e
  simp only at h
  subst h
  simp [ask, OProg.runSeq]

/-- A byte of `π` inside the body read at `pend`. -/
theorem get!_body {π : ByteArray} {pend : Nat} {c rest : List UInt8} (h : (bl π).drop pend = c ++ rest)
    {y : Nat} (hy : y < c.length) : π.get! (pend + y) = c.getD y 0 := by
  rw [get!_bl, ← getD_drop', h, List.getD_append _ _ _ _ hy]

/-- The bytes `[a, a + n)` of `π`, inside the body read at `a`. -/
theorem bl_extract_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest)
    {n : Nat} (hn : c.length = n) : bl (π.extract a (a + n)) = c := by
  rw [bl_extract, h, Nat.add_sub_cancel_left, List.take_left' hn]

theorem le_of_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest)
    (ha : a ≤ π.size) : a + c.length ≤ π.size := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_append, ← size_bl] at this
  omega

theorem drop_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest) :
    (bl π).drop (a + c.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ## Caps -/

theorem capsRel_wpend {tr : Trace} {π : ByteArray} {pend wpend wpend' : Nat} (hw : wpend ≤ wpend') :
    ∀ (pc : List (Ref × Nat × Nat)) (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    CapsRel tr π pend wpend pc dc wc → CapsRel tr π pend wpend' pc dc wc
  | [], dc, wc, h => h
  | c :: pc, d :: dc, wc, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, by omega, capsRel_wpend hw pc dc wc h4⟩
  | _ :: _, [], _, h => h.elim

theorem capsRel_settle {tr : Trace} {π : ByteArray} {pend wpend i : Nat}
    (hb : ∀ y < wpend, π.get! (pend + y) = (qOf tr i).get! (32 + y)) (pend' : Nat) :
    ∀ (pc : List (Ref × Nat × Nat)) (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    CapsRel tr π pend wpend pc dc wc →
      CapsRel tr π pend' 0 [] dc (pc.map (fun c => (c.1, i, 32 + c.2.1, c.2.2)) ++ wc)
  | [], dc, wc, h => h
  | c :: pc, d :: dc, wc, ⟨h1, h2, h3, h4⟩ => by
    refine List.Forall₂.cons ⟨h1, fun x hx => ?_⟩ (capsRel_settle hb pend' pc dc wc h4)
    simp only at hx ⊢
    rw [h2, Nat.add_assoc, hb _ (by omega), Nat.add_assoc]
  | _ :: _, [], _, h => h.elim

/-- With no pending cap, the driver finds a ref's cap where the walk does, with the same bytes. -/
theorem capsRel_find {tr : Trace} {π : ByteArray} (r : Ref) :
    ∀ (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    List.Forall₂ (fun d c => d.1 = c.1 ∧
      ∀ x < c.2.2.2, π.get! (d.2 + x) = (qOf tr c.2.1).get! (c.2.2.1 + x)) dc wc →
    ∀ {r' : Ref} {ce co nb : Nat}, wc.find? (·.1 == r) = some (r', ce, co, nb) →
    ∃ capOff, (dc.find? (·.1 == r)).map (·.2) = some capOff ∧
      ∀ x < nb, π.get! (capOff + x) = (qOf tr ce).get! (co + x)
  | [], [], _, _, _, _, _, h => by simp at h
  | d :: dc, ⟨r'', ce', co', nb'⟩ :: wc, h, r', ce, co, nb, hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := List.forall₂_cons.mp h
    simp only at h1 h2
    by_cases hc : r'' = r
    · subst hc
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      exact ⟨d.2, by simp [List.find?_cons, h1], h2⟩
    · have hne : (r'' == r) = false := by simpa using hc
      have hf' : wc.find? (·.1 == r) = some (r', ce, co, nb) := by
        simpa [List.find?_cons, hne] using hf
      obtain ⟨o, ho, hb⟩ := capsRel_find r dc wc h3 hf'
      exact ⟨o, by simpa [List.find?_cons, h1, hne] using ho, hb⟩
  | [], _ :: _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _, _ => by simp at h

/-! ## One Fiat–Shamir query -/

/-- The walk after one FS query at entry `w.i`. -/
def WS.stepFS (w : WS) : WS := { w.settle with i := w.i + 1, pend := 0, st := w.i }

/-- The driver after one FS query answered by entry `i`. -/
def dStep (tr : Trace) (i : Nat) (s : DSt) : DSt :=
  { s with log := (qOf tr i, aOf tr i) :: s.log, st := aOf tr i, pend := s.off }

theorem fs_step {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w : WS} (hI : Inv p tr π s w)
    (hi : w.i < tr.length) (hn : tr.length = (plan p).length)
    (hP : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩) (hG : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩)
    (k : DSt → Digest → OProg Bool) :
    (fsQuery π s k).runSeq (tr.drop w.i) = (k (dStep tr w.i s) (aOf tr w.i)).runSeq (tr.drop (w.i + 1)) ∧
      Inv p tr π (dStep tr w.i s) w.stepFS := by
  obtain ⟨hlen, hpre⟩ := hG
  simp only at hlen hpre
  have hbody : (bl π).drop s.pend = (bl (qOf tr w.i)).drop 32 ++ bodyFrom tr (plan p) (w.i + 1) := by
    rw [hI.body, bodyFrom_cons _ _ (by omega), hP]; rfl
  have hcl : ((bl (qOf tr w.i)).drop 32).length = w.pend := by
    rw [List.length_drop, ← size_bl, hlen]; omega
  have hq : digestBytes s.st ++ π.extract s.pend s.off = qOf tr w.i := by
    apply ba_ext
    rw [bl_append, bl_digestBytes, hI.st, hI.off, bl_extract_body hbody hcl, ← hpre, List.take_append_drop]
  refine ⟨?_, ⟨?_, rfl, by simp [dStep, WS.stepFS], ?_, ?_, ?_⟩⟩
  · rw [fsQuery, drop_cons_getD tr hi, ask_run _ _ _ (qOf tr w.i, aOf tr w.i) _ hq.symm, hq]; rfl
  · simp only [dStep, WS.stepFS, WS.settle]; rw [take_succ_rev tr hi, hI.log]
  · simp only [dStep, WS.stepFS, WS.settle]
    rw [hI.off, ← hcl]; exact drop_body hbody
  · simp only [dStep]; rw [hI.off, ← hcl]; exact le_of_body hbody hI.le
  · simp only [dStep, WS.stepFS, WS.settle]
    refine capsRel_settle (fun y hy => ?_) _ _ _ _ hI.caps
    rw [get!_body hbody (by omega), get!_bl, getD_drop']

/-! ## The positions -/

/-- The positions `posLoop` draws from the answers of entries `e, e + 1, …` (`n` answers, `rem`
positions still to draw). -/
def posOut (tr : Trace) (h : Nat) : (e n rem : Nat) → List Nat
  | _, 0, _ => []
  | e, n + 1, rem =>
    (List.range (min positionsPerAnswer rem)).map (fun j => (answerBits (aOf tr e) >>> (j * h)) % 2 ^ h) ++
      posOut tr h (e + 1) n (rem - min positionsPerAnswer rem)

/-- The positions one answer gives (`posLoop`'s `ps`). -/
def posBatch (tr : Trace) (h e cnt : Nat) : List Nat :=
  (List.range cnt).map fun j => (answerBits (aOf tr e) >>> (j * h)) % 2 ^ h

theorem posOut_eq (tr : Trace) (h : Nat) : ∀ (n e rem : Nat), rem ≤ positionsPerAnswer * n →
    posOut tr h e n rem =
      (List.range rem).map fun j => (answerBits (aOf tr (e + j / 8)) >>> (j % 8 * h)) % 2 ^ h
  | 0, e, rem, hr => by simp [posOut, show rem = 0 by simpa [positionsPerAnswer] using hr]
  | n + 1, e, rem, hr => by
    simp only [posOut]
    rw [posOut_eq tr h n (e + 1) _ (by simp [positionsPerAnswer] at hr ⊢; omega)]
    have hc : min positionsPerAnswer rem + (rem - min positionsPerAnswer rem) = rem := by omega
    conv_rhs => rw [← hc, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      have : j < 8 := by simp [positionsPerAnswer] at hj; omega
      rw [Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this, Nat.add_zero]
    · refine List.map_congr_left fun j hj => ?_
      simp only [Function.comp, positionsPerAnswer] at hj ⊢
      by_cases h8 : 8 ≤ rem
      · rw [show min 8 rem = 8 by omega, show (8 + j) / 8 = j / 8 + 1 by omega,
          show (8 + j) % 8 = j % 8 by omega, Nat.add_comm (j / 8) 1, ← Nat.add_assoc]
      · simp at hj; omega

theorem stepFS_iter (w : WS) : ∀ n, 1 ≤ n →
    (WS.stepFS^[n] w).i = w.i + n ∧ (WS.stepFS^[n] w).pend = 0 ∧ (WS.stepFS^[n] w).st = w.i + n - 1 ∧
      (WS.stepFS^[n] w).pcaps = [] ∧ (WS.stepFS^[n] w).caps = w.settle.caps
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [WS.stepFS, WS.settle]
  | n + 2, _ => by
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w.stepFS (n + 1) (by omega)
    refine ⟨by rw [h1]; simp [WS.stepFS, WS.settle]; omega, h2, by rw [h3]; simp [WS.stepFS, WS.settle]; omega,
      h4, by rw [h5]; simp [WS.stepFS, WS.settle]⟩

theorem stepFS_iter_i (w : WS) : ∀ n, (WS.stepFS^[n] w).i = w.i + n
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, stepFS_iter_i w.stepFS n]; simp [WS.stepFS, WS.settle]; omega

theorem posLoop_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (h : Nat) (k : DSt → OProg Bool) :
    ∀ (n rem : Nat) (s : DSt) (w : WS), Inv p tr π s w → w.i + n ≤ tr.length →
    (∀ x < n, (plan p).getD (w.i + x) default =
      ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩) →
    ∃ s', Inv p tr π s' (WS.stepFS^[n] w) ∧ s'.pos = s.pos ++ posOut tr h w.i n rem ∧
      (posLoop π h n rem s k).runSeq (tr.drop w.i) = (k s').runSeq (tr.drop (w.i + n))
  | 0, rem, s, w, hI, _, _ => ⟨s, hI, by simp [posOut], by simp [posLoop]⟩
  | n + 1, rem, s, w, hI, hl, hP => by
    have hP0 := hP 0 (by omega)
    simp only [ite_true, Nat.add_zero] at hP0
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by rw [← hP0]; exact hG _ (by omega)
    have hI' := (fs_step (k := fun _ _ => OProg.ret false) hI (by omega) hn hP0 hG0).2
    have hI2 : Inv p tr π { (dStep tr w.i s) with
        pos := (dStep tr w.i s).pos ++ posBatch tr h w.i (min positionsPerAnswer rem) } w.stepFS :=
      ⟨hI'.log, hI'.st, hI'.off, hI'.body, hI'.le, hI'.caps⟩
    obtain ⟨s', hI3, hpos3, hrun3⟩ := posLoop_run hn hG h k n (rem - min positionsPerAnswer rem) _ _ hI2
      (by simp [WS.stepFS, WS.settle]; omega) (fun x hx => by
        have := hP (x + 1) (by omega)
        rw [show w.i + (x + 1) = w.stepFS.i + x by simp [WS.stepFS, WS.settle]; omega] at this
        rw [this]
        rcases x with _ | x <;> simp [WS.stepFS, WS.settle] <;> omega)
    refine ⟨s', by rw [Function.iterate_succ_apply]; exact hI3, ?_, ?_⟩
    · rw [hpos3]; simp [dStep, posOut, posBatch, List.append_assoc, WS.stepFS, WS.settle]
    · rw [posLoop, (fs_step hI (by omega) hn hP0 hG0 _).1]
      rw [show w.i + (n + 1) = w.stepFS.i + n by simp [WS.stepFS, WS.settle]; omega, ← hrun3]
      rfl

/-! ## Merkle paths and openings -/

/-- **The compare rule is the position rule** on a node entry that meets its plan. -/
theorem compare_rule {q : List UInt8} {cur : List UInt8} {b : Prop} [Decidable b] (hq : q.length = 64)
    (h : (if b then q.take 32 else q.drop 32) = cur) :
    (if q.take 32 = cur then q.drop 32 else q.take 32) = (if b then q.drop 32 else q.take 32) := by
  by_cases hb : b
  · rw [if_pos hb] at h; rw [if_pos h, if_pos hb]
  · rw [if_neg hb] at h
    rw [if_neg hb]
    split
    · next h' => rw [h', ← h]
    · rfl

theorem climb_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (pe h j : Nat) (k : DSt → Digest → OProg Bool) :
    ∀ (m lvl : Nat) (cur : Digest) (s : DSt) (i : Nat),
    s.log = (tr.take i).reverse → (bl π).drop s.off = bodyFrom tr (plan p) i → s.off ≤ π.size →
    cur = aOf tr (i - 1) → i + m ≤ tr.length →
    (∀ x < m, ∃ cap, (plan p).getD (i + x) default = ⟨.node pe h j (lvl + x) cap, 64⟩) →
    (climb π (posVal tr pe h j) m lvl cur s k).runSeq (tr.drop i) =
      (k { s with off := s.off + 32 * m, log := (tr.take (i + m)).reverse }
        (if m = 0 then cur else aOf tr (i + m - 1))).runSeq (tr.drop (i + m)) ∧
      (bl π).drop (s.off + 32 * m) = bodyFrom tr (plan p) (i + m) ∧ s.off + 32 * m ≤ π.size
  | 0, lvl, cur, s, i, hlog, hb, hle, _, _, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [climb, Nat.mul_zero, Nat.add_zero, ite_true]
    rw [← hlog]
  | m + 1, lvl, cur, s, i, hlog, hb, hle, hcur, hl, hP => by
    obtain ⟨cap, hPi⟩ := hP 0 (by omega)
    simp only [Nat.add_zero] at hPi
    obtain ⟨hlen, hhalf, -⟩ := (show Good tr i ⟨.node pe h j lvl cap, 64⟩ by rw [← hPi]; exact hG i (by omega))
    have hq64 : (bl (qOf tr i)).length = 64 := by rw [← size_bl]; exact hlen
    have hbody : (bl π).drop s.off =
        (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).drop 32 else (bl (qOf tr i)).take 32) ++
          bodyFrom tr (plan p) (i + 1) := by
      rw [hb, bodyFrom_cons _ _ (by omega), hPi]
      congr 1
      show (if (bl (qOf tr i)).take 32 = (aOf tr (i - 1)).toList then (bl (qOf tr i)).drop 32
        else (bl (qOf tr i)).take 32) = _
      exact compare_rule hq64 hhalf
    have hcl : (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).drop 32
        else (bl (qOf tr i)).take 32).length = 32 := by
      split <;> simp [hq64]
    have hq : (if (posVal tr pe h j >>> lvl) % 2 = 0 then
        digestBytes cur ++ π.extract s.off (s.off + 32) else π.extract s.off (s.off + 32) ++ digestBytes cur) =
        qOf tr i := by
      apply ba_ext
      split
      · next h0 =>
        rw [bl_append, bl_digestBytes, bl_extract_body hbody hcl, if_pos h0, hcur, ← hhalf, if_pos h0,
          List.take_append_drop]
      · next h0 =>
        rw [bl_append, bl_digestBytes, bl_extract_body hbody hcl, if_neg h0, hcur, ← hhalf, if_neg h0,
          List.take_append_drop]
    have hl' : s.off + 32 ≤ π.size := by rw [← hcl]; exact le_of_body hbody hle
    have hb' : (bl π).drop (s.off + 32) = bodyFrom tr (plan p) (i + 1) := by
      rw [← hcl]; exact drop_body hbody
    obtain ⟨ih1, ih2, ih3⟩ := climb_run hn hG pe h j k m (lvl + 1) (aOf tr i)
      { s with off := s.off + 32, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by omega), hlog]) hb' hl' (by simp) (by omega)
      (fun x hx => by
        obtain ⟨c, hc⟩ := hP (x + 1) (by omega)
        exact ⟨c, by rw [show i + 1 + x = i + (x + 1) by omega, hc]; congr 2; omega⟩)
    refine ⟨?_, ?_, ?_⟩
    · rw [climb, drop_cons_getD tr (by omega)]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at ih1
      rw [ih1]
      have e1 : i + 1 + m = i + (m + 1) := by omega
      have e3 : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      have e2 : (if m = 0 then aOf tr i else aOf tr (i + 1 + m - 1)) =
          (if m + 1 = 0 then cur else aOf tr (i + (m + 1) - 1)) := by
        rcases m with _ | m
        · simp
        · simp only [Nat.add_one_ne_zero, ite_false]; congr 1; omega
      rw [e2, e3, e1]
    · simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 32, show i + 1 + m = i + (m + 1) by omega] using ih2
    · have : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      simp only at ih3
      omega

theorem shiftRight_lt_pow {n h k : Nat} (hn : n < 2 ^ h) (hk : k ≤ h) : n >>> k < 2 ^ (h - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add,
    Nat.sub_add_cancel hk]
  exact hn

theorem posVal_lt (tr : Trace) (pe h j : Nat) : posVal tr pe h j < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos h)

/-- The entries of positions `j₀ … j₀ + m − 1` of an opening. -/
def openPart (L : Level) (pe ce co j₀ m : Nat) : List PE :=
  (List.range' j₀ m).flatMap fun j => ⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
    ⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩

theorem openPlan_eq (L : Level) (pe ce co : Nat) : openPlan L pe ce co = openPart L pe ce co 0 L.t := by
  simp [openPlan, openPart, List.range_eq_range']

theorem openLoop_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (L : Level) (capOff pe ce co nb : Nat)
    (hcap : ∀ x < nb, π.get! (capOff + x) = (qOf tr ce).get! (co + x))
    (hnb : nodeBytes * 2 ^ (L.height - L.path) ≤ nb) (hp1 : 1 ≤ L.path) (hph : L.path ≤ L.height)
    (k : DSt → OProg Bool) :
    ∀ (m j₀ : Nat) (s : DSt) (i : Nat), s.log = (tr.take i).reverse →
    (bl π).drop s.off = bodyFrom tr (plan p) i → s.off ≤ π.size →
    Al (plan p) i (openPart L pe ce co j₀ m) →
    (openLoop π L capOff ((List.range' j₀ m).map (posVal tr pe L.height)) s k).runSeq (tr.drop i) =
      (k { s with
            off := s.off + m * (L.row + 32 * L.path)
            log := (tr.take (i + m * (1 + L.path))).reverse }).runSeq (tr.drop (i + m * (1 + L.path))) ∧
      (bl π).drop (s.off + m * (L.row + 32 * L.path)) = bodyFrom tr (plan p) (i + m * (1 + L.path)) ∧
      s.off + m * (L.row + 32 * L.path) ≤ π.size
  | 0, j₀, s, i, hlog, hb, hle, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [List.range'_zero, List.map_nil, openLoop, Nat.zero_mul, Nat.add_zero]
    rw [← hlog]
  | m + 1, j₀, s, i, hlog, hb, hle, hal => by
    have hsplit : openPart L pe ce co j₀ (m + 1) = (⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
        (⟨.node pe L.height j₀ lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩ : PE)) ++
        openPart L pe ce co (j₀ + 1) m := by
      simp [openPart, List.range'_succ]
    rw [hsplit, Al_append] at hal
    obtain ⟨hal1, hal2⟩ := hal
    obtain ⟨hi, hPi⟩ := Al_head hal1
    have hal1' := Al_tail hal1
    simp only [List.length_cons, List.length_map, List.length_range] at hal2
    have hlt : i + 1 + L.path ≤ tr.length := by have := hal1.1; simp at this; omega
    obtain ⟨hlen, -⟩ := (show Good tr i ⟨.leaf, L.row⟩ by rw [← hPi]; exact hG i (by omega))
    have hbody : (bl π).drop s.off = bl (qOf tr i) ++ bodyFrom tr (plan p) (i + 1) := by
      rw [hb, bodyFrom_cons _ _ hi, hPi]; rfl
    have hcl : (bl (qOf tr i)).length = L.row := by rw [← size_bl]; exact hlen
    have hq : π.extract s.off (s.off + L.row) = qOf tr i := ba_ext (bl_extract_body hbody hcl)
    have hb1 : (bl π).drop (s.off + L.row) = bodyFrom tr (plan p) (i + 1) := by
      rw [← hcl]; exact drop_body hbody
    have hle1 : s.off + L.row ≤ π.size := by rw [← hcl]; exact le_of_body hbody hle
    obtain ⟨c1, c2, c3⟩ := climb_run hn hG pe L.height j₀
      (fun s top => if top == digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) then
        openLoop π L capOff ((List.range' (j₀ + 1) m).map (posVal tr pe L.height)) s k else .ret false)
      L.path 0 (aOf tr i) { s with off := s.off + L.row, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by omega), hlog]) hb1 hle1 (by simp) hlt
      (fun x hx => ⟨if x + 1 = L.path then some (ce, co, L.path) else none, by
        have := hal1'.2 x (by simpa using hx)
        rw [this]; simp [List.getD_eq_getElem?_getD, hx]⟩)
    -- the cap check holds
    have hlast : Good tr (i + L.path) ((plan p).getD (i + L.path) default) := hG _ (by omega)
    have hPl : (plan p).getD (i + L.path) default =
        ⟨.node pe L.height j₀ (L.path - 1) (some (ce, co, L.path)), 64⟩ := by
      have := hal1'.2 (L.path - 1) (by simp; omega)
      rw [show i + 1 + (L.path - 1) = i + L.path by omega] at this
      rw [this]; simp [List.getD_eq_getElem?_getD, show L.path - 1 < L.path by omega,
        show L.path - 1 + 1 = L.path by omega]
    rw [hPl] at hlast
    obtain ⟨-, -, hcapEq⟩ := hlast
    simp only at hcapEq
    have hidx := shiftRight_lt_pow (posVal_lt tr pe L.height j₀) hph
    have htop : aOf tr (i + L.path) = digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) := by
      rw [hcapEq, digestAt]
      apply Vector.ext; intro x hx
      simp only [Vector.getElem_ofFn]
      have hb32 : nodeBytes * (posVal tr pe L.height j₀ >>> L.path) + nodeBytes ≤
          nodeBytes * 2 ^ (L.height - L.path) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hidx
      rw [Nat.add_assoc capOff, hcap _ (by simp only [nodeBytes] at hb32 hnb ⊢; omega), Nat.add_assoc]
    obtain ⟨d1, d2, d3⟩ := openLoop_run hn hG L capOff pe ce co nb hcap hnb hp1 hph k m (j₀ + 1)
      { s with off := s.off + L.row + 32 * L.path, log := (tr.take (i + 1 + L.path)).reverse } (i + 1 + L.path)
      rfl (by simpa using c2) (by simpa using c3) (by rw [show i + 1 + L.path = i + (L.path + 1) by omega]; exact hal2)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.range'_succ, List.map_cons, openLoop, drop_cons_getD tr (by omega)]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at c1
      rw [c1]
      simp only [show L.path ≠ 0 by omega, ite_false, show i + 1 + L.path - 1 = i + L.path by omega, ← htop,
        beq_self_eq_true, ite_true]
      simp only at d1
      rw [d1]
      have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) =
          s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      have e' : i + 1 + L.path + m * (1 + L.path) = i + (m + 1) * (1 + L.path) := by ring
      rw [e, e']
    · have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) = s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      have e' : i + 1 + L.path + m * (1 + L.path) = i + (m + 1) * (1 + L.path) := by ring
      simpa [e, e'] using d2
    · have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) = s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      simp only at d3
      omega

/-! ## The items -/

theorem Inv.congr {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w₁ w₂ : WS} (h : Inv p tr π s w₁)
    (hi : w₁.i = w₂.i) (hp : w₁.pend = w₂.pend) (hs : w₁.st = w₂.st) (hpc : w₁.pcaps = w₂.pcaps)
    (hc : w₁.caps = w₂.caps) : Inv p tr π s w₂ :=
  ⟨hi ▸ h.log, hs ▸ h.st, hp ▸ h.off, hi ▸ h.body, h.le, hp ▸ hpc ▸ hc ▸ h.caps⟩

theorem nPosQ_ge (L : Level) : L.t ≤ positionsPerAnswer * L.nPosQ := by
  simp only [Level.nPosQ, positionsPerAnswer]; omega

/-- **One item**: the driver runs it on its entries and continues with the rest. -/
theorem item_step {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (k : DSt → OProg Bool) (its : List Item) (it : Item) (w : WS) (s : DSt)
    (hI : Inv p tr π s w) (hPo : PosInv p tr s w) (hok : (planItem p w it).2.ok = true)
    (hal : Al (plan p) w.i (planItem p w it).1) :
    ∃ s1, Inv p tr π s1 (planItem p w it).2 ∧ PosInv p tr s1 (planItem p w it).2 ∧
      (driveItems p π (it :: its) s k).runSeq (tr.drop w.i) =
        (driveItems p π its s1 k).runSeq (tr.drop (planItem p w it).2.i) := by
  have hlen := hal.1
  cases it with
  | read m =>
    refine ⟨{ s with off := s.off + eBytes * m }, ⟨hI.log, hI.st, ?_, hI.body, hI.le,
      capsRel_wpend (by simp [planItem]) _ _ _ hI.caps⟩, hPo, rfl⟩
    simp only [planItem]; rw [hI.off]; omega
  | cap c r =>
    refine ⟨{ s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c },
      ⟨hI.log, hI.st, ?_, hI.body, hI.le, ⟨rfl, hI.off, by simp [planItem], capsRel_wpend (by simp [planItem]) _ _ _ hI.caps⟩⟩,
      hPo, rfl⟩
    simp only [planItem]; rw [hI.off]; omega
  | sample =>
    have hP0 : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩ := by
      simpa [planItem] using (Al_head (es := []) (by simpa [planItem] using hal)).2
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by rw [← hP0]; exact hG _ (by simp [planItem] at hlen; omega)
    obtain ⟨hrun, hI1⟩ := fs_step hI (by simp [planItem] at hlen; omega) hn hP0 hG0
      (fun s _ => driveItems p π its s k)
    exact ⟨dStep tr w.i s, hI1, fun r hr => hPo r hr, hrun⟩
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
    obtain ⟨s', hI', hpos', hrun'⟩ := posLoop_run (π := π) hn hG (p.level r).height
      (fun s => driveItems p π its s k) (p.level r).nPosQ (p.level r).t { s with pos := [] } w
      ⟨hI.log, hI.st, hI.off, hI.body, hI.le, hI.caps⟩ (by simp [planItem] at hlen; omega) hPx
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w _ hn1
    refine ⟨s', hI'.congr (by simp [planItem, WS.settle, h1]) (by simp [planItem, WS.settle, h2])
      (by simp [planItem, WS.settle, h3]) (by simp [planItem, WS.settle, h4])
      (by simp [planItem, h5]), fun r' hr' => ?_, ?_⟩
    · simp only [planItem, WS.settle, Option.some.injEq] at hr'
      subst hr'
      rw [hpos', List.nil_append, posOut_eq _ _ _ _ _ (nPosQ_ge _)]
      simp [planItem, WS.settle, posVal]
    · rw [driveItems, hrun']
      simp [planItem, WS.settle]
  | opening r =>
    cases hf : w.caps.find? (·.1 == r) with
    | none => simp [planItem, hf] at hok
    | some c =>
      obtain ⟨r', ce, co, nb⟩ := c
      simp only [planItem, hf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.isEmpty_iff] at hok hal hlen ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hpend⟩, hpc⟩, hpr⟩, hp1⟩, hph⟩, hnb⟩, hrow⟩, -⟩, -⟩ := hok
      have hcr := hI.caps
      rw [hpc] at hcr
      obtain ⟨capOff, hco, hbytes⟩ := capsRel_find r _ _ hcr hf
      have hpos := hPo r hpr
      have hoff : s.off = s.pend := by rw [hI.off, hpend, Nat.add_zero]
      obtain ⟨o1, o2, o3⟩ := openLoop_run (π := π) hn hG (p.level r) capOff w.pe ce co nb hbytes hnb hp1 hph
        (fun s => driveItems p π its { s with pend := s.off } k) (p.level r).t 0 s w.i hI.log
        (by rw [hoff]; exact hI.body) (by rw [hoff]; exact hI.le) (by rw [← openPlan_eq]; exact hal)
      refine ⟨{ s with
            off := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path)
            log := (tr.take (w.i + (p.level r).t * (1 + (p.level r).path))).reverse
            pend := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path) },
        ⟨by simp [Nat.mul_comm], hI.st, by simp [hpend], by simpa [Nat.mul_comm] using o2,
          by simpa using o3, by show CapsRel tr π _ _ w.pcaps s.caps w.caps; rw [hpc]; exact hcr⟩,
        fun r' hr' => hPo r' hr', ?_⟩
      rw [driveItems]
      simp only [capOffset, hco, hrow, ite_true]
      rw [hpos, List.range_eq_range', o1]
      simp only [Nat.mul_comm]
      rw [← List.range_eq_range', ← hpos]

end Lvm.Replay
