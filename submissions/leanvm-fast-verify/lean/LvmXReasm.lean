-- New for lvm (WP-13a): the extractor's reassembled proof is WP-11b-QL's reassemble.
import LvmXOut
import LvmXOutSeg
import LvmReassemble
import LvmReplay

/-!
# `reassembleL` is `Lvm.Replay.reassemble` on the extractor's trace

`Lvm.Replay.reassemble p tr` (WP-11b-QL) walks the plan: entry `i`'s contribution is picked by its
planned class (`contrib`). `reassembleL` (the extractor's, `LvmXOut`) picks it by the query's length
(`piece`), after the previous entry's answer. On the extractor's trace `readTraceL W` they agree:

* `ra_pieces_eq`: `pieces` as a `flatMap` over entry indices;
* `ra_contrib`: per entry, `contrib = piece` when the query has the planned length and the planned
  class agrees with that length (`raOk`);
* `ra_plan_chk` (static): the plan's lengths are `7 :: lensL` and every class agrees with its length
  (from `planOk_P20` and `blocks_ok`, `ra_plan_chk_of`);
* `ra_len_readTraceL`: entry `i` of `readTraceL W` has `(7 :: lensL).getD i 0` query bytes.
-/

set_option autoImplicit false

namespace Lvm.X

open RecursionFast Lvm Lvm.Replay

/-! ## `pieces` by index -/

theorem ra_pieces_eq : ∀ (prev : Digest) (tr : Trace),
    pieces prev tr = (List.range tr.length).flatMap fun i =>
      piece (if i = 0 then prev else (tr.getD (i - 1) dflt).2) (tr.getD i dflt)
  | _, [] => rfl
  | prev, e :: tr => by
    rw [pieces, ra_pieces_eq e.2 tr, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [List.getD_cons_zero]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    cases i with
    | zero => rfl
    | succ i => simp

/-- The plan's bodies as a `flatMap` over entry indices, entry by entry equal to `pieces`'. -/
theorem ra_body (tr : Trace) (P : List PE) (hl : P.length = tr.length)
    (h : ∀ i < tr.length, contrib tr i (P.getD i default) =
      piece (if i = 0 then Vector.replicate 32 0 else (tr.getD (i - 1) dflt).2) (tr.getD i dflt)) :
    bodyFrom tr P 0 = pieces (Vector.replicate 32 0) tr := by
  rw [bodyFrom, Nat.sub_zero, ← List.range_eq_range', hl, ra_pieces_eq]
  exact List.flatMap_congr fun i hi => h i (List.mem_range.mp hi)

/-! ## One entry -/

/-- The planned class agrees with the planned length (the length rule): `q₀` 7 bytes, a leaf 384
or 512, a node 64, an FS query none of these. -/
def raOk (e : PE) : Bool :=
  match e.k with
  | .q0 => e.len == 7
  | .fs _ => !(e.len == 7 || e.len == 64 || e.len == 384 || e.len == 512)
  | .leaf => e.len == 384 || e.len == 512
  | .node .. => e.len == 64

theorem ra_contrib (tr : Trace) (i : ℕ) (e : PE) (prev : Digest) (hok : raOk e = true)
    (hlen : (bl (qOf tr i)).length = e.len) (hprev : e.len = 64 → prev = aOf tr (i - 1)) :
    contrib tr i e = piece prev (tr.getD i dflt) := by
  obtain ⟨k, len⟩ := e
  have hq : (tr.getD i dflt).1.data.toList = bl (qOf tr i) := rfl
  simp only at hlen hprev
  unfold piece
  rw [hq, hlen]
  cases k with
  | q0 =>
    simp only [raOk, beq_iff_eq] at hok
    subst hok
    rfl
  | fs st =>
    simp only [raOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hok
    obtain ⟨⟨⟨h7, h64⟩, h384⟩, h512⟩ := hok
    rw [ite_eq_right h7, ite_eq_right h64, ite_eq_right (by omega)]
    rfl
  | leaf =>
    simp only [raOk, Bool.or_eq_true, beq_iff_eq] at hok
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hok]
    rfl
  | node pe h j lvl cap =>
    simp only [raOk, beq_iff_eq] at hok
    rw [ite_eq_right (by omega), ite_eq_left hok, hprev hok]
    rfl

/-! ## The static facts -/

/-- The plan has lengths `L`, and every class agrees with its length. -/
def raChk : List PE → List ℕ → Bool
  | [], [] => true
  | e :: P, l :: L => (e.len == l && raOk e) && raChk P L
  | _, _ => false

/-! The plan against the blocks: `planItems` and `itemBlks` walk the same items, so (when the walk's
static flag holds, `PlanOk`) the plan's lengths are the blocks' and every class agrees with its
length when every block is one the extractor reassembles (`blkOk`). Both facts are already decided
(`planOk_P20`, `blocks_ok`), so the kernel evaluates neither the 11,832-entry plan nor `lensL` here
(a `decide` took 10–14 s). -/

private theorem ra_chk_of : ∀ (P : List PE) (L : List ℕ), P.map PE.len = L → P.all raOk = true → raChk P L = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: P, l :: L, h, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.all_cons, Bool.and_eq_true] at h2
    simp only [raChk, h.1, beq_self_eq_true, h2.1, Bool.and_self, Bool.true_and]
    exact ra_chk_of P L h.2 h2.2

private theorem ra_item_ok (p : Params) (w : WS) (it : Item) (h : (planItem p w it).2.ok = true) : w.ok = true := by
  cases it with
  | read m => exact h
  | cap c r => exact h
  | sample => exact h
  | positions r => simp only [planItem, Bool.and_eq_true] at h; exact h.1
  | opening r =>
    simp only [planItem] at h
    split at h
    · simp at h
    · simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1

private theorem ra_items_ok (p : Params) : ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true → w.ok = true
  | [], _, h => h
  | it :: its, w, h => ra_item_ok p w it (ra_items_ok p its _ h)

private theorem ra_ok_fs (st len : ℕ) (h : len != 64 && len != 384 && len != 512) (h32 : 32 ≤ len) :
    raOk ⟨.fs st, len⟩ = true := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [raOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

private theorem ra_map_range {α : Type} (n : ℕ) (a : α) : (List.range n).map (fun _ => a) = List.replicate n a := by
  rw [List.map_const', List.length_range]

private theorem ra_flatMap_range {α : Type} (n : ℕ) (l : List α) :
    (List.range n).flatMap (fun _ => l) = (List.replicate n l).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatten_append]; simp

private theorem ra_flatMap_replicate {α β : Type} (m : ℕ) (b : α) (f : α → List β) :
    (List.replicate m b).flatMap f = (List.replicate m (f b)).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]

private theorem ra_pos_lens (m st i pend : ℕ) :
    ((List.range (m + 1)).map (fun k => if k = 0 then (⟨.fs st, 32 + pend⟩ : PE) else ⟨.fs (i + k - 1), 32⟩)).map
      PE.len = (32 + pend) :: List.replicate m 32 := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
  simp only [ite_true, Function.comp_def, Nat.succ_ne_zero, ite_false]
  rw [ra_map_range]

private theorem ra_pos_ok (m st i pend : ℕ) (h : blkOk (.one .fs (32 + pend)) = true) :
    ((List.range (m + 1)).map (fun k => if k = 0 then (⟨.fs st, 32 + pend⟩ : PE) else ⟨.fs (i + k - 1), 32⟩)).all
      raOk = true := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.all_cons]
  simp only [ite_true, Function.comp_def, Nat.succ_ne_zero, ite_false]
  rw [ra_ok_fs _ _ h (by omega), Bool.true_and, List.all_map, List.all_eq_true]
  intro x _
  rfl

private theorem ra_open_lens (L : Level) (pe ce co : ℕ) :
    (openPlan L pe ce co).map PE.len = lensB (.opn L.t L.row L.path) := by
  simp only [openPlan, lensB, Blk.queries, List.map_flatMap, List.map_cons, List.map_map,
    Function.comp_def, ra_map_range, ra_flatMap_range, List.map_flatten, List.map_replicate]

private theorem ra_open_ok (L : Level) (pe ce co : ℕ) (h : blkOk (.opn L.t L.row L.path) = true) :
    (openPlan L pe ce co).all raOk = true := by
  simp only [openPlan, List.all_flatMap, List.all_cons, List.all_map, List.all_eq_true]
  intro j _
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨h, fun _ _ => rfl⟩

private theorem ra_plan_lens (p : Params) : ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true →
    (itemBlks p its w.pend).all blkOk = true →
    (planItems p w its).1.map PE.len = (itemBlks p its w.pend).flatMap lensB ∧
      (planItems p w its).1.all raOk = true
  | [], w, _, _ => ⟨rfl, rfl⟩
  | it :: its, w, hok, hb => by
    have hok' : (planItems p (planItem p w it).2 its).2.ok = true := hok
    have ih := ra_plan_lens p its (planItem p w it).2 hok'
    have hstep := ra_items_ok p its _ hok'
    show ((planItem p w it).1 ++ (planItems p (planItem p w it).2 its).1).map PE.len = _ ∧
      ((planItem p w it).1 ++ (planItems p (planItem p w it).2 its).1).all raOk = true
    rw [List.map_append, List.all_append]
    cases it with
    | read m => exact ⟨(ih hb).1, (ih hb).2⟩
    | cap c r => exact ⟨(ih hb).1, (ih hb).2⟩
    | sample =>
      have hb' : blkOk (.one .fs (32 + w.pend)) = true ∧ (itemBlks p its 0).all blkOk = true := by
        simpa only [itemBlks, List.all_cons, Bool.and_eq_true] using hb
      obtain ⟨h1, h2⟩ := ih hb'.2
      rw [h1, h2, Bool.and_true]
      exact ⟨rfl, show raOk ⟨.fs w.st, 32 + w.pend⟩ && true = true by rw [ra_ok_fs _ _ hb'.1 (by omega)]; rfl⟩
    | positions r =>
      have hn : 1 ≤ (p.level r).nPosQ := by
        have : (w.ok && decide (1 ≤ (p.level r).nPosQ)) = true := hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      obtain ⟨m, hm⟩ : ∃ m, (p.level r).nPosQ = m + 1 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
      have hb' : blkOk (.one .fs (32 + w.pend)) = true ∧ (itemBlks p its 0).all blkOk = true := by
        simp only [itemBlks, List.all_cons, List.all_append, Bool.and_eq_true] at hb
        exact ⟨hb.1, hb.2.2⟩
      obtain ⟨h1, h2⟩ := ih hb'.2
      rw [h1, h2, Bool.and_true]
      have e1 : (planItem p w (.positions r)).1 = (List.range (m + 1)).map (fun k =>
          if k = 0 then (⟨.fs w.st, 32 + w.pend⟩ : PE) else ⟨.fs (w.i + k - 1), 32⟩) := by
        rw [← hm]; rfl
      have e2 : itemBlks p (.positions r :: its) w.pend =
          .one .fs (32 + w.pend) :: (List.replicate m (.one .fs 32) ++ itemBlks p its 0) := by
        rw [itemBlks, hm, Nat.add_sub_cancel]
      rw [e1, e2, ra_pos_lens, ra_pos_ok _ _ _ _ hb'.1]
      refine ⟨?_, rfl⟩
      rw [List.flatMap_cons, List.flatMap_append, ra_flatMap_replicate]
      simp only [lensB, Blk.queries, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have e3 : ∀ k : ℕ, (List.replicate k [32]).flatten = List.replicate k 32 := fun k => by
        induction k with
        | zero => rfl
        | succ k ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ih]; rfl
      rw [e3]
      rfl
    | opening r =>
      have hb' : blkOk (.opn (p.level r).t (p.level r).row (p.level r).path) = true ∧
          (itemBlks p its 0).all blkOk = true := by
        simpa only [itemBlks, List.all_cons, Bool.and_eq_true] using hb
      cases hc : w.caps.find? (·.1 == r) with
      | none =>
        have : (planItem p w (.opening r)).2.ok = false := by simp only [planItem, hc]
        rw [this] at hstep; exact absurd hstep (by decide)
      | some c =>
        obtain ⟨x, ce, co, nb⟩ := c
        have e1 : (planItem p w (.opening r)).1 = openPlan (p.level r) w.pe ce co := by
          simp only [planItem, hc]
        have e2 : (planItem p w (.opening r)).2.pend = 0 := by
          have h0 : (planItem p w (.opening r)).2.pend = w.pend := by simp only [planItem, hc]
          have h3 : (planItem p w (.opening r)).2.ok = true := hstep
          simp only [planItem, hc, Bool.and_eq_true, beq_iff_eq] at h3
          rw [h0]; exact h3.1.1.1.1.1.1.1.1.2
        have hb2 : (itemBlks p its (planItem p w (.opening r)).2.pend).all blkOk = true := by
          rw [e2]; exact hb'.2
        obtain ⟨h1, h2⟩ := ih hb2
        rw [h1, h2, Bool.and_true, e1, e2, ra_open_lens, ra_open_ok _ _ _ _ hb'.1]
        exact ⟨rfl, rfl⟩

private theorem ra_plan_chk_of (p : Params) (hP : PlanOk p) (hb : (blocks p).all blkOk = true) :
    raChk (plan p) (7 :: (blocks p).flatMap lensB) = true := by
  rw [blocks, List.all_cons, Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := ra_plan_lens p (schedule p) w0 hP.1 hb.2
  refine ra_chk_of _ _ ?_ ?_
  · rw [plan, blocks, List.map_cons, List.map_cons, List.flatMap_cons]
    exact congrArg (7 :: ·) (congrArg (seedLen :: ·) h1)
  · rw [plan, List.all_cons, List.all_cons, ra_ok_fs 0 seedLen hb.1 (by decide)]
    exact h2

/-- **The plan at `pX`**: lengths `7 :: lensL` (`q₀`, then the extractor's), classes agreeing. -/
theorem ra_plan_chk : raChk (plan pX) (7 :: lensL) = true := ra_plan_chk_of pX planOk_P20 blocks_ok

theorem ra_chk_spec : ∀ (P : List PE) (L : List ℕ), raChk P L = true →
    P.length = L.length ∧ ∀ i < P.length, (P.getD i default).len = L.getD i 0 ∧ raOk (P.getD i default) = true
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by simp [raChk] at h
  | _ :: _, [], h => by simp [raChk] at h
  | e :: P, l :: L, h => by
    simp only [raChk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, hok⟩, hr⟩ := h
    obtain ⟨ih1, ih2⟩ := ra_chk_spec P L hr
    refine ⟨by simp [ih1], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨hl, hok⟩
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ih2 i (by simpa using hi)

/-! ## The extractor's entries' lengths -/

theorem ra_walk_snd : ∀ (u : ℕ) (l : List ℕ), (walk u l).map Prod.snd = l
  | _, [] => rfl
  | u, len :: r => by simp [walk, ra_walk_snd _ r]

theorem ra_entL_snd : entL.map Prod.snd = lensL := ra_walk_snd 6 lensL

theorem ra_len_readTraceL (W : ℕ → Word) (i : ℕ) (hi : i < (readTraceL W).length) :
    (bl (qOf (readTraceL W) i)).length = (7 :: lensL).getD i 0 := by
  cases i with
  | zero =>
    simp only [bl, qOf, readTraceL, List.getD_cons_zero, q0Ent, bArr_data, List.length_drop,
      wordBytes_length]
  | succ k =>
    have hk : k < entL.length := by
      rw [readTraceL, List.length_cons, List.length_map] at hi; omega
    have e1 : (entL.map fun x => entAt W x.1 x.2).getD k dflt = entAt W entL[k].1 entL[k].2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    have e2 : lensL.getD k 0 = entL[k].2 := by
      rw [← ra_entL_snd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    have hmem : entL[k].2 ∈ lensL := by
      rw [← ra_entL_snd]
      exact List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩
    have h8 := (List.all_eq_true.mp lensL_facts.2) _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h8
    rw [List.getD_cons_succ, e2, bl, qOf, readTraceL, List.getD_cons_succ, e1]
    simp only [entAt, bArr_data, wordsBytes_length, length_wsAt]
    omega

/-! ## The theorem -/

/-- **The extractor's reassembled proof is `V_S`'s**: on the trace read off the child's stream,
`reassembleL` (by query lengths, the compare rule) is WP-11b-QL's `reassemble` (by the plan). -/
theorem reassemble_readTraceL (W : ℕ → Word) :
    Lvm.Replay.reassemble pX (readTraceL W) = reassembleL (readTraceL W) := by
  obtain ⟨hl, hP⟩ := ra_chk_spec _ _ ra_plan_chk
  have hlt : (plan pX).length = (readTraceL W).length := by
    rw [hl, length_readTraceL, List.length_cons, lensL_facts.1]
  have hb : bodyFrom (readTraceL W) (plan pX) 0 = pieces (Vector.replicate 32 0) (readTraceL W) := by
    refine ra_body _ _ hlt fun i hi => ?_
    obtain ⟨hlen, hok⟩ := hP i (lt_of_lt_of_eq hi hlt.symm)
    refine ra_contrib _ i _ _ hok (by rw [ra_len_readTraceL W i hi, hlen]) fun h64 => ?_
    cases i with
    | zero => exact absurd (h64.symm.trans hlen) (by rw [List.getD_cons_zero]; decide)
    | succ i => rw [ite_eq_right (Nat.succ_ne_zero i), aOf]
  rw [Lvm.Replay.reassemble, reassembleL, bArr, hb, show hdr8 = header0 from rfl]

end Lvm.X
