-- new for lvm (WP-9): leanerVM's `lookup_sound` (adapted in `LvmBusILookup`) applied to the
-- `M3Holds` clauses `Balanced` and `CountsNonzero` of the lvm instance (`LvmM3Inst`), the way
-- leanerVM `Arithmetization/Bus.lean`@25da57d32 applies it to leanISA's memory channel.
import LvmM3Inst

/-!
# The memory bus: a balanced bus with nonzero counts reads only seeded keys

On the lvm instance (`Lvm.M3.inst`) every flush is a memory message (`Tab.flushes`): a read's pull
`⟨k, c⟩` and push `⟨k, g·c⟩`, a seed's push `⟨k, 1⟩` and finalize `⟨k, f⟩`. **`mem_lookup`**: if
the bus is balanced (`M3Instance.Balanced`, a permutation counted in `ℕ`), every read count is
nonzero (`M3Instance.CountsNonzero`, the read-count columns being the instance's count columns),
the count columns are inside their tables and there are fewer than `2^64 - 1` reads, then the key
(every coordinate but the count, `keyT`) of every read tuple is the key of a seed tuple.

This is leanerVM's `lookup_sound` with the messages the evaluated sixteen-coordinate tuples, the
reads the read pulls, the seeds the seed pushes and the finalizes the finalize pulls (whose keys
are their seeds' at the same row). The `M3Holds` tuples are rearranged into that shape:
`flushTuples .push` is, table by table, the bumped reads then the seeds (`push_perm`), and
`flushTuples .pull` the reads then the finalizes (`pull_perm`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Arithmetization CompPoly CMlPolynomialEval

/-! ## Tuples -/

/-- The key of a tuple: every coordinate but the count (coordinate `2`). -/
def keyT (t : Vector K 16) : Vector K 16 := Vector.ofFn fun k ↦ if k.val = 2 then 0 else t[k]

/-- The push of a read: the count multiplied by `g`. -/
def bumpT (t : Vector K 16) : Vector K 16 := Vector.ofFn fun k ↦ if k.val = 2 then g * t[k] else t[k]

/-- The count of a tuple. -/
def cntT (t : Vector K 16) : K := t[2]

theorem keyT_bumpT (t : Vector K 16) : keyT (bumpT t) = keyT t := by
  apply Vector.ext; intro k hk; simp only [keyT, bumpT, Vector.getElem_ofFn]; split <;> simp_all

theorem cntT_bumpT (t : Vector K 16) : cntT (bumpT t) = g * cntT t := by
  simp [cntT, bumpT]

/-- A tuple of polynomials evaluated at a row. -/
noncomputable def evalV {w : ℕ} (r : Fin w → K) (v : Vector (MvPolynomial (Fin w) K) 16) :
    Vector K 16 :=
  v.map (MvPolynomial.eval r)

namespace Tab

variable (t : Tab)

theorem evalV_bumpVec (r : Fin t.w → K) (rd : Key × ℕ) :
    evalV r (t.bumpVec rd) = bumpT (evalV r (t.readVec rd)) := by
  apply Vector.ext; intro k hk
  simp only [evalV, bumpT, Vector.getElem_map, Vector.getElem_ofFn]
  by_cases h2 : k = 2
  · subst h2
    simp [bumpVec, readVec, Key.vec, CPoly.eval_toMv, CPoly.evalB, CPoly.var, FK.toBF64_x]
  · simp [h2, bumpVec, readVec, Key.vec]

theorem keyT_finVec (r : Fin t.w → K) (s : Key × ℕ) :
    keyT (evalV r (t.finVec s)) = keyT (evalV r (t.seedVec s)) := by
  apply Vector.ext; intro k hk
  simp only [keyT, evalV, finVec, seedVec, Key.vec, Vector.getElem_ofFn, Vector.getElem_map]
  split <;> simp_all

theorem cntT_readVec (r : Fin t.w → K) (rd : Key × ℕ) :
    cntT (evalV r (t.readVec rd)) = CPoly.ext r rd.2 := by
  simp [cntT, evalV, readVec, Key.vec, CPoly.eval_toMv, CPoly.evalB, CPoly.var]

end Tab

/-! ## The tuples of the instance, table by table -/

section Tuples

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (q : Column L.μ)

/-- The tuples of a list of flush vectors of table `j`, on every row. -/
noncomputable def partT (j : Fin tabs.length)
    (vs : List (Vector (MvPolynomial (Fin (tabs.get j).w) K) 16)) : List (Vector K 16) :=
  vs.flatMap fun v ↦ ((inst L tabs hτ).executed j).map fun x ↦ evalV ((inst L tabs hτ).row q j x) v

/-- Every read tuple (the reads' pulls). -/
noncomputable def readTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)

/-- Every seed tuple (the seeds' pushes). -/
noncomputable def seedTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).seedVec)

/-- Every finalize tuple. -/
noncomputable def finTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).finVec)

/-- The number of reads: `Σ_t |reads t| · 2^τ`. -/
def nReads (tabs : List Tab) : ℕ := (tabs.map fun t ↦ t.reads.length * 2 ^ t.τ).sum

theorem flatMap_append_perm {α β : Type} (l : List α) (A B : α → List β) :
    (l.flatMap fun a ↦ A a ++ B a).Perm (l.flatMap A ++ l.flatMap B) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact (List.Perm.append_left _ ih).trans (List.perm_append_comm_assoc _ _ _)

theorem partT_append (j : Fin tabs.length)
    (u v : List (Vector (MvPolynomial (Fin (tabs.get j).w) K) 16)) :
    partT L tabs hτ q j (u ++ v) = partT L tabs hτ q j u ++ partT L tabs hτ q j v := by
  unfold partT; exact List.flatMap_append

theorem flushTuples_push :
    (inst L tabs hτ).flushTuples q .push = (List.finRange tabs.length).flatMap fun j ↦
      partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).bumpVec) ++
        partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).seedVec) := by
  unfold M3Instance.flushTuples
  refine List.flatMap_congr fun j _ ↦ ?_
  show List.flatMap _ (List.filter _ (tabs.get j).flushes) = _
  simp only [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def,
    reduceCtorEq, decide_false, decide_true, List.filter_false, List.filter_true, List.map_nil,
    List.nil_append, List.append_nil, List.flatMap_map, List.flatMap_append]
  simp only [partT, List.flatMap_map, evalV]

theorem flushTuples_pull :
    (inst L tabs hτ).flushTuples q .pull = (List.finRange tabs.length).flatMap fun j ↦
      partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec) ++
        partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).finVec) := by
  unfold M3Instance.flushTuples
  refine List.flatMap_congr fun j _ ↦ ?_
  show List.flatMap _ (List.filter _ (tabs.get j).flushes) = _
  simp only [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def,
    reduceCtorEq, decide_false, decide_true, List.filter_false, List.filter_true, List.map_nil,
    List.nil_append, List.append_nil, List.flatMap_map, List.flatMap_append]
  simp only [partT, List.flatMap_map, evalV]

theorem partT_bump (j : Fin tabs.length) :
    partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).bumpVec) =
      (partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)).map bumpT := by
  simp only [partT, List.flatMap_map, List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun r _ ↦ List.map_congr_left fun x _ ↦ ?_
  exact (tabs.get j).evalV_bumpVec _ r

theorem length_readTuples : (readTuples L tabs hτ q).length = nReads tabs := by
  have hex : ∀ j : Fin tabs.length, ((inst L tabs hτ).executed j).length = 2 ^ (tabs.get j).τ := by
    intro j
    rw [M3Instance.executed_eq]
    simp [inst]
  have h1 : ∀ j : Fin tabs.length, (partT L tabs hτ q j
      ((tabs.get j).reads.map (tabs.get j).readVec)).length =
      (tabs.get j).reads.length * 2 ^ (tabs.get j).τ := by
    intro j
    simp only [partT, List.length_flatMap, List.length_map, hex, List.map_map,
      Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
  simp only [readTuples, List.length_flatMap, h1, nReads]
  rw [← List.ofFn_eq_map]
  conv_rhs => rw [← List.ofFn_get tabs]
  rw [List.map_ofFn]
  rfl

end Tuples

/-! ## The lookup -/

/-- **The memory bus reads only seeded keys.** On the lvm instance, a balanced bus with nonzero
read counts (the clauses `Balanced`, `CountsNonzero` of `M3Holds`), count columns inside their
tables and fewer than `2^64 - 1` reads: every read tuple's key is a seed tuple's key. -/
theorem mem_lookup (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (q : Column L.μ)
    (hbal : (inst L tabs hτ).Balanced q) (hcnt : (inst L tabs hτ).CountsNonzero q)
    (hin : ∀ t ∈ tabs, ∀ r ∈ t.reads, r.2 < t.w) (hlen : nReads tabs < 2 ^ 64 - 1) :
    ∀ u ∈ readTuples L tabs hτ q, keyT u ∈ (seedTuples L tabs hτ q).map keyT := by
  have hperm : ((readTuples L tabs hτ q).map bumpT ++ seedTuples L tabs hτ q).Perm
      (readTuples L tabs hτ q ++ finTuples L tabs hτ q) := by
    have h := hbal
    unfold M3Instance.Balanced M3Instance.tuples M3Instance.boundaryTuples at h
    simp only [inst, List.filter_nil, List.flatMap_nil, List.append_nil] at h
    rw [flushTuples_push L tabs hτ q, flushTuples_pull L tabs hτ q] at h
    simp only [partT_bump] at h
    have e : (readTuples L tabs hτ q).map bumpT = (List.finRange tabs.length).flatMap fun j ↦
        (partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)).map bumpT := by
      rw [readTuples, List.map_flatMap]
    rw [e]
    exact ((flatMap_append_perm _ _ _).symm.trans h).trans (flatMap_append_perm _ _ _)
  refine lookup_sound (key := keyT) (count := cntT) (bump := bumpT) keyT_bumpT cntT_bumpT
    (Good := fun k ↦ k ∈ (seedTuples L tabs hτ q).map keyT) hperm
    (fun m hm ↦ List.mem_map_of_mem hm) ?_ ?_ ?_
  · intro m hm
    simp only [finTuples, partT, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨j, -, v, ⟨s, hs, rfl⟩, x, hx, rfl⟩ := hm
    rw [Tab.keyT_finVec]
    refine List.mem_map_of_mem ?_
    simp only [seedTuples, partT, List.mem_flatMap, List.mem_map]
    exact ⟨j, List.mem_finRange _, _, ⟨s, hs, rfl⟩, x, hx, rfl⟩
  · intro m hm
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨j, -, v, ⟨r, hr, rfl⟩, x, hx, rfl⟩ := hm
    rw [Tab.cntT_readVec]
    have hrw := hin _ (List.get_mem _ _) r hr
    simp only [CPoly.ext, hrw, dif_pos]
    have hmem : (⟨r.2, hrw⟩ : Fin (tabs.get j).w) ∈ (inst L tabs hτ).counts j := by
      simp only [inst, Tab.counts, List.mem_filterMap]
      exact ⟨r, hr, by simp only [dif_pos hrw]⟩
    have hxr : x.val < (inst L tabs hτ).rows j := by simp [inst]
    exact hcnt j _ hmem x hxr
  · rw [length_readTuples]; exact hlen

end Lvm.M3
