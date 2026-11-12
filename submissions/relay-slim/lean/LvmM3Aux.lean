-- new for lvm (WP-9b): the auxiliary tables' reads through the bus (the `BITS` bridge for WP-12),
-- from WP-9's `seed_key`/`mem_lookup` and WP-10's `seed_cases`/`holds_seedMem`/`interp_unique`
-- (the first lines of `loopir_sound`'s proof, `LvmLoopSound.lean:348`).
import LvmM3Loop

/-!
# Auxiliary tables read the interpreter's cells

**The `BITS` bridge (option "reads through the bus").** An auxiliary table (`aux`, WP-12's `BITS`)
seeds nothing; it *reads* cells of the LoopIR memories through the bus, like a LoopIR piece: the
word it decomposes and each of its outputs (`shl k`, `shr k`, `bit z`, a linear form of its bit
columns). The outputs are LoopIR *input* cells (seeded by an input array, any value the prover
chose); the table's reads pin them to the word's functions. `aux_read`: on the lvm instance with
`M3Holds`, each read of an auxiliary table at each row is, coordinate by coordinate, the key of a
cell of the interpreter's run on the inputs read off the stack (`interpMem (inKOf q) (inEOf q)`):
separator `sep τ`, address `g^e`, value limbs the cell's. `aux_read_at`: with the address known
(`g^a`, `a` below the cell count, a fixed column of the table), the value limbs are cell `a`'s.

WP-12 combines this with its row lemma (`LvmBits.row_sound`: the row's constraints make every
output the word function of the word) to get `SigBits` for `M = interpMem`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly
open Lvm.Loop

/-! ## The seed memory is the interpreter's -/

/-- **Under `loopir_sound`'s hypotheses the seed memory is the interpreter's memory** on every
cell (the agreement `loopir_sound` proves on the way, `LvmLoopSound.lean:356`). -/
theorem seedMem_eq_interp (Q : Program) (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (W : Witness) (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.interp inK inE).inb = true)
    {τ : Ty} {e : ℕ} (he : e < Q.cells τ) :
    (Q.seedMem W inK inE).rd τ e = (Q.interpMem inK inE).rd τ e := by
  obtain ⟨hH, -⟩ := Q.holds_seedMem hwf hcons hbus hinj
  have hin : Q.Inputs (Q.seedMem W inK inE) inK inE :=
    ⟨fun n hn => by simp [Program.seedMem, hn], fun n hn => by simp [Program.seedMem, hn]⟩
  obtain ⟨hag, -⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact Program.Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact he)

section Aux

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The hypotheses `aux_read` shares with `loop_bus` and `loopir_sound`. -/
structure AuxHyps (q : Column L.μ) : Prop where
  wf : Q.wf = true
  grp : GrpOk Q groups
  inOk : InOk Q arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  holds : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q
  inb : (Q.interp (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).inb = true

/-- **An auxiliary table's read is a cell of the interpreter's run** (the `BITS` bridge). At row `x`
of auxiliary table `k` (instance table `groups.length + arrs.length + k`), the read `r`'s
separator, address and value limbs, evaluated on the row, are those of cell `e` of memory `τ` of
`interpMem (inKOf q) (inEOf q)`, for some `e` below the cell count. -/
theorem aux_read (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) :
    ∃ τ e, e < Q.cells τ ∧ r.1.sep = sep τ ∧
      CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) r.1.addr =
        FK.toBF64 (FK.x ^ e) ∧
      ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
          (r.1.val.getD l []) =
        FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ e)).getD l 0) := by
  set W := witOf Q pl groups arrs aux L hτ q
  set inK := inKOf Q pl groups arrs aux L hτ q
  set inE := inEOf Q pl groups arrs aux L hτ q
  have hget := get_aux Q pl groups arrs aux hk hj
  set row := (lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x
  have hrd : r ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).reads := by rw [hget]; exact hr
  have hu : evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, x, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q
    H.holds.2.1 H.holds.2.2.1 H.cnt H.len _ hu)
  obtain ⟨m', -, hm', he⟩ := seed_key Q pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds q hs
  obtain ⟨τ, e, hec, h1, h2, h3⟩ := Q.seed_cases W inK inE hm'
  have hkey : keyT (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r)) =
      keyT (encT m') := hks.symm.trans he
  have hagree := seedMem_eq_interp Q H.wf inK inE
    ⟨inKOf_size Q pl groups arrs aux L hτ q, inEOf_size Q pl groups arrs aux L hτ q⟩ W
    (loop_cons Q pl groups arrs aux L hτ H.grp q H.holds) (loop_bus Q pl groups arrs aux L hτ H.grp
      H.inOk H.auxSeeds H.cnt H.len q H.holds) H.inj H.inb hec
  have hcoord : ∀ i (hi : i < 16), i ≠ 2 →
      (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r))[i] = (encT m')[i] :=
    fun i hi hi2 ↦ keyT_coord hkey i hi hi2
  refine ⟨τ, e, hec, ?_, ?_, fun l hl ↦ ?_⟩
  · have := hcoord 0 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      if_true, MvPolynomial.eval_C] at this
    exact (FK.toBF64_injective this).trans h1
  · have := hcoord 1 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show (1 : ℕ) ≠ 0 from by decide, if_true, if_false, CPoly.eval_toMv] at this
    rw [this, h2]
  · have := hcoord (l + 3) (by omega) (by omega)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show l + 3 ≠ 0 from by omega, show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega,
      if_false, Nat.add_sub_cancel, CPoly.eval_toMv] at this
    rw [this, h3, hagree]

/-- **An auxiliary table's read at a known address is that cell of the interpreter's run**: if the
read names memory `τ` and evaluates its address to `g^a` with `a` below the cell count, its value
limbs are cell `a`'s. -/
theorem aux_read_at (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) {τ : Ty} {a : ℕ} (hsep : r.1.sep = sep τ) (ha : a < Q.cells τ)
    (haddr : CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
      r.1.addr = FK.toBF64 (FK.x ^ a)) :
    ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
        (r.1.val.getD l []) =
      FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q)).rd τ a)).getD l 0) := by
  obtain ⟨τ', e, he, h1, h2, h3⟩ := aux_read Q pl groups arrs aux L hτ q H hk hj x hr
  obtain rfl : τ' = τ := sep_inj' (h1.symm.trans hsep)
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ ↦ by cases σ <;> simp
  obtain rfl : e = a := H.inj _ _ (lt_of_lt_of_le he (hN _)) (lt_of_lt_of_le ha (hN _))
    (FK.toBF64_injective (h2.symm.trans haddr))
  exact h3

/-- **An auxiliary table's constraints vanish on every row** (`ConstraintsVanish`, on the row as
`CPoly.evalB` reads it): WP-12's row lemma starts here. -/
theorem aux_cons (q : Column L.μ) (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {C : CPoly} (hC : C ∈ aux[k].cons) :
    CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) C = 0 := by
  have hcm : C ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).cons := by
    rw [get_aux Q pl groups arrs aux hk hj]; exact hC
  have hz := hM.1 ⟨_, hj⟩ _ (List.mem_map_of_mem hcm) x
  rwa [CPoly.eval_toMv] at hz

end Aux

end Lvm.M3
