-- New for lvm (INB): `interp.inb` from a memory on which every row holds and every `readd`
-- address lies in its region. The fold follows WP-10's `fold_spec` (`LvmLoopInterp`); the segment
-- predicate `SegsIn` and its program bridge are WP-11b-QL's `SegsAssert`/`asserts_iff`/`group_assert`
-- (`LvmQBuildSem`) with `RowAssert` replaced by the region condition.
import LvmQBuildLemmas

/-!
# Every `readd` finds its cell

`RdIn M i`: if instance `i` is a `readd lo m`, its address operand's value in `M` is `g^(lo + k)` for
some `k < 2^m`.

* **`inb_of_mem`**: a memory with the inputs on which every row relation holds (`Holds`) and every
  `readd` address is in its region gives `(Q.interp inK inE).inb = true` (with `wf`, the input sizes
  and `GInj`). No `inb` is assumed: the interpreter agrees with `M` below its clock, so it computes
  the address `M` has, and `findExp` finds it.
* **`SegsIn M p δ`**: `RdIn` for every instance of the segments `δ` at `p` (the builder form);
  `segsIn_append`, `in_bind`, **`toProgram_in`** (`SegsIn` of a gadget's segments ⇒ `RdIn` on every
  instance of `toProgram`), `segsIn_of_noReadd` (segments without `readd`, by `decide`).
* **`InOk M m`**: for every pointer, the gadget's rows holding imply its `readd`s are in region;
  closed under `bind`, `seqAll`, `pure`.
-/

set_option autoImplicit false

namespace Lvm.Loop

open FE

/-- **The region condition of an instance**: a `readd lo m`'s address is `g^(lo + k)`, `k < 2^m`. -/
def RdIn (M : Mem) (i : Inst) : Prop :=
  match i.row.op with
  | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (M.arg i 0).c₀
  | _ => True

theorem findExp_isSome {α : FK} {lo m k : Nat} (hk : k < 2 ^ m) (h : FK.x ^ (lo + k) = α) :
    (findExp α lo m).isSome = true := by
  unfold findExp
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨k, List.mem_range.2 hk, by simp [h]⟩

namespace Program

variable (Q : Program)

/-- One step keeps `inb` when the instance's address is in region in a memory the state agrees
with below the clocks. -/
theorem step_inb_of (M : Mem) (s : St) (i : Inst) (hag : M.Agrees s.mem i.ck i.ce)
    (hok : InstOk Q i) (hin : RdIn M i) (hs : s.inb = true) : (Q.step s i).inb = true := by
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
    simp only [step, hop, St.put_inb] <;> try exact hs
  have ht := hok.typeOk
  simp only [Row.typeOk, hop, beq_iff_eq] at ht
  have hl : 0 < i.row.args.length := by
    have := congrArg List.length ht; simp at this; omega
  have hR : s.rd (i.row.args.getD 0 default).ty ((i.row.args.getD 0 default).at i.j) = M.arg i 0 := by
    have hlt := hok.reads _ (arg_mem hl)
    simp only [Inst.arg] at hlt
    rw [Inst.clock_eq_pick] at hlt
    rw [St.rd_eq_mem, Mem.arg]
    exact (Mem.rd_agree hag _ _ (by cases h : (i.row.args.getD 0 default).ty <;>
      simp only [h, Ty.pick] at hlt ⊢ <;> exact hlt)).symm
  simp only [RdIn, hop] at hin
  obtain ⟨k, hk, hx⟩ := hin
  rw [hR]
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (findExp_isSome hk hx)
  rw [he]
  simp only [St.put_inb]
  exact hs

/-- The fold keeps `inb` (WP-10's `fold_spec`, its agreement carried along). -/
theorem fold_inb (M : Mem) (hinj : GInj (max (Q.cells .K) (Q.cells .E))) :
    ∀ (L : List Inst) (s : St) (k e : Nat), Chain k e L → s.kc.size = k → s.ec.size = e →
      M.Agrees s.mem k e → (∀ i ∈ L, Q.RowDef M i ∧ InstOk Q i ∧ RdIn M i) → s.inb = true →
      (L.foldl Q.step s).inb = true
  | [], _, _, _, _, _, _, _, _, hs => hs
  | i :: L, s, k, e, ⟨hck, hce, hch⟩, hk, he, hag, hL, hs => by
    subst hck hce
    have hi := hL i (by simp)
    have h1 := Q.step_inb_of M s i hag hi.2.1 hi.2.2 hs
    obtain ⟨g1, g2, g3, -⟩ := Q.step_spec M s i hk he hag hi.1 hi.2.1 hinj h1
    exact fold_inb M hinj L (Q.step s i) _ _ hch g2 g3 g1 (fun j hj => hL j (by simp [hj])) h1

/-- **`inb` from a memory**: the inputs, every row relation, every `readd` address in its region. -/
theorem inb_of_mem (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (M : Mem) (hin : Q.Inputs M inK inE)
    (hM : Q.Holds M) (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hR : ∀ i ∈ Q.insts, RdIn M i) : (Q.interp inK inE).inb = true := by
  obtain ⟨hch, -, -⟩ := Q.chain_insts
  exact Q.fold_inb M hinj Q.insts ⟨inK, inE, true, true⟩ Q.nInK Q.nInE hch hsz.1 hsz.2
    ⟨fun n hn => hin.1 n hn, fun n hn => hin.2 n hn⟩
    (fun i hi => ⟨hM i hi, Q.instOk_of_mem hwf hi, hR i hi⟩) rfl

/-! ## The interpreter keeps its inputs (no `inb` needed) -/

theorem step_kc (s : St) (i : Inst) : (Q.step s i).kc = s.kc ∨ ∃ v, (Q.step s i).kc = s.kc.push v := by
  have hput : ∀ (τ : Ty) (v : FE), (s.put τ v).kc = s.kc ∨ ∃ w, (s.put τ v).kc = s.kc.push w := by
    intro τ v; cases τ
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;> simp only [step, hop]
  · exact hput _ _
  · exact hput _ _
  · simp
  · exact hput _ _
  · exact hput _ _
  · split
    · exact hput _ _
    · rcases hput i.row.ty 0 with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem foldl_kc : ∀ (L : List Inst) (s : St) (n : Nat), n < s.kc.size →
    (L.foldl Q.step s).kc.getD n 0 = s.kc.getD n 0
  | [], _, _, _ => rfl
  | i :: L, s, n, hn => by
    have hsz : n < (Q.step s i).kc.size ∧ (Q.step s i).kc.getD n 0 = s.kc.getD n 0 := by
      rcases Q.step_kc s i with h | ⟨v, h⟩
      · rw [h]; exact ⟨hn, rfl⟩
      · rw [h]; exact ⟨by simp; omega, getD_push_lt _ _ _ hn⟩
    rw [List.foldl_cons, foldl_kc L _ n hsz.1, hsz.2]

/-- **The interpreter's memory holds the `K` inputs** (with or without `inb`). -/
theorem interpMem_inK (inK : Array FK) (inE : Array FE) {n : Nat} (hn : n < inK.size) :
    (Q.interpMem inK inE).k n = inK.getD n 0 :=
  Q.foldl_kc Q.insts ⟨inK, inE, true, true⟩ n hn

end Program

namespace Build

/-! ## Segments -/

/-- Every instance of block `B` at `p` is in region. -/
def BlockIn (M : Mem) (p : Ptr) (B : Block) : Prop :=
  ∀ jf < B.size, ∀ t < B.tpl.length, RdIn M (instAt p B jf t)

/-- **Every `readd` of the segments `δ` at `p` is in region in `M`.** -/
def SegsIn (M : Mem) : Ptr → List Seg → Prop
  | _, [] => True
  | p, .row r :: δ => RdIn M (rowInst p r) ∧ SegsIn M (p.adv [.row r]) δ
  | p, .blk B :: δ => BlockIn M p B ∧ SegsIn M (p.adv [.blk B]) δ

theorem segsIn_append (M : Mem) : ∀ (p : Ptr) (δ₁ δ₂ : List Seg),
    SegsIn M p (δ₁ ++ δ₂) ↔ SegsIn M p δ₁ ∧ SegsIn M (p.adv δ₁) δ₂
  | p, [], δ₂ => by simp [SegsIn]
  | p, .row r :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsIn]
    rw [segsIn_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]
  | p, .blk B :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsIn]
    rw [segsIn_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]

theorem in_bind {α β : Type} (M : Mem) (m : BM α) (f : α → BM β) (p : Ptr) :
    SegsIn M p ((m >>= f) p).2 ↔
      SegsIn M p (m p).2 ∧ SegsIn M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2 := by
  rw [bind_apply]; exact segsIn_append M _ _ _

/-- Every block of `bs` is in region at its pointer. -/
def BlocksIn (M : Mem) : Ptr → List Block → Prop
  | _, [] => True
  | p, B :: bs => BlockIn M p B ∧ BlocksIn M (p.advBs [B]) bs

theorem blocksIn_iff (M : Mem) : ∀ (p : Ptr) (bs : List Block),
    BlocksIn M p bs ↔ ∀ b < bs.length, BlockIn M (p.advBs (bs.take b)) (bs.getD b default)
  | p, [] => by simp [BlocksIn]
  | p, B :: bs => by
    simp only [BlocksIn, blocksIn_iff M _ bs, List.length_cons]
    constructor
    · rintro ⟨h0, h⟩ b hb
      rcases b with _ | b
      · simpa [Ptr.advBs] using h0
      · have := h b (by omega)
        simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this
    · intro h
      refine ⟨by simpa [Ptr.advBs] using h 0 (by omega), fun b hb => ?_⟩
      have := h (b + 1) (by omega)
      simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this

theorem glueI_iff (M : Mem) : ∀ (p : Ptr) (rs : List Row),
    BlockIn M p ⟨[], rs⟩ ↔ SegsIn M p (rs.map .row)
  | p, [] => by simp [BlockIn, SegsIn]
  | p, r :: rs => by
    have ih := glueI_iff M (p.adv [.row r]) rs
    simp only [List.map_cons, SegsIn, ← ih, BlockIn, Block.size, Block.lsize, List.sum_nil,
      pow_zero, Nat.lt_one_iff, forall_eq, List.length_cons]
    constructor
    · intro h
      refine ⟨by simpa [instAt_glue_zero] using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega)
      rwa [instAt_glue_succ] at this
    · rintro ⟨h0, h⟩ t ht
      rcases t with _ | t
      · rw [instAt_glue_zero]; exact h0
      · rw [instAt_glue_succ]; exact h t (by omega)

theorem blocksIn_glueB (M : Mem) (p : Ptr) (rs : List Row) (bs : List Block) :
    BlocksIn M p (glueB rs bs) ↔ SegsIn M p (rs.map .row) ∧ BlocksIn M (p.adv (rs.map .row)) bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp [SegsIn]
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, BlocksIn, glueI_iff, advBs_glue]

theorem groupAux_in (M : Mem) : ∀ (p : Ptr) (δ : List Seg),
    SegsIn M p δ ↔ SegsIn M p ((groupAux δ).1.map .row) ∧
      BlocksIn M (p.adv ((groupAux δ).1.map .row)) (groupAux δ).2
  | p, [] => by simp [SegsIn, BlocksIn, groupAux]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [SegsIn, List.map_cons, List.map_nil, and_true]
      rw [groupAux_in M _ δ, blocksIn_glueB]
    · simp only [SegsIn, List.map_cons]
      rw [groupAux_in M _ δ, Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), and_assoc]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [SegsIn, List.map_nil, Ptr.adv_nil, BlocksIn, true_and]
    rw [groupAux_in M _ δ, blocksIn_glueB, advBs_blk]

theorem group_in (M : Mem) (p : Ptr) (δ : List Seg) : BlocksIn M p (group δ) ↔ SegsIn M p δ := by
  rw [group_eq, blocksIn_glueB, groupAux_in M p δ]

theorem rdIn_inst (M : Mem) (Q : Program) (b jf t : Nat) :
    RdIn M (Q.inst b jf t) ↔ RdIn M (instAt ⟨Q.start .K b, Q.start .E b⟩ (Q.blk b) jf t) := Iff.rfl

/-- `RdIn` on every instance, block by block. -/
theorem ins_iff (Q : Program) (M : Mem) :
    (∀ i ∈ Q.insts, RdIn M i) ↔ BlocksIn M ⟨Q.nInK, Q.nInE⟩ Q.blocks := by
  rw [blocksIn_iff]
  constructor
  · intro h b hb jf hjf t ht
    have hi := (Q.mem_insts (Q.inst b jf t)).mpr ⟨b, hb, jf, by simpa [Program.blk] using hjf, t,
      by simpa [Program.blk] using ht, rfl⟩
    simpa [rdIn_inst, start_ptr, Program.blk] using h _ hi
  · intro h i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    rw [rdIn_inst, start_ptr]
    exact h b hb jf (by simpa [Program.blk] using hjf) t (by simpa [Program.blk] using ht)

/-- **The bridge**: a gadget's segments in region ⇒ every instance of its program in region. -/
theorem toProgram_in {α : Type} (nK nE : Nat) (m : BM α) (M : Mem)
    (h : SegsIn M ⟨nK, nE⟩ (m ⟨nK, nE⟩).2) : ∀ i ∈ (toProgram nK nE m).insts, RdIn M i :=
  (ins_iff _ M).mpr ((group_in M _ _).mpr h)

/-! ## Segments without `readd` -/

/-- A row that is not a `readd`. -/
def rowNoRd (r : Row) : Bool := match r.op with | .readd .. => false | _ => true

/-- No `readd` in the segments (checked by `decide` on a concrete gadget). -/
def noReaddSegs : List Seg → Bool
  | [] => true
  | .row r :: δ => rowNoRd r && noReaddSegs δ
  | .blk B :: δ => B.tpl.all rowNoRd && noReaddSegs δ

theorem rdIn_of_noRd {M : Mem} {i : Inst} (h : rowNoRd i.row = true) : RdIn M i := by
  unfold RdIn; unfold rowNoRd at h
  split
  · next _ _ hop => rw [hop] at h; simp at h
  · trivial

theorem segsIn_of_noReadd (M : Mem) : ∀ (p : Ptr) (δ : List Seg), noReaddSegs δ = true → SegsIn M p δ
  | _, [], _ => trivial
  | p, .row r :: δ, h => by
    simp only [noReaddSegs, Bool.and_eq_true] at h
    exact ⟨rdIn_of_noRd h.1, segsIn_of_noReadd M _ δ h.2⟩
  | p, .blk B :: δ, h => by
    simp only [noReaddSegs, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun jf _ t ht => rdIn_of_noRd ?_, segsIn_of_noReadd M _ δ h.2⟩
    show rowNoRd (B.tpl.getD t default) = true
    rw [List.getD_eq_getElem _ _ ht]
    exact h.1 _ (List.getElem_mem ht)

/-! ## Gadgets whose rows put their `readd`s in region -/

/-- **`m`'s `readd`s are in region wherever its rows hold.** -/
def InOk (c : Ctx) (M : Mem) {α : Type} (m : BM α) : Prop :=
  ∀ p, SegsHold c M p (m p).2 → SegsIn M p (m p).2

theorem inOk_pure {c : Ctx} {M : Mem} {α : Type} (x : α) : InOk c M (pure x : BM α) :=
  fun _ _ => trivial

theorem inOk_bind {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} (hm : InOk c M m)
    (hf : ∀ p, InOk c M (f (m p).1)) : InOk c M (m >>= f) := by
  intro p h
  rw [hold_bind] at h
  rw [in_bind]
  exact ⟨hm p h.1, hf p _ h.2⟩

theorem inOk_seqAll {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)), (∀ m ∈ ms, InOk c M m) → InOk c M (seqAll ms)
  | [], _ => inOk_pure _
  | m :: ms, h => by
    simp only [seqAll]
    exact inOk_bind (h m (by simp)) fun _ =>
      inOk_bind (inOk_seqAll ms fun m' hm' => h m' (by simp [hm'])) fun _ => inOk_pure _

theorem inOk_noReadd {c : Ctx} {M : Mem} {α : Type} {m : BM α} (h : ∀ p, noReaddSegs (m p).2 = true) :
    InOk c M m := fun p _ => segsIn_of_noReadd M p _ (h p)

/-- A loop row's region condition, on the resolved operand (as `LRel`). -/
theorem loop_in_iff (M : Mem) (o : LoopOut) (jf t : Nat) :
    RdIn M (instAt o.p o.blk jf t) ↔
      match (o.tpl.getD t default).op with
      | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (o.arg M jf t 0).c₀
      | _ => True := by
  have hrow : (instAt o.p o.blk jf t).row = resRow o.p o.dims o.tpl (o.tpl.getD t default) :=
    mkLoop_row _ _ _ _
  unfold RdIn
  rw [hrow]
  simp only [resRow, instAt_loop_arg]

/-- **A loop is in region** when each `readd` template row's address is, at every iteration. -/
theorem loop_in {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : ∀ jf < 2 ^ dims.sum, ∀ t < tpl.length, ∀ lo m args, tpl.getD t default = ⟨.readd lo m, .K, args⟩ →
      ∃ k < 2 ^ m, FK.x ^ (lo + k) = ((args.getD 0 default).val M ⟨p, dims, tpl⟩ jf).c₀)
    (hK : ∀ t < tpl.length, ∀ lo m, (tpl.getD t default).op = .readd lo m → (tpl.getD t default).ty = .K) :
    SegsIn M p (loop dims tpl p).2 := by
  simp only [loop_apply, SegsIn, and_true]
  intro jf hjf t ht
  have ht' : t < tpl.length := by simpa [mkLoop] using ht
  refine (loop_in_iff M ⟨p, dims, tpl⟩ jf t).mpr ?_
  show match (tpl.getD t default).op with
    | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (LoopOut.arg M ⟨p, dims, tpl⟩ jf t 0).c₀
    | _ => True
  rcases hr : tpl.getD t default with ⟨op, ty, args⟩
  cases op with
  | readd lo m =>
    have hty : ty = .K := by have := hK t ht' lo m (by rw [hr]); rwa [hr] at this
    subst hty
    simp only [LoopOut.arg, hr]
    exact h jf hjf t ht' lo m args hr
  | _ => trivial

end Build

end Lvm.Loop
