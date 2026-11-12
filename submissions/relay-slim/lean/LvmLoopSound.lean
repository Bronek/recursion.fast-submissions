import LvmLoopPieces

/-!
# `loopir_sound`: tables that hold are the interpreter's run

**`loopir_sound`** (generic over every program): if the program check passes, every constraint of
every piece vanishes on every row, every read's key `(sep, addr, value)` is a seed's key (the
conclusion of leanVM's lookup argument from a balanced bus), `g`-powers are injective below the cell
counts, and the interpreter's `readd`s found their cells, then every committed result and operand
value of every piece row is the interpreter's cell (`WitnessOf W (interpMem …)`) and every gated
assertion holds (`interp.ok = true`).

The proof: the seeds define a memory `seedMem` (the inputs, then each cell's unique writer row's
committed result); the bus makes every read the seed memory's cell at the read's address
(`read_ok`, `readd_ok`); the constraints then give every instance's relation on that memory
(`holds_seedMem`), and `interp_unique` identifies it with the interpreter's.
-/

namespace Lvm.Loop

open FE Program

theorem sep_inj {τ τ' : Ty} (h : sep τ = sep τ') : τ = τ' := by
  cases τ <;> cases τ' <;> first | rfl | exact absurd h (by decide)

theorem limbsOf_inj_rd (M : Mem) {τ : Ty} {u : Nat → FK} {e : Nat}
    (h : (List.range τ.limbs).map u = limbsOf τ (M.rd τ e)) : valOf τ u = M.rd τ e := by
  cases τ
  · simp only [Ty.limbs, List.range_one, List.map_cons, List.map_nil, limbsOf, Mem.rd,
      List.cons.injEq, and_true] at h
    simp only [valOf, Mem.rd, h]; rfl
  · simp only [Ty.limbs, List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, limbsOf, Mem.rd, List.cons.injEq,
      and_true] at h
    simp only [valOf, Mem.rd]
    obtain ⟨h0, h1, h2⟩ := h
    rw [h0, h1, h2]

namespace Program

variable (Q : Program)

/-- **The committed values of `W` are the cells of `M`**: at every piece row, the result value (for
a writer) and every operand value. -/
def WitnessOf (W : Witness) (M : Mem) : Prop :=
  ∀ n p x, (n, p, x) ∈ Q.prows →
    (p.shape.writes = true → p.shape.resV (Q.rowVal W n p x) = M.res (Q.pinst p x)) ∧
    ∀ o < p.shape.args.length, p.shape.argV (Q.rowVal W n p x) o = M.arg (Q.pinst p x) o

/-! ## Writers -/

theorem writer_row {npx : Nat × Piece × Nat}
    (h : npx ∈ Q.prows) (hw : npx.2.1.shape.writes = true) :
    (Q.pinst npx.2.1 npx.2.2).row.writes = some npx.2.1.shape.ty ∧
      (Q.pinst npx.2.1 npx.2.2).row.ty = npx.2.1.shape.ty := by
  obtain ⟨-, hsh⟩ := Q.prow_inst (n := npx.1) (x := npx.2.2) (p := npx.2.1) h
  rw [← hsh] at hw ⊢
  simp only [Shape.writes, Row.shape, bne_iff_ne, ne_eq] at hw
  have hop : (Q.pinst npx.2.1 npx.2.2).row.op ≠ .assert0 := fun h' => hw (by rw [h']; rfl)
  simp only [Row.shape, hw, if_false, Row.writes]
  first | exact ⟨trivial, trivial⟩ | (split <;> simp_all)

theorem writer_clock {i : Inst} (hi : i ∈ Q.insts) {τ : Ty} (hw : i.row.writes = some τ) :
    Q.nIn τ ≤ i.clock τ ∧ i.clock τ < Q.cells τ := by
  obtain ⟨hch, hK, hE⟩ := Q.chain_insts
  have hc := chain_clock_le _ _ _ hch i hi
  have hw1 := Row.w_of_writes hw
  cases τ <;> simp only [Ty.ind, if_true, if_false, reduceCtorEq] at hw1
  · have := hw1 .K; simp [Ty.ind] at this
    simp only [Inst.clock, nIn]; omega
  · have := hw1 .E; simp [Ty.ind] at this
    simp only [Inst.clock, nIn]; omega

theorem chain_writer_inj : ∀ (L : List Inst) (k e : Nat), Chain k e L → ∀ {τ : Ty} {i i' : Inst},
    i ∈ L → i' ∈ L → i.row.writes = some τ → i'.row.writes = some τ → i.clock τ = i'.clock τ →
      i = i'
  | [], _, _, _, _, _, _, h, _, _, _, _ => by simp at h
  | j :: L, k, e, ⟨hk, he, hch⟩, τ, i, i', hi, hi', hw, hw', hc => by
    have hlow : j.row.writes = some τ → ∀ i'' ∈ L, j.clock τ < i''.clock τ := by
      intro hj i'' hm
      have hc := chain_clock_le _ _ _ hch i'' hm
      have hw1 := Row.w_of_writes hj
      cases τ
      · have : j.row.w .K = 1 := (hw1 .K).trans rfl
        simp only [Inst.clock]; omega
      · have : j.row.w .E = 1 := (hw1 .E).trans rfl
        simp only [Inst.clock]; omega
    rcases List.mem_cons.mp hi with rfl | hiL <;> rcases List.mem_cons.mp hi' with rfl | hiL'
    · rfl
    · exact absurd hc (Nat.ne_of_lt (hlow hw _ hiL'))
    · exact absurd hc.symm (Nat.ne_of_lt (hlow hw' _ hiL))
    · exact chain_writer_inj L _ _ hch hiL hiL' hw hw' hc

/-- A writer piece row of memory `τ` writing cell `e`. -/
def WRow (τ : Ty) (e : Nat) (npx : Nat × Piece × Nat) : Prop :=
  npx ∈ Q.prows ∧ npx.2.1.shape.writes = true ∧ npx.2.1.shape.ty = τ ∧
    (Q.pinst npx.2.1 npx.2.2).clock τ = e

/-- **One writer row per cell.** -/
theorem wrow_unique {τ : Ty} {e : Nat} {a b : Nat × Piece × Nat} (ha : Q.WRow τ e a)
    (hb : Q.WRow τ e b) : a = b := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hwa := (Q.writer_row ha1 ha2).1
  have hwb := (Q.writer_row hb1 hb2).1
  rw [ha3] at hwa; rw [hb3] at hwb
  have hi := chain_writer_inj Q.insts _ _ Q.chain_insts.1 (Q.prow_inst ha1).1 (Q.prow_inst hb1).1
    hwa hwb (ha4.trans hb4.symm)
  obtain ⟨n, p, x⟩ := a
  obtain ⟨n', p', x'⟩ := b
  obtain ⟨h1, h2, h3⟩ := Q.prow_inj ha1 hb1 hi
  subst h1 h2 h3; rfl

open Classical in
/-- The value the seeds give cell `e` of memory `τ` past the inputs: its writer row's result. -/
noncomputable def wval (W : Witness) (τ : Ty) (e : Nat) : FE :=
  if h : ∃ npx, Q.WRow τ e npx then
    (Classical.choose h).2.1.shape.resV
      (Q.rowVal W (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2)
  else 0

/-- **The memory the seeds define**: the inputs, then every cell's writer row's result. -/
noncomputable def seedMem (W : Witness) (inK : Array FK) (inE : Array FE) : Mem :=
  ⟨fun e => if e < Q.nInK then inK.getD e 0 else (Q.wval W .K e).c₀,
    fun e => if e < Q.nInE then inE.getD e 0 else Q.wval W .E e⟩

theorem wval_eq (W : Witness) {τ : Ty} {e : Nat} {npx : Nat × Piece × Nat} (h : Q.WRow τ e npx) :
    Q.wval W τ e = npx.2.1.shape.resV (Q.rowVal W npx.1 npx.2.1 npx.2.2) := by
  have hex : ∃ npx, Q.WRow τ e npx := ⟨npx, h⟩
  rw [wval, dif_pos hex, Q.wrow_unique (Classical.choose_spec hex) h]

theorem seedMem_writer (W : Witness) (inK : Array FK) (inE : Array FE) {n x : Nat} {p : Piece}
    (h : (n, p, x) ∈ Q.prows) (hw : p.shape.writes = true) :
    (Q.seedMem W inK inE).res (Q.pinst p x) = p.shape.resV (Q.rowVal W n p x) := by
  obtain ⟨hwr, hty⟩ := Q.writer_row
    (npx := (n, p, x)) h hw
  have hcl := Q.writer_clock (Q.prow_inst h).1 hwr
  have hW : Q.WRow p.shape.ty ((Q.pinst p x).clock p.shape.ty) (n, p, x) := ⟨h, hw, rfl, rfl⟩
  simp only [Mem.res]
  rw [hty]
  cases hτ : p.shape.ty
  · rw [hτ] at hW hcl
    simp only [Mem.rd, seedMem, nIn] at hcl ⊢
    rw [if_neg (by omega), Q.wval_eq W hW]
    simp only [Shape.resV, hτ, valOf]; rfl
  · rw [hτ] at hW hcl
    simp only [Mem.rd, seedMem, nIn] at hcl ⊢
    rw [if_neg (by omega), Q.wval_eq W hW]

/-- **What a seed is**: the key of cell `e < cells τ` of the seed memory. -/
theorem seed_cases (W : Witness) (inK : Array FK) (inE : Array FE) {m : Msg}
    (hm : m ∈ Q.seedMsgs W inK inE) :
    ∃ τ e, e < Q.cells τ ∧ m.sep = sep τ ∧ m.addr = FK.x ^ e ∧
      m.val = limbsOf τ ((Q.seedMem W inK inE).rd τ e) := by
  have hinK : Q.nInK ≤ Q.cells .K := by
    have := Q.chain_insts.2.1; omega
  have hinE : Q.nInE ≤ Q.cells .E := by
    have := Q.chain_insts.2.2; omega
  simp only [seedMsgs, inputSeeds, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap] at hm
  rcases hm with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨⟨n, p, x⟩, hpx, hm⟩
  · exact ⟨.K, e, by omega, rfl, rfl, by simp [limbsOf, Mem.rd, seedMem, he, FE.ofK]⟩
  · exact ⟨.E, e, by omega, rfl, rfl, by simp [limbsOf, Mem.rd, seedMem, he]⟩
  · split at hm
    · rename_i hw
      simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨hwr, hty⟩ := Q.writer_row
        (npx := (n, p, x)) hpx hw
      have hcl := Q.writer_clock (Q.prow_inst hpx).1 hwr
      refine ⟨p.shape.ty, (Q.pinst p x).clock p.shape.ty, hcl.2, rfl, ?_, ?_⟩
      · simp [Shape.seedFlush, Flush.msg, rowVal, fval, fvalBasic, hty]
      · have := Q.seedMem_writer W inK inE hpx hw
        simp only [Mem.res, hty] at this
        rw [this]
        simp only [Shape.seedFlush, Flush.msg, Shape.resVals, List.map_map]
        cases hτ : p.shape.ty
        · simp [Shape.resV, hτ, valOf, limbsOf, Ty.limbs, rowVal, FE.ofK]
        · simp [Shape.resV, hτ, valOf, limbsOf, Ty.limbs, rowVal, List.range_succ]
    · simp at hm

/-! ## The bus makes every read the seed memory's cell -/

theorem shape_args {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) :
    p.shape.args = (Q.pinst p x).row.args.map (·.ty) := by
  rw [← (Q.prow_inst h).2]; rfl

theorem shape_arg_ty {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) {o : Nat}
    (ho : o < p.shape.args.length) : p.shape.args.getD o .K = ((Q.pinst p x).arg o).ty := by
  have ha := Q.shape_args h
  have ho' : o < (Q.pinst p x).row.args.length := by rw [ha] at ho; simpa using ho
  rw [ha]
  simp [Inst.arg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho']

/-- The bus hypothesis, for one message. -/
theorem bus_key {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key) {n x : Nat}
    {p : Piece} (h : (n, p, x) ∈ Q.prows) {f : Flush} (hf : f ∈ p.shape.readFlushes) :
    ∃ τ e, e < Q.cells τ ∧ f.sep = sep τ ∧ f.addr.ev (Q.rowVal W n p x) = FK.x ^ e ∧
      f.val.map (·.ev (Q.rowVal W n p x)) = limbsOf τ ((Q.seedMem W inK inE).rd τ e) := by
  have hm : f.msg (Q.rowVal W n p x) ∈ Q.readMsgs W := by
    simp only [readMsgs, List.mem_flatMap, List.mem_map]
    exact ⟨(n, p, x), h, f, hf, rfl⟩
  obtain ⟨s, hs, hk⟩ := List.mem_map.mp (hbus _ hm)
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.seed_cases W inK inE hs
  simp only [Msg.key, Flush.msg, Prod.mk.injEq] at hk
  exact ⟨τ, e, he, hk.1.symm.trans h1, hk.2.1.symm.trans h2, hk.2.2.symm.trans h3⟩

/-- **Every operand read is the seed memory's cell.** -/
theorem read_ok (hwf : Q.wf = true) {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) {n x : Nat} {p : Piece}
    (h : (n, p, x) ∈ Q.prows) {o : Nat} (ho : o < p.shape.args.length) :
    p.shape.argV (Q.rowVal W n p x) o = (Q.seedMem W inK inE).arg (Q.pinst p x) o := by
  have hf : (⟨false, sep (p.shape.args.getD o .K), Poly2.var (.fix (.arg o)), Poly2.var (.cnt o),
      p.shape.argVals o⟩ : Flush) ∈ p.shape.readFlushes := by
    simp only [Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨o, ho, rfl⟩
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.bus_key hbus h hf
  have hτ' := Q.shape_arg_ty h ho
  have hτ : ((Q.pinst p x).arg o).ty = τ := by rw [← hτ']; exact sep_inj h1
  have hok := Q.instOk_of_mem hwf (Q.prow_inst h).1
  have hmem : (Q.pinst p x).arg o ∈ (Q.pinst p x).row.args := by
    apply arg_mem; rw [Q.shape_args h] at ho; simpa using ho
  have hlt := lt_of_lt_of_le (hok.reads _ hmem) (hok.cells _)
  simp only [Poly2.ev_var, rowVal, fval, fvalBasic] at h2
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ => by cases σ <;> simp
  rw [hτ] at hlt
  have hee : ((Q.pinst p x).arg o).at (Q.pinst p x).j = e :=
    hinj _ _ (lt_of_lt_of_le hlt (hN _)) (lt_of_lt_of_le he (hN _)) h2
  simp only [Shape.argVals, List.map_map, Function.comp_def, Poly2.ev_var] at h3
  unfold Shape.argV
  rw [Mem.arg, hτ', hτ, hee]
  rw [argLimbs_eq, hτ', hτ] at h3
  exact limbsOf_inj_rd _ h3

/-- **A computed-address read is the seed memory's cell at that address.** -/
theorem readd_ok {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key) {n x : Nat}
    {p : Piece} (h : (n, p, x) ∈ Q.prows) (hk : p.shape.kind = .readd) :
    ∃ e < Q.cells p.shape.ty, FK.x ^ e = Q.rowVal W n p x (.arg 0 0) ∧
      p.shape.resV (Q.rowVal W n p x) = (Q.seedMem W inK inE).rd p.shape.ty e := by
  have hf : (⟨false, sep p.shape.ty, Poly2.var (.arg 0 0), Poly2.var .dcnt, p.shape.resVals⟩ : Flush)
      ∈ p.shape.readFlushes := by
    simp [Shape.readFlushes, hk]
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.bus_key hbus h hf
  have hτ := sep_inj h1
  subst hτ
  refine ⟨e, he, by simpa using h2.symm, ?_⟩
  simp only [Shape.resVals, List.map_map, Function.comp_def, Poly2.ev_var] at h3
  exact limbsOf_inj_rd _ h3

/-! ## Every row relation holds on the seed memory -/

theorem fval_k {n x : Nat} {p : Piece} {W : Witness} {k k' : FK}
    (hop : (Q.pinst p x).row.op = .lin k k') :
    Q.rowVal W n p x (.fix .k) = k ∧ Q.rowVal W n p x (.fix .k') = k' := by
  simp [rowVal, fval, fvalBasic, hop]

/-- **The tables give every instance's relation and assertion on the seed memory.** -/
theorem holds_seedMem (hwf : Q.wf = true) {W : Witness} {inK : Array FK} {inE : Array FE}
    (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) :
    Q.Holds (Q.seedMem W inK inE) ∧ Q.Asserts (Q.seedMem W inK inE) := by
  have key : ∀ i ∈ Q.insts, Q.RowDef (Q.seedMem W inK inE) i ∧
      Program.RowAssert (Q.seedMem W inK inE) i := by
    intro i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    obtain ⟨n, p, x, hpx, hpi⟩ := Q.inst_prow hb hjf ht
    rw [← hpi]
    set M := Q.seedMem W inK inE
    set v := Q.rowVal W n p x
    set i := Q.pinst p x
    have hsh : i.row.shape = p.shape := (Q.prow_inst hpx).2
    have hok := Q.instOk_of_mem hwf (Q.prow_inst hpx).1
    have hrel := constraints_sound p.shape (hsh ▸ Row.shape_typeOk hok.typeOk) v
      (fun C hC => hcons (n, p, x) hpx C hC)
    have hlen : p.shape.args.length = i.row.args.length := by
      rw [← hsh]; simp [Row.shape]
    have ha : ∀ o < i.row.args.length, p.shape.argV v o = M.arg i o :=
      fun o ho => Q.read_ok hwf hbus hinj hpx (by omega)
    have hres : p.shape.writes = true → p.shape.resV v = M.res i :=
      fun hw => (Q.seedMem_writer W inK inE hpx hw).symm
    have hkind : p.shape.kind = i.row.op.kind := by rw [← hsh]; rfl
    have hty : i.row.typeOk = true := hok.typeOk
    rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
      rw [hop] at hkind <;> simp only [Op.kind] at hkind <;>
      simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at hty
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 3 := hty.1
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 2 := hty.1
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      have hk1 : v (.fix .k) = k := (Q.fval_k (W := W) (n := n) hop).1
      have hk2 : v (.fix .k') = k' := (Q.fval_k (W := W) (n := n) hop).2
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), hk1, hk2]
    · simp only [Shape.Rel, hkind] at hrel
      have hl : i.row.args.length = 2 := hty
      refine ⟨by simp [RowDef, hop], ?_⟩
      simp only [RowAssert, hop]
      rw [← ha 0 (by omega), ← ha 1 (by omega)]
      exact hrel
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 3 := by
        have := congrArg List.length hty.1; simpa using this
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      have hF : v (.fix .F) = Q.fixMat i.j := rfl
      have hl : i.row.args.length = 2 := hty.1
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), hF]
    · have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 1 := by
        have := congrArg List.length hty; simpa using this
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      obtain ⟨e, he, hpow, hval⟩ := Q.readd_ok hbus hpx hkind
      have htyeq : p.shape.ty = i.row.ty := (Q.writer_row (npx := (n, p, x)) hpx hw).2.symm
      have h0 := ha 0 (by omega)
      have hty' : (Q.pinst p x).row.args.map (·.ty) = [Ty.K] := hty
      have hK0 : p.shape.args.getD 0 .K = .K := by
        rw [Q.shape_args hpx, hty']; rfl
      rw [argV_K hK0] at h0
      refine ⟨e, htyeq ▸ he, ?_, ?_⟩
      · rw [← h0]; exact hpow
      · rw [← hres hw, hval, htyeq]
  exact ⟨fun i hi => (key i hi).1, fun i hi => (key i hi).2⟩

/-! ## The theorem -/

theorem cells_pick (τ : Ty) : τ.pick (Q.cells .K) (Q.cells .E) = Q.cells τ := by cases τ <;> rfl

/-- **`loopir_sound`.** Tables that satisfy their constraints, with a bus that matches every read to
a seed, are the interpreter's run: every committed value is the interpreter's cell, and every gated
assertion holds. -/
theorem loopir_sound (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (W : Witness)
    (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hinb : (Q.interp inK inE).inb = true) :
    Q.WitnessOf W (Q.interpMem inK inE) ∧ (Q.interp inK inE).ok = true := by
  set M := Q.seedMem W inK inE
  obtain ⟨hH, hA⟩ := Q.holds_seedMem hwf hcons hbus hinj
  have hin : Q.Inputs M inK inE :=
    ⟨fun n hn => by simp [M, seedMem, hn], fun n hn => by simp [M, seedMem, hn]⟩
  obtain ⟨hag, hok⟩ := Q.interp_unique hwf inK inE hsz M hin hH hinj hinb
  refine ⟨fun n p x h => ⟨fun hw => ?_, fun o ho => ?_⟩, hok.mpr hA⟩
  · have hwr := Q.writer_row (npx := (n, p, x)) h hw
    have hcl := Q.writer_clock (Q.prow_inst h).1 hwr.1
    simp only at hwr hcl
    rw [← Q.seedMem_writer W inK inE h hw]
    simp only [Mem.res]
    rw [hwr.2]
    exact Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact hcl.2)
  · rw [Q.read_ok hwf hbus hinj h ho, Mem.arg]
    have hok := Q.instOk_of_mem hwf (Q.prow_inst h).1
    have hmem : (Q.pinst p x).arg o ∈ (Q.pinst p x).row.args := by
      apply arg_mem; rw [Q.shape_args h] at ho; simpa using ho
    have hlt := lt_of_lt_of_le (hok.reads _ hmem) (hok.cells _)
    exact Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact hlt)

end Program

end Lvm.Loop
