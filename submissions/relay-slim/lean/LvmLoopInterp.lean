import LvmLoopLayout
import LvmFieldCorrect

/-!
# LoopIR semantics: the rows as relations on a memory, and the interpreter as their unique solution

A *memory* gives every `K` and `E` cell a value. `RowDef M i` is instance `i`'s operation as a
relation between its result cell and its operand cells (a `readd`: the result is the cell at some
exponent `e < cells` with `g^e` = the address operand's value); `RowAssert M i` is an `assert0`'s
gated assertion. `Holds M`: every instance's relation holds.

* `interp_unique`: a memory with the inputs on which every row relation holds is the interpreter's
  on every cell, and the interpreter's `ok` is then "every assertion holds on it". Hypotheses: the
  program check, every `readd` found its cell (`inb`), and `g`-powers injective below the cell
  counts (for `readd` only: the address names one cell).
* `interp_holds`: the interpreter's memory is such a memory.

The proof follows the instances in execution order: the clocks are the array sizes
(`LvmLoopLayout.chain_insts`), every read is below its clock (`inst_ok`), so the interpreter reads
cells it has already defined, and pushes the one value the relation allows.
-/

namespace Lvm.Loop

open FE

/-- A memory: a value for every cell of each memory. -/
structure Mem where
  /-- The `K` cells. -/
  k : Nat → FK
  /-- The `E` cells. -/
  e : Nat → FE

/-- Cell `n` of memory `τ`, as an `E` value. -/
def Mem.rd (M : Mem) : Ty → Nat → FE
  | .K, n => FE.ofK (M.k n)
  | .E, n => M.e n

/-- `g`-powers are injective below `N`. -/
def GInj (N : Nat) : Prop := ∀ a b, a < N → b < N → FK.x ^ a = FK.x ^ b → a = b

/-- Operand `o` of an instance. -/
def Inst.arg (i : Inst) (o : Nat) : Addr := i.row.args.getD o default

/-- The value of operand `o` of instance `i` in `M`. -/
def Mem.arg (M : Mem) (i : Inst) (o : Nat) : FE := M.rd (i.arg o).ty ((i.arg o).at i.j)

/-- The value of the result cell of instance `i` in `M`. -/
def Mem.res (M : Mem) (i : Inst) : FE := M.rd i.row.ty (i.clock i.row.ty)

/-- Two memories agree on the first `nk` `K` cells and `ne` `E` cells. -/
def Mem.Agrees (M M' : Mem) (nk ne : Nat) : Prop :=
  (∀ n < nk, M.k n = M'.k n) ∧ (∀ n < ne, M.e n = M'.e n)

/-- The interpreter state as a memory (`0` past the defined cells). -/
def St.mem (s : St) : Mem := ⟨fun n => s.kc.getD n 0, fun n => s.ec.getD n 0⟩

namespace Program

variable (Q : Program)

/-- **The relation of an instance** on a memory. -/
def RowDef (M : Mem) (i : Inst) : Prop :=
  match i.row.op with
  | .muladd => M.res i = M.arg i 0 * M.arg i 1 + M.arg i 2
  | .lin k k' => M.res i = M.arg i 0 + FE.ofK k * M.arg i 1 + FE.ofK k'
  | .assert0 => True
  | .loadE => M.res i = M.arg i 0 + FE.y * M.arg i 1 + FE.y * FE.y * M.arg i 2
  | .fixmul => M.res i = FE.ofK (Q.fixMat i.j) * M.arg i 0 + M.arg i 1
  | .readd _ _ => ∃ e < Q.cells i.row.ty, FK.x ^ e = (M.arg i 0).c₀ ∧ M.res i = M.rd i.row.ty e

/-- **The gated assertion of an instance** on a memory: `gate · a = 0`. -/
def RowAssert (M : Mem) (i : Inst) : Prop :=
  match i.row.op with
  | .assert0 => M.arg i 1 * M.arg i 0 = 0
  | _ => True

/-- Every instance's relation holds. -/
def Holds (M : Mem) : Prop := ∀ i ∈ Q.insts, Q.RowDef M i

/-- Every instance's assertion holds. -/
def Asserts (M : Mem) : Prop := ∀ i ∈ Q.insts, Program.RowAssert M i

/-- The memory holds the inputs. -/
def Inputs (M : Mem) (inK : Array FK) (inE : Array FE) : Prop :=
  (∀ n < Q.nInK, M.k n = inK.getD n 0) ∧ (∀ n < Q.nInE, M.e n = inE.getD n 0)

/-- The interpreter's memory. -/
def interpMem (inK : Array FK) (inE : Array FE) : Mem := (Q.interp inK inE).mem

end Program

/-! ## One step -/

theorem St.rd_eq_mem (s : St) (τ : Ty) (n : Nat) : s.rd τ n = s.mem.rd τ n := by
  cases τ <;> rfl

theorem Mem.rd_agree {M M' : Mem} {nk ne : Nat} (h : M.Agrees M' nk ne) (τ : Ty) (n : Nat)
    (hn : n < (match τ with | .K => nk | .E => ne)) : M.rd τ n = M'.rd τ n := by
  cases τ
  · simp only [Mem.rd, h.1 n hn]
  · simp only [Mem.rd, h.2 n hn]

theorem Inst.clock_K (i : Inst) : i.clock .K = i.ck := rfl
theorem Inst.clock_E (i : Inst) : i.clock .E = i.ce := rfl

theorem getD_push_lt {α : Type} (a : Array α) (x d : α) {n : Nat} (h : n < a.size) :
    (a.push x).getD n d = a.getD n d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h, Nat.ne_of_lt h]

theorem getD_push_eq {α : Type} (a : Array α) (x d : α) : (a.push x).getD a.size d = x := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]

/-- `1` if the memories are the same. -/
def Ty.ind (τ σ : Ty) : Nat := if τ = σ then 1 else 0

/-- The clock of memory `τ` among the two. -/
def Ty.pick (τ : Ty) (k e : Nat) : Nat := match τ with | .K => k | .E => e

theorem Inst.clock_eq_pick (i : Inst) (τ : Ty) : i.clock τ = τ.pick i.ck i.ce := by cases τ <;> rfl

/-- Pushing the memory's own next cell keeps the agreement one cell further. -/
theorem agrees_put {M : Mem} {s : St} {k e : Nat} (hk : s.kc.size = k) (he : s.ec.size = e)
    (h : M.Agrees s.mem k e) (τ : Ty) :
    M.Agrees (s.put τ (M.rd τ (τ.pick k e))).mem (k + τ.ind .K) (e + τ.ind .E) ∧
      (s.put τ (M.rd τ (τ.pick k e))).kc.size = k + τ.ind .K ∧
      (s.put τ (M.rd τ (τ.pick k e))).ec.size = e + τ.ind .E := by
  cases τ
  · refine ⟨⟨fun n hn => ?_, fun n hn => ?_⟩, ?_, ?_⟩
    · simp only [St.put, St.mem, Ty.ind, Ty.pick, Mem.rd, if_pos rfl] at hn ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · rw [getD_push_lt _ _ _ (hk ▸ hn)]; exact h.1 n hn
      · rw [← hk, getD_push_eq]; rfl
    · simp only [St.put, St.mem, Ty.ind] at hn ⊢
      exact h.2 n (by simpa using hn)
    · simp [St.put, Ty.ind, hk]
    · simp [St.put, Ty.ind, he]
  · refine ⟨⟨fun n hn => ?_, fun n hn => ?_⟩, ?_, ?_⟩
    · simp only [St.put, St.mem, Ty.ind] at hn ⊢
      exact h.1 n (by simpa using hn)
    · simp only [St.put, St.mem, Ty.ind, Ty.pick, Mem.rd, if_pos rfl] at hn ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · rw [getD_push_lt _ _ _ (he ▸ hn)]; exact h.2 n hn
      · rw [← he, getD_push_eq]
    · simp [St.put, Ty.ind, hk]
    · simp [St.put, Ty.ind, he]

theorem Row.w_of_writes {r : Row} {τ : Ty} (h : r.writes = some τ) (σ : Ty) : r.w σ = τ.ind σ := by
  simp only [Row.w, h, Option.some.injEq, Ty.ind]

/-- The conditions the program check and the instance list give one instance. -/
structure InstOk (Q : Program) (i : Inst) : Prop where
  typeOk : i.row.typeOk = true
  reads : ∀ a ∈ i.row.args, a.at i.j < i.clock a.ty
  region : ∀ lo m, i.row.op = .readd lo m → lo + 2 ^ m ≤ i.clock i.row.ty
  cells : ∀ τ, i.clock τ ≤ Q.cells τ

namespace Program

variable (Q : Program)

@[simp] theorem St.put_inb (s : St) (τ : Ty) (v : FE) : (s.put τ v).inb = s.inb := by
  cases τ <;> rfl

@[simp] theorem St.put_ok (s : St) (τ : Ty) (v : FE) : (s.put τ v).ok = s.ok := by
  cases τ <;> rfl

theorem step_inb (s : St) (i : Inst) (h : (Q.step s i).inb = true) : s.inb = true := by
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
    simp only [step, hop, St.put_inb] at h <;> try exact h
  split at h
  · simpa using h
  · simp at h

theorem foldl_inb : ∀ (L : List Inst) (s : St), (L.foldl Q.step s).inb = true → s.inb = true
  | [], _, h => h
  | i :: L, s, h => Q.step_inb s i (foldl_inb L _ h)

theorem findExp_some {α : FK} {lo m e : Nat} (h : findExp α lo m = some e) :
    ∃ i < 2 ^ m, e = lo + i ∧ FK.x ^ (lo + i) = α := by
  simp only [findExp, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hi
  have hp := List.find?_some hi
  simp only [List.mem_range] at hmem
  exact ⟨i, hmem, rfl, by simpa using hp⟩

theorem arg_mem {i : Inst} {o : Nat} (h : o < i.row.args.length) : i.arg o ∈ i.row.args := by
  simp only [Inst.arg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- A step that defines the result cell as the memory's: the agreement moves one cell. -/
theorem step_put_spec {M : Mem} {s : St} {i : Inst} (hk : s.kc.size = i.ck) (he : s.ec.size = i.ce)
    (hag : M.Agrees s.mem i.ck i.ce) {τ : Ty} (hw : i.row.writes = some τ) (hτ : i.row.ty = τ) :
    M.Agrees (s.put i.row.ty (M.res i)).mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) ∧
      (s.put i.row.ty (M.res i)).kc.size = i.ck + i.row.w .K ∧
      (s.put i.row.ty (M.res i)).ec.size = i.ce + i.row.w .E := by
  rw [Row.w_of_writes hw, Row.w_of_writes hw, Mem.res, hτ, Inst.clock_eq_pick]
  exact agrees_put hk he hag τ

/-- **One interpreter step** on an instance whose relation holds in `M`, from a state that agrees
with `M` below the clocks: the state still agrees with `M` below the new clocks, and `ok` records the
assertion. -/
theorem step_spec (M : Mem) (s : St) (i : Inst) (hk : s.kc.size = i.ck) (he : s.ec.size = i.ce)
    (hag : M.Agrees s.mem i.ck i.ce) (hdef : Q.RowDef M i) (hok : InstOk Q i)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.step s i).inb = true) :
    M.Agrees (Q.step s i).mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) ∧
      (Q.step s i).kc.size = i.ck + i.row.w .K ∧ (Q.step s i).ec.size = i.ce + i.row.w .E ∧
      ((Q.step s i).ok = true ↔ s.ok = true ∧ Program.RowAssert M i) := by
  have hR : ∀ o < i.row.args.length,
      s.rd (i.row.args.getD o default).ty ((i.row.args.getD o default).at i.j) = M.arg i o := by
    intro o ho
    have hlt := hok.reads _ (arg_mem ho)
    simp only [Inst.arg] at hlt
    rw [Inst.clock_eq_pick] at hlt
    rw [St.rd_eq_mem, Mem.arg]
    exact (Mem.rd_agree hag _ _ (by cases h : (i.row.args.getD o default).ty <;>
      simp only [h, Ty.pick] at hlt ⊢ <;> exact hlt)).symm
  have ht := hok.typeOk
  have hput : ∀ τ, i.row.writes = some τ → i.row.ty = τ → Q.step s i = s.put i.row.ty (M.res i) →
      M.Agrees (Q.step s i).mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) ∧
      (Q.step s i).kc.size = i.ck + i.row.w .K ∧ (Q.step s i).ec.size = i.ce + i.row.w .E ∧
      ((Q.step s i).ok = true ↔ s.ok = true ∧ Program.RowAssert M i) := by
    intro τ hw hτ hst
    rw [hst]
    obtain ⟨h1, h2, h3⟩ := step_put_spec hk he hag hw hτ
    refine ⟨h1, h2, h3, ?_⟩
    have hna : i.row.op ≠ .assert0 := by
      intro h; simp [Row.writes, h] at hw
    rcases hop : i.row.op <;> simp_all [RowAssert]
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩
  · refine hput _ (by simp [Row.writes, hop]) rfl ?_
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at ht
    simp only [step, hop, hR 0 (by omega), hR 1 (by omega), hR 2 (by omega)]
    simp only [RowDef, hop] at hdef; rw [hdef]
  · refine hput _ (by simp [Row.writes, hop]) rfl ?_
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at ht
    simp only [step, hop, hR 0 (by omega), hR 1 (by omega)]
    simp only [RowDef, hop] at hdef; rw [hdef]
  · simp only [Row.typeOk, hop, beq_iff_eq, List.length_map] at ht
    have hw : ∀ σ, i.row.w σ = 0 := fun σ => by simp [Row.w, Row.writes, hop]
    simp only [step, hop, hR 0 (by omega), hR 1 (by omega), hw, Nat.add_zero]
    refine ⟨hag, hk, he, ?_⟩
    simp [RowAssert, hop]
  · refine hput _ (by simp [Row.writes, hop]) rfl ?_
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq] at ht
    have hl : i.row.args.length = 3 := by
      have := congrArg List.length ht.1; simpa using this
    simp only [step, hop, hR 0 (by omega), hR 1 (by omega), hR 2 (by omega)]
    simp only [RowDef, hop] at hdef; rw [hdef]
  · refine hput _ (by simp [Row.writes, hop]) rfl ?_
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at ht
    simp only [step, hop, hR 0 (by omega), hR 1 (by omega)]
    simp only [RowDef, hop] at hdef; rw [hdef]
  · refine hput _ (by simp [Row.writes, hop]) rfl ?_
    simp only [Row.typeOk, hop, beq_iff_eq] at ht
    have hl : i.row.args.length = 1 := by
      have := congrArg List.length ht; simpa using this
    simp only [RowDef, hop] at hdef
    obtain ⟨e, he1, he2, he3⟩ := hdef
    have hinb' := hinb
    simp only [step, hop, hR 0 (by omega)] at hinb' ⊢
    rcases hf : findExp (M.arg i 0).c₀ lo m with _ | e'
    · rw [hf] at hinb'; simp at hinb'
    · obtain ⟨i', hi', rfl, hpow⟩ := findExp_some hf
      have hreg := hok.region lo m hop
      have hcl := hok.cells i.row.ty
      have hlt : lo + i' < i.clock i.row.ty := by omega
      have hN : ∀ τ, Q.cells τ ≤ max (Q.cells .K) (Q.cells .E) := by
        intro τ; cases τ <;> simp
      have hee : e = lo + i' := hinj _ _ (lt_of_lt_of_le he1 (hN _))
        (by have := hN i.row.ty; omega) (he2.trans hpow.symm)
      simp only
      rw [he3, hee, St.rd_eq_mem, Mem.rd_agree hag _ _ (by
        rw [Inst.clock_eq_pick] at hlt; cases h : i.row.ty <;> simp only [h, Ty.pick] at hlt ⊢ <;>
          exact hlt)]

/-- The interpreter over a list of instances whose relations hold in `M`. -/
theorem fold_spec (M : Mem) (hinj : GInj (max (Q.cells .K) (Q.cells .E))) :
    ∀ (L : List Inst) (s : St) (k e : Nat), Chain k e L → s.kc.size = k → s.ec.size = e →
      M.Agrees s.mem k e → (∀ i ∈ L, Q.RowDef M i ∧ InstOk Q i) → (L.foldl Q.step s).inb = true →
      M.Agrees (L.foldl Q.step s).mem (k + instW .K L) (e + instW .E L) ∧
        ((L.foldl Q.step s).ok = true ↔ s.ok = true ∧ ∀ i ∈ L, Program.RowAssert M i)
  | [], s, k, e, _, _, _, hag, _, _ => by simpa [instW] using hag
  | i :: L, s, k, e, ⟨hck, hce, hch⟩, hk, he, hag, hL, hinb => by
    subst hck hce
    have hinb1 := Q.foldl_inb L _ hinb
    obtain ⟨h1, h2, h3, h4⟩ :=
      Q.step_spec M s i hk he hag (hL i (by simp)).1 (hL i (by simp)).2 hinj hinb1
    obtain ⟨g1, g2⟩ := fold_spec M hinj L (Q.step s i) _ _ hch h2 h3 h1
      (fun j hj => hL j (by simp [hj])) hinb
    refine ⟨by simpa [instW, Nat.add_assoc] using g1, ?_⟩
    rw [List.foldl_cons, g2, h4]
    simp [and_assoc]

/-- The program check gives every instance its conditions. -/
theorem instOk_of_mem (hwf : Q.wf = true) {i : Inst} (hi : i ∈ Q.insts) : InstOk Q i := by
  obtain ⟨hch, hK, hE⟩ := Q.chain_insts
  have hc := chain_clock_le _ _ _ hch i hi
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
  obtain ⟨h1, h2, h3⟩ := Q.inst_ok hwf hb hjf ht
  refine ⟨h1, h2, h3, fun τ => ?_⟩
  cases τ
  · show (Q.inst b jf t).ck ≤ _; omega
  · show (Q.inst b jf t).ce ≤ _; omega

/-- **The interpreter is the unique solution.** A memory with the inputs on which every row
relation holds agrees with the interpreter on every cell; the interpreter's `ok` is then "every
gated assertion holds in it". -/
theorem interp_unique (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (M : Mem) (hin : Q.Inputs M inK inE)
    (hM : Q.Holds M) (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hinb : (Q.interp inK inE).inb = true) :
    M.Agrees (Q.interpMem inK inE) (Q.cells .K) (Q.cells .E) ∧
      ((Q.interp inK inE).ok = true ↔ Q.Asserts M) := by
  obtain ⟨hch, hK, hE⟩ := Q.chain_insts
  have := Q.fold_spec M hinj Q.insts ⟨inK, inE, true, true⟩ Q.nInK Q.nInE hch hsz.1 hsz.2
    ⟨fun n hn => hin.1 n hn, fun n hn => hin.2 n hn⟩
    (fun i hi => ⟨hM i hi, Q.instOk_of_mem hwf hi⟩) hinb
  rw [hK, hE] at this
  refine ⟨this.1, ?_⟩
  rw [interp, this.2]
  simp [Asserts]

/-! ## The interpreter's memory satisfies every row -/

theorem put_size (s : St) (τ : Ty) (v : FE) :
    (s.put τ v).kc.size = s.kc.size + τ.ind .K ∧ (s.put τ v).ec.size = s.ec.size + τ.ind .E := by
  cases τ <;> simp [St.put, Ty.ind]

theorem put_mem_lt (s : St) (τ : Ty) (v : FE) :
    (∀ n < s.kc.size, (s.put τ v).kc.getD n 0 = s.kc.getD n 0) ∧
      (∀ n < s.ec.size, (s.put τ v).ec.getD n 0 = s.ec.getD n 0) := by
  cases τ
  · exact ⟨fun n hn => getD_push_lt _ _ _ hn, fun _ _ => rfl⟩
  · exact ⟨fun _ _ => rfl, fun n hn => getD_push_lt _ _ _ hn⟩

theorem Mem.rd_agree' {M M' : Mem} {nk ne : Nat} (h : M.Agrees M' nk ne) (τ : Ty) (n : Nat)
    (hn : n < τ.pick nk ne) : M.rd τ n = M'.rd τ n := Mem.rd_agree h τ n (by cases τ <;> exact hn)

theorem pick_lt_add {τ : Ty} {n k e a b : Nat} (h : n < τ.pick k e) : n < τ.pick (k + a) (e + b) := by
  cases τ <;> simp only [Ty.pick] at h ⊢ <;> omega

theorem pick_lt_ind (τ : Ty) (k e : Nat) : τ.pick k e < τ.pick (k + τ.ind .K) (e + τ.ind .E) := by
  cases τ <;> simp [Ty.pick, Ty.ind]

/-- Reading below the prefix a state kept. -/
theorem St.mem_rd_prefix {s s' : St} {k e : Nat} (hpK : ∀ n < k, s'.kc.getD n 0 = s.kc.getD n 0)
    (hpE : ∀ n < e, s'.ec.getD n 0 = s.ec.getD n 0) (τ : Ty) (n : Nat) (hn : n < τ.pick k e) :
    s'.mem.rd τ n = s.mem.rd τ n := by
  cases τ
  · simp only [Ty.pick] at hn; simp only [Mem.rd, St.mem, hpK n hn]
  · simp only [Ty.pick] at hn; simp only [Mem.rd, St.mem, hpE n hn]

/-- An `E` value that is a `K` value. -/
def IsK (v : FE) : Prop := FE.ofK v.c₀ = v

theorem isK_ofK (a : FK) : IsK (FE.ofK a) := rfl

theorem isK_add {a b : FE} (ha : IsK a) (hb : IsK b) : IsK (a + b) := by
  rw [← ha, ← hb]
  show IsK (ofKRingHom _ + ofKRingHom _)
  rw [← map_add]; exact isK_ofK _

theorem isK_mul {a b : FE} (ha : IsK a) (hb : IsK b) : IsK (a * b) := by
  rw [← ha, ← hb]
  show IsK (ofKRingHom _ * ofKRingHom _)
  rw [← map_mul]; exact isK_ofK _

theorem put_rd_top (s : St) (τ : Ty) (v : FE) (hv : τ = .K → IsK v) :
    (s.put τ v).mem.rd τ (τ.pick s.kc.size s.ec.size) = v := by
  cases τ
  · simp only [St.put, St.mem, Mem.rd, Ty.pick, getD_push_eq]; exact hv rfl
  · simp only [St.put, St.mem, Mem.rd, Ty.pick, getD_push_eq]

theorem argTy_K {r : Row} (h : (r.args.map (·.ty)).all (· == .K) = true) {o : Nat}
    (ho : o < r.args.length) : (r.args.getD o default).ty = .K := by
  simp only [List.all_eq_true, List.mem_map, beq_iff_eq] at h
  apply h
  exact ⟨_, by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho,
    Option.getD_some]; exact List.getElem_mem ho, rfl⟩

theorem rd_isK (s : St) (n : Nat) : IsK (s.rd .K n) := rfl

/-- **One step defines its result from cells below its clock.** After the step, the arrays grew by
the row's writes and kept their prefix, and every memory that agrees with the new state below the
new clocks satisfies the row's relation. -/
theorem step_holds (s : St) (i : Inst) (hk : s.kc.size = i.ck) (he : s.ec.size = i.ce)
    (hok : InstOk Q i) (hinb : (Q.step s i).inb = true) :
    (Q.step s i).kc.size = i.ck + i.row.w .K ∧ (Q.step s i).ec.size = i.ce + i.row.w .E ∧
      (∀ n < i.ck, (Q.step s i).kc.getD n 0 = s.kc.getD n 0) ∧
      (∀ n < i.ce, (Q.step s i).ec.getD n 0 = s.ec.getD n 0) ∧
      ∀ M' : Mem, M'.Agrees (Q.step s i).mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) →
        Q.RowDef M' i := by
  have ht := hok.typeOk
  -- the reads of the step are the cells of any agreeing memory
  have hread : ∀ (s' : St), (∀ n < i.ck, s'.kc.getD n 0 = s.kc.getD n 0) →
      (∀ n < i.ce, s'.ec.getD n 0 = s.ec.getD n 0) → ∀ M' : Mem,
      M'.Agrees s'.mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) → ∀ o < i.row.args.length,
      M'.arg i o = s.rd (i.row.args.getD o default).ty ((i.row.args.getD o default).at i.j) := by
    intro s' hpK hpE M' hag o ho
    have hlt := hok.reads _ (arg_mem ho)
    simp only [Inst.arg] at hlt
    rw [Inst.clock_eq_pick] at hlt
    simp only [Mem.arg, Inst.arg]
    rw [Mem.rd_agree' hag _ _ (pick_lt_add hlt), St.mem_rd_prefix hpK hpE _ _ hlt, St.rd_eq_mem]
  -- a writer: the step is a put of `v`, and every agreeing memory has `v` as its result
  have hwriter : ∀ (v : FE), Q.step s i = s.put i.row.ty v → i.row.writes = some i.row.ty →
      (i.row.ty = .K → IsK v) →
      (Q.step s i).kc.size = i.ck + i.row.w .K ∧ (Q.step s i).ec.size = i.ce + i.row.w .E ∧
      (∀ n < i.ck, (Q.step s i).kc.getD n 0 = s.kc.getD n 0) ∧
      (∀ n < i.ce, (Q.step s i).ec.getD n 0 = s.ec.getD n 0) ∧
      ∀ M' : Mem, M'.Agrees (Q.step s i).mem (i.ck + i.row.w .K) (i.ce + i.row.w .E) →
        M'.res i = v ∧ ∀ o < i.row.args.length,
          M'.arg i o = s.rd (i.row.args.getD o default).ty ((i.row.args.getD o default).at i.j) := by
    intro v hst hw hv
    rw [hst]
    obtain ⟨hs1, hs2⟩ := put_size s i.row.ty v
    obtain ⟨hp1, hp2⟩ := put_mem_lt s i.row.ty v
    rw [Row.w_of_writes hw, Row.w_of_writes hw]
    refine ⟨by rw [hs1, hk], by rw [hs2, he], fun n hn => hp1 n (hk ▸ hn),
      fun n hn => hp2 n (he ▸ hn), fun M' hag => ⟨?_, ?_⟩⟩
    · have htop := put_rd_top s i.row.ty v hv
      rw [hk, he] at htop
      rw [Mem.res, Inst.clock_eq_pick, ← htop]
      exact Mem.rd_agree' hag _ _ (pick_lt_ind _ _ _)
    · refine hread _ (fun n hn => hp1 n (hk ▸ hn)) (fun n hn => hp2 n (he ▸ hn)) M' ?_
      rw [Row.w_of_writes hw, Row.w_of_writes hw]; exact hag
  set R : Nat → FE := fun o => s.rd (i.row.args.getD o default).ty
    ((i.row.args.getD o default).at i.j) with hR
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map, Bool.or_eq_true] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwriter (R 0 * R 1 + R 2) (by simp only [step, hop, hR])
      (by simp [Row.writes, hop])
      (fun hK => by
        have hall := ht.2.resolve_left (by simp [hK])
        simp only [hR]
        rw [argTy_K hall (by omega), argTy_K hall (by omega), argTy_K hall (by omega)]
        exact isK_add (isK_mul (rd_isK _ _) (rd_isK _ _)) (rd_isK _ _))
    refine ⟨h1, h2, h3, h4, fun M' hag => ?_⟩
    obtain ⟨hr, ha⟩ := h5 M' hag
    simp only [RowDef, hop, hr, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    rfl
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map, Bool.or_eq_true] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwriter (R 0 + FE.ofK k * R 1 + FE.ofK k')
      (by simp only [step, hop, hR]) (by simp [Row.writes, hop])
      (fun hK => by
        have hall := ht.2.resolve_left (by simp [hK])
        simp only [hR]
        rw [argTy_K hall (by omega), argTy_K hall (by omega)]
        exact isK_add (isK_add (rd_isK _ _) (isK_mul (isK_ofK _) (rd_isK _ _))) (isK_ofK _))
    refine ⟨h1, h2, h3, h4, fun M' hag => ?_⟩
    obtain ⟨hr, ha⟩ := h5 M' hag
    simp only [RowDef, hop, hr, ha 0 (by omega), ha 1 (by omega)]
    rfl
  · have hw : ∀ σ, i.row.w σ = 0 := fun σ => by simp [Row.w, Row.writes, hop]
    simp only [step, hop, hw, Nat.add_zero]
    refine ⟨hk, he, fun _ _ => by first | rfl | trivial, fun _ _ => by first | rfl | trivial,
      fun M' _ => ?_⟩
    simp [RowDef, hop]
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq] at ht
    have hl : i.row.args.length = 3 := by
      have := congrArg List.length ht.1; simpa using this
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwriter (R 0 + FE.y * R 1 + FE.y * FE.y * R 2)
      (by simp only [step, hop, hR]) (by simp [Row.writes, hop])
      (fun hK => by simp [ht.2] at hK)
    refine ⟨h1, h2, h3, h4, fun M' hag => ?_⟩
    obtain ⟨hr, ha⟩ := h5 M' hag
    simp only [RowDef, hop, hr, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    rfl
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map, Bool.or_eq_true] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwriter (FE.ofK (Q.fixMat i.j) * R 0 + R 1)
      (by simp only [step, hop, hR]) (by simp [Row.writes, hop])
      (fun hK => by
        have hall := ht.2.resolve_left (by simp [hK])
        simp only [hR]
        rw [argTy_K hall (by omega), argTy_K hall (by omega)]
        exact isK_add (isK_mul (isK_ofK _) (rd_isK _ _)) (rd_isK _ _))
    refine ⟨h1, h2, h3, h4, fun M' hag => ?_⟩
    obtain ⟨hr, ha⟩ := h5 M' hag
    simp only [RowDef, hop, hr, ha 0 (by omega), ha 1 (by omega)]
    rfl
  · simp only [Row.typeOk, hop, beq_iff_eq] at ht
    have hl : i.row.args.length = 1 := by
      have := congrArg List.length ht; simpa using this
    have hinb' := hinb
    simp only [step, hop] at hinb'
    rcases hf : findExp (R 0).c₀ lo m with _ | e'
    · rw [hR] at hf; simp only at hf; rw [hf] at hinb'; simp at hinb'
    obtain ⟨i', hi', rfl, hpow⟩ := findExp_some hf
    have hreg := hok.region lo m hop
    have hlt : lo + i' < i.clock i.row.ty := by omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwriter (s.rd i.row.ty (lo + i'))
      (by rw [hR] at hf; simp only at hf; simp only [step, hop, hf]) (by simp [Row.writes, hop])
      (fun hK => by rw [hK]; exact rd_isK _ _)
    refine ⟨h1, h2, h3, h4, fun M' hag => ?_⟩
    obtain ⟨hr, ha⟩ := h5 M' hag
    simp only [RowDef, hop]
    refine ⟨lo + i', lt_of_lt_of_le hlt (hok.cells _), ?_, ?_⟩
    · rw [ha 0 (by omega), hpow]
    · rw [hr]
      rw [Inst.clock_eq_pick] at hlt
      rw [Mem.rd_agree' hag _ _ (pick_lt_add hlt), St.mem_rd_prefix h3 h4 _ _ hlt, St.rd_eq_mem]

/-- The interpreter over a list of instances: every instance's relation holds in every memory that
agrees with the final state. -/
theorem fold_holds : ∀ (L : List Inst) (s : St) (k e : Nat), Chain k e L → s.kc.size = k →
    s.ec.size = e → (∀ i ∈ L, InstOk Q i) → (L.foldl Q.step s).inb = true →
    (L.foldl Q.step s).kc.size = k + instW .K L ∧ (L.foldl Q.step s).ec.size = e + instW .E L ∧
      (∀ n < k, (L.foldl Q.step s).kc.getD n 0 = s.kc.getD n 0) ∧
      (∀ n < e, (L.foldl Q.step s).ec.getD n 0 = s.ec.getD n 0) ∧
      ∀ M' : Mem, M'.Agrees (L.foldl Q.step s).mem (k + instW .K L) (e + instW .E L) →
        ∀ i ∈ L, Q.RowDef M' i
  | [], s, k, e, _, hk, he, _, _ => by
    simp only [List.foldl_nil, instW, List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨hk, he, fun _ _ => trivial, fun _ _ => trivial, fun _ _ i hi => by simp at hi⟩
  | i :: L, s, k, e, ⟨hck, hce, hch⟩, hk, he, hL, hinb => by
    subst hck hce
    have hinb1 := Q.foldl_inb L _ hinb
    obtain ⟨s1, s2, s3, s4, s5⟩ := Q.step_holds s i hk he (hL i (by simp)) hinb1
    obtain ⟨g1, g2, g3, g4, g5⟩ := fold_holds L (Q.step s i) _ _ hch s1 s2
      (fun j hj => hL j (by simp [hj])) hinb
    simp only [List.foldl_cons, instW, List.map_cons, List.sum_cons] at g1 g2 g3 g4 g5 ⊢
    refine ⟨by rw [g1]; ring, by rw [g2]; ring, fun n hn => by rw [g3 n (by omega), s3 n hn],
      fun n hn => by rw [g4 n (by omega), s4 n hn], fun M' hag j hj => ?_⟩
    have hag' : M'.Agrees (L.foldl Q.step (Q.step s i)).mem
        (i.ck + i.row.w .K + instW .K L) (i.ce + i.row.w .E + instW .E L) := by
      simpa [instW, Nat.add_assoc] using hag
    rcases List.mem_cons.mp hj with rfl | hj
    · refine s5 M' ⟨fun n hn => ?_, fun n hn => ?_⟩
      · rw [hag'.1 n (by omega)]; exact g3 n hn
      · rw [hag'.2 n (by omega)]; exact g4 n hn
    · exact g5 M' (by simpa [instW] using hag') j hj

/-- **The interpreter's memory satisfies every row relation** and holds the inputs. -/
theorem interp_holds (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (hinb : (Q.interp inK inE).inb = true) :
    Q.Holds (Q.interpMem inK inE) ∧ Q.Inputs (Q.interpMem inK inE) inK inE := by
  obtain ⟨hch, hK, hE⟩ := Q.chain_insts
  obtain ⟨g1, g2, g3, g4, g5⟩ := Q.fold_holds Q.insts ⟨inK, inE, true, true⟩ Q.nInK Q.nInE hch
    hsz.1 hsz.2 (fun i hi => Q.instOk_of_mem hwf hi) hinb
  exact ⟨fun i hi => g5 _ ⟨fun _ _ => rfl, fun _ _ => rfl⟩ i hi,
    fun n hn => g3 n hn, fun n hn => g4 n hn⟩

end Program

end Lvm.Loop
