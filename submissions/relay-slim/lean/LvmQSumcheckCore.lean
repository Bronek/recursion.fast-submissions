import LvmQBuildLemmas
import LvmDecideBase

/-!
# QA1 core: straight-line templates on QL's loops, their values as a fixed point, combinators

QA1's templates are written as instruction lists (`Ins`, operands `Src`: `loc k` this iteration's
row `k`, `prev k` the previous iteration's, `ext a` an affine address) and handed to QL's builder
as loop templates (`Ins.toLRow`, `Src.toOpd`: `loc ↦ cur`, `prev ↦ prev`, `ext ↦ abs`;
`LvmQBuild`). Their meaning is proved once, independently of the builder:

* **`Fix xv ins V`**: `V` lists one iteration's values; every writing row's value is its operation
  on `V` itself (`Ins.eval`), `xv` giving the `prev`/`ext` operands. **`fix_of_loop`**: in every
  memory where QL's `loop` holds (`loop_rel`), iteration `jf`'s cells form such a `V`.
* **Combinators** (`sumIns`, `hornerIns`, `loadI`) and their values on any fixed point (`sum_val`,
  `horner_val`, `polyEval_horner`): a gadget's correctness is then algebra on `V`.
* **Stream scalars**: the stream's lane `p` is input `K` cell `p` (WP-10); `loadE` of the lanes
  `q, q+1, q+2` is `feAt Σ (8q)`, the scalar `F` reads at byte `8q` (`load_feAt`).

New code (FR's verifier IR compiles SSA ops to R1CS rows, a different target).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Straight-line templates -/

/-- An operand of a template instruction. -/
inductive Src where
  /-- Instruction `k`'s result, this loop iteration. -/
  | loc (k : Nat)
  /-- Instruction `k`'s result, the previous iteration along dimension `0`. -/
  | prev (k : Nat)
  /-- Any other cell. -/
  | ext (a : Addr)
  deriving DecidableEq, Repr

instance : Inhabited Src := ⟨.ext default⟩

/-- A template instruction: an operation, its result memory, its operands. -/
structure Ins where
  /-- The operation. -/
  op : Op
  /-- The result memory. -/
  ty : Ty
  /-- The operands. -/
  args : List Src
  deriving DecidableEq, Repr

instance : Inhabited Ins := ⟨⟨.assert0, .K, []⟩⟩

/-- The value of an operand: `vs` holds this iteration's earlier results, `xv` the others. -/
def Src.val (xv : Src → FE) (vs : List FE) : Src → FE
  | .loc k => vs.getD k 0
  | s => xv s

/-- The value of an instruction (`0` for an assertion). -/
def Ins.eval (xv : Src → FE) (vs : List FE) (i : Ins) : FE :=
  let a (o : Nat) : FE := Src.val xv vs (i.args.getD o default)
  match i.op with
  | .muladd => a 0 * a 1 + a 2
  | .lin k k' => a 0 + FE.ofK k * a 1 + FE.ofK k'
  | .loadE => a 0 + FE.y * a 1 + FE.y * FE.y * a 2
  | _ => 0

/-- An instruction only reads results of earlier instructions that write. -/
def Ins.locOk (ins : List Ins) (k : Nat) (i : Ins) : Bool :=
  (match i.op with
    | .muladd | .lin .. | .loadE | .assert0 => true
    | _ => false) &&
  i.args.all fun s => match s with
    | .loc k' => decide (k' < k) && (ins.getD k' default).op != .assert0
    | .prev k' => decide (k' < ins.length) && (ins.getD k' default).op != .assert0
    | .ext _ => true

theorem locOk_op {ins : List Ins} {k : Nat} {i : Ins} (h : i.locOk ins k = true) :
    i.op = .muladd ∨ (∃ a b, i.op = .lin a b) ∨ i.op = .loadE ∨ i.op = .assert0 := by
  unfold Ins.locOk at h
  split at h <;> simp_all

/-- The template check. -/
def SLok (ins : List Ins) : Bool :=
  (List.range ins.length).all fun k => (ins.getD k default).locOk ins k

/-! ## Stream scalars -/

theorem FE_mk_eq (a b c : FK) :
    (⟨a, b, c⟩ : FE) = FE.ofK a + FE.y * FE.ofK b + FE.y * FE.y * FE.ofK c := by
  apply Lvm.FE.toExt3_injective
  simp only [Lvm.FE.toExt3_add, Lvm.FE.toExt3_mul, Lvm.FE.toExt3_ofK]
  rw [Lvm.FE.toExt3_eq ⟨a, b, c⟩, Lvm.FE.toExt3_eq FE.y]
  simp [FE.y]
  ring

/-- The stream's lanes are the input `K` cells: `M.k p` is the lane at byte `8p`, for `p < T`. -/
def Streamed (M : Mem) (sig : ByteArray) (T : Nat) : Prop := ∀ p < T, M.k p = kAt sig (8 * p)

/-- **`loadE` of three stream lanes is `F`'s scalar at that byte.** -/
theorem load_feAt {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {q : Nat}
    (hq : q + 2 < T) :
    FE.ofK (M.k q) + FE.y * FE.ofK (M.k (q + 1)) + FE.y * FE.y * FE.ofK (M.k (q + 2)) =
      feAt sig (8 * q) := by
  rw [hS q (by omega), hS (q + 1) (by omega), hS (q + 2) (by omega), feAt, FE_mk_eq]
  simp only [Nat.mul_add, Nat.mul_one]

/-! ## The template's values as a fixed point (for combinator lemmas) -/

/-- `V` is a fixed point of the template: every writing instruction's value is its evaluation on
`V` itself. `evalAll` is one (`fix_evalAll`); combinator lemmas are stated for any fixed point. -/
def Fix (xv : Src → FE) (ins : List Ins) (V : List FE) : Prop :=
  ∀ k < ins.length, (ins.getD k default).op ≠ .assert0 → V.getD k 0 = (ins.getD k default).eval xv V

theorem eval_congr (xv : Src → FE) {vs ws : List FE} (i : Ins)
    (h : ∀ k', Src.loc k' ∈ i.args → vs.getD k' 0 = ws.getD k' 0) : i.eval xv vs = i.eval xv ws := by
  have ha : ∀ o, Src.val xv vs (i.args.getD o default) = Src.val xv ws (i.args.getD o default) := by
    intro o
    by_cases ho : o < i.args.length
    · have hm : i.args.getD o default ∈ i.args := by
        rw [List.getD_eq_getElem _ _ ho]; exact List.getElem_mem ho
      revert hm
      cases i.args.getD o default with
      | loc k' => intro hm; exact h k' hm
      | prev k' => intro _; rfl
      | ext a => intro _; rfl
    · rw [List.getD_eq_default _ _ (by omega)]; rfl
  unfold Ins.eval
  simp only [ha]

/-- `seg` sits at position `n` of `ins`. -/
def Seg (ins : List Ins) (n : Nat) (seg : List Ins) : Prop :=
  ∀ i < seg.length, ins.getD (n + i) default = seg.getD i default

theorem seg_append (A seg B : List Ins) : Seg (A ++ seg ++ B) A.length seg := by
  intro i hi
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show A.length + i - A.length = i by omega, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD]

theorem seg_sub {ins : List Ins} {n : Nat} {seg : List Ins} (h : Seg ins n seg) (A B : List Ins)
    (hs : seg = A ++ B) : Seg ins (n + A.length) B := by
  intro i hi
  have := h (A.length + i) (by rw [hs]; simp; omega)
  rw [← Nat.add_assoc] at this
  rw [this, hs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show A.length + i - A.length = i by omega, ← List.getD_eq_getElem?_getD]

theorem seg_len {ins : List Ins} {n : Nat} {seg : List Ins} (h : Seg ins n seg) (hlen : n + seg.length ≤ ins.length)
    {i : Nat} (hi : i < seg.length) : n + i < ins.length := by omega

/-- The value of instruction `n`, if it is `i`, in a fixed point. -/
theorem fix_at {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat}
    (hn : n < ins.length) {i : Ins} (hi : ins.getD n default = i) (hw : i.op ≠ .assert0) :
    V.getD n 0 = i.eval xv V := by
  rw [hF n hn (by rw [hi]; exact hw), hi]

/-! ## Template combinators -/

/-- A `muladd` instruction `a·b + d` into `E`. -/
def mulI (a b d : Src) : Ins := ⟨.muladd, .E, [a, b, d]⟩

/-- A `lin` instruction `a + k·b + k'` into `E`. -/
def linI (k k' : FK) (a b : Src) : Ins := ⟨.lin k k', .E, [a, b]⟩

/-- `a + b`. -/
def addI (a b : Src) : Ins := linI 1 0 a b

/-- `loadE` of three `K` cells `q, q + 1, q + 2` moving by `str` per loop step (one loop dimension). -/
def loadI (q : Nat) (str : List Nat) : Ins :=
  ⟨.loadE, .E, [.ext ⟨.K, q, str⟩, .ext ⟨.K, q + 1, str⟩, .ext ⟨.K, q + 2, str⟩]⟩

theorem eval_mulI (xv : Src → FE) (V : List FE) (a b d : Src) :
    (mulI a b d).eval xv V = a.val xv V * b.val xv V + d.val xv V := rfl

theorem eval_addI (xv : Src → FE) (V : List FE) (a b : Src) :
    (addI a b).eval xv V = a.val xv V + b.val xv V := by
  show a.val xv V + FE.ofK 1 * b.val xv V + FE.ofK 0 = _
  rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]

theorem eval_linI (xv : Src → FE) (V : List FE) (k k' : FK) (a b : Src) :
    (linI k k' a b).eval xv V = a.val xv V + FE.ofK k * b.val xv V + FE.ofK k' := rfl

/-- The chain `s₀ + c₀ + c₁ + …`, one `lin` per term, from position `n`. -/
def sumIns (n : Nat) (s₀ : Src) : List Src → List Ins
  | [] => []
  | c :: cs => addI s₀ c :: sumIns (n + 1) (.loc n) cs

/-- Where the chain's value is. -/
def sumSrc (n : Nat) (s₀ : Src) (cs : List Src) : Src := if cs = [] then s₀ else .loc (n + cs.length - 1)

theorem sumIns_length (n : Nat) (s₀ : Src) (cs : List Src) : (sumIns n s₀ cs).length = cs.length := by
  induction cs generalizing n s₀ with
  | nil => rfl
  | cons c cs ih => simp [sumIns, ih]

/-- **The chain's value.** -/
theorem sum_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) :
    ∀ (cs : List Src) (n : Nat) (s₀ : Src), Seg ins n (sumIns n s₀ cs) →
      n + cs.length ≤ ins.length →
      (sumSrc n s₀ cs).val xv V = s₀.val xv V + (cs.map (Src.val xv V)).sum
  | [], n, s₀, _, _ => by simp [sumSrc]
  | c :: cs, n, s₀, hseg, hlen => by
    have h0 : V.getD n 0 = s₀.val xv V + c.val xv V := by
      rw [fix_at hF (by rw [List.length_cons] at hlen; omega) (by simpa [sumIns] using hseg 0 (by simp [sumIns]))
        (by simp [addI, linI]), eval_addI]
    have hseg' : Seg ins (n + 1) (sumIns (n + 1) (.loc n) cs) :=
      seg_sub hseg [addI s₀ c] _ (by simp [sumIns])
    have ih := sum_val hF cs (n + 1) (.loc n) hseg' (by rw [List.length_cons] at hlen; omega)
    have hs : sumSrc n s₀ (c :: cs) = sumSrc (n + 1) (.loc n) cs := by
      cases cs with
      | nil => simp [sumSrc]
      | cons _ _ => simp [sumSrc]; omega
    rw [hs, ih]
    show V.getD n 0 + _ = _
    rw [h0, List.map_cons, List.sum_cons, add_assoc]

theorem foldl_add (a : FE) (l : List FE) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

/-- Horner from the top coefficient `h`, then `cs` downwards: `((h·x + c₀)·x + c₁)·x + …`. -/
def hornerIns (x : Src) : Nat → Src → List Src → List Ins
  | _, _, [] => []
  | n, h, c :: cs => mulI h x c :: hornerIns x (n + 1) (.loc n) cs

theorem hornerIns_length (x : Src) (n : Nat) (h : Src) (cs : List Src) :
    (hornerIns x n h cs).length = cs.length := by
  induction cs generalizing n h with
  | nil => rfl
  | cons c cs ih => simp [hornerIns, ih]

/-- The value Horner computes. -/
def hornerVal (x h : FE) (cs : List FE) : FE := cs.foldl (fun acc c => acc * x + c) h

/-- **Horner's value**, at the last instruction (`sumSrc` names it). -/
theorem horner_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) (x : Src) :
    ∀ (cs : List Src) (n : Nat) (h : Src), Seg ins n (hornerIns x n h cs) →
      n + cs.length ≤ ins.length →
      (sumSrc n h cs).val xv V = hornerVal (x.val xv V) (h.val xv V) (cs.map (Src.val xv V))
  | [], n, h, _, _ => by simp [sumSrc, hornerVal]
  | c :: cs, n, h, hseg, hlen => by
    have h0 : V.getD n 0 = h.val xv V * x.val xv V + c.val xv V := by
      rw [fix_at hF (by rw [List.length_cons] at hlen; omega) (by simpa [hornerIns] using hseg 0 (by simp [hornerIns]))
        (by simp [mulI]), eval_mulI]
    have hseg' : Seg ins (n + 1) (hornerIns x (n + 1) (.loc n) cs) :=
      seg_sub hseg [mulI h x c] _ (by simp [hornerIns])
    have ih := horner_val hF x cs (n + 1) (.loc n) hseg' (by rw [List.length_cons] at hlen; omega)
    have hs : sumSrc n h (c :: cs) = sumSrc (n + 1) (.loc n) cs := by
      cases cs with
      | nil => simp [sumSrc]
      | cons _ _ => simp [sumSrc]; omega
    rw [hs, ih]
    show hornerVal _ (V.getD n 0) _ = _
    rw [h0]
    rfl

/-- `polyEval` (constant first) is Horner from the top coefficient. -/
theorem polyEval_horner (x : FE) (l : List FE) (top : FE) :
    polyEval (l ++ [top]) x = hornerVal x top l.reverse := by
  unfold polyEval hornerVal
  rw [List.foldr_append, List.foldl_reverse]
  simp

/-! ## Templates as QL loops -/

/-- An operand as a QL template operand. -/
def Src.toOpd : Src → Opd
  | .loc k => .cur k
  | .prev k => .prev k
  | .ext a => .abs a

/-- An instruction as a QL template row. -/
def Ins.toLRow (i : Ins) : LRow := ⟨i.op, i.ty, i.args.map Src.toOpd⟩

/-- A template as a QL loop template. -/
def tplOf (ins : List Ins) : List LRow := ins.map Ins.toLRow

/-- Iteration `jf`'s values of the loop's first `n` rows. -/
def iterV (M : Mem) (o : LoopOut) (n jf : Nat) : List FE := (List.range n).map fun t => (o.cell t jf).val M

/-- Iteration `jf`'s `prev`/`ext` operand values. -/
def iterXv (M : Mem) (o : LoopOut) (jf : Nat) (s : Src) : FE := s.toOpd.val M o jf

theorem tplOf_getD (ins : List Ins) {t : Nat} (ht : t < ins.length) :
    (tplOf ins).getD t default = (ins.getD t default).toLRow := by
  simp [tplOf, List.getD_eq_getElem _ _ ht, ht]

theorem iterV_getD (M : Mem) (o : LoopOut) {n t jf : Nat} (ht : t < n) :
    (iterV M o n jf).getD t 0 = (o.cell t jf).val M := by
  simp [iterV, List.getD_eq_getElem?_getD, ht]

/-- An operand's value in the loop is its template value. -/
theorem opd_val {M : Mem} {o : LoopOut} {jf : Nat} (hjf : jf < 2 ^ o.dims.sum) {n : Nat} (s : Src)
    (hs : match s with | .loc k' => k' < n | _ => True) :
    s.toOpd.val M o jf = s.val (iterXv M o jf) (iterV M o n jf) := by
  cases s with
  | loc k' => rw [Src.toOpd, Opd.val_cur M o hjf, Src.val, iterV_getD M o hs]
  | prev k' => rfl
  | ext a => rfl

theorem arg_of_loop {M : Mem} {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {jf : Nat}
    (hjf : jf < 2 ^ o.dims.sum) {t : Nat} (ht : t < ins.length)
    (hok : (ins.getD t default).locOk ins t = true) (k : Nat) :
    o.arg M jf t k = ((ins.getD t default).args.getD k default).val (iterXv M o jf)
      (iterV M o ins.length jf) := by
  simp only [LoopOut.arg, ho, tplOf_getD ins ht, Ins.toLRow]
  rw [getD_map_default Src.toOpd rfl]
  apply opd_val hjf
  simp only [Ins.locOk, Bool.and_eq_true, List.all_eq_true] at hok
  by_cases hk : k < (ins.getD t default).args.length
  · have hm := hok.2 ((ins.getD t default).args.getD k default)
      (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
    split
    · rename_i k' heq
      rw [heq] at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      omega
    · trivial
  · rw [List.getD_eq_default _ _ (by omega)]; trivial

/-- **A loop of a template computes it**: iteration `jf`'s cells are a fixed point. -/
theorem fix_of_loop {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (hok : SLok ins = true) (h : SegsHold c M p (loop dims (tplOf ins) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) :
    Fix (iterXv M (loop dims (tplOf ins) p).1 jf) ins (iterV M (loop dims (tplOf ins) p).1 ins.length jf) := by
  intro t ht hw
  have hok' : (ins.getD t default).locOk ins t = true := by
    simp only [SLok, List.all_eq_true, List.mem_range] at hok; exact hok t ht
  have hrel := loop_rel h hjf (t := t) (by simpa [tplOf] using ht)
  have harg := arg_of_loop (M := M) (o := (loop dims (tplOf ins) p).1) rfl hjf ht hok'
  rw [iterV_getD M _ ht]
  unfold LRel at hrel
  simp only [harg] at hrel
  have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = (ins.getD t default).op := by
    show ((tplOf ins).getD t default).op = _
    rw [tplOf_getD ins ht]; rfl
  rw [hop] at hrel
  unfold Ins.eval
  rcases locOk_op hok' with h1 | ⟨a, b, h1⟩ | h1 | h1 <;> simp only [h1] at hrel hw ⊢
  · exact hrel
  · exact hrel
  · exact hrel
  · exact absurd rfl hw

/-- **A loop's assertion** at iteration `jf` is `gate · a = 0` on the template values. -/
theorem assert_of_loop {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (hok : SLok ins = true) (h : SegsAssert M p (loop dims (tplOf ins) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) {t : Nat} (ht : t < ins.length) (ha : (ins.getD t default).op = .assert0) :
    ((ins.getD t default).args.getD 1 default).val (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterV M (loop dims (tplOf ins) p).1 ins.length jf) *
      ((ins.getD t default).args.getD 0 default).val (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterV M (loop dims (tplOf ins) p).1 ins.length jf) = 0 := by
  have hok' : (ins.getD t default).locOk ins t = true := by
    simp only [SLok, List.all_eq_true, List.mem_range] at hok; exact hok t ht
  have hA := loop_assert h hjf (t := t) (by simpa [tplOf] using ht)
  have harg := arg_of_loop (M := M) (o := (loop dims (tplOf ins) p).1) rfl hjf ht hok'
  unfold LAssert at hA
  have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = .assert0 := by
    show ((tplOf ins).getD t default).op = _
    rw [tplOf_getD ins ht]; exact ha
  rw [hop] at hA
  simp only [harg] at hA
  exact hA

/-- `loopP`'s loop is QL's `loop` at the pointer after the prologue. -/
theorem loopP_fst (dims : List Nat) (tpl : List LRow) (init : Nat → Cell) (p : Ptr) :
    (loopP dims tpl init p).1 = (loop dims tpl (p.adv (prologueSegs init 0 tpl))).1 := rfl

theorem hold_loop_of_loopP {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {init : Nat → Cell}
    {p : Ptr} (h : SegsHold c M p (loopP dims tpl init p).2) :
    SegsHold c M (p.adv (prologueSegs init 0 tpl)) (loop dims tpl (p.adv (prologueSegs init 0 tpl))).2 := by
  rw [loopP_apply, segsHold_append] at h
  simpa [loop_apply] using h.2

theorem assert_loop_of_loopP {M : Mem} {dims : List Nat} {tpl : List LRow} {init : Nat → Cell}
    {p : Ptr} (h : SegsAssert M p (loopP dims tpl init p).2) :
    SegsAssert M (p.adv (prologueSegs init 0 tpl)) (loop dims tpl (p.adv (prologueSegs init 0 tpl))).2 := by
  rw [loopP_apply, segsAssert_append] at h
  simpa [loop_apply] using h.2

/-- `fix_of_loop` for a loop with a prologue. -/
theorem fix_of_loopP {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {init : Nat → Cell} {p : Ptr}
    (hok : SLok ins = true) (h : SegsHold c M p (loopP dims (tplOf ins) init p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) :
    Fix (iterXv M (loopP dims (tplOf ins) init p).1 jf) ins
      (iterV M (loopP dims (tplOf ins) init p).1 ins.length jf) := by
  rw [loopP_fst]
  exact fix_of_loop hok (hold_loop_of_loopP h) hjf

/-- An `ext` operand of a one-dimensional loop at iteration `jf < 2^D`. -/
theorem iterXv_ext1 (M : Mem) (o : LoopOut) {D : Nat} (ho : o.dims = [D]) {jf : Nat} (hjf : jf < 2 ^ D)
    (τ : Ty) (b s : Nat) : iterXv M o jf (.ext ⟨τ, b, [s]⟩) = M.rd τ (b + s * jf) := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, ho, unflat, Nat.mod_eq_of_lt hjf, Addr.at, dot]
  rfl

end Lvm.Q1
