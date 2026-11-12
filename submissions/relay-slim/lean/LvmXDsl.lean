-- Ported verbatim from `flock-recursive` `FRXDsl.lean` (rf-k kk/base 8bff272b) for lvm (WP-3); namespace
-- `Lvm.X`. The field constant `cRed = 0x1B` is also lvm's `K` modulus tail (`LvmXField`).
import RecursionFast.Library.Machine
import RecursionFast.Library.Words

/-!
# `XIR`: a counted-loop language compiled to the contract's machine

The extractor is a program of the contract's step-counting machine (`Contract/Machine.lean`:
`XStmt`, `XProg`, `XProg.run`). Writing it, and proving what it computes and how many steps it
takes, directly on `XStmt` would mean unfolding the interpreter on the whole program. `XIR` is a
small structured language whose every construct compiles to a fixed `XStmt` pattern
(`compile`), with

* `semXIR I P s`: what the compiled code does to the memory and the output, as a function
  (exact, not an approximation: `compile_correct`);
* `steps I P s`: how many machine steps it takes, exactly;
* `cost P t`: a syntactic bound on `steps`, affine in the tape length `t` (`steps_le_cost`);
* `outs P t`: a syntactic bound on the output words (`outs_le`);
* `sizeIR P`: the compiled statement count (`size_compile`), for `progCap`.

Each is defined by structural recursion on `XIR`, so a lemma about a named routine
(`cost (mulF d a b) t = 57`) composes with the others by `simp` without unfolding the routine.

## Memory layout

Cells `0 … regs − 1` are **registers**; a `store` to an address below `regs` is dropped (the
compiled store tests the address first), so a register changes only through a statement that
names it. Cells `0 … 3` hold constants that the compiled code reads (`Inv`): `cOne = 1`,
`cBase = regs` (the store guard), `cRed = 0x1B` and `c63 = 63` (the field routines of
`LvmXField`). The prologue `initPs` writes them, and a well-formed program (`WF`) never names them
as a destination, so they hold throughout (`inv_sem`). Cell `cTmp = 4` is the compiler's scratch
(the store guard's flag and the loop clamp's flag). Cells `5 … 63` are the field routines'
scratch; user registers are `64 … regs − 1`; the heap starts at `regs`.

## Loops (BP-E-M5, BP-E-R2-m1)

A loop runs a number of iterations fixed when it is entered, counted down in a register `c` that
its body must not write (`WF`):

* `loopK c n K body` runs `min(M[n], K)` times for a constant `K`: the clamp is compiled in, so
  its cost `K · (cost body + 3) + 8` holds on **every** tape;
* `loopT c n cap body` runs `M[n]` times; its cost `cap t · (cost body + 3) + 3` holds when the
  count is at most `cap t` on entry. The machine cannot read the tape length `t`, so this clamp
  cannot be compiled in (BP-E-R2-m1); instead `BoundsOk I t P s` collects the condition at every
  `loopT` the run enters, and `steps_le_cost` assumes it. The extractor discharges it from the
  shape of the tape (`cap_ok`, a later stage), e.g. a log of `|L|` entries has `|L| ≤ t / 5`.

## Main statements

* `compile_correct`: `Runs I (compile P) s.M s.o (steps I P s) (semXIR I P s).M (semXIR I P s).o`
  for every well-formed `P` from a state satisfying `Inv`;
* `steps_le_cost`, `outs_le`; `compile_runs` (the blueprint's `∃ n ≤ cost` form);
* `run_toProg`: the program `toProg mem mpw P` (the prologue, then `P`) **halts within**
  `mem + mpw · t + cost P t + 8` steps on a tape of `t` words whenever `BoundsOk` holds, with the
  output of `semXIR`;
* `size_compile`; `inv_sem`, `frame`: the constants and every cell the program does not write
  are unchanged.
-/

namespace Lvm.X

open RecursionFast RecursionFast.XStmt

/-! ## Cells -/

/-- The memory. -/
abbrev Mem := Array Word

/-- Cell `i` of the memory, `0` outside it (the machine's read). -/
def rd (M : Mem) (i : ℕ) : Word := M.getD i 0

/-- The number of registers: cells below it are never written by a `store`. -/
def regs : ℕ := 256

/-- The constant `1`. -/
def cOne : ℕ := 0
/-- The constant `regs`. -/
def cBase : ℕ := 1
/-- The constant `0x1B` (the `GF(2^64)` modulus below `x^64`). -/
def cRed : ℕ := 2
/-- The constant `63`. -/
def c63 : ℕ := 3
/-- The compiler's scratch cell. -/
def cTmp : ℕ := 4

/-- The value of constant cell `i < 4`. -/
def kval : ℕ → Word
  | 0 => 1
  | 1 => 256
  | 2 => 0x1B
  | _ => 63

/-- **The invariant**: the registers exist and the constant cells hold their values. -/
def Inv (M : Mem) : Prop := regs ≤ M.size ∧ ∀ i < 4, rd M i = kval i

/-! ## Straight-line blocks -/

/-- A register statement: an operation or a constant. -/
inductive Prim where
  /-- `M[d] := M[a] ∘ M[b]`. -/
  | op (o : XOp) (d a b : ℕ)
  /-- `M[d] := w`. -/
  | const (d : ℕ) (w : Word)

namespace Prim

/-- The cell a statement writes. -/
def dst : Prim → ℕ
  | op _ d _ _ => d
  | const d _ => d

/-- The machine statement. -/
def stmt : Prim → XStmt
  | op o d a b => .op o d a b
  | const d w => .const d w

/-- What the statement does to the memory (the machine's `op`/`const`). -/
def run (M : Mem) : Prim → Mem
  | op o d a b => M.setIfInBounds d (o.eval (rd M a) (rd M b))
  | const d w => M.setIfInBounds d w

end Prim

/-- A block run in order. -/
def runPrims (ps : List Prim) (M : Mem) : Mem := ps.foldl Prim.run M

/-- The statement that does nothing in one step (`M[0] := M[0] ||| M[0]`). -/
def nop : XStmt := .op .or cOne cOne cOne

/-- A block as right-nested `seq`s; the empty block is `nop`. -/
def stmts : List Prim → XStmt
  | [] => nop
  | [p] => p.stmt
  | p :: q :: ps => .seq p.stmt (stmts (q :: ps))

/-- The steps of a block of `n` statements: `n` statements and `n − 1` `seq` nodes. -/
def blkSteps (n : ℕ) : ℕ := if n = 0 then 1 else 2 * n - 1

/-! ## The language -/

/-- An affine function `a + ⌊b · t / d⌋` of the tape length (S-H2: the divisor `d` lets a count
of log entries, at most `t / 5`, be charged at `t / 5` and not at `t`). -/
structure Aff where
  /-- The constant term. -/
  a : ℕ
  /-- The coefficient of `t`. -/
  b : ℕ
  /-- The divisor of `b · t`. -/
  d : ℕ

/-- The value at tape length `t`. -/
def Aff.eval (c : Aff) (t : ℕ) : ℕ := c.a + c.b * t / c.d

/-- **The counted-loop language.** -/
inductive XIR where
  /-- A straight-line block of register statements. -/
  | blk (ps : List Prim)
  /-- `M[d] := M[M[a]]`. -/
  | load (d a : ℕ)
  /-- `M[M[a]] := M[s]` if `M[a] ≥ regs`; nothing otherwise. -/
  | store (a s : ℕ)
  /-- `M[d] :=` tape word `M[a]`. -/
  | input (d a : ℕ)
  /-- Output `M[s]`. -/
  | out (s : ℕ)
  /-- `p`, then `q`. -/
  | seq (p q : XIR)
  /-- `p` if `M[c] ≠ 0`, else `q`. -/
  | ite (c : ℕ) (p q : XIR)
  /-- `body`, `min(M[n], K)` times, counted down in `c`. -/
  | loopK (c n : ℕ) (K : Word) (body : XIR)
  /-- `body`, `M[n]` times, counted down in `c`; `cap` bounds the count for `cost`. -/
  | loopT (c n : ℕ) (cap : Aff) (body : XIR)

/-- The decrement of a loop counter. -/
def decStmt (c : ℕ) : XStmt := .op .sub c c cOne

/-- **The compiler.** -/
def compile : XIR → XStmt
  | .blk ps => stmts ps
  | .load d a => .load d a
  | .store a s => .seq (.op .ltu cTmp a cBase) (.ite cTmp nop (.store a s))
  | .input d a => .input d a
  | .out s => .out s
  | .seq p q => .seq (compile p) (compile q)
  | .ite c p q => .ite c (compile p) (compile q)
  | .loopK c n K b => .seq (.const c K) (.seq (.op .ltu cTmp n c)
      (.seq (.ite cTmp (.op .or c n n) nop) (.loop c (.seq (compile b) (decStmt c)))))
  | .loopT c n _ b => .seq (.op .or c n n) (.loop c (.seq (compile b) (decStmt c)))

/-! ## Semantics and steps -/

/-- The machine's state besides the tape: memory and output. -/
structure St where
  /-- The memory. -/
  M : Mem
  /-- The output so far. -/
  o : Array Word

/-- The guarded store. -/
def storeM (M : Mem) (a v : ℕ) : Mem :=
  let M₁ := M.setIfInBounds cTmp (XOp.ltu.eval (rd M a) (rd M cBase))
  if rd M₁ cTmp = 0 then M₁.setIfInBounds (rd M₁ a).toNat (rd M₁ v) else M₁

/-- The entry of `loopK`: the counter `min(M[n], K)`. -/
def entryK (c n : ℕ) (K : Word) (M : Mem) : Mem :=
  let M₁ := M.setIfInBounds c K
  let M₂ := M₁.setIfInBounds cTmp (XOp.ltu.eval (rd M₁ n) (rd M₁ c))
  if rd M₂ cTmp = 0 then M₂ else M₂.setIfInBounds c (XOp.or.eval (rd M₂ n) (rd M₂ n))

/-- The entry of `loopT`: the counter `M[n]`. -/
def entryT (c n : ℕ) (M : Mem) : Mem := M.setIfInBounds c (XOp.or.eval (rd M n) (rd M n))

/-- The decrement of the counter. -/
def decS (c : ℕ) (s : St) : St := ⟨s.M.setIfInBounds c (XOp.sub.eval (rd s.M c) (rd s.M cOne)), s.o⟩

/-- `k` iterations of a loop body `f` with counter `c`. -/
def iterL (f : St → St) (c : ℕ) : ℕ → St → St
  | 0, s => s
  | k + 1, s => iterL f c k (decS c (f s))

/-- The steps of `k` iterations: the test, the `seq`, the body and the decrement each time, and
the final test. -/
def stepsL (f : St → St) (g : St → ℕ) (c : ℕ) : ℕ → St → ℕ
  | 0, _ => 1
  | k + 1, s => g s + 3 + stepsL f g c k (decS c (f s))

/-- **The semantics of `XIR`** on the tape `I`: the machine's effect, statement for statement. -/
def semXIR (I : Array Word) : XIR → St → St
  | .blk ps, s => ⟨runPrims ps s.M, s.o⟩
  | .load d a, s => ⟨s.M.setIfInBounds d (rd s.M (rd s.M a).toNat), s.o⟩
  | .store a v, s => ⟨storeM s.M a v, s.o⟩
  | .input d a, s => ⟨s.M.setIfInBounds d (I.getD (rd s.M a).toNat 0), s.o⟩
  | .out v, s => ⟨s.M, s.o.push (rd s.M v)⟩
  | .seq p q, s => semXIR I q (semXIR I p s)
  | .ite c p q, s => if rd s.M c = 0 then semXIR I q s else semXIR I p s
  | .loopK c n K b, s =>
    iterL (semXIR I b) c (rd (entryK c n K s.M) c).toNat ⟨entryK c n K s.M, s.o⟩
  | .loopT c n _ b, s => iterL (semXIR I b) c (rd (entryT c n s.M) c).toNat ⟨entryT c n s.M, s.o⟩

/-- **The exact step count** of the compiled code. -/
def steps (I : Array Word) : XIR → St → ℕ
  | .blk ps, _ => blkSteps ps.length
  | .load .., _ => 1
  | .store .., _ => 4
  | .input .., _ => 1
  | .out _, _ => 1
  | .seq p q, s => steps I p s + steps I q (semXIR I p s) + 1
  | .ite c p q, s => (if rd s.M c = 0 then steps I q s else steps I p s) + 1
  | .loopK c n K b, s =>
    7 + stepsL (semXIR I b) (steps I b) c (rd (entryK c n K s.M) c).toNat ⟨entryK c n K s.M, s.o⟩
  | .loopT c n _ b, s =>
    2 + stepsL (semXIR I b) (steps I b) c (rd (entryT c n s.M) c).toNat ⟨entryT c n s.M, s.o⟩

/-! ## Well-formedness, caps, cost -/

/-- `P` names cell `i` as a destination (directly, as a loop counter, or as the compiler's
scratch). -/
def Writes : XIR → ℕ → Prop
  | .blk ps, i => ∃ p ∈ ps, p.dst = i
  | .load d _, i => i = d
  | .store _ _, i => i = cTmp
  | .input d _, i => i = d
  | .out _, _ => False
  | .seq p q, i => Writes p i ∨ Writes q i
  | .ite _ p q, i => Writes p i ∨ Writes q i
  | .loopK c _ _ b, i => i = c ∨ i = cTmp ∨ Writes b i
  | .loopT c _ _ b, i => i = c ∨ Writes b i

/-- **Well-formed**: no destination is a constant cell, and every loop counter is a register
above `cTmp`, distinct from the loop's count register, that its body does not write (the entry
writes `c` and `cTmp` before it reads `n`, so `n ∈ {c, cTmp}` would change the count). -/
def WF : XIR → Prop
  | .blk ps => ∀ p ∈ ps, 4 ≤ p.dst
  | .load d _ => 4 ≤ d
  | .store a _ => a ≠ cTmp
  | .input d _ => 4 ≤ d
  | .out _ => True
  | .seq p q => WF p ∧ WF q
  | .ite _ p q => WF p ∧ WF q
  | .loopK c n _ b => (4 < c ∧ n ≠ c ∧ n ≠ cTmp) ∧ c < regs ∧ ¬ Writes b c ∧ WF b
  | .loopT c n _ b => (4 < c ∧ n ≠ c ∧ n ≠ cTmp) ∧ c < regs ∧ ¬ Writes b c ∧ WF b

/-- **The caps hold** on the run of `P` from `s`: every `loopT` entered has a count of at most
its cap at `t`. -/
def BoundsOk (I : Array Word) (t : ℕ) : XIR → St → Prop
  | .seq p q, s => BoundsOk I t p s ∧ BoundsOk I t q (semXIR I p s)
  | .ite c p q, s => if rd s.M c = 0 then BoundsOk I t q s else BoundsOk I t p s
  | .loopK c n K b, s => ∀ j < (rd (entryK c n K s.M) c).toNat,
      BoundsOk I t b (iterL (semXIR I b) c j ⟨entryK c n K s.M, s.o⟩)
  | .loopT c n cap b, s => (rd (entryT c n s.M) c).toNat ≤ cap.eval t ∧
      ∀ j < (rd (entryT c n s.M) c).toNat,
        BoundsOk I t b (iterL (semXIR I b) c j ⟨entryT c n s.M, s.o⟩)
  | _, _ => True

/-- **The syntactic step bound**, affine in the tape length `t`. -/
def cost : XIR → ℕ → ℕ
  | .blk ps, _ => blkSteps ps.length
  | .load .., _ => 1
  | .store .., _ => 4
  | .input .., _ => 1
  | .out _, _ => 1
  | .seq p q, t => cost p t + cost q t + 1
  | .ite _ p q, t => max (cost p t) (cost q t) + 1
  | .loopK _ _ K b, t => 8 + K.toNat * (cost b t + 3)
  | .loopT _ _ cap b, t => 3 + cap.eval t * (cost b t + 3)

/-- **The syntactic output bound.** -/
def outs : XIR → ℕ → ℕ
  | .out _, _ => 1
  | .seq p q, t => outs p t + outs q t
  | .ite _ p q, t => max (outs p t) (outs q t)
  | .loopK _ _ K b, t => K.toNat * outs b t
  | .loopT _ _ cap b, t => cap.eval t * outs b t
  | _, _ => 0

/-- The compiled statement count. -/
def sizeIR : XIR → ℕ
  | .blk ps => blkSteps ps.length
  | .load .. => 1
  | .store .. => 5
  | .input .. => 1
  | .out _ => 1
  | .seq p q => sizeIR p + sizeIR q + 1
  | .ite _ p q => sizeIR p + sizeIR q + 1
  | .loopK _ _ _ b => sizeIR b + 11
  | .loopT _ _ _ b => sizeIR b + 5

/-! ## The program -/

/-- The prologue: the constant cells. -/
def initPs : List Prim := [.const cOne 1, .const cBase 256, .const cRed 0x1B, .const c63 63]

/-- **The program of `P`**: `mem + mpw · t` memory words, the prologue, then `P`. -/
def toProg (mem mpw : ℕ) (P : XIR) : XProg := ⟨mem, mpw, compile (.seq (.blk initPs) P)⟩

/-- The state after the prologue on `m` zero words. -/
def initSt (m : ℕ) : St := ⟨runPrims initPs (Array.replicate m 0), #[]⟩


/-! ## Proof helpers: memory -/

theorem rd_set (M : Mem) (j i : ℕ) (v : Word) :
    rd (M.setIfInBounds j v) i = if j = i ∧ j < M.size then v else rd M i := by
  simp only [rd, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h; by_cases hj : j < M.size <;> simp [hj]
  · simp [h]

@[simp] theorem rd_set_self {M : Mem} {j : ℕ} {v : Word} (h : j < M.size) :
    rd (M.setIfInBounds j v) j = v := by simp [rd_set, h]

@[simp] theorem rd_set_ne {M : Mem} {j i : ℕ} {v : Word} (h : j ≠ i) :
    rd (M.setIfInBounds j v) i = rd M i := by simp [rd_set, h]

theorem set_rd_self (M : Mem) (i : ℕ) : M.setIfInBounds i (rd M i) = M := by
  by_cases h : i < M.size
  · simp [rd, Array.getD_eq_getD_getElem?, h, Array.setIfInBounds, Array.set_getElem_self]
  · simp [Array.setIfInBounds, h]

@[simp] theorem size_set (M : Mem) (i : ℕ) (v : Word) : (M.setIfInBounds i v).size = M.size :=
  Array.size_setIfInBounds

@[simp] theorem size_runPrims (ps : List Prim) (M : Mem) : (runPrims ps M).size = M.size := by
  induction ps generalizing M with
  | nil => rfl
  | cons p ps ih => cases p <;> exact (ih _).trans (size_set ..)

theorem runPrims_cons (p : Prim) (ps : List Prim) (M : Mem) :
    runPrims (p :: ps) M = runPrims ps (p.run M) := rfl

theorem runPrims_append (ps qs : List Prim) (M : Mem) :
    runPrims (ps ++ qs) M = runPrims qs (runPrims ps M) := List.foldl_append ..

-- G2: the lemmas below use `entryK` through `unfold`/its lemmas; irreducible, it is never unfolded
-- while unifying `{ M := entryK …, o := … }.M` with `entryK …` (elaboration time).
attribute [local irreducible] entryK

@[simp] theorem size_storeM (M : Mem) (a v : ℕ) : (storeM M a v).size = M.size := by
  unfold storeM; dsimp only; split <;> simp

@[simp] theorem size_entryK (c n : ℕ) (K : Word) (M : Mem) : (entryK c n K M).size = M.size := by
  unfold entryK; dsimp only; split <;> simp

@[simp] theorem size_entryT (c n : ℕ) (M : Mem) : (entryT c n M).size = M.size := by
  simp [entryT]

@[simp] theorem size_decS (c : ℕ) (s : St) : (decS c s).M.size = s.M.size := by simp [decS]

theorem size_iterL {f : St → St} (hf : ∀ s, (f s).M.size = s.M.size) (c : ℕ) :
    ∀ k s, (iterL f c k s).M.size = s.M.size
  | 0, _ => rfl
  | k + 1, s => (size_iterL hf c k _).trans ((size_decS c _).trans (hf s))

/-- The memory keeps its size. -/
@[simp] theorem size_sem (I : Array Word) : ∀ (P : XIR) (s : St), (semXIR I P s).M.size = s.M.size
  | .blk _, _ => size_runPrims ..
  | .load .., _ => size_set ..
  | .store .., _ => size_storeM ..
  | .input .., _ => size_set ..
  | .out _, _ => rfl
  | .seq p q, s => (size_sem I q _).trans (size_sem I p s)
  | .ite c p q, s => by
    simp only [semXIR]; split
    · exact size_sem I q s
    · exact size_sem I p s
  | .loopK c n K b, s => (size_iterL (size_sem I b) c _ _).trans (size_entryK ..)
  | .loopT c n _ b, s => (size_iterL (size_sem I b) c _ _).trans (size_entryT ..)

/-! ## Frame and the invariant -/

theorem rd_runPrims_of_not_writes {ps : List Prim} {i : ℕ} (h : ∀ p ∈ ps, p.dst ≠ i) (M : Mem) :
    rd (runPrims ps M) i = rd M i := by
  induction ps generalizing M with
  | nil => rfl
  | cons p ps ih =>
    rw [runPrims_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hp := h p List.mem_cons_self
    cases p <;> exact rd_set_ne hp

theorem inv_of_frame {M M' : Mem} (h : Inv M) (hs : M'.size = M.size)
    (hf : ∀ i < 4, rd M' i = rd M i) : Inv M' :=
  ⟨hs ▸ h.1, fun i hi => (hf i hi).trans (h.2 i hi)⟩

/-- A well-formed program names no constant cell. -/
theorem not_writes_const : ∀ {P : XIR}, WF P → ∀ {i : ℕ}, i < 4 → ¬ Writes P i
  | .blk _, h, _, hi, ⟨p, hp, he⟩ => by have := h p hp; omega
  | .load .., h, _, hi, he => by simp only [Writes] at he; simp only [WF] at h; omega
  | .store .., _, _, hi, he => by simp only [Writes, cTmp] at he; omega
  | .input .., h, _, hi, he => by simp only [Writes] at he; simp only [WF] at h; omega
  | .out _, _, _, _, he => he
  | .seq _ _, h, _, hi, he => he.elim (not_writes_const h.1 hi) (not_writes_const h.2 hi)
  | .ite _ _ _, h, _, hi, he => he.elim (not_writes_const h.1 hi) (not_writes_const h.2 hi)
  | .loopK .., h, _, hi, he => by
    rcases he with he | he | he
    · have := h.1; omega
    · simp only [cTmp] at he; omega
    · exact not_writes_const h.2.2.2 hi he
  | .loopT .., h, _, hi, he => by
    rcases he with he | he
    · have := h.1; omega
    · exact not_writes_const h.2.2.2 hi he

theorem storeM_frame {M : Mem} (hM : Inv M) {a v i : ℕ} (ha : a ≠ cTmp) (hi : i < regs)
    (hit : i ≠ cTmp) : rd (storeM M a v) i = rd M i := by
  have hT : cTmp < M.size := by have := hM.1; simp only [regs, cTmp] at *; omega
  have hB : rd M cBase = 256 := hM.2 1 (by decide)
  unfold storeM
  dsimp only
  simp only [rd_set_self hT, rd_set_ne (Ne.symm ha), hB]
  split
  · next h0 =>
    have hge : (256 : Word) ≤ rd M a := by simpa [XOp.eval] using h0
    have : (rd M a).toNat ≠ i := by
      have h4 : (256 : Word).toNat = 256 := rfl
      intro he; rw [BitVec.le_def, h4] at hge; simp only [regs] at hi; omega
    rw [rd_set_ne this, rd_set_ne (Ne.symm hit)]
  · exact rd_set_ne (Ne.symm hit)

theorem rd_decS {c i : ℕ} (h : c ≠ i) (s : St) : rd (decS c s).M i = rd s.M i := rd_set_ne h

theorem iterL_inv {f : St → St} {c : ℕ} (hc : 4 ≤ c) (hf : ∀ s, Inv s.M → Inv (f s).M) :
    ∀ k s, Inv s.M → Inv (iterL f c k s).M
  | 0, _, h => h
  | k + 1, s, h => iterL_inv hc hf k _ (inv_of_frame (hf s h) (size_decS ..)
      fun i hi => rd_decS (by omega) _)

theorem iterL_frame {f : St → St} {c i : ℕ} (hc : 4 ≤ c) (hic : i ≠ c)
    (hf : ∀ s, Inv s.M → Inv (f s).M) (hfi : ∀ s, Inv s.M → rd (f s).M i = rd s.M i) :
    ∀ k s, Inv s.M → rd (iterL f c k s).M i = rd s.M i
  | 0, _, _ => rfl
  | k + 1, s, h => by
    have h' : Inv (decS c (f s)).M := inv_of_frame (hf s h) (size_decS ..)
      fun j hj => rd_decS (by omega) _
    exact (iterL_frame hc hic hf hfi k _ h').trans ((rd_decS (Ne.symm hic) _).trans (hfi s h))

theorem entryK_frame {c n i : ℕ} {K : Word} (M : Mem) (hc : c ≠ i) (ht : cTmp ≠ i) :
    rd (entryK c n K M) i = rd M i := by
  unfold entryK; dsimp only; split <;> simp [rd_set_ne hc, rd_set_ne ht]

theorem entryT_frame {c n i : ℕ} (M : Mem) (hc : c ≠ i) : rd (entryT c n M) i = rd M i :=
  rd_set_ne hc

/-- **Frame**: a cell below `regs` that a well-formed program does not name is unchanged. -/
theorem frame (I : Array Word) (P : XIR) : ∀ (s : St), WF P → Inv s.M → ∀ i < regs,
    ¬ Writes P i → rd (semXIR I P s).M i = rd s.M i := by
  induction P with
  | blk _ => exact fun s _ _ i _ hw => rd_runPrims_of_not_writes (fun p hp he => hw ⟨p, hp, he⟩) _
  | load d _ => exact fun s _ _ i _ hw => rd_set_ne (Ne.symm hw)
  | store _ _ => exact fun s hP hM i hi hw => storeM_frame hM hP hi hw
  | input d _ => exact fun s _ _ i _ hw => rd_set_ne (Ne.symm hw)
  | out _ => exact fun _ _ _ _ _ _ => rfl
  | seq p q ihp ihq =>
    intro s hP hM i hi hw
    have hM' : Inv (semXIR I p s).M := inv_of_frame hM (size_sem ..)
      fun j hj => ihp s hP.1 hM j (by simp only [regs]; omega) (not_writes_const hP.1 hj)
    exact (ihq _ hP.2 hM' i hi (fun h => hw (Or.inr h))).trans
      (ihp s hP.1 hM i hi (fun h => hw (Or.inl h)))
  | ite c p q ihp ihq =>
    intro s hP hM i hi hw
    simp only [semXIR]; split
    · exact ihq s hP.2 hM i hi (fun h => hw (Or.inr h))
    · exact ihp s hP.1 hM i hi (fun h => hw (Or.inl h))
  | loopK c n K b ih =>
    intro s hP hM i hi hw
    simp only [Writes, not_or] at hw
    have hinv := fun s' h' => inv_of_frame h' (size_sem I b s')
      fun j hj => ih s' hP.2.2.2 h' j (by simp only [regs]; omega)
        (not_writes_const hP.2.2.2 hj)
    have h0 : Inv (entryK c n K s.M) := inv_of_frame hM (size_entryK ..)
      fun j hj => entryK_frame _ (by have := hP.1; omega) (by simp only [cTmp]; omega)
    simp only [semXIR]
    exact (iterL_frame (by have := hP.1; omega) hw.1 hinv
      (fun s' h' => ih s' hP.2.2.2 h' i hi hw.2.2) _ ⟨entryK c n K s.M, s.o⟩ h0).trans
      (entryK_frame _ (Ne.symm hw.1) (Ne.symm hw.2.1))
  | loopT c n _ b ih =>
    intro s hP hM i hi hw
    simp only [Writes, not_or] at hw
    have hinv := fun s' h' => inv_of_frame h' (size_sem I b s')
      fun j hj => ih s' hP.2.2.2 h' j (by simp only [regs]; omega)
        (not_writes_const hP.2.2.2 hj)
    have h0 : Inv (entryT c n s.M) := inv_of_frame hM (size_entryT ..)
      fun j hj => entryT_frame _ (by have := hP.1; omega)
    simp only [semXIR]
    exact (iterL_frame (by have := hP.1; omega) hw.1 hinv
      (fun s' h' => ih s' hP.2.2.2 h' i hi hw.2) _ ⟨entryT c n s.M, s.o⟩ h0).trans
      (entryT_frame _ (Ne.symm hw.1))

/-- **The invariant holds throughout** a well-formed program. -/
theorem inv_sem (I : Array Word) {P : XIR} (hP : WF P) {s : St} (hM : Inv s.M) :
    Inv (semXIR I P s).M :=
  inv_of_frame hM (size_sem ..) fun j hj =>
    frame I P s hP hM j (by simp only [regs]; omega) (not_writes_const hP hj)

/-! ## Running blocks -/

@[simp] theorem runPrims_nil (M : Mem) : runPrims [] M = M := rfl

@[simp] theorem eval_xor (a b : Word) : XOp.xor.eval a b = a ^^^ b := rfl
@[simp] theorem eval_or (a b : Word) : XOp.or.eval a b = a ||| b := rfl
@[simp] theorem eval_shl63 (a : Word) : XOp.shl.eval a 63 = a <<< 63 := by
  simp [XOp.eval]
@[simp] theorem eval_shr1 (a : Word) : XOp.shr.eval a 1 = a >>> 1 := by
  simp [XOp.eval]

theorem inv_runPrims {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst) {M : Mem} (hM : Inv M) :
    Inv (runPrims ps M) :=
  inv_of_frame hM (size_runPrims ..) fun i hi =>
    rd_runPrims_of_not_writes (fun p hp => by have := h p hp; omega) M

theorem rd_xor_run {M : Mem} {d a b : ℕ} (hd : d < M.size) :
    rd (runPrims [.op .xor d a b] M) d = rd M a ^^^ rd M b := rd_set_self hd

theorem xorC_frame (d a b : ℕ) {i : ℕ} (hd : i ≠ d) (M : Mem) :
    rd (runPrims [.op .xor d a b] M) i = rd M i := rd_set_ne (Ne.symm hd)

theorem xorC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) :
    Inv (runPrims [.op .xor d a b] M) :=
  inv_runPrims (by simp [Prim.dst]; omega) hM

/-! ## The compiled code runs as `semXIR` says, in `steps` steps -/

variable {I : Array Word}

theorem runs_nop (M o : Array Word) : Runs I nop M o 1 M o := by
  have h := runs_op (I := I) XOp.or cOne cOne cOne M o
  rwa [show XOp.or.eval (M.getD cOne 0) (M.getD cOne 0) = rd M cOne from BitVec.or_self,
    set_rd_self] at h

theorem runs_prim (p : Prim) (M o : Array Word) : Runs I p.stmt M o 1 (p.run M) o := by
  cases p
  · exact runs_op _ _ _ _ _ _
  · exact runs_const _ _ _ _

theorem runs_stmts : ∀ (ps : List Prim) (M o : Array Word),
    Runs I (stmts ps) M o (blkSteps ps.length) (runPrims ps M) o
  | [], M, o => runs_nop M o
  | [p], M, o => runs_prim p M o
  | p :: q :: ps, M, o => runs_mono_eq (runs_seq (runs_prim p M o) (runs_stmts (q :: ps) _ o))
      (by simp [blkSteps]; omega)

theorem runs_storeIR (a v : ℕ) (M o : Array Word) :
    Runs I (compile (.store a v)) M o 4 (storeM M a v) o := by
  have h1 := runs_op (I := I) XOp.ltu cTmp a cBase M o
  simp only [compile, storeM]
  split
  · next h0 => exact runs_seq h1 (runs_ite_false h0 (XStmt.runs_store _ _ _ _))
  · next h0 => exact runs_seq h1 (runs_ite_true h0 (runs_nop _ _))

theorem toNat_sub_one {w : Word} {k : ℕ} (h : w.toNat = k + 1) : (w - 1).toNat = k := by
  have h1 : (1 : Word).toNat = 1 := rfl
  rw [BitVec.toNat_sub, h1]; have := w.isLt; omega

/-- A counted loop runs its `k` iterations. -/
theorem runs_loop {B : XStmt} {f : St → St} {g : St → ℕ} {c : ℕ} (hc4 : 4 ≤ c) (hcr : c < regs)
    (hB : ∀ s, Inv s.M → Runs I B s.M s.o (g s) (f s).M (f s).o)
    (hinv : ∀ s, Inv s.M → Inv (f s).M) (hfc : ∀ s, Inv s.M → rd (f s).M c = rd s.M c) :
    ∀ k s, Inv s.M → (rd s.M c).toNat = k → Runs I (.loop c (.seq B (decStmt c))) s.M s.o
      (stepsL f g c k s) (iterL f c k s).M (iterL f c k s).o
  | 0, s, _, hk => runs_loop_zero (by
      show rd s.M c = 0
      exact BitVec.eq_of_toNat_eq (by simpa using hk))
  | k + 1, s, hM, hk => by
    have hf := hinv s hM
    have hne : s.M.getD c 0 ≠ 0 := by
      intro h0; change rd s.M c = 0 at h0; rw [h0] at hk; simp at hk
    have hd : Runs I (decStmt c) (f s).M (f s).o 1 (decS c (f s)).M (f s).o := runs_op _ _ _ _ _ _
    have h' : Inv (decS c (f s)).M := inv_of_frame hf (size_decS ..)
      fun j hj => rd_decS (by omega) _
    have hk' : (rd (decS c (f s)).M c).toNat = k := by
      simp only [decS]
      have h1 : rd (f s).M cOne = 1 := hf.2 0 (by decide)
      rw [rd_set_self (by have := hf.1; omega), hfc s hM, h1]
      exact toNat_sub_one hk
    exact runs_mono_eq (runs_loop_step hne (runs_seq (hB s hM) hd)
      (runs_loop hc4 hcr hB hinv hfc k _ h' hk')) (by simp only [stepsL]; omega)

theorem runs_entryK (c n : ℕ) (K : Word) (L : XStmt) (M o M' o' : Array Word) (m : ℕ)
    (hL : Runs I L (entryK c n K M) o m M' o') :
    Runs I (.seq (.const c K) (.seq (.op .ltu cTmp n c) (.seq (.ite cTmp (.op .or c n n) nop) L)))
      M o (m + 7) M' o' := by
  have h1 := runs_const (I := I) c K M o
  have h2 := runs_op (I := I) XOp.ltu cTmp n c (M.setIfInBounds c K) o
  unfold entryK at hL
  dsimp only at hL
  split at hL
  · next h0 => exact runs_mono_eq (runs_seq h1 (runs_seq h2 (runs_seq
      (runs_ite_false h0 (runs_nop _ _)) hL))) (by omega)
  · next h0 => exact runs_mono_eq (runs_seq h1 (runs_seq h2 (runs_seq
      (runs_ite_true h0 (runs_op _ _ _ _ _ _)) hL))) (by omega)

/-- **The compiler is correct**: from a state satisfying `Inv`, the compiled code of a
well-formed program runs in exactly `steps I P s` steps to `semXIR I P s`. -/
theorem compile_correct (P : XIR) : ∀ s : St, WF P → Inv s.M →
    Runs I (compile P) s.M s.o (steps I P s) (semXIR I P s).M (semXIR I P s).o := by
  induction P with
  | blk ps => exact fun s _ _ => runs_stmts ps s.M s.o
  | load d a => exact fun s _ _ => runs_load _ _ _ _
  | store a v => exact fun s _ _ => runs_storeIR a v s.M s.o
  | input d a => exact fun s _ _ => runs_input _ _ _ _
  | out v => exact fun s _ _ => runs_out _ _ _
  | seq p q ihp ihq =>
    exact fun s hP hM => runs_seq (ihp s hP.1 hM) (ihq _ hP.2 (inv_sem I hP.1 hM))
  | ite c p q ihp ihq =>
    intro s hP hM
    simp only [compile, semXIR, steps]
    split
    · next h0 => exact runs_ite_false h0 (ihq s hP.2 hM)
    · next h0 => exact runs_ite_true h0 (ihp s hP.1 hM)
  | loopK c n K b ih =>
    intro s hP hM
    have h0 : Inv (entryK c n K s.M) := inv_of_frame hM (size_entryK ..)
      fun j hj => entryK_frame _ (by have := hP.1; omega) (by simp only [cTmp]; omega)
    have hL := runs_loop (I := I) (B := compile b) (by have := hP.1; omega) hP.2.1
      (fun s' h' => ih s' hP.2.2.2 h') (fun s' h' => inv_sem I hP.2.2.2 h')
      (fun s' h' => frame I b s' hP.2.2.2 h' c hP.2.1 hP.2.2.1) _ ⟨entryK c n K s.M, s.o⟩ h0 rfl
    exact runs_mono_eq (runs_entryK c n K _ s.M s.o _ _ _ hL) (by simp only [steps]; omega)
  | loopT c n _ b ih =>
    intro s hP hM
    have h0 : Inv (entryT c n s.M) := inv_of_frame hM (size_entryT ..)
      fun j hj => entryT_frame _ (by have := hP.1; omega)
    have hL := runs_loop (I := I) (B := compile b) (by have := hP.1; omega) hP.2.1
      (fun s' h' => ih s' hP.2.2.2 h') (fun s' h' => inv_sem I hP.2.2.2 h')
      (fun s' h' => frame I b s' hP.2.2.2 h' c hP.2.1 hP.2.2.1) _ ⟨entryT c n s.M, s.o⟩ h0 rfl
    exact runs_mono_eq (runs_seq (runs_op _ _ _ _ _ _) hL) (by simp only [steps]; omega)

/-! ## Step and output bounds -/

/-- The clamp: `loopK` runs at most `K` times. -/
theorem entryK_le {c n : ℕ} {K : Word} {M : Mem} (hc : c ≠ cTmp) (hcs : c < M.size)
    (hts : cTmp < M.size) : (rd (entryK c n K M) c).toNat ≤ K.toNat := by
  unfold entryK; dsimp only
  have e1 : rd (M.setIfInBounds c K) c = K := rd_set_self hcs
  rw [e1]
  have hs1 : cTmp < (M.setIfInBounds c K).size := by simpa using hts
  by_cases hlt : rd (M.setIfInBounds c K) n < K
  · have hf : XOp.ltu.eval (rd (M.setIfInBounds c K) n) K = 1 := by simp [XOp.eval, hlt]
    have h2 : rd ((M.setIfInBounds c K).setIfInBounds cTmp 1) cTmp = 1 := rd_set_self hs1
    rw [hf, h2, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), rd_set_self (by simpa using
        hcs)]
    simp only [XOp.eval, BitVec.or_self]
    by_cases hn : n = cTmp
    · subst hn; rw [h2]; have := BitVec.lt_def.mp hlt
      have h1 : (1 : Word).toNat = 1 := rfl
      omega
    · rw [rd_set_ne (Ne.symm hn)]; exact le_of_lt (BitVec.lt_def.mp hlt)
  · have hf : XOp.ltu.eval (rd (M.setIfInBounds c K) n) K = 0 := by simp [XOp.eval, hlt]
    rw [hf, rd_set_self hs1, ite_eq_left_of_eq_true _ _ (eq_true rfl), rd_set_ne (Ne.symm hc), e1]

theorem stepsL_le {f : St → St} {g : St → ℕ} {c B : ℕ} : ∀ k s,
    (∀ j < k, g (iterL f c j s) ≤ B) → stepsL f g c k s ≤ 1 + k * (B + 3)
  | 0, _, _ => by simp [stepsL]
  | k + 1, s, h => by
    have h0 := h 0 (by omega)
    have := stepsL_le k (decS c (f s)) fun j hj => h (j + 1) (by omega)
    simp only [stepsL, iterL] at h0 ⊢
    rw [Nat.add_mul]; omega

theorem iterL_outs {f : St → St} {c B : ℕ} : ∀ k s,
    (∀ j < k, (f (iterL f c j s)).o.size ≤ (iterL f c j s).o.size + B) →
      (iterL f c k s).o.size ≤ s.o.size + k * B
  | 0, _, _ => by simp [iterL]
  | k + 1, s, h => by
    have h0 := h 0 (by omega)
    have := iterL_outs k (decS c (f s)) fun j hj => h (j + 1) (by omega)
    simp only [iterL, decS] at h0 this ⊢
    rw [Nat.add_mul]; omega

/-- **The step bound**: under the loop bounds, the compiled code takes at most `cost P t`
steps. -/
theorem steps_le_cost (t : ℕ) (P : XIR) : ∀ s : St, WF P → Inv s.M → BoundsOk I t P s →
    steps I P s ≤ cost P t := by
  induction P with
  | blk ps => intro s _ _ _; exact le_refl _
  | load | store | input | out => intro s _ _ _; exact le_refl _
  | seq p q ihp ihq =>
    intro s hP hM hB
    have := ihp s hP.1 hM hB.1
    have := ihq _ hP.2 (inv_sem I hP.1 hM) hB.2
    simp only [steps, cost]; omega
  | ite c p q ihp ihq =>
    intro s hP hM hB
    simp only [steps, cost, BoundsOk] at hB ⊢
    split at hB
    · next h0 => simp only [h0, ite_true]; have := ihq s hP.2 hM hB; omega
    · next h0 => simp only [h0, ite_false]; have := ihp s hP.1 hM hB; omega
  | loopK c n K b ih =>
    intro s hP hM hB
    have h0 : Inv (entryK c n K s.M) := inv_of_frame hM (size_entryK ..)
      fun j hj => entryK_frame _ (by have := hP.1; omega) (by simp only [cTmp]; omega)
    have hcT : c ≠ cTmp := by simp only [cTmp]; have := hP.1; omega
    have hk := entryK_le (c := c) (n := n) (K := K) (M := s.M) hcT
      (by have := hM.1; have := hP.2.1; omega) (by have := hM.1; simp only [regs, cTmp] at *; omega)
    have hl := stepsL_le (f := semXIR I b) (g := steps I b) (B := cost b t) _ ⟨entryK c n K s.M,
        s.o⟩ fun j hj =>
      ih _ hP.2.2.2 (iterL_inv (by have := hP.1; omega) (fun s' h' => inv_sem I hP.2.2.2 h') j _ h0)
        (hB j hj)
    simp only [steps, cost]
    have := Nat.mul_le_mul_right (cost b t + 3) hk
    omega
  | loopT c n cap b ih =>
    intro s hP hM hB
    have h0 : Inv (entryT c n s.M) := inv_of_frame hM (size_entryT ..)
      fun j hj => entryT_frame _ (by have := hP.1; omega)
    have hl := stepsL_le (f := semXIR I b) (g := steps I b) (B := cost b t) _ ⟨entryT c n s.M,
        s.o⟩ fun j hj =>
      ih _ hP.2.2.2 (iterL_inv (by have := hP.1; omega) (fun s' h' => inv_sem I hP.2.2.2 h') j _ h0)
        (hB.2 j hj)
    simp only [steps, cost]
    have := Nat.mul_le_mul_right (cost b t + 3) hB.1
    omega

/-- **The output bound**: under the loop bounds, at most `outs P t` words are output. -/
theorem outs_le (t : ℕ) (P : XIR) : ∀ s : St, WF P → Inv s.M → BoundsOk I t P s →
    (semXIR I P s).o.size ≤ s.o.size + outs P t := by
  induction P with
  | blk | load | store | input => intro s _ _ _; simp [semXIR, outs]
  | out => intro s _ _ _; simp [semXIR, outs]
  | seq p q ihp ihq =>
    intro s hP hM hB
    have := ihp s hP.1 hM hB.1
    have := ihq _ hP.2 (inv_sem I hP.1 hM) hB.2
    simp only [semXIR, outs]; omega
  | ite c p q ihp ihq =>
    intro s hP hM hB
    simp only [semXIR, outs, BoundsOk] at hB ⊢
    split at hB
    · next h0 => simp only [h0, ite_true]; have := ihq s hP.2 hM hB; omega
    · next h0 => simp only [h0, ite_false]; have := ihp s hP.1 hM hB; omega
  | loopK c n K b ih =>
    intro s hP hM hB
    have h0 : Inv (entryK c n K s.M) := inv_of_frame hM (size_entryK ..)
      fun j hj => entryK_frame _ (by have := hP.1; omega) (by simp only [cTmp]; omega)
    have hcT : c ≠ cTmp := by simp only [cTmp]; have := hP.1; omega
    have hk := entryK_le (c := c) (n := n) (K := K) (M := s.M) hcT
      (by have := hM.1; have := hP.2.1; omega) (by have := hM.1; simp only [regs, cTmp] at *; omega)
    have hl := iterL_outs (f := semXIR I b) (B := outs b t) _ ⟨entryK c n K s.M, s.o⟩ fun j hj =>
      ih _ hP.2.2.2 (iterL_inv (by have := hP.1; omega) (fun s' h' => inv_sem I hP.2.2.2 h') j _ h0)
        (hB j hj)
    simp only [semXIR, outs]
    have := Nat.mul_le_mul_right (outs b t) hk
    simp only at hl; omega
  | loopT c n cap b ih =>
    intro s hP hM hB
    have h0 : Inv (entryT c n s.M) := inv_of_frame hM (size_entryT ..)
      fun j hj => entryT_frame _ (by have := hP.1; omega)
    have hl := iterL_outs (f := semXIR I b) (B := outs b t) _ ⟨entryT c n s.M, s.o⟩ fun j hj =>
      ih _ hP.2.2.2 (iterL_inv (by have := hP.1; omega) (fun s' h' => inv_sem I hP.2.2.2 h') j _ h0)
        (hB.2 j hj)
    simp only [semXIR, outs]
    have := Nat.mul_le_mul_right (outs b t) hB.1
    simp only at hl; omega

/-! ## Program size -/

theorem size_stmts : ∀ ps : List Prim, (stmts ps).size = blkSteps ps.length
  | [] => rfl
  | [p] => by cases p <;> rfl
  | p :: q :: ps => by
    have := size_stmts (q :: ps)
    cases p <;> simp only [stmts, Prim.stmt, XStmt.size, this, blkSteps] <;> simp <;> omega

/-- **The compiled size is `sizeIR`**, computed without compiling. -/
theorem size_compile : ∀ P : XIR, (compile P).size = sizeIR P
  | .blk ps => size_stmts ps
  | .load .. | .input .. | .out _ | .store .. => rfl
  | .seq p q | .ite _ p q => by simp only [compile, XStmt.size, sizeIR, size_compile p,
      size_compile q]
  | .loopK _ _ _ b | .loopT _ _ _ b => by
    simp only [compile, XStmt.size, sizeIR, size_compile b, nop, decStmt]; omega

/-! ## Programs -/

/-- **`compile_runs`** (BLUEPRINT §6.4): under the loop bounds, the compiled code halts within
`cost P t` steps with at most `outs P t` more output words, at `semXIR`'s state. -/
theorem compile_runs (t : ℕ) (P : XIR) (s : St) (hP : WF P) (hM : Inv s.M)
    (hB : BoundsOk I t P s) : ∃ n ≤ cost P t,
      Runs I (compile P) s.M s.o n (semXIR I P s).M (semXIR I P s).o ∧
      (semXIR I P s).o.size ≤ s.o.size + outs P t :=
  ⟨_, steps_le_cost t P s hP hM hB, compile_correct P s hP hM, outs_le t P s hP hM hB⟩

/-- The prologue establishes the invariant. -/
theorem initSt_M (m : ℕ) : (initSt m).M = runPrims initPs (Array.replicate m 0) := by
  simp only [initSt]

theorem initSt_o (m : ℕ) : (initSt m).o = #[] := by simp only [initSt]

theorem inv_initSt {m : ℕ} (h : regs ≤ m) : Inv (initSt m).M := by
  have h4 : 4 ≤ m := by simp only [regs] at h; omega
  have e : (initSt m).M = ((((Array.replicate m (0 : Word)).setIfInBounds 0 1).setIfInBounds 1
      256).setIfInBounds 2 0x1B).setIfInBounds 3 63 := by
    rw [initSt_M]; simp only [initPs, runPrims, List.foldl, Prim.run, cOne, cBase, cRed, c63]
  refine ⟨by rw [e]; simpa using h, fun i hi => ?_⟩
  rw [e]
  have hz : ∀ j < 4, j < (Array.replicate m (0 : Word)).size := fun j hj => by simp; omega
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [rd_set_ne (by decide), rd_set_ne (by decide), rd_set_ne (by decide),
      rd_set_self (hz 0 (by decide))]; rfl
  · rw [rd_set_ne (by decide), rd_set_ne (by decide), rd_set_self (by simpa using hz 1 (by decide))]
    rfl
  · rw [rd_set_ne (by decide), rd_set_self (by simpa using hz 2 (by decide))]; rfl
  · rw [rd_set_self (by simpa using hz 3 (by decide))]; rfl

theorem runs_body {I : Array Word} {m : ℕ} (P : XIR) (hm : regs ≤ m) (hP : WF P) :
    Runs I (compile (.seq (.blk initPs) P)) (Array.replicate m 0) #[]
      (steps I P (initSt m) + 8) (semXIR I P (initSt m)).M (semXIR I P (initSt m)).o := by
  have h0 := runs_stmts (I := I) initPs (Array.replicate m 0) #[]
  rw [← initSt_M] at h0
  have h1 := compile_correct (I := I) P (initSt m) hP (inv_initSt hm)
  rw [initSt_o] at h1
  have h7 : blkSteps initPs.length = 7 := rfl
  exact runs_mono_eq (runs_seq h0 h1) (by omega)

/-- **The program halts with `semXIR`'s output** within `mem + mpw · t + cost P t + 8` steps on
a tape of `t` words, when `P` is well formed and its loop bounds hold. -/
theorem run_toProg {mem mpw : ℕ} {P : XIR} {input : List Word} {f : ℕ} (hmem : regs ≤ mem)
    (hP : WF P) (hB : BoundsOk input.toArray input.length P (initSt (mem + mpw * input.length)))
    (hf : mem + mpw * input.length + cost P input.length + 8 ≤ f) :
    (toProg mem mpw P).run input f =
      some (semXIR input.toArray P (initSt (mem + mpw * input.length))).o.toList := by
  have hc := steps_le_cost input.length P _ hP (inv_initSt (by omega)) hB
  exact XProg.run_of_runs (p := toProg mem mpw P)
    (runs_body P (by simp only [XProg.memFor, toProg]; omega) hP)
    (by simp only [XProg.memFor, toProg]; omega)

/-- The program's output has at most `outs P t` words. -/
theorem toProg_outs {mem mpw : ℕ} {P : XIR} {input : List Word} (hmem : regs ≤ mem) (hP : WF P)
    (hB : BoundsOk input.toArray input.length P (initSt (mem + mpw * input.length))) :
    (semXIR input.toArray P (initSt (mem + mpw * input.length))).o.toList.length ≤
      outs P input.length := by
  have := outs_le input.length P _ hP (inv_initSt (by omega)) hB
  simpa [initSt] using this

end Lvm.X
