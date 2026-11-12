-- New for lvm (WP-11b-QA2, H2). Searched: leanerVM `Protocol/{Bus,TableSumcheck}.lean` (Fin-vector
-- statements of the same protocol, no circuit), FR `FRSumcheck` (R1CS rounds), QL's builder
-- (`LvmQBuild*`, used here). The `for`-loop and prefix lemmas of `LvmQWhirBase` are reused.
import LvmQBuildLemmas
import LvmQWhirBase
import LvmDecideSumcheck

/-!
# QA2 bus/table gadgets: shared base

* **`F` on the stream** (`Lvm`): `readEs_run`, `sampleE_run`, `samples_run` (what the reader returns
  from a cursor), `sumcheck_run`: `F`'s `sumcheck` from an entry boundary is the fold `scFold` of
  the pure round step `rstep` over the rounds `scRounds` it reads (messages `msgAt`, challenges
  `chAt`), and moves the cursor by one FS entry per round.
* **Loops of the builder** (`Lvm.Loop.Build`): one-dimensional loops of an *all-`E`* template
  (`AllE`: every row writes an `E` cell), operand values `val1_*`, row relations `lrel_*`;
  `runLoops`: loops of one template family over consecutive chunks of rounds, and `runLoops_law`:
  a per-iteration law of the template holds at every round of the run.
-/

set_option autoImplicit false

namespace Lvm.QB

open Lvm DM

/-! ## `BEq` on `E` -/

theorem FE.beq_iff (a b : FE) : (a == b) = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  show (a0 == b0 && a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem FE.bne_iff (a b : FE) : (a != b) = true ↔ a ≠ b := by
  rw [bne, Bool.not_eq_true', ← Bool.not_eq_true, FE.beq_iff]

/-! ## The reader from a cursor -/

theorem readEs_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    readEs n sig s = ((List.range n).map (fun k => feAt sig (s.ent + 40 + s.msg + 24 * k)),
      { s with msg := s.msg + 24 * n })
  | 0, s => by simp [readEs]; rfl
  | n + 1, s => by
    show (let r := readE sig s; let r2 := readEs n sig r.2; ((r.1 :: r2.1), r2.2)) = _
    simp only [readEs_run sig n, readE, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · simp only [Function.comp_def, Nat.mul_zero, Nat.add_zero]
      exact congrArg (List.cons _) (List.map_congr_left fun k _ =>
        congrArg (feAt sig) (by simp only [Nat.succ_eq_add_one]; ring))
    · exact congrArg (fun m => RS.mk s.ent m s.ok) (by ring)

theorem sampleE_run (sig : ByteArray) (s : RS) :
    sampleE sig s = (feAt sig (s.ent + 40 + s.msg), { s with ent := s.ent + 72 + s.msg, msg := 0 }) :=
  rfl

theorem samples_run (sig : ByteArray) : ∀ (n : Nat) (s : RS), s.msg = 0 →
    samples n sig s = ((List.range n).map (fun k => feAt sig (s.ent + 40 + 72 * k)),
      { s with ent := s.ent + 72 * n })
  | 0, s, _ => by simp [samples]; rfl
  | n + 1, s, hs => by
    show (let r := sampleE sig s; let r2 := samples n sig r.2; ((r.1 :: r2.1), r2.2)) = _
    simp only [sampleE_run, hs]
    rw [samples_run sig n _ rfl]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · simp only [Function.comp_def, Nat.mul_zero, Nat.add_zero]
      exact congrArg (List.cons _) (List.map_congr_left fun k _ =>
        congrArg (feAt sig) (by simp only [Nat.succ_eq_add_one]; ring))
    · rcases s with ⟨e, m, o⟩
      simp only at hs ⊢
      subst hs
      exact congrArg (fun x => RS.mk x 0 o) (by ring)

/-! ## Sumcheck rounds as a pure fold -/

/-- The message of the FS entry at byte `o`: its first `m` scalars. -/
def msgAt (sig : ByteArray) (o m : Nat) : List FE := (List.range m).map fun k => feAt sig (o + 40 + 24 * k)

/-- The challenge of the FS entry at byte `o` with an `m`-scalar message. -/
def chAt (sig : ByteArray) (o m : Nat) : FE := feAt sig (o + 40 + 24 * m)

/-- The round polynomial `sumcheckRoundPoly` builds from the message (pure). -/
def roundPoly (claim : FE) : Option FE → List FE → List FE
  | none, msg => msg.headD 0 :: (claim + sumE msg.tail) :: msg.tail
  | some e, msg => (claim + e * sumE msg) :: msg

/-- One round: the next claim from the claim and the round's (`eq_factor`, message, challenge). -/
def rstep (claim : FE) (x : Option FE × List FE × FE) : FE := polyEval (roundPoly claim x.1 x.2.1) x.2.2

/-- The final claim of a run of rounds. -/
def scFold (claim : FE) (rs : List (Option FE × List FE × FE)) : FE := rs.foldl rstep claim

/-- The bytes of one sumcheck round's FS entry (an `m`-scalar message). -/
def entB (m : Nat) : Nat := 72 + 24 * m

/-- The rounds `F` reads from byte `o` on (one FS entry per round, `count − 1` scalars each). -/
def scRounds (sig : ByteArray) (count o : Nat) (eqs : List (Option FE)) : List (Option FE × List FE × FE) :=
  (List.range eqs.length).map fun i =>
    (eqs.getD i none, msgAt sig (o + entB (count - 1) * i) (count - 1), chAt sig (o + entB (count - 1) * i) (count - 1))

theorem sumcheckRoundPoly_run (count : Nat) (hc : 2 ≤ count) (claim : FE) (e : Option FE)
    (sig : ByteArray) (s : RS) (hs : s.msg = 0) :
    sumcheckRoundPoly count claim e sig s =
      (roundPoly claim e (msgAt sig s.ent (count - 1)), { s with msg := 24 * (count - 1) }) := by
  cases e with
  | none =>
    obtain ⟨n, rfl⟩ : ∃ n, count = n + 2 := ⟨count - 2, by omega⟩
    show (let r := readE sig s; let r2 := readEs (n + 2 - 2) sig r.2;
      (r.1 :: (claim + sumE r2.1) :: r2.1, r2.2)) = _
    simp only [readEs_run, readE, hs, roundPoly, msgAt, show n + 2 - 1 = n + 1 by omega,
      show n + 2 - 2 = n by omega, List.range_succ_eq_map, List.map_cons, List.headD_cons,
      List.tail_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · simp only [Function.comp_def, Nat.mul_zero, Nat.add_zero]
      have : (List.map (fun k => feAt sig (s.ent + 40 + (0 + 24) + 24 * k)) (List.range n)) =
          List.map (fun x => feAt sig (s.ent + 40 + 24 * (x + 1))) (List.range n) :=
        List.map_congr_left fun k _ => congrArg (feAt sig) (by ring)
      rw [this]
    · exact congrArg (fun m => RS.mk s.ent m s.ok) (by ring)
  | some e =>
    show (let r := readEs (count - 1) sig s; ((claim + e * sumE r.1) :: r.1, r.2)) = _
    simp only [readEs_run, hs, roundPoly, msgAt, Nat.add_zero, Nat.zero_add]

theorem sumcheck_cons (claim : FE) (count : Nat) (e : Option FE) (es : List (Option FE))
    (sig : ByteArray) (s : RS) :
    sumcheck claim count (e :: es) sig s =
      let r1 := sumcheckRoundPoly count claim e sig s
      let r2 := sampleE sig r1.2
      let r3 := sumcheck (polyEval r1.1 r2.1) count es sig r2.2
      ((r2.1 :: r3.1.1, r3.1.2), r3.2) := rfl

theorem scRounds_cons (sig : ByteArray) (count o : Nat) (e : Option FE) (es : List (Option FE)) :
    scRounds sig count o (e :: es) =
        (e, msgAt sig o (count - 1), chAt sig o (count - 1)) ::
          scRounds sig count (o + entB (count - 1)) es := by
  have e1 : ∀ i : Nat, o + entB (count - 1) * (i + 1) = o + entB (count - 1) + entB (count - 1) * i :=
    fun i => by ring
  simp only [scRounds, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.mul_zero, Nat.add_zero, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ, e1]

/-- **`F`'s sumcheck from an entry boundary**: the challenges are the entries' answers, the final
claim the fold of `rstep` over the rounds read, and the cursor moves one entry per round. -/
theorem sumcheck_run (count : Nat) (hc : 2 ≤ count) (sig : ByteArray) :
    ∀ (eqs : List (Option FE)) (claim : FE) (s : RS), s.msg = 0 →
    sumcheck claim count eqs sig s =
      (((scRounds sig count s.ent eqs).map (·.2.2), scFold claim (scRounds sig count s.ent eqs)),
        { s with ent := s.ent + entB (count - 1) * eqs.length })
  | [], claim, s, _ => by simp [sumcheck, scRounds, scFold]; rfl
  | e :: es, claim, s, hs => by
    rw [sumcheck_cons, sumcheckRoundPoly_run count hc claim e sig s hs]
    dsimp only
    rw [sampleE_run]
    dsimp only
    rw [sumcheck_run count hc sig es _ _ rfl, scRounds_cons]
    rcases s with ⟨en, m, o⟩
    simp only at hs
    subst hs
    simp only [List.map_cons, scFold, List.foldl_cons, rstep, List.length_cons, chAt]
    have e2 : en + entB (count - 1) = en + 72 + 24 * (count - 1) := by simp only [entB]; ring
    have e3 : en + entB (count - 1) * (es.length + 1) =
        en + 72 + 24 * (count - 1) + entB (count - 1) * es.length := by simp only [entB]; ring
    rw [e2, e3]

theorem scFold_range_succ (claim : FE) (rnd : Nat → Option FE × List FE × FE) (n : Nat) :
    scFold claim ((List.range (n + 1)).map rnd) = rstep (scFold claim ((List.range n).map rnd)) (rnd n) := by
  simp [scFold, List.range_succ, List.foldl_append]

theorem sumcheck_append (claim : FE) (count : Nat) (es₁ es₂ : List (Option FE)) (sig : ByteArray)
    (s : RS) :
    sumcheck claim count (es₁ ++ es₂) sig s =
      let r1 := sumcheck claim count es₁ sig s
      let r2 := sumcheck r1.1.2 count es₂ sig r1.2
      ((r1.1.1 ++ r2.1.1, r2.1.2), r2.2) := by
  induction es₁ generalizing claim s with
  | nil => rfl
  | cons e es ih =>
    rw [List.cons_append, sumcheck_cons, sumcheck_cons]
    simp only [ih]
    rfl

end Lvm.QB

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-! ## One-dimensional loops of an all-`E` template -/

/-- Every template row writes an `E` cell. -/
def AllE (tpl : List LRow) : Prop := ∀ r ∈ tpl, r.ty = .E ∧ r.op ≠ .assert0

theorem lrow_wE {r : LRow} (h : r.ty = .E ∧ r.op ≠ .assert0) : r.w .E = 1 ∧ r.w .K = 0 := by
  rcases r with ⟨op, ty, args⟩
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1
  cases op <;> first | exact absurd rfl h2 | simp [LRow.w, Row.w, Row.writes]

theorem lrank_allE : ∀ {tpl : List LRow}, AllE tpl → ∀ t ≤ tpl.length, lrank .E tpl t = t
  | [], _, t, ht => by simp at ht; subst ht; rfl
  | r :: rs, h, t, ht => by
    rcases t with _ | t
    · rfl
    · have ih := lrank_allE (fun x hx => h x (List.mem_cons_of_mem _ hx)) t (by simpa using ht)
      simp only [lrank, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, (lrow_wE (h r List.mem_cons_self)).1]; omega

theorem ltw_allE : ∀ {tpl : List LRow}, AllE tpl → ltw .E tpl = tpl.length ∧ ltw .K tpl = 0
  | [], _ => ⟨rfl, rfl⟩
  | r :: rs, h => by
    have ih := ltw_allE (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hr := lrow_wE (h r List.mem_cons_self)
    simp only [ltw, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih.1, ih.2, hr.1, hr.2]; simp; omega

theorem getD_ty_allE {tpl : List LRow} (h : AllE tpl) {t : Nat} (ht : t < tpl.length) :
    (tpl.getD t default).ty = .E := by
  rw [List.getD_eq_getElem _ _ ht]
  exact (h _ (List.getElem_mem ht)).1

section
variable {M : Mem} {d : Nat} {tpl : List LRow} {p : Ptr} {jf : Nat}

theorem loop1_o (d : Nat) (tpl : List LRow) (p : Ptr) :
    (loop [d] tpl p).1 = ⟨p, [d], tpl⟩ := rfl

theorem cell1 (hA : AllE tpl) {t : Nat} (ht : t < tpl.length) :
    ((loop [d] tpl p).1.cell t jf).val M = M.e (p.e + t + tpl.length * jf) := by
  rw [LoopOut.cell_val, loop1_o]
  simp only [getD_ty_allE hA ht, Ptr.at, lrank_allE hA t ht.le, (ltw_allE hA).1, Mem.rd]

theorem val1_cur (hA : AllE tpl) (hjf : jf < 2 ^ d) {t : Nat} (ht : t < tpl.length) :
    (Opd.cur t).val M (loop [d] tpl p).1 jf = M.e (p.e + t + tpl.length * jf) := by
  rw [Opd.val_cur M _ (by simpa [loop1_o] using hjf), cell1 hA ht]

theorem val1_prev (hA : AllE tpl) (hjf : jf < 2 ^ d) {t : Nat} (ht : t < tpl.length) :
    (Opd.prev t).val M (loop [d] tpl p).1 jf = M.e (p.e + t - tpl.length + tpl.length * jf) := by
  rw [Opd.val_prev M _ (by simpa [loop1_o] using hjf), loop1_o]
  simp only [getD_ty_allE hA ht, Ptr.at, lrank_allE hA t ht.le, (ltw_allE hA).1, Mem.rd]

theorem val1_absK (hjf : jf < 2 ^ d) (b s : Nat) :
    (Opd.abs ⟨.K, b, [s]⟩).val M (loop [d] tpl p).1 jf = FE.ofK (M.k (b + s * jf)) := by
  rw [Opd.val_abs, loop1_o]
  simp only [unflat_one hjf, Addr.at, dot, Nat.add_zero, Mem.rd]

theorem val1_absE (hjf : jf < 2 ^ d) (b s : Nat) :
    (Opd.abs ⟨.E, b, [s]⟩).val M (loop [d] tpl p).1 jf = M.e (b + s * jf) := by
  rw [Opd.val_abs, loop1_o]
  simp only [unflat_one hjf, Addr.at, dot, Nat.add_zero, Mem.rd]

theorem val1_cell (hjf : jf < 2 ^ d) (c : Cell) :
    c.opd.val M (loop [d] tpl p).1 jf = c.val M := by
  rw [Cell.opd, Opd.val_abs, loop1_o]
  simp only [Cell.addr, unflat_one hjf, Addr.at, dot, Nat.add_zero, Cell.val]

end

section
variable {c : Ctx} {M : Mem} {o : LoopOut} {jf t : Nat}

theorem lrel_muladd (h : LRel c M o jf t) {τ : Ty} {x y z : Opd}
    (hr : o.tpl.getD t default = ⟨.muladd, τ, [x, y, z]⟩) :
    (o.cell t jf).val M = x.val M o jf * y.val M o jf + z.val M o jf := by
  simp only [LRel, LoopOut.arg, hr] at h; exact h

theorem lrel_lin (h : LRel c M o jf t) {τ : Ty} {k k' : FK} {x y : Opd}
    (hr : o.tpl.getD t default = ⟨.lin k k', τ, [x, y]⟩) :
    (o.cell t jf).val M = x.val M o jf + FE.ofK k * y.val M o jf + FE.ofK k' := by
  simp only [LRel, LoopOut.arg, hr] at h; exact h

theorem lrel_loadE (h : LRel c M o jf t) {τ : Ty} {x y z : Opd}
    (hr : o.tpl.getD t default = ⟨.loadE, τ, [x, y, z]⟩) :
    (o.cell t jf).val M = x.val M o jf + FE.y * y.val M o jf + FE.y * FE.y * z.val M o jf := by
  simp only [LRel, LoopOut.arg, hr] at h; exact h

end

/-! ## Every row of a one-dimensional all-`E` loop as an equation between cells -/

/-- An operand's value at iteration `jf` of a one-dimensional all-`E` loop at `p` of width `L`. -/
def ov (M : Mem) (p : Ptr) (L jf : Nat) : Opd → FE
  | .cur t => M.e (p.e + t + L * jf)
  | .prev t => M.e (p.e + t - L + L * jf)
  | .abs a => M.rd a.ty (a.at [jf])

/-- `cur`/`prev` operands name template rows. -/
def opdOk (L : Nat) : Opd → Prop
  | .cur t => t < L
  | .prev t => t < L
  | .abs _ => True

/-- Every operand of the template names a template row. -/
def OpdsOk (tpl : List LRow) : Prop := ∀ r ∈ tpl, ∀ x ∈ r.args, opdOk tpl.length x

/-- Row `t`'s relation at iteration `jf`, its result the `E` cell `p.e + t + L·jf`. -/
def RowEq (M : Mem) (p : Ptr) (L jf t : Nat) (r : LRow) : Prop :=
  match r.op, r.args with
  | .muladd, [x, y, z] => M.e (p.e + t + L * jf) = ov M p L jf x * ov M p L jf y + ov M p L jf z
  | .lin k k', [x, y] => M.e (p.e + t + L * jf) = ov M p L jf x + FE.ofK k * ov M p L jf y + FE.ofK k'
  | .loadE, [x, y, z] =>
    M.e (p.e + t + L * jf) = ov M p L jf x + FE.y * ov M p L jf y + FE.y * FE.y * ov M p L jf z
  | _, _ => True

theorem opd_val_ov {M : Mem} {d : Nat} {tpl : List LRow} {p : Ptr} {jf : Nat} (hA : AllE tpl)
    (hjf : jf < 2 ^ d) (x : Opd) (hx : opdOk tpl.length x) :
    x.val M (loop [d] tpl p).1 jf = ov M p tpl.length jf x := by
  cases x with
  | cur t => exact val1_cur hA hjf hx
  | prev t => exact val1_prev hA hjf hx
  | abs a => rw [Opd.val_abs, loop1_o]; simp only [unflat_one hjf, ov]

/-- **Every row of a one-dimensional all-`E` loop**, as an equation between `E` cells. -/
theorem loop1_eqs {c : Ctx} {M : Mem} {d : Nat} {tpl : List LRow} {p : Ptr} {L : Nat}
    (h : SegsHold c M p (loop [d] tpl p).2) (hA : AllE tpl) (hok : OpdsOk tpl) (hL : tpl.length = L)
    {jf : Nat} (hjf : jf < 2 ^ d) {t : Nat} (ht : t < L) : RowEq M p L jf t (tpl.getD t default) := by
  subst hL
  have hl := loop_rel h (by simpa using hjf) ht
  have hmem : tpl.getD t default ∈ tpl := by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  have hok' := hok _ hmem
  have hcell := cell1 (M := M) (p := p) (d := d) (jf := jf) hA ht
  unfold LRel at hl
  simp only [LoopOut.arg, loop1_o] at hl hcell
  generalize tpl.getD t default = r at hl hok' hcell
  rcases r with ⟨op, ty, args⟩
  have hv : ∀ k < args.length, (args.getD k default).val M ⟨p, [d], tpl⟩ jf =
      ov M p tpl.length jf (args.getD k default) := by
    intro k hk
    have := opd_val_ov (M := M) (p := p) hA hjf (args.getD k default)
      (hok' _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk))
    rwa [loop1_o] at this
  unfold RowEq
  simp only at hl hv ⊢
  cases op <;> simp only at hl ⊢
  · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;> try trivial
    simp only [List.length_cons] at hv
    rw [← hcell, hl, hv 0 (by simp), hv 1 (by simp), hv 2 (by simp)]; rfl
  · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> try trivial
    rw [← hcell, hl, hv 0 (by simp), hv 1 (by simp)]; rfl
  · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;> try trivial
    rw [← hcell, hl, hv 0 (by simp), hv 1 (by simp), hv 2 (by simp)]; rfl

/-! ## Stream scalars in `K` cells -/

/-- The `E` scalar in `K` cells `b, b + 1, b + 2`. -/
def kE (M : Mem) (b : Nat) : FE := ⟨M.k b, M.k (b + 1), M.k (b + 2)⟩

/-- An affine `K` operand of a one-dimensional loop. -/
def kOp (b s : Nat) : Opd := .abs ⟨.K, b, [s]⟩

/-- Load the `E` scalar in `K` cells `b + s·j + (0, 1, 2)` at iteration `j`. -/
def ldRow (b s : Nat) : LRow := ⟨.loadE, .E, [kOp b s, kOp (b + 1) s, kOp (b + 2) s]⟩

theorem ldRow_val {c : Ctx} {M : Mem} {d : Nat} {tpl : List LRow} {p : Ptr} {jf t : Nat}
    (hA : AllE tpl) (hjf : jf < 2 ^ d) (ht : t < tpl.length) {b s : Nat}
    (hr : tpl.getD t default = ldRow b s) (h : LRel c M (loop [d] tpl p).1 jf t) :
    M.e (p.e + t + tpl.length * jf) = kE M (b + s * jf) := by
  have := lrel_loadE h (x := kOp b s) (y := kOp (b + 1) s) (z := kOp (b + 2) s) (τ := .E) hr
  rw [cell1 hA ht] at this
  rw [this]
  simp only [kOp, val1_absK hjf, kE]
  rw [loadE_eq]
  congr 2 <;> ring

theorem rowEq_ld {M : Mem} {p : Ptr} {L jf t b s : Nat} (h : RowEq M p L jf t (ldRow b s)) :
    M.e (p.e + t + L * jf) = kE M (b + s * jf) := by
  simp only [RowEq, ldRow, kOp, ov, Addr.at, dot, Nat.add_zero, Mem.rd] at h
  rw [h, loadE_eq]
  simp only [kE]
  congr 2 <;> ring

theorem kE_lanes {M : Mem} {sig : ByteArray} {b : Nat} (h : ∀ j < 3, M.k (b + j) = lane sig (b + j)) :
    kE M b = feAt sig (8 * b) := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [kE, h0, h1, h2, feAt, lane]
  rw [show 8 * (b + 1) = 8 * b + 8 by ring, show 8 * (b + 2) = 8 * b + 16 by ring]

/-! ## Runs of loops over consecutive rounds -/

/-- Rounds in a run of chunks of `2^d` rounds. -/
def nRounds (ds : List Nat) : Nat := (ds.map (2 ^ ·)).sum

/-- **One loop per chunk** of `2^d` rounds, the template of the chunk starting at round `i₀` being
`tplOf i₀` (all of them all-`E` of one width: the chunks' cells are contiguous). -/
def runLoops (tplOf : Nat → List LRow) : List Nat → Nat → BM Unit
  | [], _ => pure ()
  | d :: ds, i₀ => do
    let _ ← loop [d] (tplOf i₀)
    runLoops tplOf ds (i₀ + 2 ^ d)

theorem loop1_adv (d : Nat) (tpl : List LRow) (p : Ptr) (hA : AllE tpl) :
    p.adv (loop [d] tpl p).2 = ⟨p.k, p.e + tpl.length * 2 ^ d⟩ := by
  have h1 := mkLoop_tw p [d] tpl .K
  have h2 := mkLoop_tw p [d] tpl .E
  rw [(ltw_allE hA).2] at h1
  rw [(ltw_allE hA).1] at h2
  simp only [loop_apply, Ptr.adv, segsW, Seg.w, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, h1, h2, Nat.zero_mul, Block.size, Block.lsize]
  simp [mkLoop]

/-- The chunks of a run: (first round, log size). -/
def chunkStarts : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | d :: ds, i₀ => (i₀, d) :: chunkStarts ds (i₀ + 2 ^ d)

/-- **A law of the template at every round of the run.** If every chunk's loop satisfies
`Law (cell base of iteration jf) (round i₀ + jf)` (from its rows), so does the run, at round `i`
with base `p.e + L·i`. The run ends `L·n` `E` cells later. -/
theorem runLoops_law {c : Ctx} {M : Mem} (tplOf : Nat → List LRow) (L : Nat)
    (hL : ∀ i, AllE (tplOf i) ∧ (tplOf i).length = L) (Law : Nat → Nat → Prop) (lb : Nat) :
    ∀ (ds : List Nat) (i₀ : Nat) (p : Ptr),
    (∀ (p' : Ptr) (i d : Nat), (i, d) ∈ chunkStarts ds i₀ → lb ≤ p'.e →
      SegsHold c M p' (loop [d] (tplOf i) p').2 → ∀ jf < 2 ^ d, Law (p'.e + L * jf) (i + jf)) →
    lb ≤ p.e → SegsHold c M p (runLoops tplOf ds i₀ p).2 →
      (∀ i < nRounds ds, Law (p.e + L * i) (i₀ + i)) ∧
        p.adv (runLoops tplOf ds i₀ p).2 = ⟨p.k, p.e + L * nRounds ds⟩
  | [], i₀, p, _, _, _ => by
    refine ⟨fun i hi => by simp [nRounds] at hi, ?_⟩
    show p.adv [] = _
    simp [nRounds]
  | d :: ds, i₀, p, hlaw, hp, h => by
    have happ : runLoops tplOf (d :: ds) i₀ p =
        (loop [d] (tplOf i₀) >>= fun _ => runLoops tplOf ds (i₀ + 2 ^ d)) p := rfl
    rw [happ, hold_bind] at h
    rw [happ, bind_apply, Ptr.adv_append]
    have hadv := loop1_adv d (tplOf i₀) p (hL i₀).1
    rw [(hL i₀).2] at hadv
    rw [hadv] at h ⊢
    obtain ⟨ih1, ih2⟩ := runLoops_law tplOf L hL Law lb ds (i₀ + 2 ^ d) _
      (fun p' i d' hm => hlaw p' i d' (by simp [chunkStarts, hm])) (by simp; omega) h.2
    refine ⟨fun i hi => ?_, ?_⟩
    · by_cases hi' : i < 2 ^ d
      · exact hlaw p i₀ d (by simp [chunkStarts]) hp h.1 i hi'
      · have := ih1 (i - 2 ^ d) (by simp [nRounds] at hi ⊢; omega)
        simp only at this
        rw [show p.e + L * 2 ^ d + L * (i - 2 ^ d) = p.e + L * i by
            rw [Nat.add_assoc, ← Nat.mul_add]; congr 2; omega,
          show i₀ + 2 ^ d + (i - 2 ^ d) = i₀ + i by omega] at this
        exact this
    · rw [ih2]; simp only [nRounds, List.map_cons, List.sum_cons, Ptr.mk.injEq, true_and]
      ring

/-- A chain of cells `E (b + L·(i+1)) = step (E (b + L·i)) (rnd i)` is the fold. -/
theorem chain_fold (E : Nat → FE) (b L : Nat) (rnd : Nat → Option FE × List FE × FE) (n : Nat)
    (h : ∀ i < n, E (b + L * (i + 1)) = rstep (E (b + L * i)) (rnd i)) :
    E (b + L * n) = scFold (E b) ((List.range n).map rnd) := by
  induction n with
  | zero => simp [scFold]
  | succ n ih =>
    rw [scFold_range_succ, ← ih (fun i hi => h i (by omega)), h n (by omega)]

theorem linE_adv (k k' : FK) (a b : Cell) (p : Ptr) : p.adv (lin .E k k' a b p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [Ptr.adv, segsW, Seg.w, Row.w, Row.writes, lin, rowRes]

/-- A loop of an all-`E` template asserts nothing. -/
theorem loop_noassert {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr} (hA : AllE tpl) :
    SegsAssert M p (loop dims tpl p).2 := by
  simp only [loop_apply, SegsAssert, and_true]
  intro jf _ t ht
  have ht' : t < tpl.length := by simpa [mkLoop] using ht
  have hmem : tpl.getD t default ∈ tpl := by
    rw [List.getD_eq_getElem _ _ ht']; exact List.getElem_mem ht'
  have hop := (hA _ hmem).2
  unfold Program.RowAssert
  simp only [instAt, mkLoop_row, resRow]

theorem runLoops_noassert {M : Mem} (tplOf : Nat → List LRow) (hA : ∀ i, AllE (tplOf i)) :
    ∀ (ds : List Nat) (i₀ : Nat) (p : Ptr), SegsAssert M p (runLoops tplOf ds i₀ p).2
  | [], _, _ => trivial
  | d :: ds, i₀, p => by
    have happ : runLoops tplOf (d :: ds) i₀ p =
        (loop [d] (tplOf i₀) >>= fun _ => runLoops tplOf ds (i₀ + 2 ^ d)) p := rfl
    rw [happ, assert_bind]
    exact ⟨loop_noassert (hA i₀), runLoops_noassert tplOf hA ds _ _⟩

/-! ## Straight-line gadgets: values and assertions (a Hoare-style spec) -/

/-- **The spec of a gadget**: wherever its rows hold, `P` of its output, and its assertions hold
iff `A` (a fact about the inputs' values). -/
def ASpec {α : Type} (c : Ctx) (M : Mem) (g : BM α) (P : α → Prop) (A : Prop) : Prop :=
  ∀ p, SegsHold c M p (g p).2 → P (g p).1 ∧ (SegsAssert M p (g p).2 ↔ A)

section
variable {c : Ctx} {M : Mem}

theorem aspec_bind {α β : Type} {m : BM α} {f : α → BM β} {P : α → Prop} {Q : β → Prop} {A B : Prop}
    (hm : ASpec c M m P A) (hf : ∀ x, P x → ASpec c M (f x) Q B) : ASpec c M (m >>= f) Q (A ∧ B) := by
  intro p h
  rw [hold_bind] at h
  obtain ⟨h1, h2⟩ := hm p h.1
  obtain ⟨h3, h4⟩ := hf _ h1 _ h.2
  refine ⟨by rw [bind_apply]; exact h3, ?_⟩
  rw [assert_bind, h2, h4]

theorem aspec_pure {α : Type} {x : α} {P : α → Prop} (h : P x) : ASpec c M (pure x) P True :=
  fun _ _ => ⟨h, iff_of_true trivial trivial⟩

theorem aspec_congr {α : Type} {g : BM α} {P Q : α → Prop} {A B : Prop} (h : ASpec c M g P A)
    (hPQ : ∀ x, P x → Q x) (hAB : A ↔ B) : ASpec c M g Q B :=
  fun p hp => ⟨hPQ _ (h p hp).1, (h p hp).2.trans hAB⟩

theorem aspec_mulAdd (τ : Ty) (a b d : Cell) :
    ASpec c M (mulAdd τ a b d) (fun r => r.val M = a.val M * b.val M + d.val M) True :=
  fun _ h => ⟨mulAdd_spec h, iff_of_true (by simp [mulAdd, rowRes, SegsAssert, Program.RowAssert,
    rowInst]) trivial⟩

theorem aspec_lin (τ : Ty) (k k' : FK) (a b : Cell) :
    ASpec c M (lin τ k k' a b) (fun r => r.val M = a.val M + FE.ofK k * b.val M + FE.ofK k') True :=
  fun _ h => ⟨lin_spec h, iff_of_true (by simp [lin, rowRes, SegsAssert, Program.RowAssert,
    rowInst]) trivial⟩

theorem aspec_assert0 (a g : Cell) :
    ASpec c M (assert0 a g) (fun _ => True) (g.val M * a.val M = 0) := by
  intro p _
  refine ⟨trivial, ?_⟩
  have e : SegsAssert M p (assert0 a g p).2 ↔ Program.RowAssert M (rowInst p ⟨.assert0, .K, [a.addr, g.addr]⟩) :=
    segsAssert_row
  rw [e]
  show M.arg (rowInst p ⟨.assert0, .K, [a.addr, g.addr]⟩) 1 *
      M.arg (rowInst p ⟨.assert0, .K, [a.addr, g.addr]⟩) 0 = 0 ↔ _
  rw [rowInst_arg, rowInst_arg]
  rfl

/-- In characteristic 2, `a + b = 0` iff `a = b`. -/
theorem add_eq_zero_iff' (a b : FE) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this
  · rintro rfl; exact CharTwo.add_self_eq_zero a

/-- **`assertEq a b gate`**: its assertion is `gate · (a + b) = 0`. -/
theorem aspec_assertEq (a b g : Cell) :
    ASpec c M (assertEq a b g) (fun _ => True) (g.val M * (a.val M + b.val M) = 0) := by
  have := aspec_bind (c := c) (M := M) (aspec_lin (jn a.ty b.ty) 1 0 a b)
    (fun d hd => aspec_congr (aspec_assert0 d g) (fun _ _ => trivial)
      (B := g.val M * (a.val M + b.val M) = 0) (by rw [hd, ofK_one, ofK_zero, one_mul, add_zero]))
  exact aspec_congr this (fun _ _ => trivial) (by rw [true_and])

/-- With the gate on, `assertEq` is equality. -/
theorem gate_eq_iff {g : FE} (hg : g = 1) (a b : FE) : g * (a + b) = 0 ↔ a = b := by
  rw [hg, one_mul, add_eq_zero_iff']

end

end Lvm.Loop.Build.QB
