-- New for lvm (WP-14a): the stream `Σ = traceBytesB tr` entry by entry, the compiled verifier's run
-- in continuation form, and the static schedule check of the simulation.
import LvmVEqDrive
import LvmVEqRel
import RecursionFast.Library.Trace

/-!
# The stream, the compiled run in continuation form, the static check

* `entOff tr i`: the byte offset of entry `i` in `Σ = traceBytesB tr`; `stream_entry`: entry
  `i = (q, a)` sits there as `enc64 |q| ‖ q ‖ a` (its query's bytes at `+ 8`, its answer after
  the query, the next entry after the answer).
* `runK S P st buf caps body kS`: WP-5's compiled run `S.run` with a continuation (`run_eq_runK`).
* `stA p as pend cr hs`: the static facts the simulation needs of the schedule's atoms (FS queries
  within `queryCap`, nothing pending at an opening, caps in `idxS` order, each opening's level
  geometry = P20's commitment table, its positions of the commitment's height). Decided at P20
  (`LvmVEqStatic`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Protocol.Compile

/-! ## The stream -/

/-- The bytes of a byte array, as a list. -/
abbrev blb (b : ByteArray) : List UInt8 := b.data.toList

/-- The offset of entry `i` in `Σ`. -/
def entOff (tr : Trace) (i : ℕ) : ℕ := 1 + (traceBytes (tr.take i)).length

theorem traceBytes_append (A B : Trace) : traceBytes (A ++ B) = traceBytes A ++ traceBytes B := by
  simp only [traceBytes, List.flatMap_append]

theorem stream_split {tr : Trace} {i : ℕ} {q : ByteArray} {a : Digest} {rest : Trace}
    (h : tr.drop i = (q, a) :: rest) :
    blb (traceBytesB tr) = (tagTrace :: traceBytes (tr.take i)) ++
      (enc64 q.size ++ (blb q ++ (a.toList ++ traceBytes rest))) := by
  rw [blb, traceBytesB_data]
  conv_lhs => rw [← List.take_append_drop i tr, h]
  rw [traceBytes_append, traceBytes_cons]
  simp only [List.cons_append, List.append_assoc]

theorem length_enc64 (n : ℕ) : (enc64 n).length = 8 := by simp [enc64]

theorem drop_app_len {A B : List UInt8} {k : ℕ} (h : A.length = k) (t : ℕ) :
    (A ++ B).drop (k + t) = B.drop t := by
  subst h
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), Nat.add_sub_cancel_left, List.nil_append]

theorem entOff_eq (tr : Trace) (i : ℕ) : entOff tr i = (tagTrace :: traceBytes (tr.take i)).length := by
  simp [entOff]; omega

/-- **Entry `i` in the stream.** -/
theorem stream_entry {tr : Trace} {i : ℕ} {q : ByteArray} {a : Digest} {rest : Trace}
    (h : tr.drop i = (q, a) :: rest) :
    (∀ t n, t + n ≤ q.size → sbs (traceBytesB tr) (entOff tr i + 8 + t) n = ((blb q).drop t).take n) ∧
      digestAt (traceBytesB tr) (entOff tr i + 8 + q.size) = a ∧
      entOff tr (i + 1) = entOff tr i + 8 + q.size + 32 := by
  have hs := stream_split h
  have hq : (blb q).length = q.size := by simp only [blb, Array.length_toList]; rfl
  have hM : ∀ t, (blb (traceBytesB tr)).drop (entOff tr i + 8 + t) = (blb q ++ (a.toList ++ traceBytes rest)).drop t := by
    intro t
    rw [hs, Nat.add_assoc, drop_app_len (entOff_eq tr i).symm, drop_app_len (length_enc64 _)]
  refine ⟨fun t n htn ↦ ?_, ?_, ?_⟩
  · unfold sbs
    rw [show (traceBytesB tr).data.toList = blb (traceBytesB tr) from rfl, hM,
      List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply Vector.ext
    intro j hj
    simp only [digestAt, Vector.getElem_ofFn, ByteArray.get!, getElem!_def]
    have e1 : (traceBytesB tr).data[entOff tr i + 8 + q.size + j]? =
        ((blb (traceBytesB tr)).drop (entOff tr i + 8 + (q.size + j)))[0]? := by
      rw [List.getElem?_drop]; simp [blb, Nat.add_assoc]
    rw [e1, hM, ← hq, drop_app_len rfl, List.getElem?_drop, Nat.add_zero,
      List.getElem?_append_left (by simp [hj])]
    simp [hj]
  · simp only [entOff]
    have hi : tr[i]? = some (q, a) := by
      rw [← List.head?_drop, h]; rfl
    rw [List.take_add_one, hi, Option.toList_some, traceBytes_append, traceBytes_cons]
    simp only [traceBytes_nil, List.append_nil, List.length_append, length_enc64, hq,
      Vector.length_toList]
    omega

/-! ## The compiled run with a continuation -/

section RunK

variable (S : Scheme)

/-- **WP-5's compiled run (`Scheme.run`) with a continuation.** -/
def runK {α : Type} : VerifierProgram α → Digest → List UInt8 → List CapI → List UInt8 →
    (α → Digest → List UInt8 → List CapI → List UInt8 → OProg Bool) → OProg Bool
  | .ret a, st, buf, caps, body, kS => kS a st buf caps body
  | .fail, _, _, _, _, _ => .ret false
  | .grind _ _, _, _, _, _, _ => .ret false
  | .read k, st, buf, caps, body, kS =>
    if body.length < 24 then .ret false else
    runK (k (S.decE (body.take 24))) st (buf ++ body.take 24) caps (body.drop 24) kS
  | .sample k, st, buf, caps, body, kS =>
    if 32 + buf.length ≤ queryCap then
      .query (toQ (st.toList ++ buf)) fun a => runK (k (S.chal a)) a [] caps body kS
    else .ret false
  | .commit ht w k, st, buf, caps, body, kS =>
    if body.length < S.capBytes ht w then .ret false else
    runK k st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
      (body.drop (S.capBytes ht w)) kS
  | .query i ps k, st, buf, caps, body, kS =>
    match caps[i]? with
    | none => .ret false
    | some ci => (S.openAll ci ps body).bind fun
      | some (rows, rest) => runK (k rows) st buf caps rest kS
      | none => .ret false

/-- `S.run` is `runK` with the acceptance continuation. -/
theorem run_eq_runK : ∀ (P : VerifierProgram Bool) (st : Digest) (buf : List UInt8) (caps : List CapI)
    (body : List UInt8), S.run P st buf caps body =
      runK S P st buf caps body fun b _ _ _ body ↦ .ret (b && body.isEmpty)
  | .ret b, _, _, _, _ => rfl
  | .fail, _, _, _, _ => rfl
  | .grind _ _, _, _, _, _ => rfl
  | .read k, st, buf, caps, body => by
    simp only [Scheme.run, runK]
    split
    · rfl
    · exact run_eq_runK _ _ _ _ _
  | .sample k, st, buf, caps, body => by
    simp only [Scheme.run, runK]
    split
    · congr 1; funext a; exact run_eq_runK _ _ _ _ _
    · rfl
  | .commit ht w k, st, buf, caps, body => by
    simp only [Scheme.run, runK]
    split
    · rfl
    · exact run_eq_runK _ _ _ _ _
  | .query i ps k, st, buf, caps, body => by
    simp only [Scheme.run, runK]
    cases caps[i]? with
    | none => rfl
    | some ci =>
      simp only
      congr 1; funext o
      rcases o with _ | ⟨rows, rest⟩
      · rfl
      · exact run_eq_runK _ _ _ _ _

end RunK

/-! ## The static check -/

/-- An opening's level geometry is P20's commitment table. -/
def geomOk (p : Params) (r : Ref) : Bool :=
  let sh := shpS (idxS r)
  (p.level r).height == sh.1 && (p.level r).row == 8 * sh.2 &&
    (p.level r).path == sh.1 - capS sh.1 sh.2

/-- **The static facts of the atoms** (pending bytes `pend`, committed oracles `cr` in order, the
heights `hs` of the position samples since the last positions marker). -/
def stA (p : Params) : List Atom → ℕ → List Ref → List ℕ → Bool
  | [], pend, _, _ => pend == 0
  | .rd :: as, pend, cr, hs => stA p as (pend + eBytes) cr hs
  | .cap c r :: as, pend, cr, hs =>
    (idxS r == cr.length) && !(cr.contains r) && stA p as (pend + nodeBytes * 2 ^ c) (cr ++ [r]) hs
  | .sm :: as, pend, cr, hs => decide (32 + pend ≤ queryCap) && stA p as 0 cr hs
  | .pclr :: as, pend, cr, _ => stA p as pend cr []
  | .ps h _ :: as, pend, cr, hs => decide (32 + pend ≤ queryCap) && stA p as 0 cr (h :: hs)
  | .op r :: as, pend, cr, hs =>
    (pend == 0) && cr.contains r && geomOk p r && hs.all (· == (shpS (idxS r)).1) &&
      stA p as 0 cr hs

end Lvm.VEq
