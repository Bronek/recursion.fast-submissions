-- New for lvm (WP-14a): the shape of a verifier-language program against V_S's schedule (the
-- query correspondence's static half): the schedule's items as atoms, and `Fol`, "the program's
-- events follow these atoms".
import LvmVEqCore
import LvmVCore

/-!
# A program follows the schedule (`Fol`)

The schedule (`LvmSchedule.schedule`) as **atoms** (`atomsOf`): `read m` is `m` scalar atoms
(`rd`), `cap c r` one cap atom, `sample` one FS sample (`sm`), `positions r` a marker (`pclr`, the
driver empties its position list) and `⌈t/8⌉` position samples (`ps h n`: one answer, `n`
positions of `h` bits), `opening r` one opening atom (`op r`).

**`Fol cap shp idx P as pp Q`**: every run of the program `P` meets the atoms `as` in order and
then returns `a` with `Q a pp'`: a `read` meets `rd`, a `sample` meets `sm` or `ps h n` (whose
positions, the chunk of the challenge's bits, are appended to the pending positions `pp`), a
`commit ht w` meets `cap c r` with `c = cap ht w` and `shp (idx r) = (ht, w)` (the commitment's
index and shape as the compiled verifier records them), a `query i ps` meets `op r` with
`i = idx r` and `ps = pp` (the program opens exactly the positions its position samples gave);
`fail` follows anything (a failing run never accepts). `Fol.bind` composes.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- An atom of the schedule. -/
inductive Atom where
  /-- One `E` scalar. -/
  | rd
  /-- The cap (`2^c` nodes) of the oracle `r`. -/
  | cap (c : ℕ) (r : Ref)
  /-- One Fiat–Shamir sample. -/
  | sm
  /-- The start of a positions item. -/
  | pclr
  /-- One positions sample: `n` positions of `h` bits. -/
  | ps (h n : ℕ)
  /-- The openings of the oracle `r`. -/
  | op (r : Ref)
  deriving DecidableEq, Repr, Inhabited

/-- The positions an answer's challenge bits give: `n` fields of `h` bits, low first. -/
def chunk (h n bits : ℕ) : List ℕ := (List.range n).map fun j ↦ (bits >>> (j * h)) % 2 ^ h

/-- The position samples of `rem` positions in `n` answers, 8 per answer. -/
def posAtoms (h : ℕ) : ℕ → ℕ → List Atom
  | 0, _ => []
  | n + 1, rem => .ps h (min positionsPerAnswer rem) :: posAtoms h n (rem - min positionsPerAnswer rem)

/-- The atoms of an item. -/
def itemAtoms (p : Params) : Item → List Atom
  | .read m => List.replicate m .rd
  | .cap c r => [.cap c r]
  | .sample => [.sm]
  | .positions r => .pclr :: posAtoms (p.level r).height (p.level r).nPosQ (p.level r).t
  | .opening r => [.op r]

/-- The atoms of a list of items. -/
def atomsOf (p : Params) (its : List Item) : List Atom := its.flatMap (itemAtoms p)

@[simp] theorem atomsOf_nil (p : Params) : atomsOf p [] = [] := rfl

theorem atomsOf_append (p : Params) (a b : List Item) :
    atomsOf p (a ++ b) = atomsOf p a ++ atomsOf p b := by
  simp [atomsOf]

theorem atomsOf_cons (p : Params) (it : Item) (its : List Item) :
    atomsOf p (it :: its) = itemAtoms p it ++ atomsOf p its := by
  simp [atomsOf]

section Fol

variable (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (idx : Ref → ℕ)

/-- **The program's events follow the atoms**, then it returns `a` with `Q a pp'`. -/
def Fol {α : Type} : VerifierProgram α → List Atom → List ℕ → (α → List ℕ → Prop) → Prop
  | P, .pclr :: as, _, Q => Fol P as [] Q
  | .fail, _, _, _ => True
  | .ret a, [], pp, Q => Q a pp
  | .read k, .rd :: as, pp, Q => ∀ y, Fol (k y) as pp Q
  | .sample k, .sm :: as, pp, Q => ∀ y, Fol (k y) as pp Q
  | .sample k, .ps h n :: as, pp, Q =>
    ∀ y, Fol (k y) as (pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat y)) Q
  | .commit ht w k, .cap c r :: as, pp, Q => cap ht w = c ∧ shp (idx r) = (ht, w) ∧ Fol k as pp Q
  | .query i ps k, .op r :: as, pp, Q => i = idx r ∧ ps = pp ∧ ∀ rows, Fol (k rows) as pp Q
  | _, _, _, _ => False

variable {cap shp idx}

@[simp] theorem fol_fail {α : Type} (as : List Atom) (pp : List ℕ) (Q : α → List ℕ → Prop) :
    Fol cap shp idx VerifierProgram.fail as pp Q := by
  induction as generalizing pp with
  | nil => trivial
  | cons a as ih => cases a <;> first | trivial | exact ih []

@[simp] theorem fol_ret_nil {α : Type} (a : α) (pp : List ℕ) (Q : α → List ℕ → Prop) :
    Fol cap shp idx (.ret a) [] pp Q ↔ Q a pp := Iff.rfl

theorem fol_pclr {α : Type} (P : VerifierProgram α) (as : List Atom) (pp : List ℕ)
    (Q : α → List ℕ → Prop) : Fol cap shp idx P (.pclr :: as) pp Q ↔ Fol cap shp idx P as [] Q := by
  cases P <;> rfl

theorem Fol.mono {α : Type} {P : VerifierProgram α} {as : List Atom} {pp : List ℕ}
    {Q Q' : α → List ℕ → Prop} (h : Fol cap shp idx P as pp Q) (hQ : ∀ a pp', Q a pp' → Q' a pp') :
    Fol cap shp idx P as pp Q' := by
  induction as generalizing P pp with
  | nil =>
    cases P with
    | ret a => exact hQ _ _ h
    | fail => trivial
    | _ => exact h.elim
  | cons x as ih =>
    cases x with
    | pclr => rw [fol_pclr] at h ⊢; exact ih h
    | rd => cases P <;> first | trivial | exact h.elim | exact fun y ↦ ih (h y)
    | sm => cases P <;> first | trivial | exact h.elim | exact fun y ↦ ih (h y)
    | ps hh n => cases P <;> first | trivial | exact h.elim | exact fun y ↦ ih (h y)
    | cap c r =>
      cases P with
      | commit ht w k => exact ⟨h.1, h.2.1, ih h.2.2⟩
      | fail => trivial
      | _ => exact h.elim
    | op r =>
      cases P with
      | query i ps k => exact ⟨h.1, h.2.1, fun rows ↦ ih (h.2.2 rows)⟩
      | fail => trivial
      | _ => exact h.elim

/-- **Composition.** -/
theorem Fol.bind {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β}
    {as bs : List Atom} {pp : List ℕ} {Q : β → List ℕ → Prop}
    (h : Fol cap shp idx P as pp fun a pp' ↦ Fol cap shp idx (f a) bs pp' Q) :
    Fol cap shp idx (P.bind f) (as ++ bs) pp Q := by
  induction as generalizing P pp with
  | nil =>
    cases P with
    | ret a => exact h
    | fail => exact fol_fail _ _ _
    | _ => exact h.elim
  | cons x as ih =>
    cases x with
    | pclr => rw [List.cons_append, fol_pclr]; rw [fol_pclr] at h; exact ih h
    | rd => cases P <;> first | exact fol_fail _ _ _ | exact h.elim | exact fun y ↦ ih (h y)
    | sm => cases P <;> first | exact fol_fail _ _ _ | exact h.elim | exact fun y ↦ ih (h y)
    | ps hh n => cases P <;> first | exact fol_fail _ _ _ | exact h.elim | exact fun y ↦ ih (h y)
    | cap c r =>
      cases P with
      | commit ht w k => exact ⟨h.1, h.2.1, ih h.2.2⟩
      | fail => exact fol_fail _ _ _
      | _ => exact h.elim
    | op r =>
      cases P with
      | query i ps k => exact ⟨h.1, h.2.1, fun rows ↦ ih (h.2.2 rows)⟩
      | fail => exact fol_fail _ _ _
      | _ => exact h.elim

/-! ## The primitives -/

theorem fol_readScalars (n : ℕ) (pp : List ℕ) :
    Fol cap shp idx (VerifierProgram.readScalars n) (List.replicate n .rd) pp
      fun xs pp' ↦ xs.length = n ∧ pp' = pp := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro y
    have := Fol.bind (bs := []) (f := fun xs ↦ VerifierProgram.ret (y :: xs)) (Q := fun xs pp' ↦
      xs.length = n + 1 ∧ pp' = pp) (ih.mono fun xs pp' h ↦ by simp [h.1, h.2])
    simpa using this

theorem fol_sampleChallenges (n : ℕ) (pp : List ℕ) :
    Fol cap shp idx (VerifierProgram.sampleChallenges n) (List.replicate n .sm) pp
      fun xs pp' ↦ xs.length = n ∧ pp' = pp := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro y
    have := Fol.bind (bs := []) (f := fun xs ↦ VerifierProgram.ret (y :: xs)) (Q := fun xs pp' ↦
      xs.length = n + 1 ∧ pp' = pp) (ih.mono fun xs pp' h ↦ by simp [h.1, h.2])
    simpa using this

theorem fol_require (c : Prop) [Decidable c] (pp : List ℕ) :
    Fol cap shp idx (VerifierProgram.require c) [] pp fun _ pp' ↦ pp' = pp := by
  unfold VerifierProgram.require
  split
  · rfl
  · trivial

end Fol

end Lvm.VEq
