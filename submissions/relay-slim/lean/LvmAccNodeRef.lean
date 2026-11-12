-- New for lvm (AC-N, A23): refinement of a native step under a promise on its value (`RefAtP`),
-- for the accumulator check that the native `F` runs after the whole program (`decideF`: `AccOk` of
-- `decideProg`'s value) and the verifier language runs right after phase 3b (`require` of the folded
-- claim). Extends WP-14a's `RefAt` (LvmVEqCore); the bind rule is `RefAt.bind`'s proof.
import LvmVEqCore

/-!
# Refinement under a promise

**`RefAtP sig d P R Q`**: wherever the native step `d` ends with every check held *and its value
satisfies `Q`*, the program `P` read off the stream returns a value related by `R` at the same
cursor. `RefAt` is `RefAtP` with `Q = True` (`RefAt.toP`, `RefAtP.toRefAt`).

* `RefAtP.bind`: composition, the promise on the continuation's value pulled back to the first
  step's (`hQ`: e.g. a continuation that returns the first step's value);
* `RefAtP.require_ret`: a language `require` justified by the promise, against a native `pure`;
  `RefAtP.read_left`: reading the stream.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile

section Ref

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)

/-- **`d` refines `P` under the promise `Q` on `d`'s value.** -/
def RefAtP {α β : Type} (sig : ByteArray) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (Q : β → Prop) : Prop :=
  ∀ s, (runD d sig s).2.ok = true → Q (runD d sig s).1 →
    ∃ a, (ivp cap occ shp P sig s).1 = some a ∧ (ivp cap occ shp P sig s).2.ent = (runD d sig s).2.ent ∧
      (ivp cap occ shp P sig s).2.msg = (runD d sig s).2.msg ∧ R (runD d sig s).1 a

variable {cap occ shp} {sig : ByteArray}

theorem RefAt.toP {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAt cap occ shp sig d P R) (Q : β → Prop) : RefAtP cap occ shp sig d P R Q :=
  fun s hok _ ↦ h s hok

theorem RefAtP.toRefAt {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {Q : β → Prop} (h : RefAtP cap occ shp sig d P R Q) (hQ : ∀ b, Q b) : RefAt cap occ shp sig d P R :=
  fun s hok ↦ h s hok (hQ _)

theorem RefAtP.mono {α β : Type} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    {Q : β → Prop} (h : RefAtP cap occ shp sig d P R Q) (hR : ∀ b a, R b a → R' b a) :
    RefAtP cap occ shp sig d P R' Q :=
  fun s hok hq ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok hq
    exact ⟨a, h1, h2, h3, hR _ _ h4⟩

/-- **Composition under a promise**: the continuation's promise implies the first step's. -/
theorem RefAtP.bind {α α' β β' : Type} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop} {Q : β → Prop}
    {Q' : β' → Prop} (hm : ∀ b, MonoD (d' b)) (h : RefAtP cap occ shp sig d P R Q)
    (hQ : ∀ b s, Q' (runD (d' b) sig s).1 → Q b)
    (h' : ∀ b a, R b a → Q b → RefAtP cap occ shp sig (d' b) (P' a) R' Q') :
    RefAtP cap occ shp sig (d >>= d') (P.bind P') R' Q' := by
  intro s hok hq
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok hq ⊢
  have hq1 := hQ _ _ hq
  obtain ⟨a, ha, he, hmsg, hR⟩ := h s (hm _ sig _ hok) hq1
  obtain ⟨a', ha', he', hm', hR'⟩ := h' _ _ hR hq1 _ hok hq
  refine ⟨a', ?_⟩
  rw [ivp_bind]
  rcases hP : ivp cap occ shp P sig s with ⟨_ | a₀, s₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg
    simp only [Option.some.injEq] at ha
    subst ha
    obtain ⟨c1, c2, c3⟩ := ivp_congr (cap := cap) (occ := occ) (shp := shp) (P' a₀) sig he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', hR'⟩

/-- **A language `require` justified by the promise** on the native value. -/
theorem RefAtP.require_ret {α β : Type} {b : β} {a : α} {q : Prop} [Decidable q] {R : β → α → Prop}
    {Q : β → Prop} (hq : Q b → q) (hR : R b a) :
    RefAtP cap occ shp sig (Pure.pure b : DM β) ((VerifierProgram.require q).bind fun _ ↦ VerifierProgram.ret a)
      R Q := by
  intro s _ hQ
  have e : (VerifierProgram.require q).bind (fun _ ↦ VerifierProgram.ret a) = VerifierProgram.ret a := by
    simp only [VerifierProgram.require, hq hQ, ↓reduceIte]; rfl
  rw [e]
  exact ⟨a, rfl, rfl, rfl, hR⟩

/-- Reading the stream itself, then the rest (under a promise). -/
theorem RefAtP.read_left {α β : Type} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAtP cap occ shp sig (d sig) P R Q) :
    RefAtP cap occ shp sig (MonadReader.read >>= d) P R Q :=
  fun s hok hq ↦ h s hok hq

theorem runD_bind_pure {β γ : Type} (d : DM β) (a : γ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun _ ↦ Pure.pure a) sig s).1 = a := rfl

theorem runD_bind_pure_snd {β γ δ : Type} (d : DM β) (f : β → γ) (a : δ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun k ↦ Pure.pure (f k, a)) sig s).1.2 = a := rfl

end Ref

end Lvm.VEq
