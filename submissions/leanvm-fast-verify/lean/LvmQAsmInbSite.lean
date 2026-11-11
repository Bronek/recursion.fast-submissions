-- New for lvm (INB): one lemma per kind of `readd` site, so a new site (Q_arith's remaining phases,
-- Q_acc, A23) costs one instance. Builds on WP-11b-QL's `gpowBits_spec` (`LvmQBuildLemmas`).
import LvmQAsmInbCore

/-!
# `readd` sites: the generic lemmas

* `readd_in`: a straight-line `readd τ lo m α` is in region iff its address cell is `g^(lo + k)`,
  `k < 2^m`; `readd_in_gpow`: from `α = g^e`, `lo ≤ e < lo + 2^m`.
* **`gpowBits_in`**: an address from bit cells, `gpowBits lo s x bs` (WP-11b-QL), lies in
  `[lo, lo + s·(2^|bs| − 1)]` when the bits are bits (`bitsNat_lt`); `gpowBits_noReadd`: the
  address chain itself has no `readd`.
* **`readdBits` / `readdBits_in`**: the pattern "address from bits, then read" as one gadget, in
  region when `rlo ≤ lo` and `lo + s·(2^|bs| − 1) < rlo + 2^m`.
* Loop sites: `Build.loop_in` (`LvmQAsmInbCore`), instances `qltLoop_in`, `capLoop_in`
  (`LvmQAsmInbLink`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

theorem bitsNat_lt (M : Mem) : ∀ bs : List Cell, bitsNat M bs < 2 ^ bs.length
  | [] => by simp [bitsNat]
  | _ :: bs => by
    have := bitsNat_lt M bs
    simp only [bitsNat, List.length_cons, Nat.pow_succ]
    split <;> omega

/-- **A straight-line `readd`'s region condition** is its address cell's. -/
theorem readd_in {M : Mem} {p : Ptr} {τ : Ty} {lo m : Nat} {α : Cell}
    (h : ∃ k < 2 ^ m, FK.x ^ (lo + k) = (α.val M).c₀) : SegsIn M p (readd τ lo m α p).2 := by
  refine ⟨?_, trivial⟩
  show ∃ k < 2 ^ m, FK.x ^ (lo + k) = (M.arg (rowInst p ⟨.readd lo m, τ, [α.addr]⟩) 0).c₀
  rw [rowInst_arg]
  exact h

theorem readd_in_gpow {M : Mem} {p : Ptr} {τ : Ty} {lo m e : Nat} {α : Cell}
    (hα : α.ty = .K) (hv : M.k α.n = gpow e) (h1 : lo ≤ e) (h2 : e < lo + 2 ^ m) :
    SegsIn M p (readd τ lo m α p).2 := by
  refine readd_in ⟨e - lo, by omega, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, α = kc n := ⟨α.n, by cases α; simp_all [kc]⟩
  rw [show lo + (e - lo) = e by omega]
  simp only [Cell.val_K] at hv ⊢
  rw [hv]; rfl

theorem gpowBitsGo_noReadd (s : Nat) : ∀ (k : Nat) (acc : Cell) (bs : List Cell) (p : Ptr),
    noReaddSegs (gpowBits.gpowBitsGo s k acc bs p).2 = true
  | _, _, [], _ => rfl
  | k, acc, β :: bs, p => by
    rw [gpowBitsGo_cons]
    simp only [List.cons_append, List.nil_append, noReaddSegs, rowNoRd, Bool.true_and]
    exact gpowBitsGo_noReadd s _ _ bs _

/-- The address chain has no `readd`. -/
theorem gpowBits_noReadd (lo s : Nat) (x : Cell) : ∀ (bs : List Cell) (p : Ptr),
    noReaddSegs (gpowBits lo s x bs p).2 = true
  | [], _ => rfl
  | β :: bs, p => by
    rw [gpowBits_cons]
    simp only [List.cons_append, List.nil_append, noReaddSegs, rowNoRd, Bool.true_and]
    exact gpowBitsGo_noReadd s _ _ bs _

/-- **The address from bits is in `[lo, lo + s·(2^|bs| − 1)]`**: a `K` cell `g^e` with
`lo ≤ e ≤ lo + s·(2^|bs| − 1)`. -/
theorem gpowBits_in {c : Ctx} {M : Mem} {lo s : Nat} {x : Cell} {bs : List Cell} {p : Ptr}
    (hx : x.ty = .K) (hb : ∀ β ∈ bs, IsBit M β) (h : SegsHold c M p (gpowBits lo s x bs p).2) :
    (gpowBits lo s x bs p).1.ty = .K ∧ ∃ e, M.k (gpowBits lo s x bs p).1.n = gpow e ∧ lo ≤ e ∧
      e ≤ lo + s * (2 ^ bs.length - 1) := by
  obtain ⟨h1, h2⟩ := gpowBits_spec hx hb h
  have := bitsNat_lt M bs
  exact ⟨h1, _, h2, by omega, by have := Nat.mul_le_mul_left s (show bitsNat M bs ≤ 2 ^ bs.length - 1 by omega); omega⟩

/-- **Read at an address from bits**: `g^(lo + s · Σ β_k 2^k)`, then `readd τ rlo m`. -/
def readdBits (τ : Ty) (rlo m lo s : Nat) (x : Cell) (bs : List Cell) : BM Cell := do
  let a ← gpowBits lo s x bs
  readd τ rlo m a

/-- **A `readdBits` site is in region** (its rows holding, its bits bits) when the bits' range
`[lo, lo + s·(2^|bs| − 1)]` lies in the `readd` region. One instance per new site. -/
theorem readdBits_in {c : Ctx} {M : Mem} {τ : Ty} {rlo m lo s : Nat} {x : Cell} {bs : List Cell}
    (hx : x.ty = .K) (hb : ∀ β ∈ bs, IsBit M β) (h1 : rlo ≤ lo)
    (h2 : lo + s * (2 ^ bs.length - 1) < rlo + 2 ^ m) : InOk c M (readdBits τ rlo m lo s x bs) := by
  intro p h
  unfold readdBits at h ⊢
  rw [hold_bind] at h
  rw [in_bind]
  obtain ⟨hK, e, he, he1, he2⟩ := gpowBits_in hx hb h.1
  exact ⟨segsIn_of_noReadd M p _ (gpowBits_noReadd lo s x bs p),
    readd_in_gpow hK he (by omega) (by omega)⟩

end Lvm.Loop.Build
