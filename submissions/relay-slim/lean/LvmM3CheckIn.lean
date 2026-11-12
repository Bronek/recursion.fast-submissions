-- new for lvm (WP-9b): the input arrays' Boolean check (`InOk`): bundles of interleaved arrays
-- (strided inputs, WP-15b's layout) tiling each memory's input cells.
import LvmM3Loop

/-!
# The input arrays' Boolean check

WP-15b's input layout interleaves arrays: the `KS` messages `X_l` (`l < 17`, cells `17i + l`:
base `17R + l`, stride `17`) and the `KS` digests (base `34R + l`, stride `4`, `l < 4`). A
**bundle** is `s` consecutive arrays of stride `s`, one log-height `τ` and bases `c, c+1, …,
c+s−1`: together they hold the cells `[c, c + s·2^τ)`, array `k` the cells `≡ c + k` mod `s`
(`s = 1`: one contiguous array).

**`inOkB`**: one value column per limb, and per memory, in list order, the arrays are bundles laid
end to end over the input cells `[0, nIn τ)` (`bundlesB`). `inOk_of_B` gives every clause of
`InOk`, coverage included. Structural recursion (fuel: the list length), linear in the arrays.
-/

namespace Lvm.M3

open Lvm.Loop

/-! ## Bundles -/

/-- **Bundles end to end**: from cell `c`, the next `s = a.stride` arrays (`a` the first) have
stride `s`, `a`'s log-height and bases `c, c+1, …, c+s−1`; the next bundle starts at
`c + s·2^τ`; the last ends at `N`. -/
def bundlesB : ℕ → List InArr → ℕ → ℕ → Bool
  | _, [], c, N => c == N
  | 0, _ :: _, _, _ => false
  | fuel + 1, a :: l, c, N =>
    decide (0 < a.stride) && ((a :: l).take a.stride).length == a.stride &&
      (((a :: l).take a.stride).zipIdx.all fun bk ↦
        bk.1.stride == a.stride && bk.1.τ == a.τ && bk.1.base == c + bk.2) &&
      bundlesB fuel ((a :: l).drop a.stride) (c + a.stride * 2 ^ a.τ) N

/-- The cells of an input array. -/
def Cell (a : InArr) (e : ℕ) : Prop := ∃ x < 2 ^ a.τ, a.base + a.stride * x = e

/-- What a bundle check gives: strides positive, every cell inside `[c, N)`, distinct arrays
(by position) share no cell, every cell of `[c, N)` held. -/
structure BundleFacts (l : List InArr) (c N : ℕ) : Prop where
  pos : ∀ a ∈ l, 0 < a.stride
  mem : ∀ a ∈ l, ∀ e, Cell a e → c ≤ e ∧ e < N
  disj : l.Pairwise fun a a' ↦ ∀ e, Cell a e → ¬ Cell a' e
  cover : ∀ e, c ≤ e → e < N → ∃ a ∈ l, Cell a e

/-- One bundle's facts. -/
theorem bundle_facts {bd : List InArr} {s τ c : ℕ} (hs : 0 < s) (hlen : bd.length = s)
    (hb : ∀ k (hk : k < bd.length), bd[k].stride = s ∧ bd[k].τ = τ ∧ bd[k].base = c + k) :
    (∀ a ∈ bd, 0 < a.stride) ∧ (∀ a ∈ bd, ∀ e, Cell a e → c ≤ e ∧ e < c + s * 2 ^ τ) ∧
      (bd.Pairwise fun a a' ↦ ∀ e, Cell a e → ¬ Cell a' e) ∧
      (∀ e, c ≤ e → e < c + s * 2 ^ τ → ∃ a ∈ bd, Cell a e) := by
  refine ⟨fun a ha ↦ ?_, fun a ha e he ↦ ?_, ?_, fun e h1 h2 ↦ ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    rw [(hb k hk).1]; exact hs
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨h1, h2, h3⟩ := hb k hk
    obtain ⟨x, hx, rfl⟩ := he
    rw [h1, h3]; rw [h2] at hx
    refine ⟨by omega, ?_⟩
    have : s * x + s ≤ s * 2 ^ τ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hx
    omega
  · refine List.pairwise_iff_getElem.mpr fun i j hi hj hij e he he' ↦ ?_
    obtain ⟨x, -, hx⟩ := he
    obtain ⟨x', -, hx'⟩ := he'
    obtain ⟨hi1, -, hi3⟩ := hb i hi
    obtain ⟨hj1, -, hj3⟩ := hb j hj
    rw [hi1, hi3] at hx; rw [hj1, hj3] at hx'
    have hil : i < s := hlen ▸ hi
    have hjl : j < s := hlen ▸ hj
    have h1 : i + s * x = j + s * x' := by omega
    have hm := congrArg (· % s) h1
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hil, Nat.mod_eq_of_lt hjl] at hm
    omega
  · have hk : (e - c) % s < bd.length := by rw [hlen]; exact Nat.mod_lt _ hs
    obtain ⟨hk1, hk2, hk3⟩ := hb _ hk
    refine ⟨bd[(e - c) % s], List.getElem_mem hk, (e - c) / s, ?_, ?_⟩
    · rw [hk2, Nat.div_lt_iff_lt_mul hs, Nat.mul_comm]; omega
    · rw [hk1, hk3]
      have := Nat.mod_add_div (e - c) s
      omega

/-- **The bundle check's facts.** -/
theorem bundles_facts : ∀ (fuel : ℕ) (l : List InArr) (c N : ℕ), bundlesB fuel l c N = true →
    BundleFacts l c N
  | _, [], c, N, h => by
    simp only [bundlesB, beq_iff_eq] at h
    exact ⟨by simp, by simp, List.Pairwise.nil, fun e h1 h2 ↦ by omega⟩
  | 0, _ :: _, _, _, h => by simp [bundlesB] at h
  | fuel + 1, a :: l, c, N, h => by
    simp only [bundlesB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hs, hlen⟩, hall⟩, hrest⟩ := h
    set s := a.stride
    set bd := (a :: l).take s
    set rest := (a :: l).drop s
    have hb : ∀ k (hk : k < bd.length), bd[k].stride = s ∧ bd[k].τ = a.τ ∧ bd[k].base = c + k := by
      intro k hk
      have hm : (bd[k], k) ∈ bd.zipIdx := by
        have : k < bd.zipIdx.length := by simpa using hk
        have he := List.getElem_mem this
        simpa using he
      have := hall _ hm
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    obtain ⟨b1, b2, b3, b4⟩ := bundle_facts hs hlen hb
    obtain ⟨r1, r2, r3, r4⟩ := bundles_facts fuel rest _ N hrest
    have hsplit : a :: l = bd ++ rest := (List.take_append_drop s (a :: l)).symm
    rw [hsplit]
    have hcN : c + s * 2 ^ a.τ ≤ N := by
      by_cases hr : rest = []
      · have := bundles_facts fuel rest _ N hrest
        rw [hr] at hrest; simp only [bundlesB, beq_iff_eq] at hrest; omega
      · obtain ⟨a', ha'⟩ := List.exists_mem_of_ne_nil _ hr
        have := r2 a' ha' a'.base ⟨0, Nat.two_pow_pos _, by simp⟩; omega
    refine ⟨fun a' ha' ↦ ?_, fun a' ha' e he ↦ ?_, ?_, fun e h1 h2 ↦ ?_⟩
    · rcases List.mem_append.mp ha' with h' | h'
      · exact b1 a' h'
      · exact r1 a' h'
    · rcases List.mem_append.mp ha' with h' | h'
      · have := b2 a' h' e he; omega
      · have := r2 a' h' e he; omega
    · refine List.pairwise_append.mpr ⟨b3, r3, fun a' ha' a'' ha'' e he he' ↦ ?_⟩
      have := b2 a' ha' e he
      have := r2 a'' ha'' e he'
      omega
    · by_cases he : e < c + s * 2 ^ a.τ
      · obtain ⟨a', ha', hc⟩ := b4 e h1 he
        exact ⟨a', List.mem_append_left _ ha', hc⟩
      · obtain ⟨a', ha', hc⟩ := r4 e (by omega) h2
        exact ⟨a', List.mem_append_right _ ha', hc⟩

/-! ## The input arrays -/

/-- The arrays of memory `τ` are bundles tiling its input cells `[0, nIn τ)`. -/
def inTilesB (Q : Program) (arrs : List InArr) (τ : Ty) : Bool :=
  let l := arrs.filter fun a ↦ decide (a.ty = τ)
  bundlesB l.length l 0 (Q.nIn τ)

/-- **The input arrays' Boolean check**: one value column per limb, public arrays (`pub`) of
memory `K` only (A19: the public values are `K` cells; a public `E` array would repeat one value in
its three limbs), and the arrays of each memory are bundles tiling its input cells, in list order. -/
def inOkB (Q : Program) (arrs : List InArr) : Bool :=
  arrs.all (fun a ↦ a.val.length == a.ty.limbs && (a.pub.isNone || decide (a.ty = .K))) &&
    inTilesB Q arrs .K && inTilesB Q arrs .E

/-- Public arrays are `K` arrays. -/
theorem pub_K_of_B {Q : Program} {arrs : List InArr} (h : inOkB Q arrs = true) :
    ∀ a ∈ arrs, a.pub.isSome → a.ty = .K := by
  intro a ha hp
  simp only [inOkB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at h
  rcases (h.1.1 a ha).2 with h0 | h1
  · simp [h0] at hp
  · exact h1

/-- **The input arrays' check gives `InOk`**, coverage included. -/
theorem inOk_of_B {Q : Program} {arrs : List InArr} (h : inOkB Q arrs = true) : InOk Q arrs := by
  simp only [inOkB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hall', hK⟩, hE⟩ := h
  have hall : ∀ a ∈ arrs, a.val.length = a.ty.limbs := fun a ha ↦ (hall' a ha).1
  have ht : ∀ τ, inTilesB Q arrs τ = true := fun τ ↦ by cases τ <;> assumption
  have hf : ∀ τ, BundleFacts (arrs.filter fun a ↦ decide (a.ty = τ)) 0 (Q.nIn τ) := fun τ ↦
    bundles_facts _ _ _ _ (ht τ)
  have hmemf : ∀ a ∈ arrs, a ∈ arrs.filter fun a' ↦ decide (a'.ty = a.ty) := fun a ha ↦
    List.mem_filter.mpr ⟨ha, by simp⟩
  refine ⟨fun a ha ↦ hall a ha, fun a ha x hx ↦ ?_, fun i i' x x' hx hx' hty heq ↦ ?_,
    fun τ e he ↦ ?_⟩
  · exact ((hf a.ty).mem a (hmemf a ha) _ ⟨x, hx, rfl⟩).2
  · have hp := List.pairwise_iff_getElem.mp (List.pairwise_filter.mp (hf (arrs.get i).ty).disj)
    simp only [List.get_eq_getElem] at hx hx' hty heq ⊢
    rcases Nat.lt_trichotomy i.val i'.val with hlt | hv | hlt
    · exact absurd ⟨x', hx', heq.symm⟩
        (hp i.val i'.val i.isLt i'.isLt hlt (by simp) (by simpa using hty.symm) _ ⟨x, hx, rfl⟩)
    · have hii : i = i' := Fin.ext hv
      subst hii
      have hs := (hf arrs[i.val].ty).pos _ (hmemf _ (List.getElem_mem i.isLt))
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hs (by omega)⟩
    · exact absurd ⟨x, hx, heq⟩
        (hp i'.val i.val i'.isLt i.isLt hlt (by simpa using hty.symm) (by simp) _ ⟨x', hx', rfl⟩)
  · obtain ⟨a, ha, x, hx, hc⟩ := (hf τ).cover e (Nat.zero_le _) he
    obtain ⟨ha', hty⟩ := List.mem_filter.mp ha
    exact ⟨a, ha', by simpa using hty, x, hx, hc⟩

end Lvm.M3
