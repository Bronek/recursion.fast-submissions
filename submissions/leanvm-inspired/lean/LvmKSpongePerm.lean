-- New for lvm (WP-8): leanVM's Keccak-f[1600] is the contract's.
import LvmKeccakSpec
import RecursionFast.Library.KeccakFast

/-!
# leanVM's Keccak-f[1600] is the contract's (`keccakF1600_eq`)

leanVM's permutation (`LeanVM.Semantics.keccakF1600`, `LvmKeccakSpec.lean`) and the contract's
(`RecursionFast.Keccak.keccakF`, `Contract/Hash/Keccak.lean`) are written differently: leanVM reads
lanes with `getD`, rotates with `rot` (`if n = 0`), does ρ and π in one fold of `setIfInBounds`
over `KECCAK_PI`, indexes χ by `i - i % 5 + …` and ι by `setIfInBounds 0`; the contract has
`theta`, `rho`, `pi`, `chi` on `ofLanes` and `set 0`. The proof is symbolic, as in
`Library/KeccakFast.lean`: each stage of leanVM's round is the contract's on a state of free
lanes, lane by lane (`thetaL_eq`, `rhoPiL_eq`, `chiL_eq`, `iotaL_eq`), so a round is the
contract's (`keccakRound_eq`), and the 24 round constants are the same list (`keccakRC_eq`). UInt64
shifts are mod 64, so the contract's `rotl x 0` is `x` and `rot` is `rotl` at every offset
(`rot_eq`). No permutation is evaluated.
-/

set_option autoImplicit false

namespace Lvm.KSponge.F1600

open LeanVM.Parameters LeanVM.Semantics

/-! ## The stages of leanVM's round -/

/-- θ, as in `Keccak.round`. -/
def thetaL (a : KeccakState) : KeccakState :=
  let c : Vector UInt64 5 := Vector.ofFn fun x ↦
    Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^ Keccak.lane a (x + 10) ^^^
      Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)
  let cAt := fun x ↦ c.toArray.getD x 0
  Vector.ofFn fun i ↦
    Keccak.lane a i ^^^ cAt ((i.val + 4) % 5) ^^^ Keccak.rot (cAt ((i.val + 1) % 5)) 1

/-- ρ and π, as in `Keccak.round`. -/
def rhoPiL (a : KeccakState) : KeccakState :=
  (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)

/-- χ, as in `Keccak.round`. -/
def chiL (b : KeccakState) : KeccakState :=
  Vector.ofFn fun i ↦ Keccak.lane b i ^^^
    (~~~ Keccak.lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
      Keccak.lane b (i.val - i.val % 5 + (i.val + 2) % 5))

/-- ι, as in `Keccak.round`. -/
def iotaL (a : KeccakState) (rc : UInt64) : KeccakState :=
  a.setIfInBounds 0 (Keccak.lane a 0 ^^^ rc)

theorem round_stages (a : KeccakState) (rc : UInt64) :
    Keccak.round a rc = iotaL (chiL (rhoPiL (thetaL a))) rc := rfl

/-! ## Lanes, rotations and the lane permutation -/

theorem lane_eq (a : KeccakState) {i : ℕ} (hi : i < 25) : Keccak.lane a i = a[i] := by
  simp [Keccak.lane, hi]

theorem getD_ofFn {n : ℕ} (f : Fin n → UInt64) {i : ℕ} (hi : i < n) :
    (Vector.ofFn f).toArray.getD i 0 = f ⟨i, hi⟩ := by
  simp [hi]

theorem rotl_zero (x : UInt64) : RecursionFast.Keccak.rotl x 0 = x := by
  apply UInt64.toBitVec_inj.1
  simp [RecursionFast.Keccak.rotl]

/-- leanVM's rotation is the contract's, for every offset (UInt64 shifts are mod 64). -/
theorem rot_eq (x : UInt64) (n : ℕ) : Keccak.rot x n = RecursionFast.Keccak.rotl x n := by
  unfold Keccak.rot
  split_ifs with h
  · subst h; exact (rotl_zero x).symm
  · rfl

/-- The inverse of `KECCAK_PI` on lanes. -/
def piInv (k : ℕ) : ℕ := (3 * (k / 5) + k % 5) % 5 + 5 * (k % 5)

theorem keccakPi_piInv : ∀ k < 25, keccakPi (piInv k) = k := by decide

theorem piInv_keccakPi : ∀ i < 25, piInv (keccakPi i) = i := by decide

theorem piInv_lt (k : ℕ) : piInv k < 25 := by unfold piInv; omega

/-- A fold of writes whose targets miss `k` leaves entry `k`. -/
theorem foldl_set_miss (σ : ℕ → ℕ) (f : ℕ → UInt64) {k : ℕ} (hk : k < 25) :
    ∀ (l : List ℕ) (b : KeccakState), (∀ i ∈ l, σ i ≠ k) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = b[k]
  | [], _, _ => rfl
  | i :: l, b, h => by
    rw [List.foldl_cons, foldl_set_miss σ f hk l _ (fun i' hi' ↦ h i' (by simp [hi'])),
      Vector.getElem_setIfInBounds hk, ite_eq_right_iff.2 (fun h' ↦ absurd h' (h i (by simp)))]

/-- A fold of writes hitting `k` once, at `i₀`, leaves `f i₀` there. -/
theorem foldl_set_hit (σ : ℕ → ℕ) (f : ℕ → UInt64) {k i₀ : ℕ} (hk : k < 25) (hσ : σ i₀ = k) :
    ∀ (l : List ℕ) (b : KeccakState), i₀ ∈ l → (∀ i ∈ l, σ i = k → i = i₀) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = f i₀
  | [], _, h, _ => by simp at h
  | i :: l, b, hmem, huniq => by
    rw [List.foldl_cons]
    by_cases hl : i₀ ∈ l
    · exact foldl_set_hit σ f hk hσ l _ hl fun i' hi' ↦ huniq i' (by simp [hi'])
    · have hi : i = i₀ := by
        rcases List.mem_cons.1 hmem with h | h
        · exact h.symm
        · exact absurd h hl
      subst hi
      rw [foldl_set_miss σ f hk l _ (fun i' hi' he ↦ hl (huniq i' (by simp [hi']) he ▸ hi')),
        Vector.getElem_setIfInBounds hk, ite_eq_left_iff.2 (fun h' ↦ absurd hσ h')]

theorem rhoPiL_get (a : KeccakState) {k : ℕ} (hk : k < 25) :
    (rhoPiL a)[k] = Keccak.rot (Keccak.lane a (piInv k)) (keccakRho.getD (piInv k) 0) :=
  foldl_set_hit keccakPi (fun i ↦ Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)) hk
    (keccakPi_piInv k hk) _ _ (List.mem_range.2 (piInv_lt k)) fun i hi he ↦ by
      rw [← he, piInv_keccakPi i (List.mem_range.1 hi)]

/-! ## Each stage is the contract's -/

/-- Lane `k` of the contract's π is lane `piInv k`. -/
theorem pi_get (b : KeccakState) {k : ℕ} (hk : k < 25) :
    (RecursionFast.Keccak.pi b)[k] = b[piInv k]'(piInv_lt k) := by
  interval_cases k <;> rfl

theorem rho_get (a : KeccakState) {j : ℕ} (hj : j < 25) :
    (RecursionFast.Keccak.rho a)[j] =
      RecursionFast.Keccak.rotl a[j] RecursionFast.Keccak.rhoOffsets[j] := by
  simp only [RecursionFast.Keccak.rho, Vector.getElem_ofFn, Fin.getElem_fin]

/-- leanVM's `KECCAK_RHO` is the contract's `rhoOffsets`. -/
theorem keccakRho_getD {j : ℕ} (hj : j < 25) :
    keccakRho.getD j 0 = RecursionFast.Keccak.rhoOffsets[j] := by
  have h : keccakRho = RecursionFast.Keccak.rhoOffsets.toList := rfl
  simp [h, hj]

theorem thetaL_eq (a : KeccakState) : thetaL a = RecursionFast.Keccak.theta a := by
  refine Vector.ext fun i hi ↦ ?_
  simp only [thetaL, Vector.getElem_ofFn]
  rw [UInt64.xor_assoc, rot_eq]
  interval_cases i <;>
    (simp only [lane_eq, getD_ofFn, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT]; rfl)

theorem rhoPiL_eq (a : KeccakState) :
    rhoPiL a = RecursionFast.Keccak.pi (RecursionFast.Keccak.rho a) := by
  refine Vector.ext fun k hk ↦ ?_
  rw [rhoPiL_get a hk, pi_get _ hk, rho_get _ (piInv_lt k), lane_eq _ (piInv_lt k), rot_eq,
    keccakRho_getD (piInv_lt k)]

theorem chiL_eq (a : KeccakState) : chiL a = RecursionFast.Keccak.chi a := by
  refine Vector.ext fun i hi ↦ ?_
  simp only [chiL, Vector.getElem_ofFn]
  interval_cases i <;>
    (simp only [lane_eq, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT]; rfl)

theorem iotaL_eq (a : KeccakState) (rc : UInt64) : iotaL a rc = a.set 0 (a[0] ^^^ rc) := by
  refine Vector.ext fun i hi ↦ ?_
  rw [iotaL, Vector.getElem_setIfInBounds hi, Vector.getElem_set, lane_eq a (by decide)]

/-! ## A round, and the permutation -/

/-- **A round of leanVM's Keccak-f[1600] is the contract's.** -/
theorem round_eq (a : KeccakState) (c : UInt64) :
    Keccak.round a c = RecursionFast.Keccak.round a c := by
  rw [round_stages, thetaL_eq, rhoPiL_eq, chiL_eq, iotaL_eq]
  rfl

/-- leanVM's `KECCAK_RC` is the contract's `rc`. -/
theorem keccakRC_eq : keccakRC = RecursionFast.Keccak.rc.toList := rfl

end Lvm.KSponge.F1600

/-- **A round of leanVM's Keccak-f[1600] is the contract's round** (`F1600.round_eq`). -/
theorem Lvm.KSponge.keccakRound_eq (a : Vector UInt64 25) (c : UInt64) :
    LeanVM.Semantics.Keccak.round a c = RecursionFast.Keccak.round a c :=
  Lvm.KSponge.F1600.round_eq a c

/-- **leanVM's Keccak-f[1600] is the contract's.** -/
theorem Lvm.KSponge.keccakF1600_eq (a : Vector UInt64 25) :
    LeanVM.Semantics.keccakF1600 a = RecursionFast.Keccak.keccakF a := by
  have h : LeanVM.Semantics.Keccak.round = RecursionFast.Keccak.round :=
    funext fun a ↦ funext fun c ↦ Lvm.KSponge.keccakRound_eq a c
  rw [LeanVM.Semantics.keccakF1600, RecursionFast.Keccak.keccakF, Lvm.KSponge.F1600.keccakRC_eq, h,
    Vector.foldl_toList]
