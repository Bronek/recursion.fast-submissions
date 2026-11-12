-- From relay-echo (#12), `lean/FastSpecPerm.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The statements behind **L1** (`permF_eq`, `FastSpec.lean`) for the permutation of
  `FastDefs.lean`: `permF` is `roundC` on complemented lanes, its first and last rounds written out
  and rounds 1 to 22 as the loop `roundsC`. L1 follows from these by rewriting:

    `permF s` = `complL (roundC (rcInner.foldl roundC (roundC (complL s) c₀)) c₂₃)`
        (`roundsC_foldl`)
      = `complL (complL (roundF (rcInner.foldl roundF (roundF s c₀)) c₂₃))`
        (`roundC_complL`, `foldl_roundC_complL`)
      = `keccakFF s` (`complL_complL`, `keccakFF_split`).

  * `rotK_not`, `complL_complL`: complements commute with rotations and cancel.
  * `roundC_complL` (the crux): a round on complemented lanes is `roundF`, complemented. After
    `rotK_not` moves θ's complements through ρ, every lane is a Boolean identity of words, for
    example lane 0's `b₀' ⊕ (b₁' ∨ b₂') = b₀ ⊕ (¬b₁ ∧ b₂)` with `b₀' = ¬b₀`, `b₁' = b₁` and
    `b₂' = ¬b₂`.
  * `roundsC_foldl`: the loop `roundsC` is the fold of `roundC`.
  * `keccakFF_split`: `Keccak.rc`'s first and last constants, and `rcInner` between them.
-/
import WlFastDefs

namespace RecursionFast.FastCheck
open RecursionFast Keccak

/-- A rotation of a complement is the complement of the rotation. -/
theorem rotK_not (w n : UInt64) : rotK (~~~w) n = ~~~rotK w n := by
  have hm : (64 - n).toNat % 64 = (64 - n.toNat % 64) % 64 := by
    have hn := n.toNat_lt
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  apply UInt64.toBitVec_inj.1
  simp only [rotK, UInt64.toBitVec_or, UInt64.toBitVec_not, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight]
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_shiftLeft',
    BitVec.ushiftRight_eq', BitVec.getElem_ushiftRight, BitVec.getLsbD_not,
    BitVec.toNat_umod, UInt64.toNat_toBitVec, BitVec.reduceToNat, hm]
  by_cases hz : n.toNat % 64 = 0
  · simp [hz, hi, BitVec.getLsbD_eq_getElem]
  · simp only [Nat.mod_eq_of_lt (show 64 - n.toNat % 64 < 64 by omega)]
    by_cases h : i < n.toNat % 64
    · have hb : 64 - n.toNat % 64 + i < 64 := by omega
      simp [h, hb]
    · have hb : 64 ≤ 64 - n.toNat % 64 + i := by omega
      simp [h, Nat.not_lt.mpr hb, BitVec.getLsbD_of_ge _ _ hb]

/-- `complL` is an involution. -/
theorem complL_complL (s : S25) : complL (complL s) = s := by
  simp only [complL, UInt64.not_not]

/-- **The round on complemented lanes**: `roundC` of the complemented state is the complemented
`roundF`. -/
theorem roundC_complL (s : S25) (c : UInt64) : roundC (complL s) c = complL (roundF s c) := by
  simp only [roundC, complL, roundF, iotaF, chiF, piF, rhoF, thetaF, rotK_not,
    UInt64.not_xor, UInt64.xor_not, UInt64.not_not, S25.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact True.intro
    | (apply UInt64.toBitVec_inj.1; ext i hi
       simp only [UInt64.toBitVec_xor, UInt64.toBitVec_or, UInt64.toBitVec_not,
         UInt64.toBitVec_and, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_not,
         BitVec.getElem_and]
       grind)

/-- The loop is the fold of its round. -/
theorem roundsC_foldl (cs : List UInt64) (s : S25) :
    roundsC cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24 = cs.foldl roundC s := by
  cases s
  dsimp only
  fun_induction roundsC <;> simp_all only [List.foldl_cons, List.foldl_nil]
  all_goals rfl

/-- The rounds on complemented lanes, folded, are `roundF`'s, complemented. -/
theorem foldl_roundC_complL (cs : List UInt64) (s : S25) :
    cs.foldl roundC (complL s) = complL (cs.foldl roundF s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons, roundC_complL, ih]

/-- `keccakFF` with its first and last rounds apart. -/
theorem keccakFF_split (s : S25) :
    keccakFF s =
      roundF (rcInner.foldl roundF (roundF s 0x0000000000000001)) 0x8000000080008008 := by
  rfl

end RecursionFast.FastCheck
