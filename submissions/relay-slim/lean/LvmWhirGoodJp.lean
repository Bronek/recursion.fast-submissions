-- New for lvm2 (WP J2P-L, roll 5): the good branch of J2′'s relativised `C_rec` opening, unfolded for the extractor.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: J2′'s good residual)
-/

import LvmWhirParamsJp

/-!
# J2′'s good residual, unfolded

`stackedPrefixRec20JpSpec`'s post is `PostR`: `GoodRes ∨ ResC` at the final level (index `1`, code
`codeJ9R3`). `goodRes_rec20Jp` unfolds the good branch for the two-level extractor (`j_extract2`): with
the ten fold challenges split as `α₀ ∈ E^6` (level 0) and `α₁ ∈ E^4` (level 1), there is a good root
candidate `q`, a member `V` of level 1's list on `q`'s path after `α₀`, and the residual is `q`'s path
after `α₀ ++ α₁` (so its encoding is the fold of `V`'s, in the list of the folded level-1 rows).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-- `PostR`'s final level at J2′ is level `1`, after `6` fold challenges, with `4` folds. -/
theorem finInfo_rec20Jp : finInfo 0 0 cfgRec20Jp.levels = (1, 6, 4) := rfl

/-- **J2′'s good residual, unfolded.** -/
theorem goodRes_rec20Jp {Good : Column 19 → Prop} {cs : List (ℕ × ℕ × Word)}
    {r : WhirStateT × List E} {res : List E} (α₀ : Fin 6 → E) (α₁ : Fin 4 → E)
    (hfs : r.1.folds = List.ofFn α₀ ++ List.ofFn α₁)
    (hG : GoodRes (codesRec20Jp 1) 1
      (gdFinal codesRec20Jp cs r.1.folds 0 0 cfgRec20Jp.levels (gdRoot (codesRec20Jp 0) Good cs))
      r res cs) :
    ∃ q ∈ Candidates 19 2 (codesRec20Jp 0).thr (wordOf cs 0), Good q ∧
      (∃ V ∈ iList (codesRec20Jp 1).code (codesRec20Jp 1).thr
          (rowsOf 4 (laneO 1 cs (codesRec20Jp 1).n)),
        PathAt q (List.ofFn α₀) (decode (codesRec20Jp 1) V)) ∧
      (∀ x : Fin (codesRec20Jp 1).κ → Bool,
        resMsg res x = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ bitsL x)) := by
  obtain ⟨-, q, hq, hpath⟩ := hG
  have htake : r.1.folds.take (0 + (⟨6, 2, 115⟩ : Whir.Level).fold) = List.ofFn α₀ := by
    rw [hfs]; simp
  have hq' : (q ∈ Candidates 19 2 (codesRec20Jp 0).thr (wordOf cs 0) ∧ Good q) ∧
      ConsAt (codesRec20Jp 1) 4 1 cs (List.ofFn α₀) q := by
    rw [← htake]; exact hq
  obtain ⟨⟨hcand, hgood⟩, hcons⟩ := hq'
  refine ⟨q, hcand, hgood, hcons, fun x ↦ ?_⟩
  rw [hpath x, hfs]

/-- **The Johnson and the UD level-1 codes decode alike** (same `κ`, `R`, code; only the threshold
differs): X-REC2's `decodeRec1_of_ud` (stated on `decode (codesRec20 1)`, `codesRec20 1 = ud 9 3`) reads
the same message from a Johnson list member. -/
theorem decode_codeJ9R3_eq_ud {ρ : Type*} (V : ρ → Fin codeJ9R3.n → E) :
    decode codeJ9R3 V = decode (LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)) V := rfl

/-- The two level-1 codes are the same submodule. -/
theorem code_codeJ9R3_eq_ud :
    codeJ9R3.code = (LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)).code := rfl

end
end LeanVM.Protocol.Whir.Sound
