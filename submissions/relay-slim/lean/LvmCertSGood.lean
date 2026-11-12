-- WP-14 (ASM). New for lvm: WP-5's `final_law` (`LvmCompileFinal`, proof copied) with its
-- intermediate facts exposed: on a log of potential below `1`, an accepted proof's replayed history
-- is accepted, not lucky and outside doom at every boundary. Used for O5c (the extractor program
-- equals the specification extractor only where the decoder's hypotheses hold).
import LvmCompileFinal

/-!
# The replayed history of a good log

**`final_good`**: `μ K L < 1` and `S.V` accepting `π` on `L` give the statement `x` of `π`'s header
(`S.ok c x`) and a history `h` with `(S.P x).Reachable h`, `after h = ret true`, not lucky at `h`
and at every boundary prefix, not doomed at every boundary prefix, and `S.Ex ext c π L =
some (ext c x h)` for every extraction map `ext` (the replay does not depend on it).
-/

namespace Lvm.FS

open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof
open scoped NNReal

namespace Scheme

variable {S : Scheme} {R : Digest → Wit → Prop}

/-- **The replayed history of an accepted proof on a log of potential below `1`.** -/
theorem final_good (K : KCert S R) (L : Log) (c : Digest) (π : Proof) (hμ : μ K L < 1)
    (hacc : (S.V c π).runLog L = some true) :
    ∃ x h, S.ok c x = true ∧ (S.P x).Reachable h ∧ (S.P x).after h = some (.ret true) ∧
      ¬ K.B x h ∧ (∀ h', h' <+: h → Boundary h' → ¬ K.B x h') ∧
      (∀ h', h' <+: h → Boundary h' → ¬ (K.cert x).D h') ∧
      ∀ {W' : Type} (ext : Digest → S.Stmt → List Ev → W'), S.Ex ext c π L = some (ext c x h) := by
  obtain ⟨hb, hS⟩ := mu_lt_one hμ
  rw [runLog_V] at hacc
  rcases hhdr : S.hdr π with _ | ⟨x, body⟩
  · rw [hhdr] at hacc; simp at hacc
  · rw [hhdr] at hacc
    simp only at hacc
    by_cases hpre : S.preOk c x
    · rw [ite_eq_left hpre] at hacc
      have hok : S.ok c x = true := by unfold preOk at hpre; simp at hpre; exact hpre.1
      have hcap : 32 + (S.enc x).length ≤ queryCap := by unfold preOk at hpre; simp at hpre; exact hpre.2
      cases h0 : L.find? (fun e => decide (e.1 = toQ S.q0)) with
      | none => rw [h0] at hacc; simp at hacc
      | some e₀ =>
        rw [h0, Option.bind_some] at hacc
        cases h1 : L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x)) with
        | none => rw [h1] at hacc; simp at hacc
        | some e₁ =>
          rw [h1, Option.bind_some] at hacc
          cases hr : S.trun L (S.P x) e₁.2 [] [] body [] with
          | none => rw [hr] at hacc; simp at hacc
          | some res =>
            rw [hr] at hacc
            obtain ⟨b, hf⟩ := res
            simp only [Option.map_some, Option.some.injEq] at hacc
            subst hacc
            obtain ⟨hp0, r, hrL, hLr, -⟩ := List.find?_eq_some_iff_getElem.mp h0
            obtain ⟨hp1, j₁, hj₁, hLj₁, -⟩ := List.find?_eq_some_iff_getElem.mp h1
            have he0 : e₀.1 = toQ S.q0 := by simpa using hp0
            have he1 : e₁.1 = S.seedQ e₀.2 x := by simpa using hp1
            have hgr : L[r]? = some (toQ S.q0, e₀.2) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hrL, by rw [hLr, ← he0]⟩
            have hgj : L[j₁]? = some (S.seedQ e₀.2 x, e₁.2) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hj₁, by rw [hLj₁, ← he1]⟩
            have hrj : r < j₁ := by
              by_contra hle
              refine not_inWins_of_not_bad hb (i := j₁) (j := r) (by omega) hgj hgr ?_
              refine ⟨by rw [seedQ_size]; exact hcap, 0, by rw [seedQ_size]; omega, ?_⟩
              unfold win seedQ
              rw [qb_toQ, List.drop_zero, dg_toList_append]
            have hN : S.IsNode L j₁ (S.seedNI x) := IsNode.seed x hrj hgr hgj hcap
            obtain ⟨hr', ha', hB', hBp, hD'⟩ := S.trun_accept K hb hS x (S.P x) e₁.2 [] [] body []
              [] j₁ (S.seedNI x) hf hN rfl ⟨_, hgj, rfl⟩ Relation.ReflTransGen.refl
              (fun h' hp' _ hD => by rw [List.prefix_nil.mp hp'] at hD; exact hD) (K.B_nil x)
              (fun h' hp' _ => by rw [List.prefix_nil.mp hp']; exact K.B_nil x)
              (by unfold Align; rfl) hr
            refine ⟨x, hf, hok, hr', ha', hB', hBp, hD', fun ext ↦ ?_⟩
            unfold Ex
            rw [hhdr]
            simp only
            rw [ite_eq_left hpre, h0, Option.bind_some, h1, Option.bind_some, hr]
            simp
    · rw [ite_eq_right hpre] at hacc; simp at hacc

end Scheme

end Lvm.FS
