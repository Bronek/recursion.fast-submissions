-- WP-14 (ASM). New for lvm (O1): the query bound of `V_S` on every oracle path, by a static count
-- of the schedule (the driver's loops are fixed by the schedule; only rejections stop early).
import LvmVerifier
import LvmVerifierS
import LvmCertS

/-!
# The query bound of `V_S` (O1)

`qcItems p items b`: the queries the driver's items ask at most, `b` bounding the current
positions (`sample` 1; `positions r` its `nPosQ` FS queries, after which at most `t` positions;
`opening r` at most `b · (1 + path)`: a leaf and the path per position). By induction over
`climb`, `openLoop`, `posLoop`, `driveItems`: **`queries_VS_le`**, `|(VS p m vk c π).queries H| ≤
2 + qcItems p (schedule p) 0` for every oracle `H`; at P20 that is at most `16384`
(`qcItems_P20`, one kernel evaluation of the schedule, as `checks_P20`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The static query count** of a list of items, with at most `b` current positions. -/
def qcItems (p : Params) : List Item → ℕ → ℕ
  | [], _ => 0
  | .read _ :: rest, b => qcItems p rest b
  | .cap _ _ :: rest, b => qcItems p rest b
  | .sample :: rest, b => 1 + qcItems p rest b
  | .positions r :: rest, _ => (p.level r).nPosQ + qcItems p rest (p.level r).t
  | .opening r :: rest, b => b * (1 + (p.level r).path) + qcItems p rest b

section Bounds

variable (H : ByteArray → Digest) (π : ByteArray)

theorem q_climb (q : ℕ) : ∀ (j lvl : ℕ) (cur : Digest) (s : DSt) (k : DSt → Digest → OProg Bool)
    (K : ℕ), (∀ s' d, s'.pos = s.pos → ((k s' d).queries H).length ≤ K) →
    ((climb π q j lvl cur s k).queries H).length ≤ j + K
  | 0, _, cur, s, k, K, hk => by
    simp only [climb]; exact (hk s cur rfl).trans (by omega)
  | j + 1, lvl, cur, s, k, K, hk => by
    simp only [climb, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_climb q j (lvl + 1) _ _ k K ?_) 1).trans ?_
    · exact fun s' d h ↦ hk s' d h
    · omega

theorem q_openLoop (L : Level) (capOff : ℕ) : ∀ (qs : List ℕ) (s : DSt) (k : DSt → OProg Bool)
    (K : ℕ), (∀ s', s'.pos = s.pos → ((k s').queries H).length ≤ K) →
    ((openLoop π L capOff qs s k).queries H).length ≤ qs.length * (1 + L.path) + K
  | [], s, k, K, hk => by simp only [openLoop]; exact (hk s rfl).trans (by simp)
  | q :: qs, s, k, K, hk => by
    simp only [openLoop, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_climb H π q L.path 0 _ _ _ (qs.length * (1 + L.path) + K)
      ?_) 1).trans ?_
    · intro s' d h
      split
      · exact q_openLoop L capOff qs s' k K fun s'' h' ↦ hk s'' (h'.trans h)
      · simp [OProg.queries]
    · rw [Nat.add_mul, Nat.one_mul]
      omega

theorem q_posLoop (h : ℕ) : ∀ (n rem : ℕ) (s : DSt) (k : DSt → OProg Bool) (K : ℕ),
    (∀ s', s'.pos.length ≤ s.pos.length + rem → ((k s').queries H).length ≤ K) →
    ((posLoop π h n rem s k).queries H).length ≤ n + K
  | 0, rem, s, k, K, hk => by simp only [posLoop]; exact (hk s (by omega)).trans (by omega)
  | n + 1, rem, s, k, K, hk => by
    simp only [posLoop, fsQuery, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_posLoop h n (rem - min positionsPerAnswer rem) _ k K ?_) 1).trans ?_
    · intro s' hs'
      refine hk s' ?_
      simp only [List.length_append, List.length_map, List.length_range] at hs'
      have := Nat.min_le_right positionsPerAnswer rem
      omega
    · omega

theorem q_driveItems (p : Params) (k : DSt → OProg Bool) (K : ℕ)
    (hk : ∀ s, ((k s).queries H).length ≤ K) :
    ∀ (items : List Item) (b : ℕ) (s : DSt), s.pos.length ≤ b →
      ((driveItems p π items s k).queries H).length ≤ qcItems p items b + K
  | [], b, s, _ => by simp only [driveItems, qcItems]; exact (hk s).trans (by omega)
  | .read m :: rest, b, s, hs => by
    simp only [driveItems, qcItems]; exact q_driveItems p k K hk rest b _ hs
  | .cap c r :: rest, b, s, hs => by
    simp only [driveItems, qcItems]; exact q_driveItems p k K hk rest b _ hs
  | .sample :: rest, b, s, hs => by
    simp only [driveItems, qcItems, fsQuery, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_driveItems p k K hk rest b _ ?_) 1).trans ?_
    · exact hs
    · omega
  | .positions r :: rest, b, s, _ => by
    simp only [driveItems, qcItems]
    refine (q_posLoop H π (p.level r).height (p.level r).nPosQ (p.level r).t { s with pos := [] }
      _ (qcItems p rest (p.level r).t + K) fun s' hs' ↦
        q_driveItems p k K hk rest (p.level r).t s' (by simpa using hs')).trans ?_
    omega
  | .opening r :: rest, b, s, hs => by
    simp only [driveItems, qcItems]
    split
    · simp [OProg.queries]
    · rename_i capOff _
      split
      · refine (q_openLoop H π (p.level r) capOff s.pos s _ (qcItems p rest b + K)
          fun s' hs' ↦ q_driveItems p k K hk rest b _ (by simpa [hs'] using hs)).trans ?_
        have hm := Nat.mul_le_mul_right (1 + (p.level r).path) hs
        omega
      · simp [OProg.queries]

end Bounds

/-- **The query bound of `V_S`** on every oracle path. -/
theorem queries_VS_le (p : Params) (m : M3) (vk c : Digest) (π : Proof) (H : ByteArray → Digest) :
    ((VS p m vk c π).queries H).length ≤ 2 + qcItems p (schedule p) 0 := by
  unfold VS
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π p _ 0 (fun s ↦ by
      simp [OProg.queries]) (schedule p) 0 _ (by simp)) 1) 1).trans ?_
    omega
  · simp [OProg.queries]

/-- At P20 the static count is within the declared `qV`. -/
theorem qcItems_P20 : 2 + qcItems P20 (schedule P20) 0 ≤ 16384 := by decide +kernel

/-- **O1**: `V_S` at P20 on any tables asks at most `qV = 16384` queries on every oracle path
(lvm2 S2-CERT: generic in the node program's tables; `VS20`'s is `LvmSubmissionS20.hq_VS20`). -/
theorem hq_VSL (tabs : Pub → List M3.Tab) (H : ByteArray → Digest) (vk c : Digest) (π : Proof) :
    ((VSL P20 tabs vk c π).queries H).length ≤ Lvm.T.qVlvm :=
  (queries_VS_le P20 _ vk c π H).trans qcItems_P20

end Lvm

namespace Lvm.ASM

/-- **`schemeS`'s cap levels are the schedule's** (review fact): for every level of both
commitments at P20, `capOfS` of its height is its cap exponent. -/
theorem capOfS_P20 :
    ((P20.levels .main).all fun L ↦ capOfS L.height 0 == L.cap) = true ∧
      ((P20.levels .crec).all fun L ↦ capOfS L.height 0 == L.cap) = true := by
  decide +kernel

end Lvm.ASM
