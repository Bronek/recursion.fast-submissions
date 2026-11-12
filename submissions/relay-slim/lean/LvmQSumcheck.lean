import LvmQSumcheckCore
import LvmDecideSumcheck

/-!
# QA1: the generic sumcheck rounds (`F`'s `sumcheck`) as a LoopIR loop block

**`F` side** (`LvmDecideSumcheck.sumcheck`, a port of leanVM `LeanVmVerifier.lean:1146-1164`). The
reader's position `p = ent + msg` (the next message byte is `p + 40`) determines every read:
round `i` reads its `count − 1` scalars at `p_i + 40 + 24k` and its challenge at
`p_i + 40 + 24(count − 1)`, and `p_{i+1} = p_i + roundLen count`. `scSpec` is that computation on a
view `v` of the stream's scalars (`v = feAt Σ`); **`sumcheck_run`**: `F`'s `sumcheck` is `scSpec`
on `feAt Σ`, its state moved to `p + |eqs|·roundLen` with `ok` untouched (a sumcheck checks
nothing; its final claim is checked by the caller).

**Circuit side.** One round is a template (`roundIns`): load the `count − 1` message scalars and the
challenge from the stream lanes (`loadE`), the omitted coefficient (`lin` chain; plain mode
`c₁ = claim + Σ_{k≥2} c_k`, equality mode `c₀ = claim + r·Σ_{k≥1} c_k`, one `muladd`), Horner at
the challenge (`count − 1` `muladd`s). The claim is carried from the previous iteration (`prev`,
the template's last row); the loop block `scBlock` has `dims = [D]` and runs `2^D ≥ rounds`
iterations (the iterations past the rounds compute values nobody reads: no assertion, no
padding constraint). The initial claim is the `E` cell just before the block (`L.sE − 1`).
**`sc_cells`**: in every memory with `BHolds` and the stream's lanes, iteration `i < rounds` holds
challenge `i` and the claim after round `i + 1` of `scSpec`.

Row costs (WP-10 widths): plain `count = 3`: 3 `loadE` + 1 `lin` + 2 `muladd` = 74 words per round;
`count = 4`: 4 + 2 + 3 = 112; equality mode `count = 3`: 3 `loadE`, 1 `lin`, 3 `muladd` = 90.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s sumcheck on a view of the stream -/

/-- `n` scalars at bytes `o, o + 24, …`. -/
def scalarsAt (v : Nat → FE) (o n : Nat) : List FE := (List.range n).map fun k => v (o + 24 * k)

/-- The bytes of one round's FS entry: length, state, `count − 1` scalars, answer. -/
def roundLen (count : Nat) : Nat := 72 + 24 * (count - 1)

/-- The round polynomial `F` forms from the message at position `p` (`sumcheckRoundPoly`). -/
def roundPoly (v : Nat → FE) (p count : Nat) (claim : FE) : Option FE → List FE
  | none => v (p + 40) :: (claim + sumE (scalarsAt v (p + 64) (count - 2))) ::
      scalarsAt v (p + 64) (count - 2)
  | some r => (claim + r * sumE (scalarsAt v (p + 40) (count - 1))) :: scalarsAt v (p + 40) (count - 1)

/-- **`F`'s sumcheck from position `p`**: the challenges and the final claim. -/
def scSpec (v : Nat → FE) (count : Nat) : Nat → FE → List (Option FE) → List FE × FE
  | _, claim, [] => ([], claim)
  | p, claim, e :: es =>
    let ch := v (p + 40 + 24 * (count - 1))
    let r := scSpec v count (p + roundLen count) (polyEval (roundPoly v p count claim e) ch) es
    (ch :: r.1, r.2)

/-! ## Reading lemmas -/

theorem readE_run (sig : ByteArray) (s : RS) :
    readE sig s = (feAt sig (s.ent + 40 + s.msg), { s with msg := s.msg + 24 }) := rfl

theorem sampleE_run (sig : ByteArray) (s : RS) :
    sampleE sig s = (feAt sig (s.ent + 40 + s.msg), { s with ent := s.ent + 72 + s.msg, msg := 0 }) :=
  rfl

theorem bind_run {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := rfl

theorem pure_run {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) := rfl

theorem readEs_succ (n : Nat) :
    readEs (n + 1) = (readE >>= fun x => readEs n >>= fun xs => pure (x :: xs)) := rfl

theorem readEs_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    readEs n sig s = (scalarsAt (feAt sig) (s.ent + s.msg + 40) n, { s with msg := s.msg + 24 * n })
  | 0, s => rfl
  | n + 1, s => by
    rw [readEs_succ, bind_run, readE_run, bind_run, readEs_run sig n, pure_run]
    generalize feAt sig = v
    simp only [scalarsAt, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]
    have h1 : s.ent + 40 + s.msg = s.ent + s.msg + 40 + 24 * 0 := by omega
    have h2 : ∀ k, s.ent + (s.msg + 24) + 40 + 24 * k = s.ent + s.msg + 40 + 24 * (k + 1) := by
      intro k; omega
    have h3 : s.msg + 24 + 24 * n = s.msg + 24 * (n + 1) := by omega
    simp only [h1, h2, h3]

theorem roundPoly_run (sig : ByteArray) (count : Nat) (hc : 2 ≤ count) (claim : FE) (e : Option FE)
    (s : RS) :
    sumcheckRoundPoly count claim e sig s =
      (roundPoly (feAt sig) (s.ent + s.msg) count claim e, { s with msg := s.msg + 24 * (count - 1) }) := by
  cases e with
  | none =>
    rw [show sumcheckRoundPoly count claim none = (readE >>= fun constant => readEs (count - 2) >>=
      fun tail => pure (constant :: (claim + sumE tail) :: tail)) from rfl]
    rw [bind_run, readE_run, bind_run, readEs_run, pure_run]
    generalize feAt sig = v
    have h1 : s.ent + (s.msg + 24) + 40 = s.ent + s.msg + 64 := by omega
    have h2 : s.ent + 40 + s.msg = s.ent + s.msg + 40 := by omega
    have h3 : s.msg + 24 + 24 * (count - 2) = s.msg + 24 * (count - 1) := by omega
    simp only [roundPoly, h1, h2, h3]
  | some r =>
    rw [show sumcheckRoundPoly count claim (some r) = (readEs (count - 1) >>=
      fun tail => pure ((claim + r * sumE tail) :: tail)) from rfl]
    rw [bind_run, readEs_run, pure_run]
    generalize feAt sig = v
    simp only [roundPoly, Nat.add_comm 40]

/-- The reader's state after the rounds `es` of `count` coefficients from `s`. -/
def scState (count : Nat) (s : RS) : List (Option FE) → RS
  | [] => s
  | es => ⟨s.ent + s.msg + es.length * roundLen count, 0, s.ok⟩

theorem sumcheck_cons (claim : FE) (count : Nat) (e : Option FE) (es : List (Option FE)) :
    sumcheck claim count (e :: es) = (sumcheckRoundPoly count claim e >>= fun message =>
      sampleE >>= fun challenge => sumcheck (polyEval message challenge) count es >>= fun r =>
        pure (challenge :: r.1, r.2)) := rfl

/-- **`F`'s sumcheck is `scSpec`** on the stream's scalars; it moves the position by
`|eqs| · roundLen count` and checks nothing. -/
theorem sumcheck_run (sig : ByteArray) (count : Nat) (hc : 2 ≤ count) :
    ∀ (eqs : List (Option FE)) (claim : FE) (s : RS),
      sumcheck claim count eqs sig s = (scSpec (feAt sig) count (s.ent + s.msg) claim eqs, scState count s eqs)
  | [], claim, s => rfl
  | e :: es, claim, s => by
    rw [sumcheck_cons, bind_run, roundPoly_run sig count hc, bind_run, sampleE_run, bind_run,
      sumcheck_run sig count hc es, pure_run]
    have h1 : s.ent + 40 + (s.msg + 24 * (count - 1)) = s.ent + s.msg + 40 + 24 * (count - 1) := by omega
    have h2 : s.ent + 72 + (s.msg + 24 * (count - 1)) + 0 = s.ent + s.msg + roundLen count := by
      simp only [roundLen]; omega
    generalize feAt sig = v
    simp only [h1, h2, scSpec]
    cases es with
    | nil => simp only [scState, List.length_cons, List.length_nil]; congr 2; simp [roundLen]; omega
    | cons e' es' =>
      simp only [scState, List.length_cons]
      congr 1
      simp only [roundLen]
      ring

/-! ## The round template -/

/-- A round's mode: plain, or equality mode with the factor `r` read at an `E` address. -/
inductive Mode where
  | plain
  | eq (r : Addr)

/-- The sources `loc a, …, loc (a + n − 1)`. -/
def locs (a n : Nat) : List Src := (List.range n).map fun m => .loc (a + m)

/-- The `d + 1` loads of a round: the `d` message scalars from lane `q`, then the challenge. -/
def loadsIns (d q str : Nat) : List Ins := (List.range (d + 1)).map fun m => loadI (q + 3 * m) [str]

/-- **One round** of `d + 1 = count` coefficients (degree `d`), its message's first lane at `q`
and `str` lanes per round. Plain: `c₀, c₂ … c_d` loaded at `0 … d − 1`, the challenge at `d`,
`c₁ = claim + c₂ + … + c_d` at `2d − 1`, Horner at `2d … 3d − 1`. Equality: `c₁ … c_d` at
`0 … d − 1`, `c₀ = r·(c₁ + … + c_d) + claim` at `2d`, Horner at `2d + 1 … 3d`. The claim is the
previous iteration's last row. -/
def roundIns (d q str : Nat) : Mode → List Ins
  | .plain => loadsIns d q str ++ sumIns (d + 1) (.prev (3 * d - 1)) (locs 1 (d - 1)) ++
      hornerIns (.loc d) (2 * d) (.loc (d - 1)) ((locs 1 (d - 2)).reverse ++ [.loc (2 * d - 1), .loc 0])
  | .eq r => loadsIns d q str ++ sumIns (d + 1) (.loc 0) (locs 1 (d - 1)) ++
      [mulI (.ext r) (sumSrc (d + 1) (.loc 0) (locs 1 (d - 1))) (.prev (3 * d))] ++
      hornerIns (.loc d) (2 * d + 1) (.loc (d - 1)) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)])

/-- The template's last instruction: the new claim. -/
def Mode.last (d : Nat) : Mode → Nat
  | .plain => 3 * d - 1
  | .eq _ => 3 * d

theorem locs_map (xv : Src → FE) (V : List FE) (a n : Nat) :
    (locs a n).map (Src.val xv V) = (List.range n).map fun m => V.getD (a + m) 0 := by
  simp [locs, Src.val]

theorem loadsIns_length (d q str : Nat) : (loadsIns d q str).length = d + 1 := by simp [loadsIns]

theorem roundIns_length_plain (d q str : Nat) (hd : 2 ≤ d) : (roundIns d q str .plain).length = 3 * d := by
  simp [roundIns, loadsIns_length, sumIns_length, hornerIns_length, locs]; omega

theorem roundIns_length_eq (d q str : Nat) (r : Addr) (hd : 1 ≤ d) :
    (roundIns d q str (.eq r)).length = 3 * d + 1 := by
  simp [roundIns, loadsIns_length, sumIns_length, hornerIns_length, locs]; omega

/-- The value of load `m` of a round. -/
theorem load_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {d q str : Nat}
    (hseg : Seg ins 0 (loadsIns d q str)) (hlen : d + 1 ≤ ins.length) {m : Nat} (hm : m ≤ d) :
    V.getD m 0 = xv (.ext ⟨.K, q + 3 * m, [str]⟩) + FE.y * xv (.ext ⟨.K, q + 3 * m + 1, [str]⟩) +
      FE.y * FE.y * xv (.ext ⟨.K, q + 3 * m + 2, [str]⟩) := by
  have h := hseg m (by rw [loadsIns_length]; omega)
  rw [Nat.zero_add, show (loadsIns d q str).getD m default = loadI (q + 3 * m) [str] by
    simp [loadsIns, List.getD_eq_getElem?_getD, show m < d + 1 by omega]] at h
  rw [fix_at hF (by omega) h (by simp [loadI])]
  rfl

theorem reverse_locs_append (xv : Src → FE) (V : List FE) (a n : Nat) (tail : List Src) :
    ((locs a n).reverse ++ tail).reverse.map (Src.val xv V) =
      tail.reverse.map (Src.val xv V) ++ (List.range n).map fun m => V.getD (a + m) 0 := by
  simp [locs, Src.val, List.reverse_append]

/-- **A plain round's value**: the new claim is `polyEval [c₀, c₁, c₂ … c_d] ρ` with
`c₁ = claim + c₂ + … + c_d`. -/
theorem round_plain_val {xv : Src → FE} {V : List FE} {d q str : Nat} (hd : 2 ≤ d)
    (hF : Fix xv (roundIns d q str .plain) V) :
    V.getD (3 * d - 1) 0 = polyEval (V.getD 0 0 :: (xv (.prev (3 * d - 1)) +
      ((List.range (d - 1)).map fun m => V.getD (1 + m) 0).sum) ::
        ((List.range (d - 1)).map fun m => V.getD (1 + m) 0)) (V.getD d 0) := by
  have hlen := roundIns_length_plain d q str hd
  have hA := loadsIns_length d q str
  have hB := sumIns_length (d + 1) (.prev (3 * d - 1)) (locs 1 (d - 1))
  have hsum := sum_val hF (locs 1 (d - 1)) (d + 1) (.prev (3 * d - 1))
    (by have := seg_append (loadsIns d q str) (sumIns (d + 1) (.prev (3 * d - 1)) (locs 1 (d - 1)))
          (hornerIns (.loc d) (2 * d) (.loc (d - 1)) ((locs 1 (d - 2)).reverse ++ [.loc (2 * d - 1), .loc 0]))
        rw [hA] at this; exact this)
    (by rw [hlen]; simp [locs]; omega)
  have hhor := horner_val hF (.loc d) ((locs 1 (d - 2)).reverse ++ [.loc (2 * d - 1), .loc 0]) (2 * d)
    (.loc (d - 1))
    (by have := seg_append (loadsIns d q str ++ sumIns (d + 1) (.prev (3 * d - 1)) (locs 1 (d - 1)))
          (hornerIns (.loc d) (2 * d) (.loc (d - 1)) ((locs 1 (d - 2)).reverse ++ [.loc (2 * d - 1), .loc 0])) []
        rw [List.append_nil, List.length_append, hA, hB, show (locs 1 (d - 1)).length = d - 1 by simp [locs],
          show d + 1 + (d - 1) = 2 * d by omega] at this
        exact this)
    (by rw [hlen]; simp [locs]; omega)
  have hs1 : sumSrc (d + 1) (.prev (3 * d - 1)) (locs 1 (d - 1)) = .loc (2 * d - 1) := by
    simp only [sumSrc, locs, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by omega)]; congr 1; omega
  have hs2 : sumSrc (2 * d) (.loc (d - 1)) ((locs 1 (d - 2)).reverse ++ [.loc (2 * d - 1), .loc 0]) =
      .loc (3 * d - 1) := by
    simp [sumSrc, locs]; omega
  rw [hs1] at hsum
  rw [hs2] at hhor
  change V.getD (3 * d - 1) 0 = _ at hhor
  rw [hhor, show hornerVal _ _ _ = hornerVal _ _ (((locs 1 (d - 2)).reverse ++
      [Src.loc (2 * d - 1), .loc 0]).reverse.reverse.map (Src.val xv V)) by rw [List.reverse_reverse],
    List.map_reverse, ← polyEval_horner, reverse_locs_append]
  change polyEval (_ ++ [V.getD (d - 1) 0]) (V.getD d 0) = _
  congr 1
  change V.getD (2 * d - 1) 0 = _ at hsum
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append,
    List.map_cons, List.map_nil, Src.val]
  rw [hsum, locs_map]
  have hr : (List.range (d - 1)) = List.range (d - 2) ++ [d - 2] := by
    rw [show d - 1 = d - 2 + 1 by omega, List.range_succ]
  rw [hr]
  simp only [List.map_append, List.map_cons, List.map_nil, show 1 + (d - 2) = d - 1 by omega]
  rfl

/-- **An equality-mode round's value**: `polyEval [c₀, c₁ … c_d] ρ` with
`c₀ = claim + r·(c₁ + … + c_d)`. -/
theorem round_eq_val {xv : Src → FE} {V : List FE} {d q str : Nat} {r : Addr} (hd : 1 ≤ d)
    (hF : Fix xv (roundIns d q str (.eq r)) V) :
    V.getD (3 * d) 0 = polyEval ((xv (.prev (3 * d)) + xv (.ext r) *
      ((List.range d).map fun m => V.getD m 0).sum) ::
        ((List.range d).map fun m => V.getD m 0)) (V.getD d 0) := by
  have hlen := roundIns_length_eq d q str r hd
  have hA := loadsIns_length d q str
  have hB := sumIns_length (d + 1) (.loc 0) (locs 1 (d - 1))
  have hL : (locs 1 (d - 1)).length = d - 1 := by simp [locs]
  set S := sumSrc (d + 1) (.loc 0) (locs 1 (d - 1)) with hS
  have hsum := sum_val hF (locs 1 (d - 1)) (d + 1) (.loc 0)
    (by have := seg_append (loadsIns d q str) (sumIns (d + 1) (.loc 0) (locs 1 (d - 1)))
          ([mulI (.ext r) S (.prev (3 * d))] ++
            hornerIns (.loc d) (2 * d + 1) (.loc (d - 1)) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)]))
        rw [hA] at this; simpa [roundIns, List.append_assoc] using this)
    (by rw [hlen, hL]; omega)
  have hmul : V.getD (2 * d) 0 = xv (.ext r) * S.val xv V + xv (.prev (3 * d)) := by
    have hseg := seg_append (loadsIns d q str ++ sumIns (d + 1) (.loc 0) (locs 1 (d - 1)))
      [mulI (.ext r) S (.prev (3 * d))]
      (hornerIns (.loc d) (2 * d + 1) (.loc (d - 1)) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)]))
    rw [List.length_append, hA, hB, hL, show d + 1 + (d - 1) = 2 * d by omega] at hseg
    have h0 := hseg 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [fix_at hF (by omega) (by simpa [roundIns, List.append_assoc] using h0) (by simp [mulI]), eval_mulI]
    rfl
  have hhor := horner_val hF (.loc d) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)]) (2 * d + 1)
    (.loc (d - 1))
    (by have := seg_append (loadsIns d q str ++ sumIns (d + 1) (.loc 0) (locs 1 (d - 1)) ++
            [mulI (.ext r) S (.prev (3 * d))])
          (hornerIns (.loc d) (2 * d + 1) (.loc (d - 1)) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)])) []
        rw [List.append_nil, List.length_append, List.length_append, hA, hB, hL,
          show d + 1 + (d - 1) + [mulI (.ext r) S (.prev (3 * d))].length = 2 * d + 1 by simp; omega] at this
        simpa [roundIns, List.append_assoc] using this)
    (by rw [hlen]; simp [locs]; omega)
  have hs2 : sumSrc (2 * d + 1) (.loc (d - 1)) ((locs 0 (d - 1)).reverse ++ [.loc (2 * d)]) = .loc (3 * d) := by
    simp [sumSrc, locs]; omega
  rw [hs2] at hhor
  change V.getD (3 * d) 0 = _ at hhor
  rw [hhor, show hornerVal _ _ _ = hornerVal _ _ (((locs 0 (d - 1)).reverse ++
      [Src.loc (2 * d)]).reverse.reverse.map (Src.val xv V)) by rw [List.reverse_reverse],
    List.map_reverse, ← polyEval_horner, reverse_locs_append]
  change polyEval (_ ++ [V.getD (d - 1) 0]) (V.getD d 0) = _
  congr 1
  have hSv : S.val xv V = ((List.range d).map fun m => V.getD m 0).sum := by
    rw [hsum, locs_map]
    have hr : List.range d = 0 :: (List.range (d - 1)).map (· + 1) := by
      rw [show d = d - 1 + 1 by omega, List.range_succ_eq_map]; simp
    rw [hr]
    simp [Src.val, Nat.add_comm 1, Function.comp_def]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, Src.val,
    List.cons_append]
  rw [hmul, hSv]
  have hr : List.range d = List.range (d - 1) ++ [d - 1] := by
    rw [show d = d - 1 + 1 by omega, List.range_succ]; simp
  congr 1
  · ring
  · conv_rhs => rw [hr]
    simp

/-! ## `scSpec`, round by round -/

/-- One round of `F`'s sumcheck at position `p`. -/
def scStep (v : Nat → FE) (count p : Nat) (claim : FE) (e : Option FE) : FE :=
  polyEval (roundPoly v p count claim e) (v (p + 40 + 24 * (count - 1)))

theorem scSpec_snd_take (v : Nat → FE) (count : Nat) : ∀ (i : Nat) (es : List (Option FE)) (p : Nat) (claim : FE),
    i < es.length →
    (scSpec v count p claim (es.take (i + 1))).2 =
      scStep v count (p + i * roundLen count) (scSpec v count p claim (es.take i)).2 (es.getD i none)
  | 0, e :: es, p, claim, _ => by simp [scSpec, scStep]
  | i + 1, e :: es, p, claim, h => by
    simp only [List.take_succ_cons, scSpec, List.getD_cons_succ]
    rw [scSpec_snd_take v count i es _ _ (by simp at h; omega)]
    congr 1
    ring

theorem scSpec_fst_getD (v : Nat → FE) (count : Nat) : ∀ (i : Nat) (es : List (Option FE)) (p : Nat) (claim : FE),
    i < es.length →
    (scSpec v count p claim es).1.getD i 0 = v (p + i * roundLen count + 40 + 24 * (count - 1))
  | 0, e :: es, p, claim, _ => by simp [scSpec]
  | i + 1, e :: es, p, claim, h => by
    simp only [scSpec, List.getD_cons_succ]
    rw [scSpec_fst_getD v count i es _ _ (by simp at h; omega)]
    congr 1
    ring

/-! ## The gadget -/

/-- Lanes per round: `roundLen count / 8`. -/
def roundLanes (count : Nat) : Nat := 9 + 3 * (count - 1)

theorem roundLen_eq (count : Nat) : roundLen count = 8 * roundLanes count := by
  simp only [roundLen, roundLanes]; omega

/-- The template of a sumcheck of `d + 1` coefficients whose first message lane is `q`. -/
def scTpl (d q : Nat) (mode : Mode) : List Ins := roundIns d q (roundLanes (d + 1)) mode

/-- **The sumcheck gadget**: `2^D` iterations of the round template after a prologue holding the
initial claim. Rounds past the sumcheck's (`R ≤ 2^D`) compute values nobody reads. -/
def scGadget (D d q : Nat) (mode : Mode) (claim : Cell) : BM LoopOut :=
  loopP [D] (tplOf (scTpl d q mode)) (fun _ => claim)

/-- The equality factors a mode gives `F`'s sumcheck: none, or the cells `r` at round `i`. -/
def modeEqs (M : Mem) (R : Nat) : Mode → List (Option FE)
  | .plain => List.replicate R none
  | .eq r => (List.range R).map fun i => some (M.rd r.ty (r.at [i]))

theorem scTpl_ok_2 (q : Nat) : SLok (scTpl 2 q .plain) = true := rfl
theorem scTpl_ok_3 (q : Nat) : SLok (scTpl 3 q .plain) = true := rfl
theorem scTpl_ok_eq2 (q : Nat) (r : Addr) : SLok (scTpl 2 q (.eq r)) = true := rfl

/-- The loads of iteration `jf` are the stream's scalars. -/
theorem sc_loads {c : Ctx} {M : Mem} {p : Ptr} {D d q : Nat} {mode : Mode} {claim : Cell}
    {sig : ByteArray} {T : Nat} (hok : SLok (scTpl d q mode) = true)
    (hS : Streamed M sig T) (h : SegsHold c M p (scGadget D d q mode claim p).2) {jf : Nat}
    (hjf : jf < 2 ^ D) (hT : q + roundLanes (d + 1) * jf + 3 * d + 3 ≤ T) {m : Nat} (hm : m ≤ d) :
    (iterV M (scGadget D d q mode claim p).1 (scTpl d q mode).length jf).getD m 0 =
      feAt sig (8 * (q + 3 * m + roundLanes (d + 1) * jf)) := by
  have hF : Fix (iterXv M (scGadget D d q mode claim p).1 jf) (scTpl d q mode)
      (iterV M (scGadget D d q mode claim p).1 (scTpl d q mode).length jf) :=
    fix_of_loopP (dims := [D]) hok h (jf := jf) (by simpa using hjf)
  have hlen : d + 1 ≤ (scTpl d q mode).length := by
    cases mode <;> simp [scTpl, roundIns, loadsIns_length]
  have hseg : Seg (scTpl d q mode) 0 (loadsIns d q (roundLanes (d + 1))) := by
    obtain ⟨B, hB⟩ : ∃ B, scTpl d q mode = loadsIns d q (roundLanes (d + 1)) ++ B := by
      cases mode <;> exact ⟨_, by simp only [scTpl, roundIns, List.append_assoc]; rfl⟩
    rw [hB]
    have := seg_append [] (loadsIns d q (roundLanes (d + 1))) B
    simpa using this
  rw [load_val hF hseg hlen hm]
  have ho : (scGadget D d q mode claim p).1.dims = [D] := rfl
  rw [iterXv_ext1 M _ ho hjf, iterXv_ext1 M _ ho hjf, iterXv_ext1 M _ ho hjf]
  simp only [Mem.rd]
  rw [show q + 3 * m + 1 + roundLanes (d + 1) * jf = q + 3 * m + roundLanes (d + 1) * jf + 1 by omega,
    show q + 3 * m + 2 + roundLanes (d + 1) * jf = q + 3 * m + roundLanes (d + 1) * jf + 2 by omega]
  exact load_feAt hS (by omega)

theorem sc_pos (q d jf : Nat) (hq : 5 ≤ q) (m : Nat) :
    8 * q - 40 + jf * roundLen (d + 1) + 40 + 24 * m = 8 * (q + 3 * m + roundLanes (d + 1) * jf) := by
  rw [roundLen_eq]; ring_nf; omega

theorem sumE_eq_sum (l : List FE) : sumE l = l.sum := by
  rw [sumE, foldl_add, zero_add]

/-- One iteration of the plain gadget is one round of `F`'s sumcheck, from the claim its `prev`
operand reads. -/
theorem sc_iter_plain {c : Ctx} {M : Mem} {p : Ptr} {D d q : Nat} {claim : Cell}
    {sig : ByteArray} {T : Nat} (hd : 2 ≤ d) (hok : SLok (scTpl d q .plain) = true)
    (hq : 5 ≤ q) (hS : Streamed M sig T) (h : SegsHold c M p (scGadget D d q .plain claim p).2)
    {jf : Nat} (hjf : jf < 2 ^ D) (hT : q + roundLanes (d + 1) * jf + 3 * d + 3 ≤ T) :
    ((scGadget D d q .plain claim p).1.cell d jf).val M =
        feAt sig (8 * q - 40 + jf * roundLen (d + 1) + 40 + 24 * d) ∧
    ((scGadget D d q .plain claim p).1.cell (3 * d - 1) jf).val M =
      scStep (feAt sig) (d + 1) (8 * q - 40 + jf * roundLen (d + 1))
        ((Opd.prev (3 * d - 1)).val M (scGadget D d q .plain claim p).1 jf) none := by
  have hlen : (scTpl d q .plain).length = 3 * d := roundIns_length_plain d q _ hd
  have hF : Fix (iterXv M (scGadget D d q .plain claim p).1 jf) (scTpl d q .plain)
      (iterV M (scGadget D d q .plain claim p).1 (scTpl d q .plain).length jf) :=
    fix_of_loopP (dims := [D]) hok h (jf := jf) (by simpa using hjf)
  have hv : ∀ m ≤ d, (iterV M (scGadget D d q .plain claim p).1 (scTpl d q .plain).length jf).getD m 0 =
      feAt sig (8 * q - 40 + jf * roundLen (d + 1) + 40 + 24 * m) := by
    intro m hm
    rw [sc_loads hok hS h hjf hT hm, sc_pos q d jf hq m]
  have hc : ∀ t < 3 * d, ((scGadget D d q .plain claim p).1.cell t jf).val M =
      (iterV M (scGadget D d q .plain claim p).1 (scTpl d q .plain).length jf).getD t 0 := by
    intro t ht; rw [iterV_getD M _ (by omega)]
  refine ⟨by rw [hc d (by omega), hv d le_rfl], ?_⟩
  rw [hc _ (by omega), round_plain_val hd hF]
  unfold scStep roundPoly
  rw [hv 0 (by omega), hv d le_rfl, sumE_eq_sum]
  have hl : ((List.range (d - 1)).map fun m =>
      (iterV M (scGadget D d q .plain claim p).1 (scTpl d q .plain).length jf).getD (1 + m) 0) =
      scalarsAt (feAt sig) (8 * q - 40 + jf * roundLen (d + 1) + 64) (d + 1 - 2) := by
    rw [show d + 1 - 2 = d - 1 by omega, scalarsAt]
    apply List.map_congr_left
    intro m hm
    rw [hv (1 + m) (by simp at hm; omega)]
    congr 1; ring
  rw [hl]
  rfl

theorem roundIns_noA (d q str : Nat) (mode : Mode) :
    ∀ i ∈ roundIns d q str mode, i.op ≠ .assert0 := by
  have hs : ∀ (n : Nat) (s : Src) (cs : List Src), ∀ i ∈ sumIns n s cs, i.op ≠ .assert0 := by
    intro n s cs
    induction cs generalizing n s with
    | nil => simp [sumIns]
    | cons c cs ih =>
      intro i hi
      simp only [sumIns, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [addI, linI]
      · exact ih _ _ i hi
  have hh : ∀ (x : Src) (n : Nat) (s : Src) (cs : List Src), ∀ i ∈ hornerIns x n s cs, i.op ≠ .assert0 := by
    intro x n s cs
    induction cs generalizing n s with
    | nil => simp [hornerIns]
    | cons c cs ih =>
      intro i hi
      simp only [hornerIns, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [mulI]
      · exact ih _ _ i hi
  have hl : ∀ i ∈ loadsIns d q str, i.op ≠ .assert0 := by
    intro i hi
    simp only [loadsIns, List.mem_map] at hi
    obtain ⟨_, _, rfl⟩ := hi
    simp [loadI]
  intro i hi
  cases mode with
  | plain =>
    simp only [roundIns, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact hl i hi
    · exact hs _ _ _ i hi
    · exact hh _ _ _ _ i hi
  | eq r =>
    simp only [roundIns, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact hl i hi
    · exact hs _ _ _ i hi
    · rw [hi]; simp [mulI]
    · exact hh _ _ _ _ i hi

theorem tplOf_op_ne (ins : List Ins) (hA : ∀ i ∈ ins, i.op ≠ .assert0) {t : Nat} (ht : t < ins.length) :
    ((tplOf ins).getD t default).op ≠ .assert0 := by
  rw [tplOf_getD ins ht]
  exact hA _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)

/-- **The plain sumcheck gadget computes `F`'s sumcheck**: iteration `i < R` holds challenge `i`
(row `d`) and the claim after round `i + 1` (the last row). -/
theorem sc_spec_plain {c : Ctx} {M : Mem} {p : Ptr} {D d q R : Nat} {claim : Cell}
    {sig : ByteArray} {T : Nat} (hd : 2 ≤ d) (hok : SLok (scTpl d q .plain) = true) (hR : R ≤ 2 ^ D)
    (hq : 5 ≤ q) (hS : Streamed M sig T) (hT : q + roundLanes (d + 1) * R + 3 * d + 3 ≤ T)
    (h : SegsHold c M p (scGadget D d q .plain claim p).2) :
    ∀ i < R,
      ((scGadget D d q .plain claim p).1.cell d i).val M =
          (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) (List.replicate R none)).1.getD i 0 ∧
      ((scGadget D d q .plain claim p).1.cell (3 * d - 1) i).val M =
          (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) ((List.replicate R none).take (i + 1))).2 := by
  have hlen : (scTpl d q .plain).length = 3 * d := roundIns_length_plain d q _ hd
  have hstr : ∀ i < R, q + roundLanes (d + 1) * i + 3 * d + 3 ≤ T := by
    intro i hi
    have : roundLanes (d + 1) * i ≤ roundLanes (d + 1) * R := Nat.mul_le_mul_left _ hi.le
    omega
  have hch : ∀ i < R, ((scGadget D d q .plain claim p).1.cell d i).val M =
      (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) (List.replicate R none)).1.getD i 0 := by
    intro i hi
    rw [(sc_iter_plain hd hok hq hS h (by omega) (hstr i hi)).1,
      scSpec_fst_getD _ _ i _ _ _ (by simpa using hi)]
    congr 1
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨hch 0 hi, ?_⟩
    rw [(sc_iter_plain hd hok hq hS h (jf := 0) (by omega) (hstr 0 hi)).2,
      scSpec_snd_take _ _ 0 _ _ _ (by simpa using hi)]
    have hp : (Opd.prev (3 * d - 1)).val M (scGadget D d q .plain claim p).1 0 = claim.val M :=
      loopP_prev_zero h (by rw [tplOf, List.length_map, hlen]; omega)
        (tplOf_op_ne _ (roundIns_noA d q _ .plain) (by rw [roundIns_length_plain _ _ _ hd]; omega))
    rw [hp]
    simp [scSpec, List.getD_eq_getElem?_getD]
  | succ i ih =>
    intro hi
    refine ⟨hch (i + 1) hi, ?_⟩
    rw [(sc_iter_plain hd hok hq hS h (jf := i + 1) (by omega) (hstr (i + 1) hi)).2,
      scSpec_snd_take _ _ (i + 1) _ _ _ (by simpa using hi)]
    have hp : (Opd.prev (3 * d - 1)).val M (scGadget D d q .plain claim p).1 (i + 1) =
        ((scGadget D d q .plain claim p).1.cell (3 * d - 1) i).val M :=
      loopP_prev_succ M [D] _ _ p (by simp; omega) _
    rw [hp, (ih (by omega)).2]
    simp [List.getD_eq_getElem?_getD, show i + 1 < R from hi]

/-- One iteration of the equality-mode gadget is one round of `F`'s sumcheck with factor `r`. -/
theorem sc_iter_eq {c : Ctx} {M : Mem} {p : Ptr} {D d q : Nat} {r : Addr} {claim : Cell}
    {sig : ByteArray} {T : Nat} (hd : 1 ≤ d) (hok : SLok (scTpl d q (.eq r)) = true)
    (hq : 5 ≤ q) (hS : Streamed M sig T) (h : SegsHold c M p (scGadget D d q (.eq r) claim p).2)
    {jf : Nat} (hjf : jf < 2 ^ D) (hT : q + roundLanes (d + 1) * jf + 3 * d + 3 ≤ T) :
    ((scGadget D d q (.eq r) claim p).1.cell d jf).val M =
        feAt sig (8 * q - 40 + jf * roundLen (d + 1) + 40 + 24 * d) ∧
    ((scGadget D d q (.eq r) claim p).1.cell (3 * d) jf).val M =
      scStep (feAt sig) (d + 1) (8 * q - 40 + jf * roundLen (d + 1))
        ((Opd.prev (3 * d)).val M (scGadget D d q (.eq r) claim p).1 jf)
        (some (M.rd r.ty (r.at (unflat [D] jf)))) := by
  have hlen : (scTpl d q (.eq r)).length = 3 * d + 1 := roundIns_length_eq d q _ r hd
  have hF : Fix (iterXv M (scGadget D d q (.eq r) claim p).1 jf) (scTpl d q (.eq r))
      (iterV M (scGadget D d q (.eq r) claim p).1 (scTpl d q (.eq r)).length jf) :=
    fix_of_loopP (dims := [D]) hok h (jf := jf) (by simpa using hjf)
  have hv : ∀ m ≤ d, (iterV M (scGadget D d q (.eq r) claim p).1 (scTpl d q (.eq r)).length jf).getD m 0 =
      feAt sig (8 * q - 40 + jf * roundLen (d + 1) + 40 + 24 * m) := by
    intro m hm
    rw [sc_loads hok hS h hjf hT hm, sc_pos q d jf hq m]
  have hc : ∀ t < 3 * d + 1, ((scGadget D d q (.eq r) claim p).1.cell t jf).val M =
      (iterV M (scGadget D d q (.eq r) claim p).1 (scTpl d q (.eq r)).length jf).getD t 0 := by
    intro t ht; rw [iterV_getD M _ (by omega)]
  refine ⟨by rw [hc d (by omega), hv d le_rfl], ?_⟩
  rw [hc _ (by omega), round_eq_val hd hF]
  unfold scStep roundPoly
  rw [hv d le_rfl, sumE_eq_sum]
  have hl : ((List.range d).map fun m =>
      (iterV M (scGadget D d q (.eq r) claim p).1 (scTpl d q (.eq r)).length jf).getD m 0) =
      scalarsAt (feAt sig) (8 * q - 40 + jf * roundLen (d + 1) + 40) (d + 1 - 1) := by
    rw [show d + 1 - 1 = d by omega, scalarsAt]
    apply List.map_congr_left
    intro m hm
    rw [hv m (by simp at hm; omega)]
  rw [hl, show d + 1 - 1 = d by omega]
  dsimp only
  rw [sumE_eq_sum]
  rfl

/-- **The equality-mode sumcheck gadget computes `F`'s sumcheck** with the factors read at `r`. -/
theorem sc_spec_eq {c : Ctx} {M : Mem} {p : Ptr} {D d q R : Nat} {r : Addr} {claim : Cell}
    {sig : ByteArray} {T : Nat} (hd : 1 ≤ d) (hok : SLok (scTpl d q (.eq r)) = true) (hR : R ≤ 2 ^ D)
    (hq : 5 ≤ q) (hS : Streamed M sig T) (hT : q + roundLanes (d + 1) * R + 3 * d + 3 ≤ T)
    (hr : r.strides.length ≤ 1)
    (h : SegsHold c M p (scGadget D d q (.eq r) claim p).2) :
    ∀ i < R,
      ((scGadget D d q (.eq r) claim p).1.cell d i).val M =
          (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) (modeEqs M R (.eq r))).1.getD i 0 ∧
      ((scGadget D d q (.eq r) claim p).1.cell (3 * d) i).val M =
          (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) ((modeEqs M R (.eq r)).take (i + 1))).2 := by
  have hlen : (scTpl d q (.eq r)).length = 3 * d + 1 := roundIns_length_eq d q _ r hd
  have hstr : ∀ i < R, q + roundLanes (d + 1) * i + 3 * d + 3 ≤ T := by
    intro i hi
    have : roundLanes (d + 1) * i ≤ roundLanes (d + 1) * R := Nat.mul_le_mul_left _ hi.le
    omega
  have hmodlen : (modeEqs M R (.eq r)).length = R := by simp [modeEqs]
  have hge : ∀ i < R, (modeEqs M R (.eq r)).getD i none = some (M.rd r.ty (r.at (unflat [D] i))) := by
    intro i hi
    rw [show unflat [D] i = [i] by simp only [unflat, Nat.mod_eq_of_lt (show i < 2 ^ D by omega)]]
    simp [modeEqs, List.getD_eq_getElem?_getD, hi]
  have hch : ∀ i < R, ((scGadget D d q (.eq r) claim p).1.cell d i).val M =
      (scSpec (feAt sig) (d + 1) (8 * q - 40) (claim.val M) (modeEqs M R (.eq r))).1.getD i 0 := by
    intro i hi
    rw [(sc_iter_eq hd hok hq hS h (by omega) (hstr i hi)).1,
      scSpec_fst_getD _ _ i _ _ _ (by rw [hmodlen]; exact hi), Nat.add_sub_cancel]
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨hch 0 hi, ?_⟩
    rw [(sc_iter_eq hd hok hq hS h (jf := 0) (by omega) (hstr 0 hi)).2,
      scSpec_snd_take _ _ 0 _ _ _ (by rw [hmodlen]; exact hi), hge 0 hi]
    have hp : (Opd.prev (3 * d)).val M (scGadget D d q (.eq r) claim p).1 0 = claim.val M :=
      loopP_prev_zero h (by rw [tplOf, List.length_map, hlen]; omega)
        (tplOf_op_ne _ (roundIns_noA d q _ (.eq r)) (by rw [roundIns_length_eq _ _ _ _ hd]; omega))
    rw [hp]
    simp [scSpec]
  | succ i ih =>
    intro hi
    refine ⟨hch (i + 1) hi, ?_⟩
    rw [(sc_iter_eq hd hok hq hS h (jf := i + 1) (by omega) (hstr (i + 1) hi)).2,
      scSpec_snd_take _ _ (i + 1) _ _ _ (by rw [hmodlen]; exact hi), hge (i + 1) hi]
    have hp : (Opd.prev (3 * d)).val M (scGadget D d q (.eq r) claim p).1 (i + 1) =
        ((scGadget D d q (.eq r) claim p).1.cell (3 * d) i).val M :=
      loopP_prev_succ M [D] _ _ p (by simp; omega) _
    rw [hp, (ih (by omega)).2]

end Lvm.Q1
