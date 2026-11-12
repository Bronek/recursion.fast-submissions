-- New for lvm (WP-14a): the query correspondence: V_S's driver, the compiled verifier's run and the
-- program read off the stream move in lockstep over the schedule's atoms.
import LvmVEqSimOpen

/-!
# The simulation

For a program `P` that follows the atoms `as` (`Fol`), a run of V_S's driver over `as` that the
trace `tr` accepts, and the program read off `Σ = traceBytesB tr` (`ivp`) returning `a`: the compiled
verifier's run of `P` (`runK`) asks the same queries on `tr`, reads the same values, and reaches its
continuation with `a`, at a state that again matches the driver's (`J`) — `sim`.

`J`: the compiled run's state is the driver's (`st`, the absorbed-but-unsqueezed bytes
`π[pend, off)`, the rest of the body `π[off..]`, the commitment records of the caps read at the
driver's cap offsets, `CapsJ`), and the stream cursor is at entry `i` with `off − pend` message
bytes read.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

section Sim

variable (S : Scheme) (π : ByteArray) (tr : Trace) (p : Params)

/-- The compiled verifier's commitment records against the driver's caps. -/
def CapsJ (caps : List CapI) (dcaps : List (Ref × ℕ)) (cr : List Ref) : Prop :=
  ∃ offs : List ℕ, offs.length = cr.length ∧ dcaps = (cr.zip offs).reverse ∧
    caps = (cr.zip offs).map (fun ro ↦ S.capI (shpS (idxS ro.1)).1 (shpS (idxS ro.1)).2
      ((blb π).drop ro.2)) ∧
    (∀ j (hj : j < cr.length), idxS cr[j] = j) ∧ cr.Nodup

/-- **The states match.** -/
structure J (s : DSt) (st : Digest) (buf : List UInt8) (caps : List CapI) (body : List UInt8)
    (rs : RS) (i : ℕ) (cr : List Ref) : Prop where
  st : st = s.st
  pend : s.pend ≤ s.off
  off : s.off ≤ π.size
  buf : buf = ((blb π).drop s.pend).take (s.off - s.pend)
  body : body = (blb π).drop s.off
  ent : rs.ent = entOff tr i
  msg : rs.msg = s.off - s.pend
  caps : CapsJ S π caps s.caps cr

/-- The pending positions are below `2^h` for a height `h` of the position samples. -/
def PosOK (pp hs : List ℕ) : Prop := ∀ q ∈ pp, ∃ h ∈ hs, q < 2 ^ h

variable {S π tr p}

/-- The body cursor bound from an accepting run. -/
theorem bound_of_drive {as : List Atom} {s : DSt} {k : DSt → OProg Bool} {i : ℕ}
    (hk : ∀ s' n, (k s').runSeq (tr.drop n) = some true → s'.off ≤ π.size)
    (h : (driveAtoms p π as s k).runSeq (tr.drop i) = some true) : s.off + pendA as ≤ π.size := by
  obtain ⟨s', n, h1, -, h3, -⟩ := drive_run p π as s k _ h
  have := hk s' (i + n) (by rw [← List.drop_drop]; exact h1)
  omega

/-- After pending bytes, a Fiat–Shamir query comes. -/
theorem nextFS_of_stA : ∀ (as : List Atom) (pend : ℕ) (cr : List Ref) (hs : List ℕ),
    stA p as pend cr hs = true → 0 < pend → NextFS as
  | [], pend, _, _, h, hp => by simp only [stA, beq_iff_eq] at h; omega
  | .rd :: as, pend, cr, hs, h, _ => nextFS_of_stA as _ cr hs h (by simp [eBytes])
  | .cap c r :: as, pend, cr, hs, h, _ => by
    simp only [stA, Bool.and_eq_true] at h
    exact nextFS_of_stA as _ _ hs h.2 (by simp only [nodeBytes]; positivity)
  | .sm :: _, _, _, _, _, _ => trivial
  | .pclr :: as, pend, cr, hs, h, hp => nextFS_of_stA as pend cr [] h hp
  | .ps _ _ :: _, _, _, _, _, _ => trivial
  | .op r :: as, pend, cr, hs, h, hp => by
    simp only [stA, Bool.and_eq_true, beq_iff_eq] at h; omega

/-- **The message bytes on the stream**: under a lookahead entry `st ‖ π[pend, E)`, the message
bytes from `off` are `π`'s. -/
theorem msg_bytes {i : ℕ} {st : Digest} {pend off E n : ℕ} {a₀ : Digest} {rest : Trace}
    (hdrop : tr.drop i = (digestBytes st ++ π.extract pend E, a₀) :: rest) (hE : E ≤ π.size)
    (hpo : pend ≤ off) (hoE : off + n ≤ E) :
    sbs (traceBytesB tr) (entOff tr i + 40 + (off - pend)) n = ((blb π).drop off).take n := by
  have hsz : (digestBytes st ++ π.extract pend E).size = 32 + (E - pend) := by
    rw [ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]; simp [length_blb]; omega
  have := (stream_entry hdrop).1 (32 + (off - pend)) n (by rw [hsz]; omega)
  rw [show entOff tr i + 40 + (off - pend) = entOff tr i + 8 + (32 + (off - pend)) by omega, this,
    blb_append, blb_digestBytes, blb_extract, drop_app_len (show st.toList.length = 32 by simp),
    List.drop_take, List.drop_drop, show pend + (off - pend) = off by omega, List.take_take]
  congr 1; omega

end Sim

theorem find_unique {l : List (Ref × ℕ)} {r : Ref} {o : ℕ} (hmem : (r, o) ∈ l)
    (hu : ∀ x ∈ l, x.1 = r → x.2 = o) : (l.find? (·.1 == r)).map (·.2) = some o := by
  induction l with
  | nil => simp at hmem
  | cons x l ih =>
    by_cases hx : x.1 = r
    · simp [List.find?_cons, hx, hu x List.mem_cons_self hx]
    · have hx' : (x.1 == r) = false := by simpa using hx
      rw [List.find?_cons, hx']
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd (by rw [← h]) hx
      · exact ih h fun y hy ↦ hu y (List.mem_cons_of_mem _ hy)

/-- A committed oracle's cap: the driver finds its offset, the compiled verifier its record. -/
theorem capsJ_lookup {S : Scheme} {π : ByteArray} {caps : List CapI} {dcaps : List (Ref × ℕ)} {cr : List Ref} {r : Ref}
    (h : CapsJ S π caps dcaps cr) (hr : r ∈ cr) :
    ∃ capOff, (dcaps.find? (·.1 == r)).map (·.2) = some capOff ∧
      caps[idxS r]? = some (S.capI (shpS (idxS r)).1 (shpS (idxS r)).2 ((blb π).drop capOff)) := by
  obtain ⟨offs, hlen, hd, hc, hidx, hnd⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hjo : j < offs.length := by omega
  refine ⟨offs[j], ?_, ?_⟩
  · rw [hd]
    apply find_unique
    · rw [List.mem_reverse]
      exact List.mem_iff_getElem.mpr ⟨j, by simp [hlen]; omega, by simp⟩
    · intro x hx hxr
      rw [List.mem_reverse] at hx
      obtain ⟨j', hj', hx'⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_zip, Nat.lt_min] at hj'
      rw [← hx'] at hxr ⊢
      simp only [List.getElem_zip] at hxr ⊢
      have := (List.Nodup.getElem_inj_iff hnd).mp hxr
      subst this; rfl
  · have hz : (cr.zip offs)[j]? = some (cr[j], offs[j]) := by
      rw [List.getElem?_eq_getElem (by simp; omega)]; simp
    rw [hc, hidx j hj, List.getElem?_map, hz, Option.map_some, hidx j hj]

theorem buf_ext (l : List UInt8) {pend off : ℕ} (h : pend ≤ off) (n : ℕ) :
    (l.drop pend).take (off - pend) ++ (l.drop off).take n = (l.drop pend).take (off + n - pend) := by
  rw [show off + n - pend = (off - pend) + n by omega, List.take_add, List.drop_drop,
    show pend + (off - pend) = off by omega]

theorem capS_le (i : ℕ) : capS (shpS i).1 (shpS i).2 ≤ (shpS i).1 := by
  rcases i with _ | _ | _ | _ | _ | i <;> simp [capS, shpS]

section FS

variable {S : Scheme} {π : ByteArray} {tr : Trace}

theorem J.fsQ {s : DSt} {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8}
    {rs : RS} {i : ℕ} {cr : List Ref} (hJ : J S π tr s st buf caps body rs i cr) :
    toQ (st.toList ++ buf) = digestBytes s.st ++ π.extract s.pend s.off ∧
      buf.length = s.off - s.pend := by
  have hpo := hJ.pend
  have hoff := hJ.off
  refine ⟨toQ_eq ?_, ?_⟩
  · rw [blb_append, blb_digestBytes, blb_extract, hJ.st, hJ.buf]
  · rw [hJ.buf]; simp [length_blb]; omega

/-- **A Fiat–Shamir query in lockstep**: the stream's answer, and the states after it. -/
theorem J.fs {s : DSt} {st : Digest} {buf : List UInt8} {caps : List CapI} {body : List UInt8}
    {rs : RS} {i : ℕ} {cr : List Ref} {a₀ : Digest} {rest : Trace}
    (hJ : J S π tr s st buf caps body rs i cr)
    (hdrop : tr.drop i = (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: rest) :
    digestAt (traceBytesB tr) (rs.ent + 40 + rs.msg) = a₀ ∧ tr.drop (i + 1) = rest ∧
      ∀ s₁ : DSt, s₁.off = s.off → s₁.pend = s.off → s₁.st = a₀ → s₁.caps = s.caps →
        J S π tr s₁ a₀ [] caps body { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } (i + 1) cr := by
  have hpo := hJ.pend
  have hoff := hJ.off
  have hsz : (digestBytes s.st ++ π.extract s.pend s.off).size = 32 + (s.off - s.pend) := by
    rw [ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]; simp [length_blb]; omega
  have he := stream_entry hdrop
  refine ⟨?_, by rw [← List.drop_drop, hdrop]; rfl, fun s₁ h1 h2 h3 h4 ↦ ?_⟩
  · rw [hJ.ent, hJ.msg, show entOff tr i + 40 + (s.off - s.pend) = entOff tr i + 8 + (32 + (s.off - s.pend)) by
      omega, ← hsz]
    exact he.2.1
  · refine ⟨h3.symm, by omega, by omega, by rw [h1, h2]; simp, by rw [h1]; exact hJ.body, ?_, ?_, ?_⟩
    · show rs.ent + 72 + rs.msg = _
      rw [he.2.2, hJ.ent, hJ.msg, hsz]; omega
    · show 0 = _; omega
    · rw [h4]; exact hJ.caps

end FS

section Main

variable {S : Scheme} {π : ByteArray} {tr : Trace} {p : Params}

theorem take_drop_append (l : List UInt8) (a m n : ℕ) (h : a + m + n ≤ l.length) :
    (l.drop a).take m ++ (l.drop (a + m)).take n = (l.drop a).take (m + n) := by
  rw [List.take_add, List.drop_drop]

/-- **The simulation.** -/
theorem sim (hdecE : S.decE = eOfBytes) (hchal : S.chal = chalOf) (hdecK : S.decK = kOfBytes)
    (hcap : S.capOf = capS) (hocc : S.occ = occS) : ∀ (as : List Atom) {α : Type} (P : VerifierProgram α) (pp : List ℕ)
    (Q : α → List ℕ → Prop) (s : DSt) (st : Digest) (buf : List UInt8) (caps : List CapI)
    (body : List UInt8) (rs : RS) (i : ℕ) (cr : List Ref) (hs : List ℕ) (k : DSt → OProg Bool)
    (a : α) (rs' : RS),
    Fol capS shpS idxS P as pp Q → stA p as (s.off - s.pend) cr hs = true →
    J S π tr s st buf caps body rs i cr → s.pos = pp → PosOK pp hs →
    (∀ s' n, (k s').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (driveAtoms p π as s k).runSeq (tr.drop i) = some true →
    ivp capS occS shpS P (traceBytesB tr) rs = (some a, rs') →
    ∃ s' st' buf' caps' body' i' cr', J S π tr s' st' buf' caps' body' rs' i' cr' ∧
      (k s').runSeq (tr.drop i') = some true ∧ Q a s'.pos ∧
      ∀ kS : α → Digest → List UInt8 → List CapI → List UInt8 → OProg Bool,
        (runK S P st buf caps body kS).runSeq (tr.drop i) = (kS a st' buf' caps' body').runSeq (tr.drop i')
  | [], α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, _, _, hd, hiv => by
    cases P with
    | ret b =>
      simp only [ivp, Prod.mk.injEq, Option.some.injEq] at hiv
      obtain ⟨rfl, rfl⟩ := hiv
      exact ⟨s, st, buf, caps, body, i, cr, hJ, hd, hpos ▸ hF, fun kS ↦ rfl⟩
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .rd :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    cases P with
    | read k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      have hpo := hJ.pend
      have hst' : stA p as (s.off - s.pend + eBytes) cr hs = true := hst
      have hd' : (driveAtoms p π as { s with off := s.off + eBytes } k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_drive hk hd'
      simp only at hb
      have hnext : NextFS (Atom.rd :: as) :=
        nextFS_of_stA (p := p) as _ cr hs hst' (by simp [eBytes])
      obtain ⟨a₀, rest, hdrop⟩ := drive_next p π (Atom.rd :: as) s k _ hnext hd
      have hval : sbs (traceBytesB tr) (rs.ent + 40 + rs.msg) 24 = ((blb π).drop s.off).take 24 := by
        rw [hJ.ent, hJ.msg]
        exact msg_bytes hdrop (by simp only [pendA, eBytes] at hb ⊢; omega) hpo
          (by simp only [pendA, eBytes]; omega)
      have hiv' : ivp capS occS shpS (k' (eOfBytes (((blb π).drop s.off).take 24))) (traceBytesB tr)
          { rs with msg := rs.msg + 24 } = (some a, rs') := by
        simp only [ivp, hval] at hiv; exact hiv
      have h24 : s.off + 24 ≤ π.size := by simp only [eBytes] at hb; omega
      have hJ' : J S π tr { s with off := s.off + eBytes } st (buf ++ body.take 24) caps (body.drop 24)
          { rs with msg := rs.msg + 24 } i cr := by
        refine ⟨hJ.st, by simp only; omega, by simp only [eBytes]; omega, ?_, ?_, hJ.ent, ?_, hJ.caps⟩
        · simp only [eBytes]
          rw [hJ.buf, hJ.body, buf_ext _ hpo]
        · simp only; rw [hJ.body, List.drop_drop]; simp [eBytes]
        · simp only [eBytes]; rw [hJ.msg]; omega
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        sim hdecE hchal hdecK hcap hocc as (k' _) pp Q _ st _ caps _ _ i cr hs k a rs' (hF' _)
          (by simp only; rw [show s.off + eBytes - s.pend = s.off - s.pend + eBytes by omega]; exact hst')
          hJ' hpos hpk hk hd' hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hlen : ¬ body.length < 24 := by rw [hJ.body, List.length_drop, length_blb]; omega
      simp only [runK, hlen, ↓reduceIte, hdecE]
      rw [hJ.body] at h4 ⊢
      exact h4 kS
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .cap c r :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    cases P with
    | commit ht w k' =>
      obtain ⟨hc, hshp, hF'⟩ := hF
      have hpo := hJ.pend
      simp only [stA, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hst
      obtain ⟨⟨hidx, hnot⟩, hst'⟩ := hst
      have hnot' : r ∉ cr := by simpa using hnot
      have hd' : (driveAtoms p π as { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_drive hk hd'
      simp only at hb
      have hcb : S.capBytes ht w = nodeBytes * 2 ^ c := by
        simp only [Scheme.capBytes, hcap, hc, nodeBytes]
      have hoff : s.off + nodeBytes * 2 ^ c ≤ π.size := by omega
      have hiv' : ivp capS occS shpS k' (traceBytesB tr) { rs with msg := rs.msg + nodeBytes * 2 ^ c } =
          (some a, rs') := by
        simp only [ivp, hc] at hiv; exact hiv
      have hJ' : J S π tr { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
          (body.drop (S.capBytes ht w)) { rs with msg := rs.msg + nodeBytes * 2 ^ c } i (cr ++ [r]) := by
        refine ⟨hJ.st, by simp only; omega, by simp only; omega, ?_, ?_, hJ.ent, ?_, ?_⟩
        · simp only; rw [hcb, hJ.buf, hJ.body, buf_ext _ hpo]
        · simp only; rw [hJ.body, List.drop_drop, hcb]
        · simp only; rw [hJ.msg]; omega
        · obtain ⟨offs, hlen, hdc, hcs, hix, hnd⟩ := hJ.caps
          refine ⟨offs ++ [s.off], by simp [hlen], ?_, ?_, ?_, ?_⟩
          · simp only; rw [hdc, List.zip_append hlen.symm]; simp
          · rw [hcs, List.zip_append hlen.symm, List.map_append, hJ.body]
            simp [hshp]
          · intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_or_ge j cr.length with hj' | hj'
            · rw [List.getElem_append_left hj']; exact hix j hj'
            · rw [List.getElem_append_right (by omega)]
              simp only [show j - cr.length = 0 by omega, List.getElem_singleton]
              omega
          · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton r, by
              intro a ha b hb; rw [List.mem_singleton] at hb; rw [hb]; intro hab; rw [hab] at ha; exact hnot' ha⟩
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        sim hdecE hchal hdecK hcap hocc as k' pp Q _ st _ _ _ _ i (cr ++ [r]) hs k a rs' hF'
          (by simp only; rw [show s.off + nodeBytes * 2 ^ c - s.pend = s.off - s.pend + nodeBytes * 2 ^ c by
            omega]; exact hst')
          hJ' hpos hpk hk hd' hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hlen : ¬ body.length < S.capBytes ht w := by rw [hJ.body, List.length_drop, length_blb, hcb]; omega
      simp only [runK, hlen, ↓reduceIte]
      exact h4 kS
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .sm :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      simp only [stA, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtoms, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivp capS occS shpS (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } = (some a, rs') := by
        simp only [ivp, hans] at hiv; exact hiv
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        sim hdecE hchal hdecK hcap hocc as (k' _) pp Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off }
          a₀ [] caps body _ (i + 1) cr hs k a rs' (hF' _)
          (by show stA p as (s.off - s.off) cr hs = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl) hpos hpk hk (by rw [hrest]; exact hd') hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runK, hle, ↓reduceIte, hq, hdrop, runSeq_query_eq, hchal]
      rw [← hrest]
      exact h4 kS
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .pclr :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    rw [fol_pclr] at hF
    exact sim hdecE hchal hdecK hcap hocc as P [] Q { s with pos := [] } st buf caps body rs i cr [] k a rs'
      hF hst ⟨hJ.1, hJ.2, hJ.3, hJ.4, hJ.5, hJ.6, hJ.7, hJ.8⟩ rfl (fun _ h ↦ by simp at h) hk hd hiv
  | .ps h n :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as
          (pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat y)) Q := hF
      simp only [stA, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtoms, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivp capS occS shpS (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } = (some a, rs') := by
        simp only [ivp, hans] at hiv; exact hiv
      have hpos' : (pp ++ chunk h n (answerBits a₀)) =
          pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat (chalOf a₀)) := by rw [answerBits_eq]
      obtain ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, h4⟩ :=
        sim hdecE hchal hdecK hcap hocc as (k' _) _ Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off, pos := s.pos ++ chunk h n (answerBits a₀) }
          a₀ [] caps body _ (i + 1) cr (h :: hs) k a rs' (hF' _)
          (by show stA p as (s.off - s.off) cr (h :: hs) = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl)
          (by show s.pos ++ chunk h n (answerBits a₀) = _; rw [hpos, ← hpos']) (by
            intro q hq'
            rcases List.mem_append.mp hq' with hq'' | hq''
            · obtain ⟨h', hh', hlt⟩ := hpk q hq''
              exact ⟨h', List.mem_cons_of_mem _ hh', hlt⟩
            · refine ⟨h, List.mem_cons_self, ?_⟩
              obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq''
              exact Nat.mod_lt _ (Nat.two_pow_pos _)) hk
          (by rw [hrest]; exact hd') hiv'
      refine ⟨s', st', buf', caps', body', i', cr', h1, h2, h3, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runK, hle, ↓reduceIte, hq, hdrop, runSeq_query_eq, hchal]
      rw [← hrest]
      exact h4 kS
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .op r :: as, α, P, pp, Q, s, st, buf, caps, body, rs, i, cr, hs, k, a, rs', hF, hst, hJ, hpos, hpk, hk, hd, hiv => by
    cases P with
    | query ix ps k' =>
      obtain ⟨hix, hps, hF'⟩ := hF
      subst hix hps
      have hpo := hJ.pend
      simp only [stA, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at hst
      obtain ⟨⟨⟨⟨hp0, hrc⟩, hgeo⟩, hhs⟩, hst'⟩ := hst
      have hoffp : s.off = s.pend := by omega
      simp only [geomOk, Bool.and_eq_true, beq_iff_eq] at hgeo
      obtain ⟨⟨hht, hrow⟩, hpath⟩ := hgeo
      obtain ⟨capOff, hco, hcaps⟩ := capsJ_lookup hJ.caps hrc
      set ht := (shpS (idxS r)).1 with hhtdef
      set wd := (shpS (idxS r)).2 with hwddef
      -- the driver's opening
      simp only [driveAtoms, capOffset, hco] at hd
      split at hd
      · rename_i hrq
        have hk'' : ∀ (s' : DSt) (n : ℕ), ((fun s : DSt ↦ driveAtoms p π as { s with pend := s.off } k) s').runSeq
            (tr.drop n) = some true → s'.off ≤ π.size := fun s' n h ↦ by
          have := bound_of_drive hk h; simp only at this; omega
        have hlt : ∀ q ∈ ps, q < 2 ^ ht := by
          intro q hq
          obtain ⟨h', hh', hlt⟩ := hpk q (hpos ▸ hq)
          have := hhs h' hh'
          rw [this] at hlt; exact hlt
        rw [hpos] at hd
        obtain ⟨s', n, h1, hst1, hpe1, hca1, hpo1, hle1, hent1, hrun1⟩ :=
          openAll_sim S π tr hdecK (p.level r) capOff ht wd hht (by rw [hrow, hocc]) (by rw [hpath, hcap])
            (by rw [hcap]; exact capS_le _) ps s i _ hlt hk'' hd
        have hoff' : s'.off ≤ π.size := hk'' s' (i + n) h1
        set rows := (opRows (traceBytesB tr) wd (S.occ ht wd) (p.level r).path ps.length (entOff tr i)).1
        have hiv' : ivp capS occS shpS (k' rows) (traceBytesB tr) { rs with ent := entOff tr (i + n) } =
            (some a, rs') := by
          simp only [ivp] at hiv
          rw [← hhtdef, ← hwddef, ← hpath, show occS ht wd = S.occ ht wd by rw [hocc], hJ.ent, hent1] at hiv
          exact hiv
        have hJ' : J S π tr { s' with pend := s'.off } st [] caps ((blb π).drop s'.off)
            { rs with ent := entOff tr (i + n) } (i + n) cr := by
          refine ⟨by rw [hJ.st]; exact hst1.symm, le_rfl, hoff', by simp, rfl, rfl, ?_, ?_⟩
          · show rs.msg = s'.off - s'.off; rw [hJ.msg, hoffp]; simp
          · show CapsJ S π caps s'.caps cr; rw [hca1]; exact hJ.caps
        obtain ⟨s'', st', buf', caps', body', i', cr', h2, h3, h4, h5⟩ :=
          sim hdecE hchal hdecK hcap hocc as (k' rows) ps Q { s' with pend := s'.off } st [] caps _ _ (i + n)
            cr hs k a rs' (hF' rows) (by show stA p as (s'.off - s'.off) cr hs = true; rw [Nat.sub_self]; exact hst')
            hJ' (by show s'.pos = ps; rw [hpo1, hpos]) hpk hk h1 hiv'
        refine ⟨s'', st', buf', caps', body', i', cr', h2, h3, h4, fun kS ↦ ?_⟩
        have hbuf : buf = [] := by rw [hJ.buf, hoffp]; simp
        simp only [runK, hcaps, hJ.body]
        rw [hrun1]
        simp only [hbuf] at h5 ⊢
        exact h5 kS
      · exact absurd (runSeq_ret_true hd).2 (by simp)
    | fail => simp [ivp] at hiv
    | _ => exact absurd hF (by simp [Fol])

end Main

end Lvm.VEq
