-- New for lvm (WP-11b-QL). `entryAt`, `readEntries`, `WfAt`, `entry_bytes`, `take_readEntries` are
-- adapted from rf-k/submissions/flock-recursive/lean/FRNodeReadCore.lean and FRNodeRun4.lean@8bff272b
-- (`Read.entryAt`, `Read.readItems`, `WfAt`, `entry_bytes`, `take_readItems`): FR's `Item` replaced by
-- a plain query length. The lane-level link (`LaneLink`) and its bridge to `LinkOk` are new.
import LvmReplay
import RecursionFast.Library.Words

/-!
# The stream as lanes, the trace it encodes, and Q_link's conditions on lanes

The circuit sees the child's stream `Σ = tagTrace ‖ traceBytes tr` as **lanes** (`ws : List Word`,
eight little-endian bytes each; `wordsBytes ws` the bytes). The trace is read off the stream at the
plan's offsets (`decode p ws`, FR's `readItems`): entry `0` at byte `1`, entry `i + 1` at
`o_i + 40 + |q_i|`, its query the `|q_i|` bytes after the length word, its answer the next 32.
Every entry after `q₀` starts on a lane (`eLane`), its answer at lane `ansLane`.

**`LaneLink p ws`** is what Q_link asserts, lane by lane: the first two lanes are the constants
`0x54 ‖ enc64 7 ‖ q₀`, every length lane is the plan's length, every FS query's first four lanes
are its state entry's answer lanes, every node query holds the previous answer's four lanes in the
half its position bit selects, and every path ends on its cap node; the stream covers the trace.
**`linkOk_of_laneLink`**: then `decode p ws` is a trace of the schedule (`LinkOk`), and
**`stream_of_laneLink`**: the stream's first `hashedLen p` bytes are `tagTrace :: traceBytes`
of it.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay

/-! ## Reading entries off a byte stream (FR's `readItems`) -/

/-- The entry at byte `o` with a query of `len` bytes: the `len` bytes after the length word, then
the 32-byte answer. -/
def entryAt (B : List UInt8) (o len : Nat) : ByteArray × Digest :=
  (⟨((B.drop (o + 8)).take len).toArray⟩, Vector.ofFn fun i : Fin 32 => B.getD (o + 8 + len + i.val) 0)

/-- The entries of query lengths `ls` from byte `o` on. -/
def readEntries (B : List UInt8) : Nat → List Nat → Trace
  | _, [] => []
  | o, len :: ls => entryAt B o len :: readEntries B (o + 40 + len) ls

/-- The length words of the entries are their query lengths. -/
def WfAt (B : List UInt8) : Nat → List Nat → Prop
  | _, [] => True
  | o, len :: ls => (B.drop o).take 8 = enc64 len ∧ WfAt B (o + 40 + len) ls

/-- The bytes entries of query lengths `ls` take. -/
def slenS (ls : List Nat) : Nat := (ls.map (40 + ·)).sum

theorem readEntries_length (B : List UInt8) : ∀ (o : Nat) (ls : List Nat), (readEntries B o ls).length = ls.length
  | _, [] => rfl
  | o, _ :: ls => by simp [readEntries, readEntries_length B _ ls]

theorem entry_bytes {B : List UInt8} {o len : Nat} (hl : o + 40 + len ≤ B.length)
    (hw : (B.drop o).take 8 = enc64 len) :
    (B.drop o).take (40 + len) = enc64 (entryAt B o len).1.size ++ (entryAt B o len).1.data.toList ++
      (entryAt B o len).2.toList := by
  have hq : (entryAt B o len).1.size = len := by
    show ((B.drop (o + 8)).take len).toArray.size = _
    rw [List.size_toArray, List.length_take, List.length_drop]; omega
  have h1 : (entryAt B o len).1.data.toList = ((B.drop o).drop 8).take len := by
    show ((B.drop (o + 8)).take len).toArray.toList = _
    rw [List.toList_toArray, List.drop_drop, Nat.add_comm]
  have h2 : (entryAt B o len).2.toList = ((B.drop o).drop (8 + len)).take 32 := by
    simp only [entryAt, Vector.toList_ofFn]
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take, List.length_drop]; omega)
      fun i h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₁
    rw [List.getElem_ofFn]
    simp only
    rw [List.getElem_take, List.getElem_drop, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1; omega
  rw [hq, show 40 + len = 8 + (len + 32) by omega, List.take_add, List.take_add, hw, h1, h2, List.drop_drop,
    List.drop_drop]
  simp only [List.append_assoc, List.drop_drop, Nat.add_assoc]

theorem traceBytes_cons (e : ByteArray × Digest) (tr : Trace) :
    traceBytes (e :: tr) = (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList) ++ traceBytes tr := by
  simp [traceBytes]

/-- **On well-formed bytes, the entries' span is the encoding of what `readEntries` reads.** -/
theorem take_readEntries (B : List UInt8) : ∀ (ls : List Nat) (o : Nat), WfAt B o ls →
    o + slenS ls ≤ B.length → (B.drop o).take (slenS ls) = traceBytes (readEntries B o ls)
  | [], _, _, _ => by simp [slenS, readEntries, traceBytes]
  | len :: ls, o, ⟨hw, hr⟩, hl => by
    have hs : slenS (len :: ls) = (40 + len) + slenS ls := by simp [slenS]
    rw [hs] at hl ⊢
    rw [List.take_add, entry_bytes (by omega) hw, List.drop_drop, ← Nat.add_assoc,
      take_readEntries B ls _ hr (by omega), readEntries, traceBytes_cons]

theorem readEntries_getD (B : List UInt8) : ∀ (ls : List Nat) (o i : Nat), i < ls.length →
    (readEntries B o ls).getD i dflt = entryAt B (o + slenS (ls.take i)) (ls.getD i 0)
  | [], _, _, h => absurd h (by simp)
  | len :: ls, o, 0, _ => by simp [readEntries, slenS]
  | len :: ls, o, i + 1, h => by
    simp only [readEntries, List.getD_cons_succ, List.take_succ_cons]
    rw [readEntries_getD B ls _ i (by simpa using h)]
    congr 1
    simp [slenS]; omega

/-! ## The trace a stream of lanes encodes -/

/-- The plan's query lengths. -/
def lens (p : Params) : List Nat := (plan p).map PE.len

/-- **The trace the stream encodes**, cut at the plan's lengths. -/
def decode (p : Params) (ws : List Word) : Trace := readEntries (wordsBytes ws) 1 (lens p)

/-- The byte offset of entry `i` in the stream. -/
def bOff (p : Params) (i : Nat) : Nat := 1 + slenS ((lens p).take i)

/-- The lane of entry `i`'s length word (entries `i ≥ 1` start on a lane). -/
def eLane (p : Params) (i : Nat) : Nat := bOff p i / 8

/-- The first lane of entry `i`'s answer (`q₀`'s answer is lanes 2–5). -/
def ansLane (p : Params) (i : Nat) : Nat :=
  if i = 0 then 2 else eLane p i + 1 + ((plan p).getD i default).len / 8

/-- Lane `j` as a number. -/
def lw (ws : List Word) (j : Nat) : Nat := (ws.getD j 0).toNat

/-- Lane 0 of every stream: `0x54 ‖ enc64 7 [0..7)`. -/
def lane0C : Nat := 0x754

/-- Lane 1 of every stream: the last byte of `enc64 7` (zero) and `q₀`. -/
def lane1C : Nat := ofLE (0 :: q0Bytes)

/-- The bit `n` of the answer lanes 0–2 of entry `e` (a positions answer). -/
def ansBit (p : Params) (ws : List Word) (e n : Nat) : Bool := (lw ws (ansLane p e + n / 64)).testBit (n % 64)

/-- The position the lanes give: `h` bits from bit `s` of the answer of entry `e`. -/
def posL (p : Params) (ws : List Word) (e s h : Nat) : Nat :=
  ((List.range h).map fun z => if ansBit p ws e (s + z) then 2 ^ z else 0).sum

/-- **Q_link's conditions, lane by lane** (BLUEPRINT §4.6). -/
structure LaneLink (p : Params) (ws : List Word) : Prop where
  /-- The stream covers the trace. -/
  size : hashedLen p ≤ 8 * ws.length
  /-- The two constant lanes. -/
  c0 : lw ws 0 = lane0C
  c1 : lw ws 1 = lane1C
  /-- Every length lane is the plan's length. -/
  len : ∀ i, 1 ≤ i → i < (plan p).length → lw ws (eLane p i) = ((plan p).getD i default).len
  /-- Every FS query starts with its state entry's answer. -/
  fs : ∀ i < (plan p).length, ∀ st, ((plan p).getD i default).k = .fs st →
    ∀ l < 4, lw ws (eLane p i + 1 + l) = lw ws (ansLane p st + l)
  /-- Every node query holds the previous answer in the half its position bit selects. -/
  node : ∀ i < (plan p).length, ∀ pe h j lvl cap, ((plan p).getD i default).k = .node pe h j lvl cap →
    ∀ l < 4, lw ws ((if ansBit p ws (pe + j / 8) (j % 8 * h + lvl) then eLane p i + 5 else eLane p i + 1) + l) =
      lw ws (eLane p i - 4 + l)
  /-- Every path ends on its cap node. -/
  cap : ∀ i < (plan p).length, ∀ pe h j lvl ce co path,
    ((plan p).getD i default).k = .node pe h j lvl (some (ce, co, path)) →
    ∀ l < 4, lw ws (eLane p i + 9 + l) =
      lw ws (eLane p ce + 1 + co / 8 + 4 * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + l)

end Lvm.QLink
