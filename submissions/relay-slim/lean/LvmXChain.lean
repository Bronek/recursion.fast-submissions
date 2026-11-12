-- adapted from rf-k/submissions/flock-recursive/lean/FRXChainTop.lean@kk/base
-- (WP-13a, lvm extractor; FR's former `FRXChainDefs`, `FRXChain`, `FRXChainSem`, `FRXChainLoop`,
-- `FRXChainTop`, one section each, and the chain's loop bounds of `FRXDec`). Namespace `Lvm.X`.
-- Changes for lvm's Fiat–Shamir format (no tag bytes): `stateIn` is a query's first 32 bytes;
-- a target `p ≥ 1` is `st ‖ msg` (header `h = 4`: the previous answer, stored at `H[0 … 3]`),
-- the seed `q₀` is 7 bytes (`h = 1`); the table holds `tl, o` per position (no tag word); the
-- region is `[2^24, 2^24 + 2^14 + 2^13)` and the target count `N < 2^11`. FR's toy controls are
-- dropped.
import LvmXLookup

section LvmXChainDefs

/-!
# The Fiat–Shamir chain replayed off the log: the pure half

`runLog` answers each query by the **first** entry of the log with exactly that query
(`OProg.runLog`, `List.find?`), and the chain's query at position `p` is built from the answer at
`p − 1` (lvm's queries: `st ‖ msg` for an absorb, `st` for a squeeze). So the chain's answers are

* `fmAns T st₀ L p`: the first-match chain, for any target family `T p st` (the query at position
  `p` when the previous answer is `st`; `T 0` is the seed).

The extractor does not sort the log by query (a merge sort whose key is a whole query costs a
query's length per comparison, over the linear fuel). It **scans the log once, in order**, with the
next target in hand (`scanC`): an entry whose query is the target records its answer and moves to
the next target.

* **`scanC_fm`**: on a log with no state hit (`StateHit`: an answer equal to the first 32 bytes of
  a query asked before it or by the same entry), the scan's answers are the first-match chain's, at
  every position below the target count. A query that carries the state `a_{p−1}` cannot come
  before the entry that answered `a_{p−1}`: that would be a state hit. So the first entry with the
  target of `p` lies after the one found for `p − 1`.
-/

namespace Lvm.X

open RecursionFast

/-! ## The state field of a query -/

/-- The state of a query: its first 32 bytes (lvm's Fiat–Shamir queries are `st ‖ msg`), for a
query of `32 … queryCap` bytes. -/
def stateIn (q : ByteArray) : Option Digest :=
  if 32 ≤ q.size ∧ q.size ≤ queryCap then some (Vector.ofFn fun i => q.data.toList.getD i 0)
  else none

/-- *State hit*: an answer equal to the state field of a query asked before it or by the same
entry. -/
def StateHit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i ≤ j) (hj : j < L.length), stateIn (L[i]'(by omega)).1 = some L[j].2

/-! ## The first-match chain and the forward scan -/

/-- **The first-match chain**: the answer at position `p` when every query is answered by the
first entry of `L` with that query (`runLog`'s reading), the query at `p` being `T p st` with `st`
the answer at `p − 1` (`st₀` for the seed). `none` from the first query `L` does not answer. -/
def fmAns (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) : ℕ → Option Digest
  | 0 => (L.find? fun e => e.1 = T 0 st₀).map Prod.snd
  | p + 1 => (fmAns T st₀ L p).bind fun st => (L.find? fun e => e.1 = T (p + 1) st).map Prod.snd

/-- The scan's state: the next target's index, the current state, the answers found. -/
abbrev SS := ℕ × Digest × List Digest

/-- **One entry of the scan**: an entry whose query is the next target (of the first `N`) records
its answer, which becomes the state. -/
def scanStep (T : ℕ → Digest → ByteArray) (N : ℕ) (x : SS) (e : ByteArray × Digest) : SS :=
  if x.1 < N ∧ e.1 = T x.1 x.2.1 then (x.1 + 1, e.2, x.2.2 ++ [e.2]) else x

/-- **The forward scan** of the log for the first `N` targets. -/
def scanC (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log) : SS :=
  L.foldl (scanStep T N) (0, st₀, [])

theorem scanC_snoc (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log)
    (e : ByteArray × Digest) : scanC T N st₀ (L ++ [e]) = scanStep T N (scanC T N st₀ L) e := by
  simp [scanC, List.foldl_append]

/-- The state before position `p`. -/
def fmPrev (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) : ℕ → Option Digest
  | 0 => some st₀
  | p + 1 => fmAns T st₀ L p

theorem fmAns_eq (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) (p : ℕ) :
    fmAns T st₀ L p =
      (fmPrev T st₀ L p).bind fun st => (L.find? fun e => e.1 = T p st).map Prod.snd := by
  cases p <;> rfl

/-- An answer of a prefix stays an answer. -/
theorem fmAns_snoc_some (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log)
    (e : ByteArray × Digest) : ∀ p a, fmAns T st₀ L p = some a → fmAns T st₀ (L ++ [e]) p = some a
  | 0, a, h => by
    simp only [fmAns, Option.map_eq_some_iff] at h ⊢
    obtain ⟨y, hy, rfl⟩ := h
    exact ⟨y, by rw [List.find?_append, hy, Option.some_or], rfl⟩
  | p + 1, a, h => by
    simp only [fmAns, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨st, hst, y, hy, rfl⟩ := h
    exact ⟨st, fmAns_snoc_some T st₀ L e p st hst, y,
      by rw [List.find?_append, hy, Option.some_or], rfl⟩

/-- A broken chain stays broken. -/
theorem fmAns_none_le (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) {p : ℕ}
    (h : fmAns T st₀ L p = none) : ∀ q, p ≤ q → fmAns T st₀ L q = none := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact h
  | succ q _ ih => simp only [fmAns, ih, Option.bind_none]

theorem stateHit_of_snoc {L : Log} {e : ByteArray × Digest} (h : StateHit L) :
    StateHit (L ++ [e]) := by
  obtain ⟨i, j, hij, hj, hs⟩ := h
  refine ⟨i, j, hij, by simp; omega, ?_⟩
  rw [List.getElem_append_left (by omega), List.getElem_append_left hj]
  exact hs

/-- **No query carrying the last answer as its state**, on a log with no state hit. -/
theorem find?_state_none {L : Log} {e : ByteArray × Digest} (hS : ¬ StateHit (L ++ [e]))
    {q : ByteArray} (hq : stateIn q = some e.2) :
    (L ++ [e]).find? (fun y => y.1 = q) = none := by
  rw [List.find?_eq_none]
  intro y hy hyq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  simp only [decide_eq_true_eq] at hyq
  refine hS ⟨i, L.length, by simp at hi; omega, by simp, ?_⟩
  rw [hyq, hq, List.getElem_concat_length rfl]

/-- The scan's invariant: as many answers as targets passed, the state is the last answer, and
the answers are the first-match chain's. -/
def ScanInv (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log) (x : SS) : Prop :=
  x.2.2.length = x.1 ∧ x.1 ≤ N ∧ fmPrev T st₀ L x.1 = some x.2.1 ∧
    ∀ p < N, x.2.2[p]? = fmAns T st₀ L p

theorem scanInv_nil (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) :
    ScanInv T N st₀ [] (0, st₀, []) := by
  refine ⟨rfl, Nat.zero_le _, rfl, fun p _ => ?_⟩
  rw [fmAns_none_le T st₀ [] (p := 0) (by simp [fmAns]) p (Nat.zero_le _)]
  rfl

theorem scanInv_snoc {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    {e : ByteArray × Digest} (hT : ∀ p st, 0 < p → stateIn (T p st) = some st)
    (hS : ¬ StateHit (L ++ [e])) {x : SS} (hI : ScanInv T N st₀ L x) :
    ScanInv T N st₀ (L ++ [e]) (scanStep T N x e) := by
  obtain ⟨n, st, acc⟩ := x
  obtain ⟨hlen, hnN, hprev, hacc⟩ := hI
  simp only at hlen hnN hprev hacc
  -- the old answers
  have hold : ∀ p < n, fmAns T st₀ (L ++ [e]) p = acc[p]? := fun p hp => by
    obtain ⟨a, ha⟩ : ∃ a, acc[p]? = some a := ⟨acc[p], List.getElem?_eq_getElem (by omega)⟩
    rw [ha]
    exact fmAns_snoc_some T st₀ L e p a (by rw [← hacc p (by omega), ha])
  have hprev' : fmPrev T st₀ (L ++ [e]) n = some st := by
    cases n with
    | zero => exact hprev
    | succ n =>
      simp only [fmPrev] at hprev ⊢
      exact fmAns_snoc_some T st₀ L e n st hprev
  -- the target `n` is not answered by `L`
  have hnone : n < N → L.find? (fun y => y.1 = T n st) = none := fun hn => by
    have h := hacc n hn
    rw [List.getElem?_eq_none (by omega), fmAns_eq, hprev, Option.bind_some] at h
    exact Option.map_eq_none_iff.mp h.symm
  have hnew : n < N → fmAns T st₀ (L ++ [e]) n =
      if e.1 = T n st then some e.2 else none := fun hn => by
    rw [fmAns_eq, hprev', Option.bind_some, List.find?_append, hnone hn, Option.none_or]
    by_cases he : e.1 = T n st <;> simp [he]
  unfold scanStep
  simp only
  by_cases hm : n < N ∧ e.1 = T n st
  · rw [if_pos hm]
    refine ⟨by simp [hlen], hm.1, ?_, fun p hp => ?_⟩
    · simp only [fmPrev]
      rw [hnew hm.1, if_pos hm.2]
    · have hn1 : fmAns T st₀ (L ++ [e]) (n + 1) = none := by
        rw [fmAns_eq]
        simp only [fmPrev]
        rw [hnew hm.1, if_pos hm.2, Option.bind_some, find?_state_none hS (hT _ _ (by omega)),
          Option.map_none]
      rcases Nat.lt_trichotomy p n with h | rfl | h
      · rw [hold p h, List.getElem?_append_left (by omega)]
      · rw [hnew hm.1, if_pos hm.2, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        rfl
      · rw [fmAns_none_le T st₀ _ hn1 p (by omega), List.getElem?_eq_none (by simp; omega)]
  · rw [if_neg hm]
    refine ⟨hlen, hnN, hprev', fun p hp => ?_⟩
    rcases Nat.lt_or_ge p n with h | h
    · rw [hold p h]
    · have hn0 : fmAns T st₀ (L ++ [e]) n = none := by
        have hn : n < N := by omega
        rw [hnew hn, if_neg fun he => hm ⟨hn, he⟩]
      rw [fmAns_none_le T st₀ _ hn0 p h, List.getElem?_eq_none (by simp only at hlen ⊢; omega)]

/-- **`scanC_fm`**: on a log with no state hit, the forward scan's answers are the first-match
chain's at every position below `N`, when every query after the seed carries its state
(`stateIn (T p st) = some st`). -/
theorem scanC_fm {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    (hT : ∀ p st, 0 < p → stateIn (T p st) = some st) (hS : ¬ StateHit L) :
    ScanInv T N st₀ L (scanC T N st₀ L) := by
  induction L using List.reverseRecOn with
  | nil => exact scanInv_nil T N st₀
  | append_singleton L e ih =>
    rw [scanC_snoc]
    exact scanInv_snoc hT hS (ih fun h => hS (stateHit_of_snoc h))

theorem scanC_answers {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    (hT : ∀ p st, 0 < p → stateIn (T p st) = some st) (hS : ¬ StateHit L) {p : ℕ} (hp : p < N) :
    (scanC T N st₀ L).2.2[p]? = fmAns T st₀ L p :=
  (scanC_fm hT hS).2.2.2 p hp

end Lvm.X

end LvmXChainDefs

section LvmXChainProg

/-!
# The chain scan on the machine: the program

One pass over the log's words (`chainIR N`), with the next target in hand. The target of position
`p` is a query of `tl` bytes whose packed words are `Ex j`: the first `h` from the header buffer
`H` (cells `hB …`), the rest from the tape at `o` (`Ex j = I[o + j − h]`: an absorb's message is a
slice of π). The seed's header is its single word (`h = 1`, the seed is 7 bytes, no message); every
later target's header is the 4 words of the previous answer (`h = 4`). The table at `chB` gives,
for each position `p`, the words `tl, o, 0, 0`.

Per word of the log (`wordIR`): at an entry's length word, `rQw := ⌈|q|/8⌉` and the match flag
`rMt := [|q| = tl]`; at query word `j`, `rMt &&= [word = Ex j]`; at answer word `m`, the word goes
to `rS_m`; after answer word 3, if `rMt` and `p < N` (`recIR`): the answer goes to `ansB + 4p` and
to `H[0 … 3]`, `p += 1`, and the next target is loaded from the table.

The loop count is the log's word count, `rP − pL − 1` after a store-free walk (`cntIR`); its cap
is `t`. Everything inside the loop is straight-line or `ite`: the cost is `t` times a constant.

**Parameters.** The count and the start read the log at tape word `pL` (`cntIR pL`, `startPs pL`,
`chainIR pL`); lvm instantiates `pL = posL pz`.
-/

namespace Lvm.X

open RecursionFast

/-! ## Registers (user registers `190 …`) and memory -/

/-- The word read. -/ def rWd : ℕ := 190
/-- Its tape position. -/ def rWp : ℕ := 191
/-- The offset in the entry (`0`: the length word). -/ def rEo : ℕ := 192
/-- The entry's query words. -/ def rQw : ℕ := 193
/-- The match flag. -/ def rMt : ℕ := 194
/-- The target's length in bytes. -/ def rTl : ℕ := 195
/-- The target's header words. -/ def rTh : ℕ := 196
/-- The target's message on the tape. -/ def rTo : ℕ := 197
/-- The target index `p`. -/ def rPi : ℕ := 198
/-- A flag. -/ def rZ : ℕ := 199
/-- `j` or `m`. -/ def rKj : ℕ := 200
/-- An address. -/ def rAd4 : ℕ := 201
/-- The expected word. -/ def rE : ℕ := 202
/-- Answer word 0. -/ def rS0 : ℕ := 203
/-- Answer word 1. -/ def rS1 : ℕ := 204
/-- Answer word 2. -/ def rS2 : ℕ := 205
/-- Answer word 3. -/ def rS3 : ℕ := 206
/-- The loop counter. -/ def rCC : ℕ := 208
/-- The loop count. -/ def rCn5 : ℕ := 209
/-- Constant scratch. -/ def rKd : ℕ := 210
/-- Mask scratch. -/ def rMk5 : ℕ := 211

/-- The target table: `4` words per position, `N + 1 ≤ 2^11` positions (`2^24`). -/
def chB : ℕ := 16777216
/-- The header buffer `H` (16 cells; `2^24 + 2^13`). -/
def hB : ℕ := 16785408
/-- The answers: `4` words per position (`2^24 + 2^14`). -/
def ansB : ℕ := 16793600
/-- The end of the chain's region (`ansB + 2^13`). -/
def chEnd : ℕ := 16801792

theorem chB_eq : chB = 16777216 := rfl
theorem hB_eq : hB = 16785408 := rfl
theorem ansB_eq : ansB = 16793600 := rfl
theorem chEnd_eq : chEnd = 16801792 := rfl
theorem layout_eq : chB = 2 ^ 24 ∧ hB = 2 ^ 24 + 2 ^ 13 ∧ ansB = 2 ^ 24 + 2 ^ 14 ∧
    chEnd = 2 ^ 24 + 2 ^ 14 + 2 ^ 13 := by
  norm_num [chB, hB, ansB, chEnd]

/-! ## The word step -/

/-- The length word: `rQw := ⌈w/8⌉`, `rMt := [w = tl]`, `eo := 1`. -/
def lenIR : XIR := .blk (ceil8Ps rQw rWd ++ [.op .eq rMt rWd rTl, .const rEo 1])

/-- Query word `j = eo − 1`: the expected word from `H` (`j < h`) or from the tape. -/
def qryIR : XIR :=
  .seq (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh])
    (.seq (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) (.load rE rAd4))
        (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4)))
      (.blk [.op .eq rZ rWd rE, .op .and rMt rMt rZ, .op .add rEo rEo cOne]))

/-- `r := w` if `m = k`, else unchanged (branch-free). -/
def setSPs (m r : ℕ) : List Prim :=
  [.const rKd (toWord m), .op .eq rMk5 rKj rKd, .const rKd 0, .op .sub rMk5 rKd rMk5,
   .op .xor rKd r rWd, .op .and rKd rKd rMk5, .op .xor r r rKd]

/-- Answer word `m = eo − qw − 1` into `rS_m`; `rZ := [m = 3]`. -/
def ansPs : List Prim :=
  [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] ++ setSPs 0 rS0 ++ setSPs 1 rS1 ++ setSPs 2 rS2 ++
    setSPs 3 rS3 ++ [.const rKd 3, .op .eq rZ rKj rKd]

/-- A store of register `r` at `rAd4 + 1`. -/
def stNext (r : ℕ) : XIR := .seq (.blk [.op .add rAd4 rAd4 cOne]) (.store rAd4 r)

/-- Four stores of `rS0 … rS3` at `rAd4, rAd4 + 1, …` (`rAd4` ends at the last). -/
def st4IR : XIR := .seq (.store rAd4 rS0) (.seq (stNext rS1) (.seq (stNext rS2) (stNext rS3)))

/-- `p += 1`, `rAd4 :=` the table entry of `p`. -/
def nextPs : List Prim :=
  [.op .add rPi rPi cOne, .const rKd 4, .op .mul rAd4 rPi rKd, .const rKd (toWord chB),
    .op .add rAd4 rAd4 rKd]

/-- The block of `nextPs`. -/
def nextPre : XIR := .blk nextPs

/-- The next target from the table: `p += 1`, `tl`, `o`, `h := 4`. -/
def nextIR : XIR :=
  .seq nextPre
  (.seq (.load rTl rAd4) (.seq (.blk [.op .add rAd4 rAd4 cOne]) (.seq (.load rTo rAd4)
  (.blk [.const rTh 4]))))

/-- `rAd4 := ansB + 4p`. -/
def recPs : List Prim :=
  [.const rKd 4, .op .mul rAd4 rPi rKd, .const rKd (toWord ansB), .op .add rAd4 rAd4 rKd]

/-- The block of `recPs`. -/
def recPre : XIR := .blk recPs

/-- **The record** of a match at `p`: the answer at `ansB + 4p` and in `H[0 … 3]`, then the next
target (`nextIR`). -/
def recIR : XIR :=
  .seq recPre
    (.seq st4IR (.seq (.blk [.const rAd4 (toWord hB)]) (.seq st4IR nextIR)))

/-- After answer word 3: record if `rMt` and `p < N`; `eo := 0`. -/
def lastIR (N : ℕ) : XIR :=
  .seq (.blk [.const rKd (toWord N), .op .ltu rZ rPi rKd, .op .and rZ rZ rMt])
    (.seq (.ite rZ recIR (.blk [])) (.blk [.const rEo 0]))

/-- An answer word. -/
def ansIR (N : ℕ) : XIR := .seq (.blk ansPs) (.ite rZ (lastIR N) (.blk [.op .add rEo rEo cOne]))

/-- **One word of the log.** -/
def wordIR (N : ℕ) : XIR :=
  .seq (.input rWd rWp) (.seq (.blk [.const rKd 0, .op .eq rZ rEo rKd])
    (.seq (.ite rZ lenIR (.seq (.blk [.op .ltu rZ rQw rEo]) (.ite rZ (ansIR N) qryIR)))
      (.blk [.op .add rWp rWp cOne])))

/-! ## Before the loop -/

/-- The walk without its store: `rP` ends at the log's end. -/
def cntBody : XIR :=
  .seq (.input rQL rP) (.blk (ceil8Ps rT1 rQL ++ [.op .add rP rP rT1, .const rKc 5,
    .op .add rP rP rKc]))

/-- **The count**: the log's words, `rCn5 := rP − pL − 1` after the walk. -/
def cntIR (pL : ℕ) : XIR :=
  .seq (.seq (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL))
      (.loopT rCW rN ⟨0, 1, 5⟩ cntBody))
    (.blk [.const rKd (toWord (pL + 1)), .op .sub rCn5 rP rKd])

/-- Straight-line stores of the words `ws` at `b, b + 1, …`. -/
def storesIR (b : ℕ) : List Word → XIR
  | [] => .blk []
  | w :: ws => .seq (.seq (.blk [.const rAd4 (toWord b), .const rKd w]) (.store rAd4 rKd))
      (storesIR (b + 1) ws)

/-- The registers at the start: the first word, `eo = 0`, `p = 0`, the seed's `tl = 7`,
`h = 1`. -/
def startPs (pL : ℕ) : List Prim :=
  [.const rWp (toWord (pL + 1)), .const rEo 0, .const rPi 0, .const rTl 7, .const rTh 1,
   .const rTo 0, .const rMt 0]

/-- **The chain scan** for `N` targets: the count, the table `tab` at `chB`, the seed's header
(`sd`, which writes `H[0]`), the start, then the loop over the log's words. -/
def chainIR (pL N : ℕ) (tab : List Word) (sd : XIR) : XIR :=
  .seq (.seq (cntIR pL) (.seq (storesIR chB tab) (.seq sd (.blk (startPs pL)))))
    (.loopT rCC rCn5 ⟨0, 1, 1⟩ (wordIR N))

/-! ## Well formed, cost, size -/

theorem wf_storesIR : ∀ (b : ℕ) (ws : List Word), WF (storesIR b ws)
  | _, [] => by simp +decide only [storesIR, WF]
  | b, _ :: ws => ⟨by simp +decide only [WF, Prim.dst, rAd4, rKd, cTmp, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], wf_storesIR (b + 1) ws⟩

theorem lo_free_storesIR : ∀ (b : ℕ) (ws : List Word) (i : ℕ), i ≠ rAd4 → i ≠ rKd → i ≠ cTmp →
    ¬ Writes (storesIR b ws) i
  | _, [], i, _, _, _ => by simp +decide only [storesIR, Writes, List.mem_nil_iff, false_and,
    exists_false]
  | b, _ :: ws, i, h1, h2, h3 => by
    simp only [storesIR, Writes, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
      Prim.dst, exists_eq_left, not_or]
    exact ⟨⟨⟨Ne.symm h1, Ne.symm h2⟩, h3⟩, lo_free_storesIR (b + 1) ws i h1 h2 h3⟩

theorem cost_storesIR (t : ℕ) : ∀ (b : ℕ) (ws : List Word), cost (storesIR b ws) t = 9 * ws.length + 1
  | _, [] => rfl
  | b, _ :: ws => by
    simp only [storesIR, cost, blkSteps, List.length_cons, List.length_nil, cost_storesIR t (b + 1) ws]
    norm_num; ring

theorem size_storesIR : ∀ (b : ℕ) (ws : List Word), sizeIR (storesIR b ws) = 10 * ws.length + 1
  | _, [] => rfl
  | b, _ :: ws => by
    simp only [storesIR, sizeIR, blkSteps, List.length_cons, List.length_nil, size_storesIR (b + 1) ws]
    norm_num; ring

theorem noLoopT_storesIR : ∀ (b : ℕ) (ws : List Word), NoLoopT (storesIR b ws)
  | _, [] => trivial
  | b, _ :: ws => ⟨⟨trivial, trivial⟩, noLoopT_storesIR (b + 1) ws⟩

theorem outs_storesIR (t : ℕ) : ∀ (b : ℕ) (ws : List Word), outs (storesIR b ws) t = 0
  | _, [] => rfl
  | b, _ :: ws => by simp only [storesIR, outs, outs_storesIR t (b + 1) ws]

theorem wf_wordIR (N : ℕ) : WF (wordIR N) := by
  simp +decide only [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs,
    st4IR, nextIR, nextPre, nextPs, stNext, ceil8Ps, WF, Prim.dst, rWd, rWp, rEo, rQw, rMt,
    rTl, rTh, rTo, rPi, rZ, rKj, rAd4, rE, rS0, rS1, rS2, rS3, rKd, rMk5, rKc, rT2, cTmp,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true,
    List.cons_append, List.nil_append]

theorem not_writes_wordIR_rCC (N : ℕ) : ¬ Writes (wordIR N) rCC := by
  simp +decide only [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs,
    st4IR, nextIR, nextPre, nextPs, stNext, ceil8Ps, Writes, Prim.dst, rWd, rWp, rEo, rQw,
    rMt, rTl, rTh, rTo, rPi, rZ, rKj, rAd4, rE, rS0, rS1, rS2, rS3, rKd, rMk5, rKc, rT2, cTmp,
    rCC, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false,
    List.cons_append, List.nil_append]

theorem wf_cntIR (pL : ℕ) : WF (cntIR pL) := by
  simp +decide [cntIR, cntBody, readAt, ceil8Ps, WF, Writes, Prim.dst, rP, rN, rA, rCW, rQL,
    rT1, rT2, rKc, rKd, rCn5, cTmp, regs, or_false, and_true, List.cons_append, List.nil_append]

theorem wf_chainIR (pL : ℕ) (N : ℕ) (tab : List Word) {sd : XIR} (hsd : WF sd) (hc : ¬ Writes sd rCC) :
    WF (chainIR pL N tab sd) := by
  refine ⟨⟨(wf_cntIR pL), wf_storesIR _ _, hsd,
    by simp +decide [startPs, WF, Prim.dst, rWp, rEo, rPi, rTl, rTh, rTo, rMt]⟩, ⟨by decide, by decide, by decide⟩, by decide, not_writes_wordIR_rCC N,
    wf_wordIR N⟩

theorem cost_wordIR (N t : ℕ) : cost (wordIR N) t = 165 := by
  simp only [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stNext, ceil8Ps,
    cost, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem cost_cntIR (pL : ℕ) (t : ℕ) : cost (cntIR pL) t = 13 + t / 5 * 24 := by
  simp only [cntIR, cntBody, readAt, ceil8Ps, cost, blkSteps, List.length_cons, List.length_nil,
    List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  omega

theorem cost_chainIR (pL : ℕ) (N t : ℕ) (tab : List Word) (sd : XIR) :
    cost (chainIR pL N tab sd) t = 34 + 9 * tab.length + cost sd t + t / 5 * 24 + t * 168 := by
  simp only [chainIR, cost, cost_cntIR, cost_storesIR, cost_wordIR, startPs, blkSteps,
    List.length_cons, List.length_nil, Aff.eval, Nat.one_mul, Nat.div_one]
  norm_num
  omega

theorem sizeIR_chainIR (pL : ℕ) (N : ℕ) (tab : List Word) (sd : XIR) :
    sizeIR (chainIR pL N tab sd) = 272 + 10 * tab.length + sizeIR sd := by
  simp only [chainIR, cntIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR,
    recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stNext, ceil8Ps, startPs, sizeIR, size_storesIR, blkSteps, List.length_cons,
    List.length_nil, List.length_append]
  norm_num
  omega

theorem outs_chainIR (pL : ℕ) (N t : ℕ) (tab : List Word) {sd : XIR} (hsd : outs sd t = 0) :
    outs (chainIR pL N tab sd) t = 0 := by
  simp [chainIR, cntIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stNext,
    outs, outs_storesIR, hsd]

end Lvm.X

end LvmXChainProg

section LvmXChainSem

/-!
# The chain scan on the machine: the blocks of one word

The semantics of `wordIR`'s blocks, each on any state satisfying `Inv`, with the registers it
reads given as hypotheses: the length word (`lenIR_sem`), a query word (`qryIR_sem`, against the
expected word `exW`), an answer word (`ansPs_sem`), the record (`recIR_sem`) and the decision after
answer word 3 (`lastIR_sem`). Heap frames: every block but the record writes registers only
(`Lo`); the record writes `ansB + 4p + m` and `hB + m` only.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM runPrims

/-- The expected word `j` of the current target: header cell `hB + j` below `h`, else the tape
word `o + j − h`. -/
def exW (I : Array Word) (M : Mem) (h o j : ℕ) : Word :=
  if j < h then rd M (hB + j) else I.getD (o + j - h) 0

theorem toWord_sub_one (j : ℕ) (hj : j + 1 < 2 ^ 64) :
    XOp.sub.eval (toWord (j + 1)) 1 = toWord j := by
  have := sub_toWord (a := j + 1) (b := 1) hj (by omega)
  rwa [Nat.add_sub_cancel] at this

/-! ## The length word -/

theorem lo_lenIR : Lo lenIR := by
  simp +decide only [lenIR, ceil8Ps, Lo, Prim.dst, regs, rQw, rWd, rMt, rTl, rEo, rKc, rT2,
    List.cons_append, List.nil_append]

theorem wf_lenIR : WF lenIR := by
  simp +decide only [lenIR, ceil8Ps, WF, Prim.dst, rQw, rMt, rEo, rKc, rT2, List.cons_append,
    List.nil_append]

theorem lenIR_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I lenIR s).M rQw = ceil8 (rd s.M rWd) ∧
    rd (semXIR I lenIR s).M rMt = XOp.eq.eval (rd s.M rWd) (rd s.M rTl) ∧
    rd (semXIR I lenIR s).M rEo = 1 := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [lenIR, ceil8Ps, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append, Prim.run, rKc, rT2, rQw, rWd, rMt, rTl, rEo]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self,
    rd_set_ne]
  exact ⟨by simp only [ceil8, XOp.eval]; rfl, by trivial, by trivial⟩

/-! ## A query word -/

theorem lo_qryIR : Lo qryIR := by
  simp +decide only [qryIR, Lo, Prim.dst, regs, rKj, rZ, rKd, rAd4, rE, rMt, rEo, and_true]

theorem wf_qryIR : WF qryIR := by
  simp +decide only [qryIR, WF, Prim.dst, rKj, rZ, rKd, rAd4, rE, rMt, rEo, and_true]

theorem qryIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {j h o : ℕ} {b : Bool}
    (hj : j + 2 < 2 ^ 64) (hh : h ≤ 16) (ho : o + j < 2 ^ 64)
    (hE : rd s.M rEo = toWord (j + 1)) (hH : rd s.M rTh = toWord h) (hO : rd s.M rTo = toWord o)
    (hT : rd s.M rMt = bW b) :
    rd (semXIR I qryIR s).M rMt = bW (b && decide (rd s.M rWd = exW I s.M h o j)) ∧
    rd (semXIR I qryIR s).M rEo = toWord (j + 2) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have w1 : WF (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) := by
    simp +decide only [WF, Prim.dst, rKj, rZ]
  have hM1 := inv_sem I w1 hM
  have hk1 : rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M rKj =
      toWord j := by
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
      runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
    rw [hE, h1, toWord_sub_one j (by omega)]
  have hz1 : rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M rZ =
      bW (decide (j < h)) := by
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
      runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
    rw [hE, h1, toWord_sub_one j (by omega), hH, ltW_toWord (by omega) (by omega)]
  have fr1 : ∀ r, r < regs → r ≠ rKj → r ≠ rZ →
      rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M r = rd s.M r :=
    fun r hr h1 h2 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hp1 : ∀ x, regs ≤ x →
      rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M x = rd s.M x :=
    fun x hx => hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, rKj, rZ]) x hx
  rw [qryIR, semXIR_seq]
  generalize semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s = s1
    at hM1 hk1 hz1 fr1 hp1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the expected word
  have hex : rd (semXIR I (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
      (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh])
      (.input rE rAd4))) s1).M rE = exW I s.M h o j := by
    rw [semXIR_ite, hz1, exW]
    by_cases hjh : j < h
    · rw [if_neg (by rw [decide_eq_true hjh]; decide), if_pos hjh, semXIR_seq]
      have ha : rd (semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1).M rAd4 =
          toWord (hB + j) := by
        simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
          runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
        rw [hk1, add_toWord]
      have hp : rd (semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1).M
          (hB + j) = rd s.M (hB + j) := by
        rw [hframe I _ s1 (by simp +decide only [Lo, Prim.dst, regs, rKd, rAd4]) _
            (by simp only [regs, hB_eq]; omega),
          hp1 _ (by simp only [regs, hB_eq]; omega)]
      have z2 := size_sem I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1
      generalize semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1 = s2
        at ha hp z2
      simp only [semXIR]
      rw [rd_set_self (by simp only [rE]; omega), ha, toNat_toWord (by simp only [hB_eq]; omega), hp]
    · rw [if_pos (by rw [decide_eq_false hjh]; decide), if_neg hjh, semXIR_seq]
      have ha : rd (semXIR I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1).M rAd4 =
          toWord (o + j - h) := by
        simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
          runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
        rw [hk1, fr1 rTo (by decide) (by decide) (by decide), hO, add_toWord,
          fr1 rTh (by decide) (by decide) (by decide), hH, sub_toWord (by omega) (by omega)]
      have z2 := size_sem I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1
      generalize semXIR I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1 = s2 at ha z2
      simp only [semXIR]
      rw [rd_set_self (by simp only [rE]; omega), ha, toNat_toWord (by omega)]
  have fr2 : ∀ r, r < regs → r ≠ rKd → r ≠ rAd4 → r ≠ rE → rd (semXIR I (.ite rZ (.seq (.blk
      [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) (.load rE rAd4)) (.seq (.blk [.op .add rAd4
      rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4))) s1).M r = rd s1.M r :=
    fun r hr a b c =>
      frame I _ s1 (by simp +decide only [WF, Prim.dst, rKd, rAd4, rE, and_true]) hM1 r hr (by
        simp [Writes, Prim.dst]; exact ⟨⟨⟨Ne.symm a, Ne.symm b⟩, c⟩, Ne.symm b, c⟩)
  have hM2 := inv_sem I (P := .ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
    (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4)))
    (by simp +decide only [WF, Prim.dst, rKd, rAd4, rE, and_true]) hM1
  rw [semXIR_seq]
  generalize semXIR I (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
    (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh])
    (.input rE rAd4))) s1 = s2 at hex fr2 hM2
  have hs2 := hM2.1
  have h12 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  simp only [regs] at hs2
  have hw2 : rd s2.M rWd = rd s.M rWd := by
    rw [fr2 rWd (by decide) (by decide) (by decide) (by decide),
      fr1 rWd (by decide) (by decide) (by decide)]
  have hmt2 : rd s2.M rMt = bW b := by
    rw [fr2 rMt (by decide) (by decide) (by decide) (by decide),
      fr1 rMt (by decide) (by decide) (by decide), hT]
  have heo2 : rd s2.M rEo = toWord (j + 1) := by
    rw [fr2 rEo (by decide) (by decide) (by decide) (by decide),
      fr1 rEo (by decide) (by decide) (by decide), hE]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
    runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
  rw [hw2, hex, hmt2, heo2, h12, eq_bW, bW_and, add_one_toWord]
  exact ⟨rfl, rfl⟩


/-! ## An answer word -/

/-- The branch-free selection of `setSPs`. -/
theorem maskSel (x w : Word) (b : Bool) :
    XOp.xor.eval x (XOp.and.eval (XOp.xor.eval x w) (XOp.sub.eval 0 (bW b))) = if b then w else x := by
  cases b
  · simp [XOp.eval, bW]
  · simp only [XOp.eval, bW, if_true]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]

theorem setSPs_run (M : Mem) (hs : 256 ≤ M.size) {m r k : ℕ} (hr : r ∈ [rS0, rS1, rS2, rS3])
    (hm : m < 4) (hk : rd M rKj = toWord k) (hk2 : k < 2 ^ 64) :
    rd (runPrims (setSPs m r) M) r = (if k = m then rd M rWd else rd M r) ∧
    ∀ i, i ≠ rKd → i ≠ rMk5 → i ≠ r → rd (runPrims (setSPs m r) M) i = rd M i := by
  have hrr : r < 256 ∧ r ≠ rKd ∧ r ≠ rMk5 ∧ r ≠ rKj ∧ r ≠ rWd := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrr
  refine ⟨?_, fun i a b c => rd_runPrims_of_not_writes (by
    simp only [setSPs, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;>
      first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c) _⟩
  simp only [setSPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | (exact Nat.lt_of_lt_of_le (m := 256) h1 (by assumption)) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) h1 (by assumption)) | (exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne, Ne.symm h2, Ne.symm h3, h4, h5, Ne.symm h4, Ne.symm h5]
  rw [hk, eqW_toWord hk2 (by omega), maskSel]
  by_cases h : k = m <;> simp [h]

theorem lo_ansPs : Lo (.blk ansPs) := by
  simp +decide only [ansPs, setSPs, Lo, Prim.dst, regs, rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ]

theorem wf_ansPs : WF (.blk ansPs) := by
  simp +decide only [ansPs, setSPs, WF, Prim.dst, rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ]

/-- **An answer word** `m = eo − qw − 1`: `rS_m := w`, `rZ := [m = 3]`. -/
theorem ansPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {qw m : ℕ} (hm : m < 4)
    (hq : 1 + qw + m < 2 ^ 64) (hE : rd s.M rEo = toWord (1 + qw + m))
    (hQ : rd s.M rQw = toWord qw) :
    (∀ i < 4, rd (semXIR I (.blk ansPs) s).M (rS0 + i) =
      if i = m then rd s.M rWd else rd s.M (rS0 + i)) ∧
    rd (semXIR I (.blk ansPs) s).M rZ = bW (decide (m = 3)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have e : semXIR I (.blk ansPs) s = ⟨runPrims ([.const rKd 3, .op .eq rZ rKj rKd])
      (runPrims (setSPs 3 rS3) (runPrims (setSPs 2 rS2) (runPrims (setSPs 1 rS1)
      (runPrims (setSPs 0 rS0) (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M))))),
      s.o⟩ := by
    simp only [semXIR, ansPs, runPrims_append]
  rw [e]
  simp only
  -- the index `m`
  have hk0 : rd (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M) rKj = toWord m := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hE, hQ, h1, sub_toWord hq (by omega), show 1 + qw + m - qw = m + 1 by omega,
      toWord_sub_one m (by omega)]
  have hw0 : ∀ i, i ≠ rKj → rd (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M) i =
      rd s.M i := fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z0 := size_runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M
  generalize runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M = M0 at hk0 hw0 z0
  have hs0 : 256 ≤ M0.size := by omega
  obtain ⟨a0, b0⟩ := setSPs_run M0 hs0 (m := 0) (r := rS0) (by simp) (by norm_num) hk0 (by omega)
  have z1 := size_runPrims (setSPs 0 rS0) M0
  generalize runPrims (setSPs 0 rS0) M0 = M1 at a0 b0 z1
  have hk1 : rd M1 rKj = toWord m := by rw [b0 _ (by decide) (by decide) (by decide), hk0]
  obtain ⟨a1, b1⟩ := setSPs_run M1 (by omega) (m := 1) (r := rS1) (by simp) (by norm_num) hk1 (by omega)
  have z2 := size_runPrims (setSPs 1 rS1) M1
  generalize runPrims (setSPs 1 rS1) M1 = M2 at a1 b1 z2
  have hk2 : rd M2 rKj = toWord m := by rw [b1 _ (by decide) (by decide) (by decide), hk1]
  obtain ⟨a2, b2⟩ := setSPs_run M2 (by omega) (m := 2) (r := rS2) (by simp) (by norm_num) hk2 (by omega)
  have z3 := size_runPrims (setSPs 2 rS2) M2
  generalize runPrims (setSPs 2 rS2) M2 = M3 at a2 b2 z3
  have hk3 : rd M3 rKj = toWord m := by rw [b2 _ (by decide) (by decide) (by decide), hk2]
  obtain ⟨a3, b3⟩ := setSPs_run M3 (by omega) (m := 3) (r := rS3) (by simp) (by norm_num) hk3 (by omega)
  have z4 := size_runPrims (setSPs 3 rS3) M3
  generalize runPrims (setSPs 3 rS3) M3 = M4 at a3 b3 z4
  have hk4 : rd M4 rKj = toWord m := by rw [b3 _ (by decide) (by decide) (by decide), hk3]
  have hs4 : 256 ≤ M4.size := by omega
  have hfin : ∀ i, i ≠ rKd → i ≠ rZ → rd (runPrims [.const rKd 3, .op .eq rZ rKj rKd] M4) i =
      rd M4 i := fun i a b => rd_runPrims_of_not_writes (by
        simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
  have hw : ∀ i, i ≠ rKj → rd M0 i = rd s.M i := hw0
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hfin _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rZ]; omega)]
    interval_cases i
    · rw [b3 _ (by decide) (by decide) (by decide), b2 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), show rS0 + 0 = rS0 from rfl, a0,
        hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 0 <;> simp [h, eq_comm]
    · rw [b3 _ (by decide) (by decide) (by decide), b2 _ (by decide) (by decide) (by decide),
        show rS0 + 1 = rS1 from rfl, a1, b0 _ (by decide) (by decide) (by decide),
        b0 _ (by decide) (by decide) (by decide), hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 1 <;> simp [h, eq_comm]
    · rw [b3 _ (by decide) (by decide) (by decide), show rS0 + 2 = rS2 from rfl, a2,
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 2 <;> simp [h, eq_comm]
    · rw [show rS0 + 3 = rS3 from rfl, a3, b2 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        b2 _ (by decide) (by decide) (by decide), b1 _ (by decide) (by decide) (by decide),
        b0 _ (by decide) (by decide) (by decide), hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 3 <;> simp [h, eq_comm]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hk4]
    exact eqW_toWord (b := 3) (by omega) (by norm_num)

/-! ## Stores -/

theorem stNext_sem (I : Array Word) (s : St) (hM : Inv s.M) {a r : ℕ} (hr : r < regs)
    (hr4 : r ≠ cTmp) (hrA : r ≠ rAd4) (hA : rd s.M rAd4 = toWord a) (ha : regs ≤ a + 1)
    (ha2 : a + 1 < 2 ^ 64) (has : a + 1 < s.M.size) :
    rd (semXIR I (stNext r) s).M rAd4 = toWord (a + 1) ∧
    (∀ i, i ≠ cTmp → i ≠ rAd4 →
      rd (semXIR I (stNext r) s).M i = if i = a + 1 then rd s.M r else rd s.M i) ∧
    Inv (semXIR I (stNext r) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hr ha
  have hM1 := inv_sem I (P := .blk [.op .add rAd4 rAd4 cOne]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM
  have ha1 : rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M rAd4 = toWord (a + 1) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hA, h1, add_one_toWord]
  have hf1 : ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z1 := size_sem I (.blk [.op .add rAd4 rAd4 cOne]) s
  rw [stNext, semXIR_seq]
  generalize semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s = s1 at hM1 ha1 hf1 z1
  have e : semXIR I (.store rAd4 r) s1 = ⟨storeM s1.M rAd4 r, s1.o⟩ := rfl
  rw [e]
  refine ⟨?_, fun i hi hiA => ?_, inv_sem I (P := .store rAd4 r) (by simp +decide only [WF, rAd4,
    cTmp]) hM1⟩
  · rw [storeM_frame hM1 (by decide) (by decide) (by decide), ha1]
  · rw [rd_storeM hM1 ha1 ha ha2 (by omega) (by decide) hr4 hi, hf1 r hrA, hf1 i hiA]

/-- **Four stores** of `rS0 … rS3` at `b … b + 3`. -/
theorem st4IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {b : ℕ} (hA : rd s.M rAd4 = toWord b)
    (hb : regs ≤ b) (hb2 : b + 4 < 2 ^ 64) (hbs : b + 4 ≤ s.M.size) :
    rd (semXIR I st4IR s).M rAd4 = toWord (b + 3) ∧
    (∀ i, i ≠ cTmp → i ≠ rAd4 → rd (semXIR I st4IR s).M i =
      if b ≤ i ∧ i < b + 4 then rd s.M (rS0 + (i - b)) else rd s.M i) ∧
    Inv (semXIR I st4IR s).M := by
  have hs := hM.1
  simp only [regs] at hs hb
  have e0 : semXIR I (.store rAd4 rS0) s = ⟨storeM s.M rAd4 rS0, s.o⟩ := rfl
  have hM0 := inv_sem I (P := .store rAd4 rS0) (by simp +decide only [WF, rAd4, cTmp]) hM
  rw [e0] at hM0
  have a0 : rd (storeM s.M rAd4 rS0) rAd4 = toWord b := by
    rw [storeM_frame hM (by decide) (by decide) (by decide), hA]
  have f0 : ∀ i, i ≠ cTmp → rd (storeM s.M rAd4 rS0) i = if i = b then rd s.M rS0 else rd s.M i :=
    fun i hi => rd_storeM hM hA (by simp only [regs]; omega) (by omega) (by omega) (by decide)
      (by decide) hi
  rw [st4IR, semXIR_seq, e0, semXIR_seq]
  generalize hS0 : (⟨storeM s.M rAd4 rS0, s.o⟩ : St) = s0 at hM0
  have a0' : rd s0.M rAd4 = toWord b := by rw [← hS0]; exact a0
  have f0' : ∀ i, i ≠ cTmp → rd s0.M i = if i = b then rd s.M rS0 else rd s.M i := by
    rw [← hS0]; exact f0
  have z0 : s0.M.size = s.M.size := by rw [← hS0]; exact size_storeM ..
  obtain ⟨a1, f1, hM1⟩ := stNext_sem I s0 hM0 (r := rS1) (by decide) (by decide) (by decide) a0'
    (by simp only [regs]; omega) (by omega) (by omega)
  have z1 := size_sem I (stNext rS1) s0
  rw [semXIR_seq]
  generalize semXIR I (stNext rS1) s0 = s1 at a1 f1 hM1 z1
  obtain ⟨a2, f2, hM2⟩ := stNext_sem I s1 hM1 (r := rS2) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (stNext rS2) s1
  generalize semXIR I (stNext rS2) s1 = s2 at a2 f2 hM2 z2
  obtain ⟨a3, f3, hM3⟩ := stNext_sem I s2 hM2 (r := rS3) (by decide) (by decide) (by decide) a2
    (by simp only [regs]; omega) (by omega) (by omega)
  refine ⟨by rw [a3, show b + 1 + 1 + 1 = b + 3 by omega], fun i hi hiA => ?_, hM3⟩
  have r1 : rd s0.M rS1 = rd s.M rS1 := by rw [f0' _ (by decide), if_neg (by simp only [rS1]; omega)]
  have r2 : rd s1.M rS2 = rd s.M rS2 := by
    rw [f1 _ (by decide) (by decide), if_neg (by simp only [rS2]; omega), f0' _ (by decide),
      if_neg (by simp only [rS2]; omega)]
  have r3 : rd s2.M rS3 = rd s.M rS3 := by
    rw [f2 _ (by decide) (by decide), if_neg (by simp only [rS3]; omega), f1 _ (by decide) (by decide),
      if_neg (by simp only [rS3]; omega), f0' _ (by decide), if_neg (by simp only [rS3]; omega)]
  rw [f3 i hi hiA, f2 i hi hiA, f1 i hi hiA, f0' i hi, r1, r2, r3]
  split_ifs <;> first | omega | rfl |
    (rw [show rS0 + (i - b) = rS3 by simp only [rS0, rS3]; omega]) |
    (rw [show rS0 + (i - b) = rS2 by simp only [rS0, rS2]; omega]) |
    (rw [show rS0 + (i - b) = rS1 by simp only [rS0, rS1]; omega]) |
    (rw [show i - b = 0 by omega]; rfl)


/-! ## The record -/

theorem mulW_toWord (a b : ℕ) : XOp.mul.eval (toWord a) (toWord b) = toWord (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval, toWord, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

theorem load_semC (I : Array Word) (s : St) (hM : Inv s.M) {d a : ℕ} (hd : d < regs) :
    rd (semXIR I (.load d a) s).M d = rd s.M (rd s.M a).toNat ∧
    ∀ i, i ≠ d → rd (semXIR I (.load d a) s).M i = rd s.M i := by
  have hs := hM.1
  exact ⟨rd_set_self (by simp only [regs] at hs hd; omega), fun i hi => rd_set_ne (Ne.symm hi)⟩

theorem addOne_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ}
    (hA : rd s.M rAd4 = toWord a) :
    rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M rAd4 = toWord (a + 1) ∧
    ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M i = rd s.M i := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _⟩
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  rw [hA, h1, add_one_toWord]

theorem nextPs_frame (M : Mem) (i : ℕ) (a : i ≠ rPi) (b : i ≠ rKd) (c : i ≠ rAd4) :
    rd (runPrims nextPs M) i = rd M i := by
  apply rd_runPrims_of_not_writes
  simp only [nextPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl)
  · exact Ne.symm a
  · exact Ne.symm b
  · exact Ne.symm c
  · exact Ne.symm b
  · exact Ne.symm c

/-- **The next target**: `p + 1`, `tl`, `o` from the table, `h = 4`; the heap is kept. -/
theorem nextIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : p + 1 < 2 ^ 11)
    (hP : rd s.M rPi = toWord p) :
    rd (semXIR I nextIR s).M rPi = toWord (p + 1) ∧
    rd (semXIR I nextIR s).M rTl = rd s.M (chB + 4 * (p + 1)) ∧
    rd (semXIR I nextIR s).M rTo = rd s.M (chB + 4 * (p + 1) + 1) ∧
    rd (semXIR I nextIR s).M rTh = 4 ∧
    (∀ x, regs ≤ x → rd (semXIR I nextIR s).M x = rd s.M x) ∧
    (∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo →
      i ≠ rTh → rd (semXIR I nextIR s).M i = rd s.M i) ∧
    Inv (semXIR I nextIR s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have e0 : semXIR I nextPre s = ⟨runPrims nextPs s.M, s.o⟩ := rfl
  have w0 : WF nextPre := by simp +decide only [nextPre, nextPs, WF, Prim.dst, rPi, rKd, rAd4]
  have hM0 := inv_sem I w0 hM
  have a0 : rd (semXIR I nextPre s).M rAd4 = toWord (chB + 4 * (p + 1)) ∧
      rd (semXIR I nextPre s).M rPi = toWord (p + 1) := by
    rw [e0]
    simp only [nextPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, h1, add_one_toWord]
    refine ⟨?_, rfl⟩
    rw [show (4 : Word) = toWord 4 from rfl, mulW_toWord, add_toWord]
    congr 1
    ring
  have f0 : ∀ i, i ≠ rPi → i ≠ rKd → i ≠ rAd4 → rd (semXIR I nextPre s).M i = rd s.M i :=
    fun i a b c => by simp only [e0]; exact nextPs_frame s.M i a b c
  rw [nextIR, semXIR_seq]
  generalize semXIR I nextPre s = s0 at hM0 a0 f0
  obtain ⟨a0, p0⟩ := a0
  -- two loads
  obtain ⟨l1, g1⟩ := load_semC I s0 hM0 (d := rTl) (a := rAd4) (by decide)
  have hM1 := inv_sem I (P := .load rTl rAd4) (by simp +decide only [WF, rTl]) hM0
  rw [semXIR_seq]
  generalize semXIR I (.load rTl rAd4) s0 = s1 at l1 g1 hM1
  obtain ⟨n1, k1⟩ := addOne_sem I s1 hM1 (a := chB + 4 * (p + 1)) (by rw [g1 _ (by decide), a0])
  have hM2 := inv_sem I (P := .blk [.op .add rAd4 rAd4 cOne]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s1 = s2 at n1 k1 hM2
  obtain ⟨l2, g2⟩ := load_semC I s2 hM2 (d := rTo) (a := rAd4) (by decide)
  have hM3 := inv_sem I (P := .load rTo rAd4) (by simp +decide only [WF, rTo]) hM2
  rw [semXIR_seq]
  generalize semXIR I (.load rTo rAd4) s2 = s3 at l2 g2 hM3
  -- the heap is unchanged
  have hh3 : ∀ x, regs ≤ x → rd s3.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [g2 x (by simp only [rTo]; omega), k1 x (by simp only [rAd4]; omega),
      g1 x (by simp only [rTl]; omega), f0 x (by simp only [rPi]; omega) (by simp only [rKd]; omega)
      (by simp only [rAd4]; omega)]
  have hr3 : ∀ i < regs, i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo →
      rd s3.M i = rd s.M i := fun i _ a b c d e => by
    rw [g2 i e, k1 i a, g1 i d, f0 i c b a]
  have vTl : rd s3.M rTl = rd s.M (chB + 4 * (p + 1)) := by
    rw [g2 _ (by decide), k1 _ (by decide), l1, a0,
      toNat_toWord (by simp only [chB_eq]; omega), f0 _ (by simp only [chB_eq, rPi]; omega)
      (by simp only [chB_eq, rKd]; omega) (by simp only [chB_eq, rAd4]; omega)]
  have vTo : rd s3.M rTo = rd s.M (chB + 4 * (p + 1) + 1) := by
    rw [l2, n1, toNat_toWord (by simp only [chB_eq]; omega),
      k1 _ (by simp only [chB_eq, rAd4]; omega), g1 _ (by simp only [chB_eq, rTl]; omega),
      f0 _ (by simp only [chB_eq, rPi]; omega) (by simp only [chB_eq, rKd]; omega)
      (by simp only [chB_eq, rAd4]; omega)]
  have vPi : rd s3.M rPi = toWord (p + 1) := by
    rw [g2 _ (by decide), k1 _ (by decide), g1 _ (by decide), p0]
  -- `h := 4`
  have t4 : rd (semXIR I (.blk [.const rTh 4]) s3).M rTh = 4 := by
    have := hM3.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTh]; omega)
  have f4 : ∀ i, i ≠ rTh → rd (semXIR I (.blk [.const rTh 4]) s3).M i = rd s3.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  refine ⟨?_, ?_, ?_, t4, fun x hx => ?_, fun i hi _ a k x1 x2 x3 x4 => ?_,
    inv_sem I (P := .blk [.const rTh 4]) (by simp +decide only [WF, Prim.dst, rTh]) hM3⟩
  · rw [f4 _ (by decide), vPi]
  · rw [f4 _ (by decide), vTl]
  · rw [f4 _ (by decide), vTo]
  · rw [f4 x (by simp only [regs] at hx; simp only [rTh]; omega), hh3 x hx]
  · rw [f4 i x4, hr3 i hi a k x1 x2 x3]


theorem recPs_frame (M : Mem) (i : ℕ) (b : i ≠ rKd) (c : i ≠ rAd4) :
    rd (runPrims recPs M) i = rd M i := by
  apply rd_runPrims_of_not_writes
  simp only [recPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl)
  · exact Ne.symm b
  · exact Ne.symm c
  · exact Ne.symm b
  · exact Ne.symm c

/-- **The record**: the answer registers at `ansB + 4p … + 3` and at `hB … hB + 3`; `p + 1`,
`tl`, `o` from the table, `h = 4`. -/
theorem recIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : p + 1 < 2 ^ 11)
    (hP : rd s.M rPi = toWord p) (hsz : chEnd ≤ s.M.size) :
    rd (semXIR I recIR s).M rPi = toWord (p + 1) ∧
    rd (semXIR I recIR s).M rTl = rd s.M (chB + 4 * (p + 1)) ∧
    rd (semXIR I recIR s).M rTo = rd s.M (chB + 4 * (p + 1) + 1) ∧
    rd (semXIR I recIR s).M rTh = 4 ∧
    (∀ x, regs ≤ x → rd (semXIR I recIR s).M x =
      if ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4 then rd s.M (rS0 + (x - (ansB + 4 * p)))
      else if hB ≤ x ∧ x < hB + 4 then rd s.M (rS0 + (x - hB)) else rd s.M x) ∧
    (∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo →
      i ≠ rTh → rd (semXIR I recIR s).M i = rd s.M i) ∧
    Inv (semXIR I recIR s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have q1 : regs ≤ ansB + 4 * p := by rw [ansB_eq]; simp only [regs]; omega
  have q2 : ansB + 4 * p + 4 < 2 ^ 64 := by rw [ansB_eq]; omega
  have q3 : ansB + 4 * p + 4 ≤ s.M.size := by rw [ansB_eq]; simp only [chEnd] at hsz; omega
  have q4 : regs ≤ hB := by rw [hB_eq]; simp only [regs]; omega
  have q5 : hB + 4 < 2 ^ 64 := by rw [hB_eq]; omega
  have q6 : hB + 4 ≤ s.M.size := by rw [hB_eq]; simp only [chEnd] at hsz; omega
  have q7 : ∀ k < 2, regs ≤ chB + 4 * (p + 1) + k := fun k _ => by rw [chB_eq]; simp only [regs]; omega
  have e0 : semXIR I recPre s = ⟨runPrims recPs s.M, s.o⟩ := rfl
  have hM0 :=
    inv_sem I (P := recPre) (by simp +decide only [recPre, recPs, WF, Prim.dst, rKd, rAd4]) hM
  have a0 : rd (semXIR I recPre s).M rAd4 = toWord (ansB + 4 * p) := by
    simp only [e0, recPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, show (4 : Word) = toWord 4 from rfl, mulW_toWord, add_toWord]
    congr 1
    ring
  have f0 : ∀ i, i ≠ rKd → i ≠ rAd4 → rd (semXIR I recPre s).M i = rd s.M i :=
    fun i b c => by simp only [e0]; exact recPs_frame s.M i b c
  have z0 := size_sem I recPre s
  rw [recIR, semXIR_seq]
  generalize semXIR I recPre s = s0 at hM0 a0 f0 z0
  -- the answer at `ansB + 4p`
  obtain ⟨a1, f1, hM1⟩ := st4IR_sem I s0 hM0 (b := ansB + 4 * p) a0 q1 q2
    (by rw [z0]; exact q3)
  have z1 := size_sem I st4IR s0
  rw [semXIR_seq]
  generalize semXIR I st4IR s0 = s1 at a1 f1 hM1 z1
  -- `rAd4 := hB`
  have hM2 := inv_sem I (P := .blk [.const rAd4 (toWord hB)]) (by simp +decide only [WF,
    Prim.dst, rAd4])
    hM1
  have a2 : rd (semXIR I (.blk [.const rAd4 (toWord hB)]) s1).M rAd4 = toWord hB := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rAd4]; omega)
  have f2 : ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.const rAd4 (toWord hB)]) s1).M i =
      rd s1.M i := fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z2 := size_sem I (.blk [.const rAd4 (toWord hB)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rAd4 (toWord hB)]) s1 = s2 at hM2 a2 f2 z2
  -- the answer at `hB`
  obtain ⟨a3, f3, hM3⟩ := st4IR_sem I s2 hM2 (b := hB) a2 q4 q5
    (by rw [z2, z1, z0]; exact q6)
  rw [semXIR_seq]
  generalize semXIR I st4IR s2 = s3 at a3 f3 hM3
  -- registers kept so far
  have r3 : ∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → rd s3.M i = rd s.M i := fun i hi c a k => by
    simp only [regs] at hi
    rw [f3 i c a, if_neg (by simp only [hB_eq]; omega), f2 i a, f1 i c a,
      if_neg (by simp only [ansB_eq]; omega), f0 i k a]
  have hS : ∀ j < 4, rd s2.M (rS0 + j) = rd s.M (rS0 + j) := fun j hj => by
    rw [f2 _ (by simp only [rS0, rAd4]; omega), f1 _ (by simp only [rS0, cTmp]; omega)
      (by simp only [rS0, rAd4]; omega), if_neg (by simp only [rS0, ansB_eq]; omega),
      f0 _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rAd4]; omega)]
  have h3 : ∀ x, regs ≤ x → rd s3.M x =
      if ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4 then rd s.M (rS0 + (x - (ansB + 4 * p)))
      else if hB ≤ x ∧ x < hB + 4 then rd s.M (rS0 + (x - hB)) else rd s.M x :=
    fun x hx => by
      simp only [regs] at hx
      rw [f3 x (by simp only [cTmp]; omega) (by simp only [rAd4]; omega),
        f2 x (by simp only [rAd4]; omega), f1 x (by simp only [cTmp]; omega)
        (by simp only [rAd4]; omega)]
      by_cases hA : ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4
      · rw [if_neg (by simp only [hB_eq, ansB_eq] at hA ⊢; omega), if_pos hA, if_pos hA,
          f0 _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rAd4]; omega)]
      · rw [if_neg hA, if_neg hA]
        by_cases hH : hB ≤ x ∧ x < hB + 4
        · rw [if_pos hH, if_pos hH, hS _ (by omega)]
        · rw [if_neg hH, if_neg hH, f0 x (by simp only [rKd]; omega)
            (by simp only [rAd4]; omega)]
  have hP3 : rd s3.M rPi = toWord p := by
    rw [r3 _ (by decide) (by decide) (by decide) (by decide), hP]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nextIR_sem I s3 hM3 hp hP3
  have hT : ∀ k < 2, rd s3.M (chB + 4 * (p + 1) + k) = rd s.M (chB + 4 * (p + 1) + k) :=
    fun k hk => by
      have hx : regs ≤ chB + 4 * (p + 1) + k := q7 k hk
      have h1 : ¬ (ansB + 4 * p ≤ chB + 4 * (p + 1) + k ∧ chB + 4 * (p + 1) + k < ansB + 4 * p + 4) :=
        by simp only [chB_eq, ansB_eq]; omega
      have h2 : ¬ (hB ≤ chB + 4 * (p + 1) + k ∧ chB + 4 * (p + 1) + k < hB + 4) := by
        simp only [chB_eq, hB_eq]; omega
      rw [h3 _ hx, if_neg h1, if_neg h2]
  refine ⟨n1, ?_, ?_, n4, fun x hx => ?_, fun i hi c a k x1 x2 x3 x4 => ?_, n7⟩
  · rw [n2]; exact hT 0 (by norm_num)
  · rw [n3, hT 1 (by norm_num)]
  · rw [n5 x hx, h3 x hx]
  · rw [n6 i hi c a k x1 x2 x3 x4, r3 i hi c a k]


/-! ## After answer word 3 -/

/-- The test before the record: `rZ := [p < N] ∧ rMt`. -/
def lastPs (N : ℕ) : List Prim := [.const rKd (toWord N), .op .ltu rZ rPi rKd, .op .and rZ rZ rMt]

theorem lastIR_eq (N : ℕ) : lastIR N =
    .seq (.blk (lastPs N)) (.seq (.ite rZ recIR (.blk [])) (.blk [.const rEo 0])) := rfl

/-- **The decision after answer word 3**: the test block leaves a state `s₁` equal to `s` but for
`rKd` and `rZ`; then the record runs on `s₁` iff `p < N` and the flag is set; then `eo := 0`. -/
theorem lastIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N p : ℕ} {b : Bool}
    (hN : N < 2 ^ 64) (hp : p < 2 ^ 64) (hP : rd s.M rPi = toWord p) (hT : rd s.M rMt = bW b) :
    ∃ s₁ : St, Inv s₁.M ∧ s₁.M.size = s.M.size ∧
      (∀ i, i ≠ rKd → i ≠ rZ → rd s₁.M i = rd s.M i) ∧
      semXIR I (lastIR N) s = semXIR I (.blk [.const rEo 0])
        (if p < N ∧ b = true then semXIR I recIR s₁ else s₁) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨semXIR I (.blk (lastPs N)) s, inv_sem I (by simp +decide only [lastPs, WF, Prim.dst, rKd,
    rZ, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]) hM,
    size_sem .., fun i a b => rd_runPrims_of_not_writes (by
      simp only [lastPs, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b
      · exact Ne.symm b) _, ?_⟩
  have hz : rd (semXIR I (.blk (lastPs N)) s).M rZ = bW (decide (p < N) && b) := by
    simp only [semXIR, lastPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, ltW_toWord hp hN, hT, bW_and]
  rw [lastIR_eq, semXIR_seq, semXIR_seq, semXIR_ite, hz]
  by_cases h : p < N ∧ b = true
  · rw [if_pos h, if_neg (by rw [decide_eq_true h.1, h.2]; decide)]
  · rw [if_neg h, if_pos (by
      by_cases h1 : p < N
      · have : b = false := by simpa [h1] using h
        rw [this]; simp; rfl
      · rw [decide_eq_false h1]; rfl)]
    with_unfolding_all rfl

end Lvm.X

end LvmXChainSem

section LvmXChainLoop

/-!
# The chain scan on the machine: the loop

* `Stat`: what the loop keeps between entries and inside one: the target index `p` and the
  answers found (`ansB + 4q`), the current target's length and words (`exW`), the heap outside
  `H` and the answers.
* `TabOK`: the table and the tape realise the targets `T p st` for `0 < p < N` (the previous
  answer's 4 words, then tape words).
* The four cases of one word (`word_len`, `word_qry`, `word_ans`, `word_last`), then one entry
  (`entry_sem`: `qWords e` iterations do `scanStep`), then the log (`scan_sem`).
-/

namespace Lvm.X

open RecursionFast

/-! ## The invariant -/

/-- **What the loop keeps**: `p` and the answers found; the current target (when `p < N`):
its length in `rTl`, its words `exW` (header `h ≤ 16`, tape offset `o < 2^62`); the heap outside
`H` and the answers is the loop's initial heap `M₀`. -/
structure Stat (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (M₀ : Mem) (x : SS)
    (s : St) : Prop where
  inv : Inv s.M
  size : chEnd ≤ s.M.size
  pi : rd s.M rPi = toWord x.1
  pN : x.1 ≤ N
  len : x.2.2.length = x.1
  th : (rd s.M rTh).toNat ≤ 16
  tof : (rd s.M rTo).toNat < 2 ^ 62
  tg : x.1 < N → rd s.M rTl = toWord (T x.1 x.2.1).size ∧ (T x.1 x.2.1).size < 2 ^ 64 ∧
    ∀ j < ((T x.1 x.2.1).size + 7) / 8, (packBytes (T x.1 x.2.1).data.toList).getD j 0 =
      exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j
  ans : ∀ q < x.1, ∀ m < 4,
    rd s.M (ansB + 4 * q + m) = (packBytes (x.2.2.getD q default).toList).getD m 0
  heap : ∀ y, regs ≤ y → (y < hB ∨ hB + 16 ≤ y) → (y < ansB ∨ chEnd ≤ y) → rd s.M y = rd M₀ y

/-- **The table realises the targets** `T p st` for `0 < p < N`: the length at `chB + 4p`, the
tape offset at `chB + 4p + 1`, and the words: the state's 4, then the tape from the offset. Entry
`N` has an offset below `2^62` too (it is loaded after the last record). -/
def TabOK (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (M₀ : Mem) : Prop :=
  ∀ p, 0 < p → p ≤ N → (rd M₀ (chB + 4 * p + 1)).toNat < 2 ^ 62 ∧ (p < N → ∀ st : Digest,
    rd M₀ (chB + 4 * p) = toWord (T p st).size ∧ (T p st).size < 2 ^ 64 ∧
    ∀ j < ((T p st).size + 7) / 8, (packBytes (T p st).data.toList).getD j 0 =
      if j < 4 then (packBytes st.toList).getD j 0
      else I.getD ((rd M₀ (chB + 4 * p + 1)).toNat + (j - 4)) 0)

theorem exW_congr {I : Array Word} {M M' : Mem} (h : ∀ y, regs ≤ y → rd M' y = rd M y)
    (hh o j : ℕ) : exW I M' hh o j = exW I M hh o j := by
  unfold exW; split_ifs
  · exact h _ (by simp only [hB_eq, regs]; omega)
  · rfl

/-- `Stat` survives code that keeps `rPi, rTl, rTh, rTo` and the heap. -/
theorem Stat.frame {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s s' : St} (h : Stat I T N M₀ x s) (hM : Inv s'.M) (hsz : s'.M.size = s.M.size)
    (hr : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd s'.M r = rd s.M r)
    (hh : ∀ y, regs ≤ y → rd s'.M y = rd s.M y) : Stat I T N M₀ x s' where
  inv := hM
  size := hsz ▸ h.size
  pi := (hr _ (.inl rfl)).trans h.pi
  pN := h.pN
  len := h.len
  th := (hr rTh (.inr (.inr (.inl rfl)))).symm ▸ h.th
  tof := (hr rTo (.inr (.inr (.inr rfl)))).symm ▸ h.tof
  tg := fun hp => by
    obtain ⟨a, b, c⟩ := h.tg hp
    refine ⟨(hr _ (.inr (.inl rfl))).trans a, b, fun j hj => ?_⟩
    rw [c j hj, hr rTh (.inr (.inr (.inl rfl))), hr rTo (.inr (.inr (.inr rfl))), exW_congr hh]
  ans := fun q hq m hm => (hh _ (by simp only [ansB_eq, regs]; omega)).trans (h.ans q hq m hm)
  heap := fun y hy h1 h2 => (hh y hy).trans (h.heap y hy h1 h2)

/-- Code that keeps `rPi, rTl, rTh, rTo` and the heap. -/
def Keep (s s' : St) : Prop :=
  (∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd s'.M r = rd s.M r) ∧
    ∀ y, regs ≤ y → rd s'.M y = rd s.M y

/-! ## The pieces of one word -/

/-- The test of the length word. -/
def w2Ps : List Prim := [.const rKd 0, .op .eq rZ rEo rKd]

/-- The query or answer word. -/
def restIR (N : ℕ) : XIR := .seq (.blk [.op .ltu rZ rQw rEo]) (.ite rZ (ansIR N) qryIR)

/-- The next word. -/
def incPs : List Prim := [.op .add rWp rWp cOne]

theorem wordIR_eq (N : ℕ) : wordIR N =
    .seq (.input rWd rWp) (.seq (.blk w2Ps) (.seq (.ite rZ lenIR (restIR N)) (.blk incPs))) := rfl

theorem pre_sem (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) :
    rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M rWd = I.getD pos 0 ∧
    rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M rZ =
      bW (decide (rd s.M rEo = 0)) ∧
    (∀ i, i ≠ rWd → i ≠ rKd → i ≠ rZ →
      rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M i = rd s.M i) ∧
    Inv (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M := by
  have hs := hM.1
  simp only [regs] at hs
  have hM1 := inv_sem I (P := .input rWd rWp) (by simp +decide only [WF, rWd]) hM
  have i1 : rd (semXIR I (.input rWd rWp) s).M rWd = I.getD pos 0 := by
    simp only [semXIR]
    rw [rd_set_self (by simp only [rWd]; omega), hW, toNat_toWord hpos]
  have f1 : ∀ i, i ≠ rWd → rd (semXIR I (.input rWd rWp) s).M i = rd s.M i :=
    fun i hi => rd_set_ne (Ne.symm hi)
  generalize semXIR I (.input rWd rWp) s = s1 at hM1 i1 f1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have e : semXIR I (.blk w2Ps) s1 = ⟨runPrims w2Ps s1.M, s1.o⟩ := rfl
  refine ⟨?_, ?_, fun i a b c => ?_,
    inv_sem I (by simp +decide only [w2Ps, WF, Prim.dst, rKd, rZ]) hM1⟩
  · simp only [e]
    rw [rd_runPrims_of_not_writes (by simp [w2Ps, Prim.dst, rKd, rZ, rWd]) _]; exact i1
  · rw [e]
    simp only [w2Ps, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rZ]; omega), rd_set_self (by simp only [rKd]; omega),
      rd_set_ne (by decide), f1 _ (by decide), eq_bW]
  · simp only [e]
    rw [rd_runPrims_of_not_writes (by
      simp only [w2Ps, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm b
      · exact Ne.symm c) _, f1 i a]

theorem inc_sem (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos) :
    rd (semXIR I (.blk incPs) s).M rWp = toWord (pos + 1) ∧
    (∀ i, i ≠ rWp → rd (semXIR I (.blk incPs) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk incPs) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [incPs, Prim.dst]; exact Ne.symm hi) _,
    inv_sem I (by simp +decide only [incPs, WF, Prim.dst, rWp]) hM⟩
  simp only [semXIR, incPs, runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [rWp]; omega), hW, h1, add_one_toWord]

/-- The heap is kept by every block of a word but the record. -/
theorem lo_restQ : Lo qryIR := lo_qryIR


theorem toWord_toNat (w : Word) : toWord w.toNat = w := by simp [toWord]

/-- The common head of a word: the word read, the test `eo = 0`. -/
theorem word_head (I : Array Word) (s : St) (hM : Inv s.M) (N : ℕ) :
    semXIR I (wordIR N) s = semXIR I (.blk incPs) (semXIR I (.ite rZ lenIR (restIR N))
      (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s))) := by
  rw [wordIR_eq]; rfl

/-! ## The four cases of one word -/

/-- **The length word.** -/
theorem word_len {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hE : rd s.M rEo = 0) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = 1 ∧
    rd (semXIR I (wordIR N) s).M rQw = ceil8 (I.getD pos 0) ∧
    rd (semXIR I (wordIR N) s).M rMt = XOp.eq.eval (I.getD pos 0) (rd s.M rTl) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  rw [semXIR_ite, p2, hE, if_neg (by decide)]
  obtain ⟨l1, l2, l3⟩ := lenIR_sem I s2 p4
  have hh3 := hframe I lenIR s2 lo_lenIR
  have z3 := size_sem I lenIR s2
  have hM3 := inv_sem I wf_lenIR p4
  have f3 : ∀ i < regs, ¬ Writes lenIR i → rd (semXIR I lenIR s2).M i = rd s2.M i :=
    fun i hi hw => frame I lenIR s2 wf_lenIR p4 i hi hw
  generalize semXIR I lenIR s2 = s3 at l1 l2 l3 hh3 z3 hM3 f3
  have w3 : rd s3.M rWp = toWord pos := by
    rw [f3 _ (by decide) (by simp +decide only [lenIR, ceil8Ps, Writes, Prim.dst, rWp, rQw, rMt,
      rEo, rKc, rT2, List.cons_append, List.nil_append]),
      p3 _ (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM4⟩ := inc_sem I s3 hM3 w3
  have hl : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd (semXIR I (.blk incPs) s3).M r =
      rd s.M r := fun r hr => by
    have hr' : r < regs ∧ ¬ Writes lenIR r ∧ r ≠ rWd ∧ r ≠ rKd ∧ r ≠ rZ ∧ r ≠ rWp := by
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp +decide only [lenIR, ceil8Ps, Writes, Prim.dst, regs, rWp, rQw, rMt, rEo, rKc, rT2,
          rPi, rTl, rTh, rTo, rWd, rKd, rZ, and_true, List.cons_append, List.nil_append]
    rw [i2 r hr'.2.2.2.2.2, f3 r hr'.1 hr'.2.1, p3 r hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1]
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s3).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh3 y hy, hh2 y hy]
  refine ⟨⟨hl, hH⟩, h.frame hM4 (by rw [size_sem, z3, z2]) hl hH, i1, ?_, ?_, ?_⟩
  · rw [i2 _ (by decide), l3]
  · rw [i2 _ (by decide), l1, p1]
  · rw [i2 _ (by decide), l2, p1, p3 _ (by decide) (by decide) (by decide)]

/-- **A query word** `j < qw`. -/
theorem word_qry {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos j qw : ℕ} {b : Bool} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hj : j < qw) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (j + 1)) (hQ : rd s.M rQw = toWord qw) (hT : rd s.M rMt = bW b) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = toWord (j + 2) ∧
    rd (semXIR I (wordIR N) s).M rQw = toWord qw ∧
    rd (semXIR I (wordIR N) s).M rMt =
      bW (b && decide (I.getD pos 0 = exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j)) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  have hne : rd s.M rEo ≠ 0 := by
    rw [hE]; intro e
    have := congrArg BitVec.toNat e
    rw [toNat_toWord (by omega)] at this
    simp at this
  rw [semXIR_ite, p2, decide_eq_false hne, if_pos (by decide), restIR, semXIR_seq]
  -- the phase test: a query word
  have hs2 := p4.1
  simp only [regs] at hs2
  have q1 : rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M rZ = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rZ]; omega), p3 _ (by decide) (by decide) (by decide),
      p3 _ (by decide) (by decide) (by decide), hQ, hE, ltW_toWord (by omega) (by omega),
      decide_eq_false (by omega)]
    rfl
  have g1 : ∀ i, i ≠ rZ → rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M i = rd s2.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM5 :=
    inv_sem I (P := .blk [.op .ltu rZ rQw rEo]) (by simp +decide only [WF, Prim.dst, rZ]) p4
  have hh5 := hframe I (.blk [.op .ltu rZ rQw rEo]) s2 (by simp +decide only [Lo, Prim.dst, regs,
    rZ])
  have z5 := size_sem I (.blk [.op .ltu rZ rQw rEo]) s2
  generalize semXIR I (.blk [.op .ltu rZ rQw rEo]) s2 = s5 at q1 g1 hM5 hh5 z5
  rw [semXIR_ite, q1, if_pos rfl]
  have r5 : ∀ r, r ≠ rZ → r ≠ rWd → r ≠ rKd → rd s5.M r = rd s.M r := fun r a b c => by
    rw [g1 r a, p3 r b c a]
  have hth : (rd s.M rTh).toNat ≤ 16 := h.th
  have hto : (rd s.M rTo).toNat < 2 ^ 62 := h.tof
  obtain ⟨k1, k2⟩ := qryIR_sem I s5 hM5 (j := j) (h := (rd s.M rTh).toNat) (o := (rd s.M rTo).toNat)
    (b := b) (by omega) hth (by omega)
    (by rw [r5 _ (by decide) (by decide) (by decide), hE])
    (by rw [r5 _ (by decide) (by decide) (by decide), toWord_toNat])
    (by rw [r5 _ (by decide) (by decide) (by decide), toWord_toNat])
    (by rw [r5 _ (by decide) (by decide) (by decide), hT])
  have hh6 := hframe I qryIR s5 lo_qryIR
  have z6 := size_sem I qryIR s5
  have hM6 := inv_sem I wf_qryIR hM5
  have f6 : ∀ i < regs, ¬ Writes qryIR i → rd (semXIR I qryIR s5).M i = rd s5.M i :=
    fun i hi hw => frame I qryIR s5 wf_qryIR hM5 i hi hw
  have wd : rd s5.M rWd = I.getD pos 0 := by rw [g1 _ (by decide), p1]
  have ex : exW I s5.M (rd s.M rTh).toNat (rd s.M rTo).toNat j =
      exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j :=
    exW_congr (fun y hy => by rw [hh5 y hy, hh2 y hy]) _ _ _
  rw [wd, ex] at k1
  generalize semXIR I qryIR s5 = s6 at k1 k2 hh6 z6 hM6 f6
  have w6 : rd s6.M rWp = toWord pos := by
    rw [f6 _ (by decide) (by simp +decide only [qryIR, Writes, Prim.dst, rWp, rKj, rZ, rKd, rAd4,
      rE, rMt, rEo, or_false]),
      r5 _ (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM7⟩ := inc_sem I s6 hM6 w6
  have hl : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo ∨ r = rQw) →
      rd (semXIR I (.blk incPs) s6).M r = rd s.M r := fun r hr => by
    have hr' : r < regs ∧ ¬ Writes qryIR r ∧ r ≠ rWd ∧ r ≠ rKd ∧ r ≠ rZ ∧ r ≠ rWp := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [qryIR, Writes, Prim.dst, regs, rWp, rKj, rZ, rKd, rAd4, rE, rMt, rEo,
          rPi, rTl, rTh, rTo, rWd, rQw, or_false, and_true]
    rw [i2 r hr'.2.2.2.2.2, f6 r hr'.1 hr'.2.1, r5 r hr'.2.2.2.2.1 hr'.2.2.1 hr'.2.2.2.1]
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s6).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh6 y hy, hh5 y hy, hh2 y hy]
  have hl4 : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) →
      rd (semXIR I (.blk incPs) s6).M r = rd s.M r :=
    fun r hr => hl r (by rcases hr with h | h | h | h <;> simp [h])
  refine ⟨⟨hl4, hH⟩, h.frame hM7 (by rw [size_sem, z6, z5, z2]) hl4 hH, i1, ?_, ?_, ?_⟩
  · rw [i2 _ (by decide), k2]
  · rw [hl _ (.inr (.inr (.inr (.inr rfl)))), hQ]
  · rw [i2 _ (by decide), k1]


/-- The path to an answer word: past the length test and the phase test, then `ansPs`. -/
theorem word_ans_path {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos qw m : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hm : m < 4) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + m)) (hQ : rd s.M rQw = toWord qw) :
    ∃ s3 : St, Inv s3.M ∧ s3.M.size = s.M.size ∧ (∀ y, regs ≤ y → rd s3.M y = rd s.M y) ∧
      (∀ i < 4, rd s3.M (rS0 + i) = if i = m then I.getD pos 0 else rd s.M (rS0 + i)) ∧
      rd s3.M rZ = bW (decide (m = 3)) ∧
      (∀ r, r < regs → r ≠ rWd → r ≠ rKd → r ≠ rZ → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 → r ≠ rS1 →
        r ≠ rS2 → r ≠ rS3 → rd s3.M r = rd s.M r) ∧
      semXIR I (wordIR N) s = semXIR I (.blk incPs)
        (semXIR I (.ite rZ (lastIR N) (.blk [.op .add rEo rEo cOne])) s3) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  have hne : rd s.M rEo ≠ 0 := by
    rw [hE]; intro e
    have := congrArg BitVec.toNat e
    rw [toNat_toWord (by omega)] at this
    simp at this
  rw [semXIR_ite, p2, decide_eq_false hne, if_pos (by decide), restIR, semXIR_seq]
  have hs2 := p4.1
  simp only [regs] at hs2
  have q1 : rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M rZ = bW true := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rZ]; omega), p3 _ (by decide) (by decide) (by decide),
      p3 _ (by decide) (by decide) (by decide), hQ, hE, ltW_toWord (by omega) (by omega),
      decide_eq_true (by omega)]
  have g1 : ∀ i, i ≠ rZ → rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M i = rd s2.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM5 :=
    inv_sem I (P := .blk [.op .ltu rZ rQw rEo]) (by simp +decide only [WF, Prim.dst, rZ]) p4
  have hh5 := hframe I (.blk [.op .ltu rZ rQw rEo]) s2 (by simp +decide only [Lo, Prim.dst, regs,
    rZ])
  have z5 := size_sem I (.blk [.op .ltu rZ rQw rEo]) s2
  generalize semXIR I (.blk [.op .ltu rZ rQw rEo]) s2 = s5 at q1 g1 hM5 hh5 z5
  rw [semXIR_ite, q1, if_neg (by decide), ansIR, semXIR_seq]
  have r5 : ∀ r, r ≠ rZ → r ≠ rWd → r ≠ rKd → rd s5.M r = rd s.M r := fun r a b c => by
    rw [g1 r a, p3 r b c a]
  obtain ⟨a1, a2⟩ := ansPs_sem I s5 hM5 (qw := qw) (m := m) hm (by omega) (by rw [r5 _ (by decide) (by decide)
    (by decide), hE]) (by rw [r5 _ (by decide) (by decide) (by decide), hQ])
  refine ⟨semXIR I (.blk ansPs) s5, inv_sem I wf_ansPs hM5, by rw [size_sem, z5, z2],
    fun y hy => by rw [hframe I _ s5 lo_ansPs y hy, hh5 y hy, hh2 y hy], fun i hi => ?_, a2,
    fun r hr a b c d e f g k l => ?_, rfl⟩
  · rw [a1 i hi, g1 rWd (by decide), p1, g1 (rS0 + i) (by simp only [rS0, rZ]; omega),
      p3 (rS0 + i) (by simp only [rS0, rWd]; omega) (by simp only [rS0, rKd]; omega)
      (by simp only [rS0, rZ]; omega)]
  · rw [frame I _ s5 wf_ansPs hM5 r hr (by
      simp +decide only [Writes, ansPs, setSPs, Prim.dst, List.mem_cons, List.mem_nil_iff,
        exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]
      simp only [rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ] at *
      lia), r5 r c a b]

/-- **A non-final answer word** `m < 3`. -/
theorem word_ans {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos qw m : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hm : m < 3) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + m)) (hQ : rd s.M rQw = toWord qw) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = toWord (1 + qw + (m + 1)) ∧
    rd (semXIR I (wordIR N) s).M rQw = toWord qw ∧
    rd (semXIR I (wordIR N) s).M rMt = rd s.M rMt ∧
    ∀ i < 4, rd (semXIR I (wordIR N) s).M (rS0 + i) =
      if i = m then I.getD pos 0 else rd s.M (rS0 + i) := by
  obtain ⟨s3, hM3, z3, hh3, hS3, hZ3, hr3, e⟩ :=
    word_ans_path h hW hpos (by omega) hqw hE hQ
  rw [e, semXIR_ite, hZ3, decide_eq_false (by omega), if_pos (by decide)]
  have hs3 := hM3.1
  have h13 : rd s3.M cOne = 1 := hM3.2 0 (by decide)
  simp only [regs] at hs3
  have k1 : rd (semXIR I (.blk [.op .add rEo rEo cOne]) s3).M rEo = toWord (1 + qw + (m + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rEo]; omega), hr3 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE, h13,
      add_one_toWord, Nat.add_assoc]
  have g1 : ∀ i, i ≠ rEo → rd (semXIR I (.blk [.op .add rEo rEo cOne]) s3).M i = rd s3.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM4 := inv_sem I (P := .blk [.op .add rEo rEo cOne]) (by simp +decide only [WF, Prim.dst,
    rEo]) hM3
  have hh4 := hframe I (.blk [.op .add rEo rEo cOne]) s3 (by simp +decide only [Lo, Prim.dst, regs,
    rEo])
  have z4 := size_sem I (.blk [.op .add rEo rEo cOne]) s3
  generalize semXIR I (.blk [.op .add rEo rEo cOne]) s3 = s4 at k1 g1 hM4 hh4 z4
  have w4 : rd s4.M rWp = toWord pos := by
    rw [g1 _ (by decide), hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM5⟩ := inc_sem I s4 hM4 w4
  have keep : ∀ r, r < regs → r ≠ rWd → r ≠ rKd → r ≠ rZ → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 →
      r ≠ rS1 → r ≠ rS2 → r ≠ rS3 → r ≠ rEo → r ≠ rWp →
      rd (semXIR I (.blk incPs) s4).M r = rd s.M r := fun r hr a b c d e f g k l n o => by
    rw [i2 r o, g1 r n, hr3 r hr a b c d e f g k l]
  have hl4 : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) →
      rd (semXIR I (.blk incPs) s4).M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s4).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh4 y hy, hh3 y hy]
  refine ⟨⟨hl4, hH⟩, h.frame hM5 (by rw [size_sem, z4, z3]) hl4 hH, i1,
    by rw [i2 _ (by decide), k1], ?_, ?_, fun i hi => ?_⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hQ]
  · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [i2 _ (by simp only [rS0, rWp]; omega), g1 _ (by simp only [rS0, rEo]; omega), hS3 i hi]


/-- `eo := 0` then the next word. -/
theorem word_tail (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos) :
    rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M rEo = 0 ∧
    (∀ i, i ≠ rWp → i ≠ rEo → rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M i =
      rd s.M i) ∧
    Inv (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M ∧
    (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have hM1 := inv_sem I (P := .blk [.const rEo 0]) (by simp +decide only [WF, Prim.dst, rEo]) hM
  have e1 : rd (semXIR I (.blk [.const rEo 0]) s).M rEo = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rEo]; omega)
  have g1 : ∀ i, i ≠ rEo → rd (semXIR I (.blk [.const rEo 0]) s).M i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z1 := size_sem I (.blk [.const rEo 0]) s
  generalize semXIR I (.blk [.const rEo 0]) s = s1 at hM1 e1 g1 z1
  obtain ⟨i1, i2, hM2⟩ := inc_sem I s1 hM1 (by rw [g1 _ (by decide), hW])
  exact ⟨i1, by rw [i2 _ (by decide), e1], fun i a b => by rw [i2 i a, g1 i b], hM2,
    by rw [size_sem, z1]⟩

/-- **The last answer word**: after it, `eo = 0`, and the scan state advances iff `p < N` and the
flag is set (the record), with the answer `a` whose words are the four answer words. -/
theorem word_last {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) (hTab : TabOK I T N M₀) (hN : N < 2 ^ 11) {pos qw : ℕ}
    {b : Bool} (hW : rd s.M rWp = toWord pos) (hpos : pos < 2 ^ 64) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + 3)) (hQ : rd s.M rQw = toWord qw)
    (hT : rd s.M rMt = bW b) (a : Digest)
    (hA : ∀ i < 4, (if i = 3 then I.getD pos 0 else rd s.M (rS0 + i)) =
      (packBytes a.toList).getD i 0) :
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = 0 ∧
    Stat I T N M₀ (if x.1 < N ∧ b = true then (x.1 + 1, a, x.2.2 ++ [a]) else x)
      (semXIR I (wordIR N) s) := by
  obtain ⟨s3, hM3, z3, hh3, hS3, hZ3, hr3, e⟩ := word_ans_path h hW hpos (m := 3) (by omega) hqw hE hQ
  rw [e, semXIR_ite, hZ3, decide_eq_true rfl, if_neg (by decide)]
  have hp : x.1 ≤ N := h.pN
  have hP3 : rd s3.M rPi = toWord x.1 := by
    rw [hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.pi]
  have hT3 : rd s3.M rMt = bW b := by
    rw [hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hT]
  obtain ⟨s₁, hM₁, z₁, f₁, e₁⟩ := lastIR_sem I s3 hM3 (N := N) (p := x.1) (b := b) (by omega)
    (by omega) hP3 hT3
  rw [e₁]
  have w₁ : ∀ r, r ≠ rKd → r ≠ rZ → r < regs → r ≠ rWd → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 → r ≠ rS1 →
      r ≠ rS2 → r ≠ rS3 → rd s₁.M r = rd s.M r := fun r a b c d e f g k l m => by
    rw [f₁ r a b, hr3 r c d a b e f g k l m]
  have hh₁ : ∀ y, regs ≤ y → rd s₁.M y = rd s.M y := fun y hy => by
    rw [f₁ y (by simp only [rKd, regs] at hy ⊢; omega) (by simp only [rZ, regs] at hy ⊢; omega),
      hh3 y hy]
  have hS₁ : ∀ i < 4, rd s₁.M (rS0 + i) = (packBytes a.toList).getD i 0 := fun i hi => by
    rw [f₁ _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rZ]; omega), hS3 i hi, ← hA i hi]
  by_cases hc : x.1 < N ∧ b = true
  · rw [if_pos hc, if_pos hc]
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := recIR_sem I s₁ hM₁ (p := x.1) (by omega)
      (by rw [w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), h.pi]) (by rw [z₁, z3]; exact h.size)
    have z6 := size_sem I recIR s₁
    generalize semXIR I recIR s₁ = s6 at n1 n2 n3 n4 n5 n6 n7 z6
    have w6 : rd s6.M rWp = toWord pos := by
      rw [n6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hW]
    obtain ⟨t1, t2, t3, t4, t5⟩ := word_tail I s6 n7 w6
    generalize semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s6) = s8 at t1 t2 t3 t4 t5
    -- the table entry `p + 1` is `M₀`'s
    have hM0 : ∀ k < 2, rd s₁.M (chB + 4 * (x.1 + 1) + k) = rd M₀ (chB + 4 * (x.1 + 1) + k) :=
      fun k hk => by
        rw [hh₁ _ (by simp only [chB_eq, regs]; omega), h.heap _ (by simp only [chB_eq, regs]; omega)
          (.inl (by simp only [chB_eq, hB_eq]; omega)) (.inl (by simp only [chB_eq, ansB_eq]; omega))]
    obtain ⟨hto, htg⟩ := hTab (x.1 + 1) (by omega) (by omega)
    have r8 : ∀ r, r ≠ rWp → r ≠ rEo → rd s8.M r = rd s6.M r := t3
    refine ⟨t1, t2, ?_⟩
    have tl8 : rd s8.M rTl = rd M₀ (chB + 4 * (x.1 + 1)) := by
      rw [r8 _ (by decide) (by decide), n2]; exact hM0 0 (by norm_num)
    have to8 : rd s8.M rTo = rd M₀ (chB + 4 * (x.1 + 1) + 1) := by
      rw [r8 _ (by decide) (by decide), n3, hM0 1 (by norm_num)]
    have th8 : rd s8.M rTh = 4 := by rw [r8 _ (by decide) (by decide), n4]
    have heap8 : ∀ y, regs ≤ y → rd s8.M y =
        if ansB + 4 * x.1 ≤ y ∧ y < ansB + 4 * x.1 + 4 then (packBytes a.toList).getD
          (y - (ansB + 4 * x.1)) 0
        else if hB ≤ y ∧ y < hB + 4 then (packBytes a.toList).getD (y - hB) 0
        else rd s.M y := fun y hy => by
      rw [r8 y (by simp only [rWp, regs] at hy ⊢; omega) (by simp only [rEo, regs] at hy ⊢; omega),
        n5 y hy]
      split_ifs with q1 q2
      · exact hS₁ _ (by omega)
      · exact hS₁ _ (by omega)
      · exact hh₁ y hy
    exact {
      inv := t4
      size := by rw [t5, z6, z₁, z3]; exact h.size
      pi := by rw [r8 _ (by decide) (by decide), n1]
      pN := by simp only; omega
      len := by simp [h.len]
      th := by rw [th8]; decide
      tof := by rw [to8]; exact hto
      tg := fun hlt => by
        obtain ⟨g1, g2, g3⟩ := htg hlt a
        refine ⟨by rw [tl8, g1], g2, fun j hj => ?_⟩
        rw [g3 j hj, th8, to8, show (4 : Word).toNat = 4 from rfl, exW]
        by_cases hj4 : j < 4
        · rw [if_pos hj4, if_pos hj4, heap8 (hB + j) (by simp only [hB_eq, regs]; omega),
            if_neg (show ¬ (ansB + 4 * x.1 ≤ hB + j ∧ hB + j < ansB + 4 * x.1 + 4) by
              simp only [hB_eq, ansB_eq]; omega),
            if_pos (show hB ≤ hB + j ∧ hB + j < hB + 4 by omega), show hB + j - hB = j by omega]
        · rw [if_neg hj4, if_neg hj4, show (rd M₀ (chB + 4 * (x.1 + 1) + 1)).toNat + j - 4 =
            (rd M₀ (chB + 4 * (x.1 + 1) + 1)).toNat + (j - 4) by omega]
      ans := fun q hq m hm => by
        simp only at hq ⊢
        rw [heap8 (ansB + 4 * q + m) (by simp only [ansB_eq, regs]; omega)]
        by_cases hqx : q = x.1
        · subst hqx
          rw [if_pos (by omega), show ansB + 4 * x.1 + m - (ansB + 4 * x.1) = m by omega,
            List.getD_append_right _ _ _ _ (by rw [h.len]), h.len, Nat.sub_self]
          rfl
        · rw [if_neg (by omega), if_neg (by simp only [ansB_eq, hB_eq]; omega),
            List.getD_append _ _ _ _ (by rw [h.len]; omega)]
          exact h.ans q (by omega) m hm
      heap := fun y hy h1 h2 => by
        rw [heap8 y hy, if_neg (by simp only [ansB_eq, chEnd] at h2 ⊢; omega),
          if_neg (by simp only [hB_eq] at h1 ⊢; omega)]
        exact h.heap y hy h1 h2 }
  · rw [if_neg hc, if_neg hc]
    have w₁' : rd s₁.M rWp = toWord pos := by
      rw [w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hW]
    obtain ⟨t1, t2, t3, t4, t5⟩ := word_tail I s₁ hM₁ w₁'
    refine ⟨t1, t2, h.frame t4 (by rw [t5, z₁, z3]) (fun r hr => ?_) (fun y hy => ?_)⟩
    · rcases hr with rfl | rfl | rfl | rfl <;>
        rw [t3 _ (by decide) (by decide), w₁ _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [t3 y (by simp only [rWp, regs] at hy ⊢; omega) (by simp only [rEo, regs] at hy ⊢; omega),
        hh₁ y hy]


/-! ## One entry -/

theorem iterL_add (f : St → St) (c : ℕ) : ∀ (a b : ℕ) (s : St),
    iterL f c (a + b) s = iterL f c b (iterL f c a s)
  | 0, b, s => by simp [iterL]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iterL]
    exact iterL_add f c a b _

theorem iterL_one (f : St → St) (c : ℕ) (s : St) : iterL f c 1 s = decS c (f s) := rfl

theorem Keep.trans {s₀ s s' : St} (h : Keep s₀ s) (h' : Keep s s') : Keep s₀ s' :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), fun y hy => (h'.2 y hy).trans (h.2 y hy)⟩

theorem Keep.refl (s : St) : Keep s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem keep_decS (s : St) : Keep s (decS rCC s) :=
  ⟨fun r hr => rd_decS (by rcases hr with rfl | rfl | rfl | rfl <;> decide) s,
    fun y hy => rd_decS (by simp only [rCC, regs] at hy ⊢; omega) s⟩

theorem Stat.decS {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) : Stat I T N M₀ x (Lvm.X.decS rCC s) :=
  h.frame (inv_of_frame h.inv (size_decS ..) fun i hi => rd_decS (by
    simp only [rCC]; omega) _) (size_decS ..) (keep_decS s).1 (keep_decS s).2

/-- **The tape holds entry `e` at `pos`**: `|q|`, its packed words, its answer's 4 words. -/
structure EntryAt (I : Array Word) (pos : ℕ) (e : ByteArray × Digest) : Prop where
  len : I.getD pos 0 = toWord e.1.size
  lt : e.1.size < 2 ^ 64
  qry : ∀ j < (e.1.size + 7) / 8, I.getD (pos + 1 + j) 0 = (packBytes e.1.data.toList).getD j 0
  ans : ∀ m < 4, I.getD (pos + 1 + (e.1.size + 7) / 8 + m) 0 = (packBytes e.2.toList).getD m 0
  fit : pos + qWords e ≤ 2 ^ 64

/-- **Byte strings of one length with the same packed words are equal.** -/
theorem eq_of_packBytes {q Q : ByteArray} (hs : q.size = Q.size)
    (hw : ∀ j < (q.size + 7) / 8, (packBytes q.data.toList).getD j 0 =
      (packBytes Q.data.toList).getD j 0) : q = Q := by
  have hl : q.data.toList = Q.data.toList := by
    refine List.ext_getElem (by simp only [Array.length_toList]; exact hs) fun i h1 h2 => ?_
    have hi : i < q.size := by simpa using h1
    have e1 := wordByte_packBytes q.data.toList i
    have e2 := wordByte_packBytes Q.data.toList i
    rw [List.getD_eq_getElem _ _ h1] at e1
    rw [List.getD_eq_getElem _ _ h2] at e2
    rw [← e1, ← e2]
    unfold wordByte
    rw [hw (i / 8) (by omega)]
  obtain ⟨d⟩ := q
  obtain ⟨D⟩ := Q
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.mp hl

/-- The query phase: from word `j` to word `qw`, the flag is the conjunction so far. -/
theorem qry_loop {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    (s₀ : St) (A : Prop) [Decidable A] {pos qw : ℕ} (hqw : qw < 2 ^ 62)
    (hpos : pos + 1 + qw < 2 ^ 64) :
    ∀ k j (s : St), j + k = qw → Stat I T N M₀ x s → Keep s₀ s →
      rd s.M rWp = toWord (pos + 1 + j) → rd s.M rEo = toWord (1 + j) →
      rd s.M rQw = toWord qw →
      rd s.M rMt = bW (decide (A ∧ ∀ j' < j, I.getD (pos + 1 + j') 0 =
        exW I s₀.M (rd s₀.M rTh).toNat (rd s₀.M rTo).toNat j')) →
      Stat I T N M₀ x (iterL (semXIR I (wordIR N)) rCC k s) ∧
      Keep s₀ (iterL (semXIR I (wordIR N)) rCC k s) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rWp = toWord (pos + 1 + qw) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rEo = toWord (1 + qw) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rQw = toWord qw ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rMt = bW (decide (A ∧ ∀ j' < qw,
        I.getD (pos + 1 + j') 0 = exW I s₀.M (rd s₀.M rTh).toNat (rd s₀.M rTo).toNat j'))
  | 0, j, s, hj, h, hk, hW, hE, hQ, hT => by
    simp only [iterL]
    obtain rfl : j = qw := by omega
    exact ⟨h, hk, hW, hE, hQ, hT⟩
  | k + 1, j, s, hj, h, hk, hW, hE, hQ, hT => by
    obtain ⟨K, h1, w1, e1, q1, t1⟩ := word_qry (N := N) h hW (by omega) (j := j) (qw := qw)
      (by omega) hqw (by rw [hE, Nat.add_comm]) hQ hT
    have hK : Keep s₀ (Lvm.X.decS rCC (semXIR I (wordIR N) s)) :=
      (hk.trans K).trans (keep_decS _)
    simp only [iterL]
    refine qry_loop s₀ A hqw hpos k (j + 1) _ (by omega) h1.decS hK ?_ ?_ ?_ ?_
    · rw [rd_decS (by decide), w1, Nat.add_assoc]
    · rw [rd_decS (by decide), e1, Nat.add_comm 1 (j + 1)]
    · rw [rd_decS (by decide), q1]
    · rw [rd_decS (by decide), t1, hk.1 _ (.inr (.inr (.inl rfl))), hk.1 _ (.inr (.inr (.inr rfl))),
        exW_congr hk.2]
      refine congrArg bW ?_
      rw [← Bool.decide_and, decide_eq_decide]
      constructor
      · rintro ⟨⟨hA, hall⟩, hj'⟩
        refine ⟨hA, fun j' h => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
        · exact hall j' h
        · exact hj'
      · rintro ⟨hA, hall⟩
        exact ⟨⟨hA, fun j' h => hall j' (by omega)⟩, hall j (by omega)⟩


theorem ceil8_toWord {a : ℕ} (h : a < 2 ^ 64) : ceil8 (toWord a) = toWord ((a + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ceil8 h, toNat_toWord (by omega)]

/-- **One entry**: its `qWords e` words do `scanStep` on the scan state. -/
theorem entry_sem {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) (hTab : TabOK I T N M₀) (hN : N < 2 ^ 11) {pos : ℕ}
    {e : ByteArray × Digest} (hW : rd s.M rWp = toWord pos) (hE : rd s.M rEo = 0)
    (he : EntryAt I pos e) :
    Stat I T N M₀ (scanStep T N x e) (iterL (semXIR I (wordIR N)) rCC (qWords e) s) ∧
    rd (iterL (semXIR I (wordIR N)) rCC (qWords e) s).M rWp = toWord (pos + qWords e) ∧
    rd (iterL (semXIR I (wordIR N)) rCC (qWords e) s).M rEo = 0 := by
  have hfit := he.fit
  simp only [qWords] at hfit ⊢
  generalize hqw : (e.1.size + 7) / 8 = qw at hfit he
  have hqw62 : qw < 2 ^ 62 := by have := he.lt; omega
  have hp6 : pos + 1 + qw + 1 + 1 + 1 < 2 ^ 64 := by omega
  rw [show 5 + qw = 1 + qw + 1 + 1 + 1 + 1 by omega, iterL_add, iterL_add, iterL_add, iterL_add,
    iterL_add, iterL_one, iterL_one, iterL_one, iterL_one, iterL_one]
  -- the length word
  obtain ⟨K1, h1, w1, e1, q1, t1⟩ := word_len (N := N) h hW (by omega) hE
  rw [he.len, ceil8_toWord he.lt, hqw] at q1
  rw [he.len, eq_bW] at t1
  generalize semXIR I (wordIR N) s = s1 at K1 h1 w1 e1 q1 t1
  -- the query words
  obtain ⟨h2, K2, w2, e2, q2, t2⟩ := qry_loop (N := N) s (toWord e.1.size = rd s.M rTl) (pos := pos)
    hqw62 (by omega) qw 0 (Lvm.X.decS rCC s1) (by omega) h1.decS (K1.trans (keep_decS _))
    (by rw [rd_decS (by decide), w1, Nat.add_zero]) (by rw [rd_decS (by decide), e1]; rfl)
    (by rw [rd_decS (by decide), q1]) (by
      rw [rd_decS (by decide), t1]
      exact congrArg bW (decide_eq_decide.mpr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun h => h.1⟩))
  generalize iterL (semXIR I (wordIR N)) rCC qw (Lvm.X.decS rCC s1) = s2 at h2 K2 w2 e2 q2 t2
  -- the flag means `q = T p st`
  set b := decide (toWord e.1.size = rd s.M rTl ∧ ∀ j' < qw, I.getD (pos + 1 + j') 0 =
    exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j') with hb
  have hbT : x.1 < N → (b = true ↔ e.1 = T x.1 x.2.1) := fun hx => by
    obtain ⟨g1, g2, g3⟩ := h.tg hx
    rw [hb, decide_eq_true_iff, g1]
    constructor
    · rintro ⟨hA, hall⟩
      have hs : e.1.size = (T x.1 x.2.1).size := by
        have := congrArg BitVec.toNat hA
        rwa [toNat_toWord he.lt, toNat_toWord g2] at this
      refine eq_of_packBytes hs fun j hj => ?_
      rw [← he.qry j (by omega), hall j (by omega), g3 j (by omega)]
    · intro hq
      refine ⟨by rw [hq], fun j' hj' => ?_⟩
      rw [he.qry j' (by omega), ← g3 j' (by rw [← hq]; omega), hq]
  -- the answer words
  obtain ⟨K3, h3, w3, e3, q3, t3, S3⟩ := word_ans (N := N) h2 w2 (by omega) (m := 0) (by omega)
    hqw62 (by rw [e2, Nat.add_zero]) q2
  generalize semXIR I (wordIR N) s2 = s3 at K3 h3 w3 e3 q3 t3 S3
  obtain ⟨K4, h4, w4, e4, q4, t4, S4⟩ := word_ans (N := N) h3.decS (pos := pos + 1 + qw + 1)
    (by rw [rd_decS (by decide), w3]) (by omega) (m := 1) (by omega) hqw62
    (by rw [rd_decS (by decide), e3]) (by rw [rd_decS (by decide), q3])
  generalize semXIR I (wordIR N) (Lvm.X.decS rCC s3) = s4 at K4 h4 w4 e4 q4 t4 S4
  obtain ⟨K5, h5, w5, e5, q5, t5, S5⟩ := word_ans (N := N) h4.decS (pos := pos + 1 + qw + 1 + 1)
    (by rw [rd_decS (by decide), w4]) (by omega) (m := 2) (by omega) hqw62
    (by rw [rd_decS (by decide), e4]) (by rw [rd_decS (by decide), q4])
  generalize semXIR I (wordIR N) (Lvm.X.decS rCC s4) = s5 at K5 h5 w5 e5 q5 t5 S5
  have hS : ∀ i < 4, (if i = 3 then I.getD (pos + 1 + qw + 1 + 1 + 1) 0
      else rd (Lvm.X.decS rCC s5).M (rS0 + i)) = (packBytes e.2.toList).getD i 0 := fun i hi => by
    have a0 := he.ans
    rw [hqw] at a0
    interval_cases i
    · rw [if_neg (by omega), rd_decS (by decide), S5 0 (by omega), if_neg (by omega),
        rd_decS (by decide), S4 0 (by omega), if_neg (by omega), rd_decS (by decide), S3 0 (by omega),
        if_pos rfl, ← a0 0 (by omega)]
      rfl
    · rw [if_neg (by omega), rd_decS (by decide), S5 1 (by omega), if_neg (by omega),
        rd_decS (by decide), S4 1 (by omega), if_pos rfl, ← a0 1 (by omega)]
    · rw [if_neg (by omega), rd_decS (by decide), S5 2 (by omega), if_pos rfl, ← a0 2 (by omega),
        show pos + 1 + qw + 1 + 1 = pos + 1 + qw + 2 by omega]
    · rw [if_pos rfl, ← a0 3 (by omega), show pos + 1 + qw + 1 + 1 + 1 = pos + 1 + qw + 3 by omega]
  have hT5 : rd (Lvm.X.decS rCC s5).M rMt = bW b := by
    rw [rd_decS (by decide), t5, rd_decS (by decide), t4, rd_decS (by decide), t3, t2]
  obtain ⟨w6, e6, h6⟩ := word_last (N := N) h5.decS hTab hN (pos := pos + 1 + qw + 1 + 1 + 1)
    (qw := qw) (b := b) (by rw [rd_decS (by decide), w5]) hp6 hqw62
    (by rw [rd_decS (by decide), e5]) (by rw [rd_decS (by decide), q5]) hT5 e.2 hS
  have hx : (if x.1 < N ∧ b = true then (x.1 + 1, e.2, x.2.2 ++ [e.2]) else x) =
      scanStep T N x e := by
    unfold scanStep
    by_cases hx : x.1 < N
    · by_cases hq : e.1 = T x.1 x.2.1
      · rw [if_pos ⟨hx, (hbT hx).mpr hq⟩, if_pos ⟨hx, hq⟩]
      · rw [if_neg fun ⟨_, h⟩ => hq ((hbT hx).mp h), if_neg fun ⟨_, h⟩ => hq h]
    · rw [if_neg fun ⟨h, _⟩ => hx h, if_neg fun ⟨h, _⟩ => hx h]
  rw [hx] at h6
  refine ⟨h6.decS, ?_, ?_⟩
  · rw [rd_decS (by decide), w6, show pos + 1 + qw + 1 + 1 + 1 + 1 = pos + (1 + qw + 1 + 1 + 1 + 1) by
      omega]
  · rw [rd_decS (by decide), e6]


/-! ## The log -/

/-- The tape holds the entries `L` from `pos` on, one after the other. -/
def EntriesAt (I : Array Word) : ℕ → Log → Prop
  | _, [] => True
  | pos, e :: L => EntryAt I pos e ∧ EntriesAt I (pos + qWords e) L

/-- The words of the entries `L`. -/
def wordsOf (L : Log) : ℕ := (L.map qWords).sum

/-- **The loop over the log's words** runs the scan over its entries. -/
theorem scan_sem {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem}
    (hTab : TabOK I T N M₀) (hN : N < 2 ^ 11) :
    ∀ (L : Log) (x : SS) (s : St) (pos : ℕ), Stat I T N M₀ x s → rd s.M rWp = toWord pos →
      rd s.M rEo = 0 → EntriesAt I pos L →
      Stat I T N M₀ (L.foldl (scanStep T N) x) (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s) ∧
      rd (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s).M rWp = toWord (pos + wordsOf L) ∧
      rd (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s).M rEo = 0
  | [], x, s, pos, h, hW, hE, _ => by
    simp only [wordsOf, List.map_nil, List.sum_nil, iterL, List.foldl_nil, Nat.add_zero]
    exact ⟨h, hW, hE⟩
  | e :: L, x, s, pos, h, hW, hE, hL => by
    have hw : wordsOf (e :: L) = qWords e + wordsOf L := by simp [wordsOf]
    rw [hw, iterL_add, List.foldl_cons]
    obtain ⟨h1, w1, e1⟩ := entry_sem h hTab hN hW hE hL.1
    obtain ⟨h2, w2, e2⟩ := scan_sem hTab hN L _ _ _ h1 w1 e1 hL.2
    exact ⟨h2, by rw [w2, Nat.add_assoc], e2⟩

/-! ## The tape: query words (FR's `FRXReadDefs`) -/

theorem size_toList (q : ByteArray) : q.data.toList.length = q.size := Array.length_toList

/-- The query words of an entry within the log's words. -/
theorem entries_getD_q : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (j : ℕ),
    j < (L[k].1.size + 7) / 8 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0
  | e :: L, 0, _, j, hj => by
    have hl : (packBytes e.1.data.toList).length = (e.1.size + 7) / 8 := by
      rw [packBytes_length, size_toList]
    simp only [List.getElem_cons_zero] at hj ⊢
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      Nat.zero_add, bytesWords, List.cons_append]
    rw [List.getD_eq_getElem?_getD, Nat.add_comm, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  | e :: L, k + 1, hk, j, hj => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := entries_getD_q L k (by simp at hk; omega) j hj
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; omega), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    omega

/-- **The tape at entry `k`'s query**: word `j < ⌈|q|/8⌉` of `packBytes q`. -/
theorem tape_query4 {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    {k : ℕ} (hk : k < L.length) {j : ℕ} (hj : j < (L[k].1.size + 7) / 8) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k + 1 + j) 0 =
      (packBytes L[k].1.data.toList).getD j 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, show pL + 1 + entryOff L k + 1 + j =
      (pL + 1) + (entryOff L k + 1 + j) by omega, ← hl, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact entries_getD_q L k hk j hj

/-- **The extractor's tape holds the log's entries** from `pL + 1` on (`tape_entry4`,
`tape_query4`, `tape_answer4`). -/
theorem entriesAt_tape {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∀ k, k ≤ L.length → EntriesAt (extractorInput c π L).toArray (pL + 1 + entryOff L k)
      (L.drop k) := by
  intro k hk
  induction h : L.length - k generalizing k with
  | zero =>
    rw [List.drop_eq_nil_of_le (by omega)]; trivial
  | succ n ih =>
    have hkL : k < L.length := by omega
    rw [List.drop_eq_getElem_cons hkL]
    have hend := tape_entries_end4 c π L hs
    have hle : entryOff L (k + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (k + 1)
    rw [entryOff_succ L hkL] at hle
    refine ⟨⟨?_, hq _ (List.getElem_mem hkL), fun j hj => ?_, fun m hm => ?_, ?_⟩, ?_⟩
    · rw [getD_toArray, tape_entry4 c π L hs hkL]
    · rw [getD_toArray]; exact tape_query4 c π L hs hkL hj
    · rw [getD_toArray]; exact tape_answer4 c π L hs hkL hm
    · omega
    · have := ih (k + 1) (by omega) (by omega)
      rwa [entryOff_succ L hkL, ← Nat.add_assoc] at this

end Lvm.X

end LvmXChainLoop

section LvmXChainTop

/-!
# The chain scan on the machine: the whole program

* `cnt_sem`: the store-free walk leaves the log's word count `wordsOf L` in `rCn5`, from every
  state (this is also `Safe`'s count bound).
* `storesIR_sem`: the table's words land at `chB …`.
* **`chainIR_sem`**: on a domain tape of a SNARK proof, given a table `tab` that realises the
  targets (`TabW`) and a seed block `sd` that writes the seed's word into `H[0]` (`SeedOK`), the
  answers left at `ansB + 4q` are the forward scan's (`scanC`).
* `safe_chainIR` (FR's `FRXDec`): the chain's loop bounds on every SNARK tape (the count loop's is
  `|L| ≤ t / 5`, the scan's is the log's word count `≤ t`).
-/

namespace Lvm.X

open RecursionFast

/-! ## The count -/

theorem sub_toWord' {a b : ℕ} (hb : b ≤ a) (ha : a - b < 2 ^ 64) :
    XOp.sub.eval (toWord a) (toWord b) = toWord (a - b) := by
  rw [show a = (a - b) + b by omega, ← add_toWord, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem cntBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : rd s.M rP = toWord p)
    (hp2 : p < 2 ^ 64) :
    rd (semXIR I cntBody s).M rP = toWord (p + 5 + (ceil8 (I.getD p 0)).toNat) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [cntBody, semXIR, ceil8Ps, runPrims, List.foldl, List.cons_append, List.nil_append,
    Prim.run, rP, rQL, rT1, rT2, rKc] at hp ⊢
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne,
    XOp.eval, hp, toNat_toWord hp2]
  change toWord p + ceil8 (I[p]?.getD 0#64) + 5#64 = toWord (p + 5 + (ceil8 (I[p]?.getD 0#64)).toNat)
  generalize ceil8 (I[p]?.getD 0#64) = C
  have := C.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem wf_cntBody : WF cntBody := by
  simp +decide only [cntBody, ceil8Ps, WF, Prim.dst, rP, rQL, rT1, rT2, rKc, and_true,
    List.cons_append, List.nil_append]

theorem cntLoop (I : Array Word) (n : ℕ) (pos : ℕ → ℕ)
    (hpos : ∀ j < n, pos j < 2 ^ 64 ∧ pos (j + 1) = pos j + 5 + (ceil8 (I.getD (pos j) 0)).toNat) :
    ∀ (m j : ℕ) (s : St), j + m = n → Inv s.M → rd s.M rP = toWord (pos j) →
      rd (iterL (semXIR I cntBody) rCW m s).M rP = toWord (pos n)
  | 0, j, s, hj, _, hp => by simp only [iterL]; rw [hp, show j = n by omega]
  | m + 1, j, s, hj, hM, hp => by
    simp only [iterL]
    have hM' : Inv (decS rCW (semXIR I cntBody s)).M := inv_of_frame
      (inv_sem I wf_cntBody hM) (size_decS ..) fun i hi => rd_decS (by simp only [rCW]; omega) _
    refine cntLoop I n pos hpos m (j + 1) _ (by omega) hM' ?_
    rw [rd_decS (by decide), cntBody_sem I s hM hp (hpos j (by omega)).1, (hpos j (by omega)).2]

/-- **The count**: from every state, on a domain tape of a SNARK proof, `(cntIR pL)` leaves the log's
word count in `rCn5`. -/
theorem cnt_sem {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) :
    rd (semXIR (extractorInput c π L).toArray (cntIR pL) s).M rCn5 = toWord (wordsOf L) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have hcnt : (I.getD pL 0).toNat = L.length := by
    rw [hI, getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by
      have := length_logEntries L
      have h5 : 5 * L.length ≤ entryOff L L.length := by
        rwa [entries_length, ← entryOff_length] at this
      omega)]
  have hpos : ∀ j < L.length, pL + 1 + entryOff L j < 2 ^ 64 ∧
      pL + 1 + entryOff L (j + 1) = pL + 1 + entryOff L j + 5 +
        (ceil8 (I.getD (pL + 1 + entryOff L j) 0)).toNat := fun j hj => by
    have hq' := hq _ (List.getElem_mem hj)
    have hend' : entryOff L (j + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hend' ⊢
    rw [hI, getD_toArray, tape_entry4 c π L hs hj, toNat_ceil8 hq']
    simp only [qWords] at hend' ⊢
    omega
  have w0 : WF (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [readAt, WF, Prim.dst, rP, rN, rA, and_true]
  have hM1 := inv_sem I w0 hM
  have hs1 := hM1.1
  simp only [regs] at hs1
  have hn1 : rd (semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s).M rN =
      I.getD pL 0 :=
    rd_seq_readAt I _ s (by simp +decide [WF, Prim.dst, rP]) hM (by decide)
      (by omega)
  have hp1 : rd (semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s).M rP =
      toWord (pL + 1) := by
    have := hM.1; simp only [regs] at this
    simp only [readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
  rw [cntIR, semXIR_seq, semXIR_seq]
  generalize semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s = s1
    at hM1 hs1 hn1 hp1
  have hc : rCW < s1.M.size := by simp only [rCW]; omega
  have e : semXIR I (.loopT rCW rN ⟨0, 1, 5⟩ cntBody) s1 = iterL (semXIR I cntBody) rCW L.length
      ⟨entryT rCW rN s1.M, s1.o⟩ := by
    simp only [semXIR, rd_entryT hc, hn1, hcnt]
  rw [e]
  have hE : Inv (entryT rCW rN s1.M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have hEp : rd (entryT rCW rN s1.M) rP = toWord (pL + 1 + entryOff L 0) := by
    rw [entryT_frame _ (by decide), hp1]; rfl
  have hP := cntLoop I L.length (fun j => pL + 1 + entryOff L j) hpos L.length 0
    ⟨entryT rCW rN s1.M, s1.o⟩ (by omega) hE hEp
  have hM2 := iterL_inv (f := semXIR I cntBody) (c := rCW) (by decide)
    (fun s h => inv_sem I wf_cntBody h) L.length ⟨entryT rCW rN s1.M, s1.o⟩ hE
  generalize iterL (semXIR I cntBody) rCW L.length ⟨entryT rCW rN s1.M, s1.o⟩ = s2 at hP hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [size_set, rCn5]; omega), rd_set_self (by simp only [rKd]; omega),
    rd_set_ne (by decide), hP, sub_toWord' (by omega) (by omega),
    show pL + 1 + entryOff L L.length - (pL + 1) = wordsOf L by
      rw [entryOff_length]; simp only [wordsOf]; omega]

/-- `(cntIR pL)` leaves the heap alone. -/
theorem cnt_heap (pL : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) {y : ℕ} (hy : regs ≤ y) :
    rd (semXIR I (cntIR pL) s).M y = rd s.M y := by
  have lo1 : Lo (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [Lo, readAt, Prim.dst, regs, rP, rN, rA, and_true]
  have lob : Lo cntBody := by simp +decide [Lo, cntBody, ceil8Ps, Prim.dst, regs, rP, rQL, rT1,
    rT2, rKc, and_true, List.cons_append, List.nil_append]
  have w1 : WF (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [readAt, WF, Prim.dst, rP, rN, rA, and_true]
  rw [cntIR, semXIR_seq, semXIR_seq]
  have hM1 := inv_sem I w1 hM
  have h1 := hframe I _ s lo1 y hy
  generalize semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s = s1 at hM1 h1
  simp only [regs] at hy
  have hE : Inv (entryT rCW rN s1.M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have h2 := iterL_frame (f := semXIR I cntBody) (c := rCW) (i := y) (by decide)
    (by simp only [rCW]; omega) (fun s h => inv_sem I wf_cntBody h)
    (fun s _ => hframe I cntBody s lob y (by simp only [regs]; omega))
    (rd (entryT rCW rN s1.M) rCW).toNat ⟨entryT rCW rN s1.M, s1.o⟩ hE
  simp only [semXIR] at h2 ⊢
  rw [rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl) <;> simp only [Prim.dst, rKd, rCn5] <;> omega) _, h2,
    entryT_frame _ (by simp only [rCW]; omega), h1]

theorem cnt_regs (pL : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (hw : r ≠ rP ∧ r ≠ rN ∧ r ≠ rA ∧ r ≠ rCW ∧ r ≠ rQL ∧ r ≠ rT1 ∧ r ≠ rT2 ∧ r ≠ rKc ∧ r ≠ rKd ∧
      r ≠ rCn5) : rd (semXIR I (cntIR pL) s).M r = rd s.M r := by
  obtain ⟨a, b, c, d, e, f, g, k, l, m⟩ := hw
  refine frame I (cntIR pL) s (wf_cntIR pL) hM r hr ?_
  simp +decide [cntIR, cntBody, readAt, ceil8Ps, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]
  simp only [rP, rN, rA, rCW, rQL, rT1, rT2, rKc, rKd, rCn5] at *
  lia

/-! ## The table -/

theorem storesIR_sem (I : Array Word) : ∀ (ws : List Word) (b : ℕ) (s : St), Inv s.M →
    regs ≤ b → b + ws.length ≤ s.M.size → b + ws.length < 2 ^ 64 →
    (∀ i < ws.length, rd (semXIR I (storesIR b ws) s).M (b + i) = ws.getD i 0) ∧
    (∀ y, y ≠ cTmp → y ≠ rAd4 → y ≠ rKd → (y < b ∨ b + ws.length ≤ y) →
      rd (semXIR I (storesIR b ws) s).M y = rd s.M y) ∧
    Inv (semXIR I (storesIR b ws) s).M ∧ (semXIR I (storesIR b ws) s).M.size = s.M.size
  | [], b, s, hM, _, _, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, hM,
      rfl⟩
  | w :: ws, b, s, hM, hb, hbs, hb2 => by
    have hs := hM.1
    simp only [regs] at hs hb
    simp only [List.length_cons] at hbs hb2
    have hM1 := inv_sem I (P := .blk [.const rAd4 (toWord b), .const rKd w])
      (by simp +decide only [WF, Prim.dst, rAd4, rKd, List.mem_cons, List.mem_nil_iff,
        forall_eq_or_imp, forall_eq, or_false, and_true]) hM
    have a1 : rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M rAd4 = toWord b := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by decide), rd_set_self (by simp only [rAd4]; omega)]
    have k1 : rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M rKd = w := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [size_set, rKd]; omega)]
    have f1 : ∀ y, y ≠ rAd4 → y ≠ rKd →
        rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M y = rd s.M y :=
      fun y a b => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
    have z1 := size_sem I (.blk [.const rAd4 (toWord b), .const rKd w]) s
    rw [storesIR, semXIR_seq, semXIR_seq]
    generalize semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s = s1 at hM1 a1 k1 f1 z1
    have e2 : semXIR I (.store rAd4 rKd) s1 = ⟨storeM s1.M rAd4 rKd, s1.o⟩ := rfl
    rw [e2]
    have st : ∀ i, i ≠ cTmp → rd (storeM s1.M rAd4 rKd) i = if i = b then w else rd s1.M i :=
      fun i hi => by
        rw [rd_storeM hM1 a1 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
          (by decide) hi, k1]
    have hM2 := inv_sem I (P := .store rAd4 rKd) (by simp +decide only [WF, rAd4, cTmp]) hM1
    rw [e2] at hM2
    obtain ⟨r1, r2, r3, r4⟩ := storesIR_sem I ws (b + 1) ⟨storeM s1.M rAd4 rKd, s1.o⟩ hM2
      (by simp only [regs]; omega) (by simp only [size_storeM]; omega) (by omega)
    refine ⟨fun i hi => ?_, fun y a c d e => ?_, r3, by rw [r4]; simp only [size_storeM]; omega⟩
    · rcases i with _ | i
      · rw [show b + 0 = b from rfl, r2 b (by simp only [cTmp]; omega) (by simp only [rAd4]; omega)
          (by simp only [rKd]; omega) (.inl (by omega))]
        simp only
        rw [st _ (by simp only [cTmp]; omega), if_pos (by omega)]
        rfl
      · rw [show b + (i + 1) = b + 1 + i by omega, r1 i (by simp at hi; omega)]
        rfl
    · simp only [List.length_cons] at e
      rw [r2 y a c d (by omega)]
      simp only
      rw [st y a, if_neg (by omega), f1 y c d]

/-! ## The whole scan -/

/-- **The table words realise the targets** (the list form of `TabOK`). -/
def TabW (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (tab : List Word) : Prop :=
  tab.length = 4 * (N + 1) ∧ ∀ p, 0 < p → p ≤ N → (tab.getD (4 * p + 1) 0).toNat < 2 ^ 62 ∧
    (p < N → ∀ st : Digest, tab.getD (4 * p) 0 = toWord (T p st).size ∧ (T p st).size < 2 ^ 64 ∧
      ∀ j < ((T p st).size + 7) / 8, (packBytes (T p st).data.toList).getD j 0 =
        if j < 4 then (packBytes st.toList).getD j 0
        else I.getD ((tab.getD (4 * p + 1) 0).toNat + (j - 4)) 0)

/-- **The seed block** writes the seed's packed word (a 7-byte seed is one word) into `H[0]`,
keeps `rCn5` and the heap outside `H`. -/
def SeedOK (sd : XIR) (I : Array Word) (Q : ByteArray) : Prop :=
  WF sd ∧ ¬ Writes sd rCC ∧ ∀ s : St, Inv s.M → chEnd ≤ s.M.size →
    rd (semXIR I sd s).M hB = (packBytes Q.data.toList).getD 0 0 ∧
    rd (semXIR I sd s).M rCn5 = rd s.M rCn5 ∧
    (∀ y, regs ≤ y → (y < hB ∨ hB + 16 ≤ y) → rd (semXIR I sd s).M y = rd s.M y)


theorem startPs_vals (pL : ℕ) (M : Mem) (hs : regs ≤ M.size) :
    rd (runPrims (startPs pL) M) rWp = toWord (pL + 1) ∧ rd (runPrims (startPs pL) M) rEo = 0 ∧
    rd (runPrims (startPs pL) M) rPi = toWord 0 ∧ rd (runPrims (startPs pL) M) rTl = toWord 7 ∧
    rd (runPrims (startPs pL) M) rTh = toWord 1 ∧ rd (runPrims (startPs pL) M) rTo = toWord 0 := by
  simp only [regs] at hs
  simp only [startPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) only [rd_set_self, rd_set_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem startPs_frame (pL : ℕ) (M : Mem) {i : ℕ} (h : i ≠ rWp ∧ i ≠ rEo ∧ i ≠ rPi ∧ i ≠ rTl ∧ i ≠ rTh ∧
    i ≠ rTo ∧ i ≠ rMt) : rd (runPrims (startPs pL) M) i = rd M i := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  apply rd_runPrims_of_not_writes
  simp only [startPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;>
    first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c | exact Ne.symm d |
      exact Ne.symm e | exact Ne.symm f | exact Ne.symm g

/-- **The chain scan, end to end**: on a domain tape of a SNARK proof, with a table that realises
the targets and a seed block that writes the seed's word, the answers at `ansB + 4q` are the
forward scan's; the heap outside `[chB, chEnd)` is kept. -/
theorem chainIR_sem {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    {T : ℕ → Digest → ByteArray} {N : ℕ} (hN : N < 2 ^ 11) {tab : List Word} {sd : XIR}
    {st₀ : Digest} (hT : TabW (extractorInput c π L).toArray T N tab)
    (hsd : SeedOK sd (extractorInput c π L).toArray (T 0 st₀)) (h7 : (T 0 st₀).size = 7)
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (scanC T N st₀ L).1 ≤ N ∧
    (∀ q < (scanC T N st₀ L).1, ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N tab sd) s).M (ansB + 4 * q + m) =
        (packBytes ((scanC T N st₀ L).2.2.getD q default).toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N tab sd) s).M y = rd s.M y) := by
  set I := (extractorInput c π L).toArray with hI
  have hW : wordsOf L < 2 ^ 64 := by
    have := tape_entries_end4 c π L hs
    rw [entryOff_length] at this
    simp only [wordsOf]; omega
  have htl : tab.length = 4 * (N + 1) := hT.1
  -- the count
  have c1 := cnt_sem c π L hs hq ht s hM
  have hh1 : ∀ y, regs ≤ y → rd (semXIR I (cntIR pL) s).M y = rd s.M y := fun y hy => cnt_heap pL I s hM hy
  have hM1 := inv_sem I (wf_cntIR pL) hM
  have z1 := size_sem I (cntIR pL) s
  rw [chainIR, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (cntIR pL) s = s1 at c1 hh1 hM1 z1
  -- the table
  obtain ⟨t1, t2, hM2, z2⟩ := storesIR_sem I tab chB s1 hM1 (by simp only [chB_eq, regs]; omega)
    (by rw [z1, htl]; simp only [chB_eq, chEnd] at hsz ⊢; omega) (by rw [htl, chB_eq]; omega)
  try rw [semXIR_seq]
  generalize semXIR I (storesIR chB tab) s1 = s2 at t1 t2 hM2 z2
  have c2 : rd s2.M rCn5 = toWord (wordsOf L) := by
    rw [t2 _ (by decide) (by decide) (by decide) (.inl (by simp only [rCn5, chB_eq]; omega)), c1]
  -- the seed
  obtain ⟨wsd, -, hsd⟩ := hsd
  obtain ⟨d1, d2, d3⟩ := hsd s2 hM2 (by rw [z2, z1]; exact hsz)
  have hM3 := inv_sem I wsd hM2
  have z3 := size_sem I sd s2
  try rw [semXIR_seq]
  generalize semXIR I sd s2 = s3 at d1 d2 d3 hM3 z3
  -- the start
  have hs3 := hM3.1
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := startPs_vals pL s3.M hs3
  have e4 : semXIR I (.blk (startPs pL)) s3 = ⟨runPrims (startPs pL) s3.M, s3.o⟩ := rfl
  rw [e4]
  have hM4 : Inv (runPrims (startPs pL) s3.M) := inv_runPrims (by
    simp [startPs, Prim.dst, rWp, rEo, rPi, rTl, rTh, rTo, rMt]) hM3
  have hh4 : ∀ y, regs ≤ y → rd (runPrims (startPs pL) s3.M) y = rd s3.M y := fun y hy =>
    startPs_frame pL _ (by simp only [regs] at hy; simp only [rWp, rEo, rPi, rTl, rTh, rTo, rMt]; omega)
  have c4 : rd (runPrims (startPs pL) s3.M) rCn5 = toWord (wordsOf L) := by
    rw [startPs_frame pL _ (by decide), d2, c2]
  generalize hM4' : runPrims (startPs pL) s3.M = M4 at v1 v2 v3 v4 v5 v6 hM4 hh4 c4
  -- the loop
  have hc : rCC < M4.size := by have := hM4.1; simp only [regs] at this; simp only [rCC]; omega
  have e5 : semXIR I (.loopT rCC rCn5 ⟨0, 1, 1⟩ (wordIR N)) ⟨M4, s3.o⟩ =
      iterL (semXIR I (wordIR N)) rCC (wordsOf L) ⟨entryT rCC rCn5 M4, s3.o⟩ := by
    simp only [semXIR, rd_entryT hc, c4, toNat_toWord hW]
  rw [e5]
  have hE : Inv (entryT rCC rCn5 M4) := inv_of_frame hM4 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCC]; omega)
  have ef : ∀ i, i ≠ rCC → rd (entryT rCC rCn5 M4) i = rd M4 i := fun i hi => entryT_frame _
    (Ne.symm hi)
  have zE : (entryT rCC rCn5 M4).size = s.M.size := by
    rw [size_entryT, ← hM4', size_runPrims, z3, z2, z1]
  -- the table and the seed in the loop's heap
  have tabE : ∀ i < tab.length, rd (entryT rCC rCn5 M4) (chB + i) = tab.getD i 0 := fun i hi => by
    rw [ef _ (by simp only [rCC, chB_eq]; omega), hh4 _ (by simp only [chB_eq, regs]; omega),
      d3 _ (by simp only [chB_eq, regs]; omega)
        (.inl (by rw [htl] at hi; simp only [chB_eq, hB_eq] at hi ⊢; omega)), t1 i hi]
  have hst : Stat I T N (entryT rCC rCn5 M4) (0, st₀, []) ⟨entryT rCC rCn5 M4, s3.o⟩ := {
    inv := hE
    size := by rw [zE]; exact hsz
    pi := by rw [ef _ (by decide), v3]
    pN := Nat.zero_le _
    len := rfl
    th := by rw [ef _ (by decide), v5]; decide
    tof := by rw [ef _ (by decide), v6]; decide
    tg := fun _ => by
      refine ⟨by rw [ef _ (by decide), v4, h7], by rw [h7]; norm_num, fun j hj => ?_⟩
      rw [h7] at hj
      obtain rfl : j = 0 := by omega
      rw [ef _ (by decide), v5, ef _ (by decide), v6, exW, toNat_toWord (by norm_num),
        if_pos (by norm_num), Nat.add_zero, ef _ (by simp only [rCC, hB_eq]; omega),
        hh4 _ (by simp only [hB_eq, regs]; omega), d1]
    ans := fun q hq => absurd hq (Nat.not_lt_zero _)
    heap := fun _ _ _ _ => rfl }
  have hTab : TabOK I T N (entryT rCC rCn5 M4) := fun p hp0 hpN => by
    obtain ⟨a1, a2⟩ := hT.2 p hp0 hpN
    have r : ∀ k < 2, rd (entryT rCC rCn5 M4) (chB + 4 * p + k) = tab.getD (4 * p + k) 0 :=
      fun k hk => by rw [Nat.add_assoc, tabE _ (by rw [htl]; omega)]
    refine ⟨by rw [r 1 (by norm_num)]; exact a1, fun hpN' st => ?_⟩
    obtain ⟨b1, b2, b3⟩ := a2 hpN' st
    refine ⟨by rw [show chB + 4 * p = chB + 4 * p + 0 from rfl, r 0 (by norm_num)]; exact b1, b2,
      fun j hj => ?_⟩
    rw [b3 j hj, r 1 (by norm_num)]
  have hent := entriesAt_tape c π L hs hq ht 0 (Nat.zero_le _)
  simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero,
    List.drop_zero] at hent
  obtain ⟨g1, -, -⟩ := scan_sem hTab hN L (0, st₀, []) ⟨entryT rCC rCn5 M4, s3.o⟩ (pL + 1) hst
    (by rw [ef _ (by decide), v1]) (by rw [ef _ (by decide), v2]) hent
  refine ⟨g1.pN, fun q hq m hm => g1.ans q hq m hm, fun y hy hyc => ?_⟩
  have y1 : y < hB ∨ hB + 16 ≤ y := by
    rcases hyc with h | h
    · left; simp only [chB_eq, hB_eq] at h ⊢; omega
    · right; simp only [chEnd, hB_eq] at h ⊢; omega
  have y2 : y < ansB ∨ chEnd ≤ y := by
    rcases hyc with h | h
    · left; simp only [chB_eq, ansB_eq] at h ⊢; omega
    · right; exact h
  have y3 : y < chB ∨ chB + tab.length ≤ y := by
    rw [htl]
    rcases hyc with h | h
    · left; exact h
    · right; simp only [chEnd, chB_eq] at h ⊢; omega
  have hy' := hy
  simp only [regs] at hy'
  rw [g1.heap y hy y1 y2, ef _ (by simp only [rCC]; omega), hh4 y hy, d3 y hy y1,
    t2 y (by simp only [cTmp]; omega) (by simp only [rAd4]; omega) (by simp only [rKd]; omega) y3,
    hh1 y hy]

/-! ## The loop bounds (FR's `FRXDec`) -/

theorem safe_cntIR (pL : ℕ) {I : Array Word} {t : ℕ} (hp : pL < 2 ^ 64)
    (h : (I.getD pL 0).toNat ≤ t / 5) : Safe I t (cntIR pL) := by
  unfold cntIR
  refine .seq (.loopT (safe_of_noLoopT (by simp [readAt, NoLoopT])) (fun s hM => ?_)
    (safe_of_noLoopT (by simp [cntBody, NoLoopT]))) (.blk _)
  rw [rd_seq_readAt I _ s (by simp [WF, Prim.dst, rP]) hM (by simp [rN, regs])
    hp]
  simpa [Aff.eval] using h

theorem wordsOf_le {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) :
    pL + 1 + wordsOf L ≤ (extractorInput c π L).length := by
  have := tape_entries_end4 c π L hs
  rw [entryOff_length] at this
  simpa only [wordsOf] using this

theorem noLoopT_wordIR (N : ℕ) : NoLoopT (wordIR N) := by
  simp [wordIR, lenIR, qryIR, ansIR, lastIR, recIR, recPre, st4IR, nextIR, nextPre, stNext,
    NoLoopT]

/-- **The chain's loop bounds** on every SNARK tape: the walk's count is `|L| ≤ t/5`, the scan's
is the log's word count `≤ t`. -/
theorem safe_chainIR {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (N : ℕ)
    (tab : List Word) {sd : XIR} (hsd : NoLoopT sd) (hwf : WF sd) (hw : ¬ Writes sd rCn5) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (chainIR pL N tab sd) := by
  set I := (extractorInput c π L).toArray
  have hc : Safe I (extractorInput c π L).length (cntIR pL) :=
    safe_cntIR pL (by have := tape_entries_end4 c π L hs; omega) (tape_count_le4 c π L hs ht)
  refine .loopT (.seq hc (.seq (safe_of_noLoopT (noLoopT_storesIR _ _)) (.seq (safe_of_noLoopT hsd)
    (.blk _)))) (fun s hM => ?_) (safe_of_noLoopT (noLoopT_wordIR N))
  rw [semXIR_seq, semXIR_seq, semXIR_seq]
  have hM1 := inv_sem I (wf_cntIR pL) hM
  have c1 := cnt_sem c π L hs hq ht s hM
  generalize semXIR I (cntIR pL) s = s1 at hM1 c1
  have hM2 := inv_sem I (wf_storesIR chB tab) hM1
  have c2 := frame I (storesIR chB tab) s1 (wf_storesIR _ _) hM1 rCn5 (by decide)
    (lo_free_storesIR _ _ _ (by decide) (by decide) (by decide))
  generalize semXIR I (storesIR chB tab) s1 = s2 at hM2 c2
  have c3 := frame I sd s2 hwf hM2 rCn5 (by decide) hw
  have hM3 := inv_sem I hwf hM2
  generalize semXIR I sd s2 = s3 at hM3 c3
  have c4 := frame I (.blk (startPs pL)) s3 (by simp [WF, startPs, Prim.dst, rWp, rEo, rPi, rTl, rTh,
    rTo, rMt]) hM3 rCn5 (by decide) (by simp [Writes, startPs, Prim.dst, rCn5, rWp, rEo, rPi, rTl,
    rTh, rTo, rMt])
  have hw := wordsOf_le c π L hs
  have := tape_entries_end4 c π L hs
  rw [c4, c3, c2, c1, toNat_toWord (by omega)]
  simp only [Aff.eval, Nat.zero_add, Nat.one_mul, Nat.div_one]
  omega

end Lvm.X

end LvmXChainTop
