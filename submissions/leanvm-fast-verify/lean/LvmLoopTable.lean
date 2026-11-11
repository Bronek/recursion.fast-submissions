import LvmLoopIR

/-!
# LoopIR tables: columns, degree-2 constraints, bus messages, fixed-column closed forms

BLUEPRINT §4.4–4.5, compiled per *piece* (`LvmLoopIR.Piece`): `2^a` template rows of one shape
times a block's `2^lsize` loop indices, a table of height `2^(a + lsize)` with no padding row
(WP-0 flag 1: a block's rows of one shape are cut by the binary decomposition of their count).

* **Columns.** A row of a piece has *committed* columns (`Var`): the result value (`res l`, one or
  three limbs) and its finalize count (`fin`), each operand's value (`arg o l`) and read count
  (`cnt o`), and for `readd` the computed read's count (`dcnt`); and *fixed* columns (`Var.fix c`,
  `FCol`): the result address `g^{clock}`, each operand address `g^{exponent}`, `lin`'s `k`, `k'`,
  `fixmul`'s `F`.
* **Constraints** (`Shape.constraints`): one degree-2 polynomial per result limb, as a `Poly2` (a
  list of monomials of at most two variables, fixed columns counting as variables); `readd` has
  none. Characteristic 2: every sign is `+`.
* **Bus.** Each operand is a read: pull `⟨sep τ, addr, cnt, v⟩`, push `⟨sep τ, addr, g·cnt, v⟩`.
  A result *is* its cell: the writing row pushes the cell's seed `⟨sep τ, g^{clock}, 1, c⟩` and
  pulls its finalize `⟨sep τ, g^{clock}, fin, c⟩` (leanVM's seed/finalize, §6.2, with the memory
  value the row's own result column). `readd` pulls `⟨sep τ, α, dcnt, c⟩` and pushes it with
  `g·dcnt`, where `α` is its operand's committed value: the computed address. The inputs' seeds and
  finalizes come from the tables that hold them (stream, digests, bit fields).
* **What the soundness theorem asks of the bus** (`LvmLoopSound.loopir_sound`): every read's key
  `(sep, addr, value)` is the key of a seed (`readMsgs`, `seedMsgs`). That is the conclusion of
  leanVM's lookup argument (`Arithmetization/Soundness/Lookup.lean`, `lookup_sound`) from a
  balanced bus, nonzero read counts and fewer than `2^64 - 1` reads: WP-9 discharges it.
* **Fixed columns** are verifier-known; `Program.fval` defines them row by row, and
  `pieceEval` evaluates their multilinear extensions in `O(2^a · lsize)` products
  (the closed forms proved equal to `mle` in `LvmLoopSound`).
-/

namespace Lvm.Loop

/-! ## Columns and polynomials -/

/-- A column of a piece's row: committed, or fixed (`fix`). -/
inductive Var where
  | res (l : Nat)
  | fin
  | arg (o l : Nat)
  | cnt (o : Nat)
  | dcnt
  | fix (c : FCol)
  deriving DecidableEq, Repr, Inhabited

/-- A monomial: a coefficient times at most two columns. -/
structure Mono where
  /-- The coefficient. -/
  coef : FK
  /-- The columns multiplied, at most two. -/
  vars : List Var
  deriving DecidableEq, Repr

/-- A polynomial of degree at most two in a row's columns. -/
abbrev Poly2 := List Mono

/-- A product of field elements. -/
def prodK : List FK → FK
  | [] => 1
  | a :: as => a * prodK as

/-- The value of a polynomial at a row. -/
def Poly2.ev (P : Poly2) (v : Var → FK) : FK :=
  P.foldr (fun m acc => m.coef * prodK (m.vars.map v) + acc) 0

/-- The one-term polynomial `c·u`. -/
def Poly2.var (u : Var) : Poly2 := [⟨1, [u]⟩]

/-- The constant polynomial. -/
def Poly2.const (c : FK) : Poly2 := [⟨c, []⟩]

/-- The limbs of `y^e` reduced by `y^3 = y + 1` (`e ≤ 4`, the products of two degree-2 elements). -/
def red : Nat → List Nat
  | 0 => [0]
  | 1 => [1]
  | 2 => [2]
  | 3 => [0, 1]
  | 4 => [1, 2]
  | _ => []

/-- The limb pairs `(i, j)` whose product `u_i·w_j` enters limb `l` of `u·w` (`la`, `lb` limbs). -/
def prodTerms (la lb l : Nat) : List (Nat × Nat) :=
  (List.range la).flatMap fun i =>
    (List.range lb).filterMap fun j => if l ∈ red (i + j) then some (i, j) else none

/-- Limb `l` of `u·w` for operand columns `u`, `w`, scaled by `coef`. -/
def prodPoly (u w : Nat → Var) (la lb l : Nat) : Poly2 :=
  (prodTerms la lb l).map fun (i, j) => ⟨1, [u i, w j]⟩

/-- Limb `l` of an operand of `n` limbs (`0` above). -/
def limbPoly (u : Nat → Var) (n l : Nat) : Poly2 := if l < n then Poly2.var (u l) else []

/-- Limb `l` of an operand times a fixed column. -/
def limbFix (c : FCol) (u : Nat → Var) (n l : Nat) : Poly2 :=
  if l < n then [⟨1, [.fix c, u l]⟩] else []

namespace Shape

variable (σ : Shape)

/-- Limbs of operand `o`. -/
def argLimbs (o : Nat) : Nat := (σ.args.getD o .K).limbs

/-- The constraint polynomials of a shape: each must vanish on every row. -/
def constraints : List Poly2 :=
  let res (l : Nat) := Poly2.var (.res l)
  let A (o : Nat) : Nat → Var := Var.arg o
  match σ.kind with
  | .muladd => (List.range σ.ty.limbs).map fun l =>
      res l ++ prodPoly (A 0) (A 1) (σ.argLimbs 0) (σ.argLimbs 1) l ++ limbPoly (A 2) (σ.argLimbs 2) l
  | .lin => (List.range σ.ty.limbs).map fun l =>
      res l ++ limbPoly (A 0) (σ.argLimbs 0) l ++ limbFix .k (A 1) (σ.argLimbs 1) l ++
        (if l = 0 then Poly2.var (.fix .k') else [])
  | .assert0 =>
      (List.range (if σ.argLimbs 0 = 1 ∧ σ.argLimbs 1 = 1 then 1 else 3)).map fun l =>
        prodPoly (A 0) (A 1) (σ.argLimbs 0) (σ.argLimbs 1) l
  | .loadE => (List.range 3).map fun l => res l ++ Poly2.var (.arg l 0)
  | .fixmul => (List.range σ.ty.limbs).map fun l =>
      res l ++ limbFix .F (A 0) (σ.argLimbs 0) l ++ limbPoly (A 1) (σ.argLimbs 1) l
  | .readd => []

/-- The committed columns of a shape, in order (its layout in the commitment). -/
def committed : List Var :=
  (if σ.writes then (List.range σ.ty.limbs).map .res ++ [.fin] else []) ++
    ((List.range σ.args.length).flatMap fun o =>
      (List.range (σ.argLimbs o)).map (.arg o) ++ [.cnt o]) ++
    (if σ.kind = .readd then [.dcnt] else [])

end Shape

/-! ## Bus messages -/

/-- The domain separator of memory `τ`'s lookup array (`g^3`, `g^4`; leanVM uses `g^0 … g^2`). -/
def sep : Ty → FK
  | .K => FK.x ^ 3
  | .E => FK.x ^ 4

/-- A bus message `⟨sep, addr, cnt, value limbs⟩`. -/
structure Msg where
  /-- The domain separator. -/
  sep : FK
  /-- The address. -/
  addr : FK
  /-- The count. -/
  cnt : FK
  /-- The value, one coordinate per limb. -/
  val : List FK
  deriving DecidableEq, Repr

/-- What the lookup argument matches: everything but the count. -/
def Msg.key (m : Msg) : FK × FK × List FK := (m.sep, m.addr, m.val)

/-- The limbs of an `E` value of memory `τ`. -/
def limbsOf : Ty → FE → List FK
  | .K, v => [v.c₀]
  | .E, v => [v.c₀, v.c₁, v.c₂]

/-- The value of `n` limbs read from columns `u` (`K`: the constant coefficient). -/
def valOf (τ : Ty) (u : Nat → FK) : FE :=
  match τ with
  | .K => FE.ofK (u 0)
  | .E => ⟨u 0, u 1, u 2⟩

/-- A flush, symbolically: side (`true` = push), separator, then address, count and value
coordinates as polynomials in the row's columns. -/
structure Flush where
  /-- `true` for a push, `false` for a pull. -/
  push : Bool
  /-- The domain separator. -/
  sep : FK
  /-- The address coordinate. -/
  addr : Poly2
  /-- The count coordinate. -/
  cnt : Poly2
  /-- The value coordinates. -/
  val : List Poly2

/-- The message a flush sends at a row. -/
def Flush.msg (f : Flush) (v : Var → FK) : Msg :=
  ⟨f.sep, f.addr.ev v, f.cnt.ev v, f.val.map (·.ev v)⟩

namespace Shape

variable (σ : Shape)

/-- The value coordinates of operand `o`. -/
def argVals (o : Nat) : List Poly2 := (List.range (σ.argLimbs o)).map fun l => Poly2.var (.arg o l)

/-- The value coordinates of the result. -/
def resVals : List Poly2 := (List.range σ.ty.limbs).map fun l => Poly2.var (.res l)

/-- The pull of each read: every operand, and `readd`'s computed read. -/
def readFlushes : List Flush :=
  ((List.range σ.args.length).map fun o =>
    ⟨false, sep (σ.args.getD o .K), Poly2.var (.fix (.arg o)), Poly2.var (.cnt o), σ.argVals o⟩) ++
  (if σ.kind = .readd then [⟨false, sep σ.ty, Poly2.var (.arg 0 0), Poly2.var .dcnt, σ.resVals⟩]
    else [])

/-- A read pushed back: its count multiplied by `g`. -/
def bumpFlush (f : Flush) : Flush := { f with push := true, cnt := f.cnt.map fun m => { m with coef := FK.x * m.coef } }

/-- The result's seed (push, count `1`). -/
def seedFlush : Flush := ⟨true, sep σ.ty, Poly2.var (.fix .res), Poly2.const 1, σ.resVals⟩

/-- The result's finalize (pull, count `fin`). -/
def finFlush : Flush := ⟨false, sep σ.ty, Poly2.var (.fix .res), Poly2.var .fin, σ.resVals⟩

/-- Every flush of a row of the shape: the reads, their bumped pushes, and for a writer the seed and
the finalize. -/
def flushes : List Flush :=
  σ.readFlushes ++ σ.readFlushes.map bumpFlush ++ (if σ.writes then [σ.seedFlush, σ.finFlush] else [])

end Shape

/-! ## A witness and its messages -/

/-- The committed part of every piece: piece index (in `Program.pieces`), row, column. -/
abbrev Witness := Nat → Nat → Var → FK

namespace Program

variable (Q : Program)

/-- Every column of row `x` of piece number `n`. -/
def rowVal (W : Witness) (n : Nat) (p : Piece) (x : Nat) : Var → FK
  | .fix c => Q.fval p c x
  | u => W n x u

/-- The pieces with their indices. -/
def ipieces : List (Nat × Piece) := Q.pieces.zipIdx.map fun (p, n) => (n, p)

/-- The rows of every piece, with the piece index. -/
def prows : List (Nat × Piece × Nat) :=
  Q.ipieces.flatMap fun (n, p) => (List.range (2 ^ Q.height p)).map fun x => (n, p, x)

/-- Every read the pieces make (their pull messages). -/
def readMsgs (W : Witness) : List Msg :=
  Q.prows.flatMap fun (n, p, x) => p.shape.readFlushes.map fun f => f.msg (Q.rowVal W n p x)

/-- The seeds of the inputs. -/
def inputSeeds (inK : Array FK) (inE : Array FE) : List Msg :=
  (List.range Q.nInK).map (fun e => ⟨sep .K, FK.x ^ e, 1, [inK.getD e 0]⟩) ++
    (List.range Q.nInE).map fun e => ⟨sep .E, FK.x ^ e, 1, limbsOf .E (inE.getD e 0)⟩

/-- Every seed: the inputs', then every result's. -/
def seedMsgs (W : Witness) (inK : Array FK) (inE : Array FE) : List Msg :=
  Q.inputSeeds inK inE ++
    Q.prows.flatMap fun (n, p, x) =>
      if p.shape.writes then [p.shape.seedFlush.msg (Q.rowVal W n p x)] else []

/-- Every constraint of every piece vanishes on every row. -/
def ConstraintsHold (W : Witness) : Prop :=
  ∀ npx ∈ Q.prows, ∀ C ∈ npx.2.1.shape.constraints, C.ev (Q.rowVal W npx.1 npx.2.1 npx.2.2) = 0

end Program

/-! ## Multilinear extensions and the fixed-column closed forms -/

/-- The multilinear extension of the table `f` (rows `[0, 2^|r|)`) at the point `r`, variable `i`
being bit `i` of the row index (lowest first). -/
def mle : List FE → (Nat → FE) → FE
  | [], f => f 0
  | r :: rs, f => (1 - r) * mle rs (fun x => f (2 * x)) + r * mle rs (fun x => f (2 * x + 1))

/-- `eq(r, x) = Π_i (x_i ? r_i : 1 - r_i)`. -/
def eqW : List FE → Nat → FE
  | [], _ => 1
  | r :: rs, x => (if x % 2 = 1 then r else 1 - r) * eqW rs (x / 2)

/-- The extension of the power column `x ↦ c^x` (`c^{2^b}` by squaring): `Π_b (1 - r_b + r_b c^{2^b})`. -/
def powEval : List FE → FK → FE
  | [], _ => 1
  | r :: rs, c => (1 - r + r * FE.ofK c) * powEval rs (c * c)

/-- The extension of `j ↦ Π_d (g^{s_d})^{j_d}` on a box `dims`, the point split per dimension. -/
def boxEval : List Nat → List Nat → List FE → FE
  | d :: ds, s :: ss, r => powEval (r.take d) (FK.x ^ s) * boxEval ds ss (r.drop d)
  | _, _, _ => 1

/-- The coefficients of a template-row-indexed sum: `Σ_i eq(r, i)·f i` over `2^|r|` rows. -/
def tplSum (r : List FE) (f : Nat → FE) : FE := mle r f

/-- The strides of a dense result: `w, w·2^{D₀}, w·2^{D₀+D₁}, …` (so `dot` is `w · flat`). -/
def scaledStrides : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, w => w :: scaledStrides ds (w * 2 ^ d)

namespace Program

variable (Q : Program)

/-- The exponent base and strides of an address column at template row `t` of a piece's block. -/
def colAffine (p : Piece) (c : FCol) (t : Nat) : Nat × List Nat :=
  let B := Q.blk p.blk
  let r := B.tpl.getD t default
  match c with
  | .res => (Q.start r.ty p.blk + B.rank r.ty t, scaledStrides B.dims (B.tw r.ty))
  | .arg o => ((r.args.getD o default).base, (r.args.getD o default).strides)
  | _ => (0, [])

/-- **The closed form of a structured fixed column** at the piece point `r` (loop variables first,
then the `a` template variables): for an address column `Σ_i eq(r_I, i)·g^{base_i}·boxEval`, for a
constant column `Σ_i eq(r_I, i)·k_i`. Cost `O(2^a · lsize)` products (`O(2^a + lsize)` when the
template rows share their strides). `fixmul`'s `F` is the glue matrix's, evaluated by
`fixMatEval`. -/
def pieceEval (p : Piece) (c : FCol) (r : List FE) : FE :=
  let B := Q.blk p.blk
  let rJ := r.take B.lsize
  let rI := r.drop B.lsize
  match c with
  | .res | .arg _ => tplSum rI fun i =>
      let t := p.ts.getD i 0
      let (base, s) := Q.colAffine p c t
      FE.ofK (FK.x ^ base) * boxEval B.dims s rJ
  | .k | .k' => tplSum rI fun i => FE.ofK (Q.fvalBasic p c (B.size * i))
  | .F => 0

end Program

end Lvm.Loop
