/-
`qasm`: the node program's placement record and program blob, generated from the entry's Lean.

Run through `qasm.py` (README.md); `QAsmMain.lean` is the executable. This module is not part of
the certificate: it lives outside `lean/`, may use `IO`, and is built only by the tool's own Lake
tree, where other programs can import it.
-/
import LvmQAsmProg
import LvmM3Grp
import LvmDecideM3Real

/-!
# The assembler and the blob dumper

The node program `Q C = QT C (dataOf C)` is built from its own placement record (`QData`): the table
phase of `Q_arith` reads the record's table shapes (`Har.qarithT`). The record is in turn computed
from the program. This tool computes it and iterates `D ↦ mkData C (QT C D)` to a fixed point,
then prints:

* the record as a Lean module (`LvmQAsmData8.lean`, `LvmQAsmData20.lean`);
* the program and its tables' inputs as a `LOOPIR1` blob (`q-p8.blob`, `q-p20.blob`), the grammar
  of `prover/src/lvm/loopir.rs`.

Every definition of the program, the groups, the arrays and the `BITS` classes is the entry's own
(imported, not restated). What the entry's Lean does not define, and this tool adds, is marked
**Tool logic** below: the placement order, the blob's encoding of the
array kinds, of the public arrays' lanes and of the free words, and the printers.
-/

set_option autoImplicit false

namespace QAsmTool

open Lvm Lvm.Loop Lvm.M3 Lvm.QAsm Lvm.BitsTab Lvm.Bits

/-! ## Parameter sets -/

/-- A parameter set: its configuration and the names of its generated files. -/
structure PSet where
  name : String
  cfg : QCfg
  defName : String
  dataFile : String
  blobFile : String

/-- The two parameter sets of the entry. -/
def psets : List PSet :=
  [⟨"P8", cfg8, "data8", "LvmQAsmData8.lean", "q-p8.blob"⟩,
   ⟨"P20", cfg20, "data20", "LvmQAsmData20.lean", "q-p20.blob"⟩]

/-! ## The record -/

/-- The first word of `C_main`'s free region, from the entry's shared layout (`LvmLayout`).
At P8 the digest tape follows `KS`'s `X` columns, so their end is not the free region's start.
The configuration selector is the one used by `QAsm.xOff` and `Har.dataOf`. -/
def freeLo (C : QCfg) : Nat := if C.rl = 14 then CMain.freeLo20 else CMain.freeLo8

/-- The committed columns of a `BITS` class, in column order (`BSpec.col`). -/
def bitsCom (S : BSpec) : List (Bool × Nat) :=
  (List.range S.width).filterMap fun c => match S.col c with
    | .com r o => some (r, o)
    | .fix .. => none

/-- **Tool logic.** The written input array: `LvmQAsmLay`'s `BITS` output region `ob`, the only
array whose value column the record places (`aval`). -/
def isWritten (C : QCfg) (a : InArr) : Bool := a.pub.isNone && a.base == obB C

/-- Cut `xs` into consecutive pieces of the lengths `ks`. -/
def splitBy : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | k :: ks, xs => xs.take k :: splitBy ks (xs.drop k)

/-- **Tool logic: the placement.** Every committed column the record places, in the record's field
order (the groups' columns in `Shape.committed` order, the arrays' finalize counts in `arrs` order,
the written array's value column, the `BITS` classes' columns in column order), sorted by height,
largest first and stable, and laid out back to back from `freeLo C` rounded up to the largest
column. Every height is a power of two, so every column is aligned. Returns the offsets in field
order and the first word past the last column. -/
def place (C : QCfg) (hs : List Nat) : List Nat × Nat :=
  let top := hs.foldl max 0
  let lo := (freeLo C + 2 ^ top - 1) / 2 ^ top * 2 ^ top
  let order := (List.range (top + 1)).reverse.flatMap fun t => hs.zipIdx.filter (·.1 == t)
  let r := order.foldl (fun (acc : Array Nat × Nat) (ti : Nat × Nat) =>
    (acc.1.set! ti.2 acc.2, acc.2 + 2 ^ ti.1)) (Array.replicate hs.length 0, lo)
  (r.1.toList, r.2)

/-- **The record of a program**: its groups (`autoGroups`, the entry's), then the placements. -/
def mkData (C : QCfg) (Q : Program) : Except String QData := do
  let groups := autoGroups Q
  let D0 : QData := ⟨groups, [], [], 0, []⟩
  let arrs := Har.arrsS C D0
  let some w := arrs.find? (isWritten C) | throw "no written input array"
  let gk := groups.map fun g => g.σ.committed.length
  let bs := bspecs C D0
  let bk := bs.map fun S => (bitsCom S).length
  let hs := (groups.zip gk).flatMap (fun (g, k) => List.replicate k g.τ) ++ arrs.map (·.τ) ++
    [w.τ] ++ (bs.zip bk).flatMap (fun (S, k) => List.replicate k S.τ)
  let (offs, past) := place C hs
  if past > 2 ^ C.p.nuMain then
    throw s!"the record does not fit C_main: its columns end at {past} > 2^{C.p.nuMain}"
  let ng := gk.sum
  let na := arrs.length
  pure ⟨groups, splitBy gk (offs.take ng), (offs.drop ng).take na, offs.getD (ng + na) 0,
    splitBy bk (offs.drop (ng + na + 1))⟩

/-- Two records are equal. -/
def same (D E : QData) : Bool :=
  (D.groups.map fun g => (g.σ, g.τ, g.mem)) == (E.groups.map fun g => (g.σ, g.τ, g.mem)) &&
    D.gpl == E.gpl && D.afin == E.afin && D.aval == E.aval && D.bpl == E.bpl

/-- The program's committed words: every group's committed columns (the groups tile the pieces). -/
def qWords (D : QData) : Nat := (D.groups.map fun g => 2 ^ g.τ * g.σ.committed.length).sum

/-- The numbers the parameter record freezes and `fitsR` checks against the tables: `busDepth`,
`leafdecReads`, `tableRounds`, `tableEvals` (the schedule) and `pubTab` (the `PUB` table's
index). -/
structure Nums where
  busDepth : Nat
  leafdecReads : Nat
  tableRounds : Nat
  tableEvals : Nat
  pubTab : Nat
  deriving BEq

instance : ToString Nums :=
  ⟨fun s => s!"({s.busDepth}, {s.leafdecReads}, {s.tableRounds}, {s.tableEvals}), \
    pubTab {s.pubTab}"⟩

/-- The numbers the record's tables make, as `fitsR` computes them (it requires `leafdecReads = 1`).
The `PUB` table's index counts the sumcheck tables before it in `lvmTabs`' order (groups, input
arrays, `BITS` tables). -/
def numsOf (C : QCfg) (D : QData) : Nums :=
  let T := Har.tabsS C D
  let st := sumcheckTabs T
  let k := ((Har.arrsS C D).findIdx? (·.base == pbB C)).getD 0
  ⟨log2Ceil (pushLeavesR T), 1, (st.map (·.τ)).foldl max 0, (st.map (·.w)).sum,
    (sumcheckTabs (T.take (D.groups.length + k))).length⟩

/-- The numbers frozen in the configuration's parameter record. -/
def numsFrozen (C : QCfg) : Nums :=
  ⟨C.p.busDepth, C.p.leafdecReads, C.p.tableRounds, C.p.tableEvals, C.p.pubTab⟩

/-- **The assembler's iteration** `D ↦ mkData C (QT C D)` from `D`, at most `fuel` steps: the fixed
point and the program built from it, if it reaches one. The program is the specified `QAsm.QT`, the
one the certificate is about (`QAsm.Q C = QT C (dataOf C)`), not its linear-time mirror `VF.QTF`. -/
def fixpoint (C : QCfg) (D : QData) : Nat → (log : String → IO Unit) → IO (Option (QData × Program))
  | 0, _ => pure none
  | fuel + 1, log => do
    let Q := QAsm.QT C D
    let D' ← IO.ofExcept (mkData C Q)
    log s!"  record -> program -> record: {D'.groups.length} groups, \
      Q {qWords D'} committed words, numbers {numsOf C D'}"
    if same D' D then pure (some (D, Q)) else fixpoint C D' fuel log

/-! ## The record as a Lean module -/

def tyStr : Ty → String
  | .K => ".K"
  | .E => ".E"

def kindStr : Kind → String
  | .muladd => ".muladd"
  | .lin => ".lin"
  | .assert0 => ".assert0"
  | .loadE => ".loadE"
  | .fixmul => ".fixmul"
  | .readd => ".readd"

def shapeStr (σ : Shape) : String :=
  s!"⟨{kindStr σ.kind}, {tyStr σ.ty}, [{", ".intercalate (σ.args.map tyStr)}]⟩"

def natList (l : List Nat) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"

def grpStr (g : Grp) : String :=
  s!"⟨{shapeStr g.σ}, {g.τ}, [{", ".intercalate (g.mem.map fun (n, o) => s!"({n}, {o})")}]⟩"

/-- A list one item per line. -/
def lines (items : List String) : String :=
  "[\n" ++ ",\n".intercalate (items.map ("    " ++ ·)) ++ "]"

/-- **Tool logic: the printer.** The record module; `header` (comment lines) comes first. -/
def renderData (header defName : String) (D : QData) : String :=
  header ++ "import LvmQAsmTabs\n\nset_option autoImplicit false\n\nnamespace Lvm.QAsm\n\n" ++
    "open Lvm.Loop Lvm.M3\n\nset_option maxRecDepth 200000 in\n" ++
    "/-- The placement record (`QData`). -/\ndef " ++ defName ++ " : QData where\n" ++
    "  groups := " ++ lines (D.groups.map grpStr) ++ "\n" ++
    "  gpl := " ++ lines (D.gpl.map natList) ++ "\n" ++
    "  afin := " ++ natList D.afin ++ "\n" ++
    "  aval := " ++ toString D.aval ++ "\n" ++
    "  bpl := " ++ lines (D.bpl.map natList) ++ "\n\nend Lvm.QAsm\n"

/-! ## The program as a `LOOPIR1` blob -/

/-- Tokens. -/
abbrev W := StateM (Array String)

def tok (s : String) : W Unit := modify (·.push s)
def num (k : Nat) : W Unit := tok (toString k)
def bit (b : Bool) : W Unit := num (if b then 1 else 0)
/-- A list with its length first. -/
def many {α : Type} (l : List α) (f : α → W Unit) : W Unit := do
  num l.length
  for x in l do f x

def tyW (t : Ty) : W Unit := num (match t with | .K => 0 | .E => 1)

def opW : Op → W Unit
  | .muladd => num 0
  | .lin k k' => do num 1; num k.val.toNat; num k'.val.toNat
  | .assert0 => num 2
  | .loadE => num 3
  | .fixmul => num 4
  | .readd lo m => do num 5; num lo; num m

def rowW (r : Loop.Row) : W Unit := do
  opW r.op; tyW r.ty
  many r.args fun (a : Addr) => do tyW a.ty; num a.base; many a.strides num

/-- `LOOPIR1 nInK nInE nBlocks {nDims {dim} nRows {row}} nGlue {glue}`. -/
def progW (Q : Program) : W Unit := do
  tok "LOOPIR1"; num Q.nInK; num Q.nInE
  many Q.blocks fun B => do many B.dims num; many B.tpl rowW
  many Q.glue num

def plW (p : Bool × Nat) : W Unit := do bit p.1; num p.2

def boutW : BOut → W Unit
  | .shl k => do num 0; num k; num 0; num 0
  | .shr k => do num 1; num k; num 0; num 0
  | .bit z => do num 2; num z; num 0; num 0
  | .fld z m d => do num 3; num z; num m; num d

/-- **Tool logic: the public lanes.** The prover's public lanes (`m3::pub_lanes`) are the header's
lanes from byte 8 with the statement `c`'s four lanes inserted after `vk`; `Pub.hdrLanes` is the
same list without `c`. So header lane `i` is public lane `i` below 5 and `i + 4` from 5 on, and the
constant lanes (`PUBX`) start at `pubLanes + 4`. -/
def hdrSel : List Nat := (List.range pubLanes).map fun i => if i < 5 then i else i + 4

/-- The lanes a public array selects: the header (`PUB`, at `pbB C`) or Q_link's static table
(`QLT`, at `qtB C`, the `PUBX` lanes). -/
def pubSel (C : QCfg) (nQlt : Nat) (a : InArr) : Except String (List Nat) :=
  if a.base == pbB C then pure hdrSel
  else if a.base == qtB C then pure ((List.range nQlt).map (pubLanes + 4 + ·))
  else throw s!"a public input array at {a.base} that is neither PUB nor QLT"

/-- **Tool logic: the free words.** A `BITS` class that reads no word (`rd = false`, Q_sig's `cs`)
gets the prover-computed WOTS checksum of the message digest in `(sigIn C).md` (kind 0). -/
def frees (C : QCfg) (bs : List BSpec) : List (Nat × Nat × Nat) :=
  bs.zipIdx.filterMap fun (S, k) => if S.rd then none else some (k, 0, (sigIn C).md)

/-- The `M3B` section: `lvmTabs`' inputs (groups, input arrays, `BITS` classes), then `PUBX` and
`FREE`. -/
def m3W (C : QCfg) (D : QData) (sel : InArr → Except String (List Nat)) (qlt : List FK) :
    ExceptT String W Unit := do
  tok "M3B"
  many D.groups.zipIdx fun (g, i) => do
    num g.τ
    many g.mem fun (n, o) => do num n; num o
    many (g.σ.committed.map (plOf D i)) plW
  num (Har.arrsS C D).length
  for a in Har.arrsS C D do
    tyW a.ty; num a.τ; num a.base; num a.stride
    -- **Tool logic: the array kinds** (0 aliased, 1 written, 2 public)
    num (if a.pub.isSome then 2 else if isWritten C a then 1 else 0)
    many a.val plW; plW a.fin
    if a.pub.isSome then
      let s ← sel a
      many s num
  tok "BITS"
  let bs := bspecs C D
  many bs fun S => do
    num S.τ; num S.n; bit S.rd
    many S.outs boutW
    for x in List.range S.n do num (S.wc x)
    for j in List.range S.outs.length do
      for x in List.range S.n do num (S.oc j x)
    many (bitsCom S) plW
  tok "PUBX"
  many qlt fun v => num v.val.toNat
  tok "FREE"
  many (frees C bs) fun (k, kind, cell) => do num k; num kind; num cell

/-- **The blob** of a program and its record. -/
def renderBlob (C : QCfg) (Q : Program) (D : QData) : Except String String :=
  let qlt := QLink.qltData C.p (lay C)
  let w : ExceptT String W Unit := do progW Q; m3W C D (pubSel C qlt.length) qlt
  let (r, toks) := w.run.run #[]
  r.map fun _ => " ".intercalate toks.toList ++ "\n"

/-! ## The command line -/

def usage : String :=
  "usage: qasm SET OUTDIR HEADER [--start shipped|empty] [--max-iter N]\n" ++
  "  SET: P8 or P20; HEADER: a file whose text heads the record module (comment lines)\n" ++
  "  exit status: 0 done, 2 usage, 3 written but the frozen numbers (schedule, pubTab) differ,\n" ++
  "  4 no fixed point (nothing written)"

def parseOpts : List String → Except String (String × Nat)
  | [] => pure ("shipped", 8)
  | "--start" :: s :: rest => do let (_, n) ← parseOpts rest; pure (s, n)
  | "--max-iter" :: n :: rest => do
    let (s, _) ← parseOpts rest
    match n.toNat? with
    | some k => pure (s, k)
    | none => throw s!"--max-iter {n}: not a number"
  | x :: _ => throw s!"unknown option {x}\n{usage}"

def main (args : List String) : IO UInt32 := do
  match args with
  | set :: outDir :: headerFile :: opts =>
    let some ps := psets.find? (·.name == set)
      | do IO.eprintln s!"unknown set {set}\n{usage}"; pure 2
    let (start, maxIt) ← IO.ofExcept (parseOpts opts)
    let C := ps.cfg
    let header ← IO.FS.readFile headerFile
    let D0 ← match start with
      | "shipped" => pure (Har.dataOf C)
      | "empty" => pure (⟨[], [], [], 0, []⟩ : QData)
      | s => throw (IO.userError s!"--start {s}: shipped or empty")
    IO.println s!"{set}: the iteration from the {start} record"
    match ← fixpoint C D0 maxIt IO.println with
    | none =>
      IO.println s!"{set}: no fixed point after {maxIt} iterations \
        (README.md, \"When the fixed point breaks\")"
      pure 4
    | some (D, Q) =>
      let ns := numsOf C D
      IO.println s!"{set}: fixed point: {D.groups.length} groups, {Q.blocks.length} blocks, \
        Q {qWords D} committed words; numbers {ns}, frozen {numsFrozen C}"
      IO.FS.createDirAll outDir
      IO.FS.writeFile (System.FilePath.mk outDir / ps.dataFile) (renderData header ps.defName D)
      IO.FS.writeFile (System.FilePath.mk outDir / ps.blobFile) (← IO.ofExcept (renderBlob C Q D))
      IO.println s!"{set}: wrote {ps.dataFile} and {ps.blobFile} to {outDir}"
      if ns != numsFrozen C then
        IO.println s!"{set}: the numbers {ns} differ from the frozen {numsFrozen C}: the \
          parameter record must change too (README.md)"
        pure 3
      else pure 0
  | _ => IO.eprintln usage; pure 2

end QAsmTool
