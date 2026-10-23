import Thrackle78Core.Search

/-!
# Reading certificates in the text format (core Lean only)

One record per line, decimal numbers separated by spaces: `E` (expand the node), `K …` (a `K₅` model) or `B …`
(a `K₃,₃` model); a model lists, for each branch set in order, its size `s` and `s` pairs `(vertex id, parent
position)`, then for each edge of `hEdges` a pair of positions. The soundness of `check` holds for every `Reader`;
this one only decodes the data.
-/

namespace Thrackle78Core

/-- The byte at a position (`0` beyond the end). -/
@[inline] def byteAt (b : ByteArray) (pos : Nat) : UInt8 := if h : pos < b.size then b[pos] else 0

/-- Skip spaces and line ends. -/
def skipWs (b : ByteArray) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos =>
    let c := byteAt b pos
    if c == 32 || c == 10 || c == 13 then skipWs b fuel (pos + 1) else pos

/-- Read decimal digits into the accumulator. -/
def readDigits (b : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | 0, acc, pos => (acc, pos)
  | fuel + 1, acc, pos =>
    let c := byteAt b pos
    if 48 ≤ c && c ≤ 57 then readDigits b fuel (acc * 10 + (c.toNat - 48)) (pos + 1) else (acc, pos)

/-- Read a natural number (after spaces). -/
def readNat (b : ByteArray) (pos : Nat) : Nat × Nat := readDigits b 20 0 (skipWs b 64 pos)

/-- Read `cnt` pairs of numbers. -/
def readPairs (b : ByteArray) : Nat → Nat → Array (Nat × Nat) → Array (Nat × Nat) × Nat
  | 0, pos, acc => (acc, pos)
  | cnt + 1, pos, acc =>
    let x := readNat b pos
    let y := readNat b x.2
    readPairs b cnt y.2 (acc.push (x.1, y.1))

/-- Read `cnt` branch lists (each: its size, then the pairs). -/
def readBranches (b : ByteArray) : Nat → Nat → Array (Array (Nat × Nat)) → Array (Array (Nat × Nat)) × Nat
  | 0, pos, acc => (acc, pos)
  | cnt + 1, pos, acc =>
    let s := readNat b pos
    let br := readPairs b s.1 s.2 #[]
    readBranches b cnt br.2 (acc.push br.1)

/-- Read a model record starting at its letter `K` or `B`. -/
def readCert (b : ByteArray) (pos : Nat) : MinorCert × Nat :=
  let p0 := skipWs b 64 pos
  let k5 := byteAt b p0 == 75
  let br := readBranches b (if k5 then 5 else 6) (p0 + 1) #[]
  let wit := readPairs b (if k5 then 10 else 9) br.2 #[]
  ({ k5 := k5, branch := br.1, wit := wit.1 }, wit.2)

/-- The tag of the record at a position: `E` gives `0` (and the position after it), `K`/`B` give `1` (and the
position of the letter), anything else `2`. -/
def readTag (b : ByteArray) (pos : Nat) : Nat × Nat :=
  let p := skipWs b 64 pos
  let c := byteAt b p
  if c == 69 then (0, p + 1) else if c == 75 || c == 66 then (1, p) else (2, p)

/-- The text-format reader of the data `b`. -/
def textReader (b : ByteArray) : Reader where
  tag := readTag b
  cert := readCert b

end Thrackle78Core
