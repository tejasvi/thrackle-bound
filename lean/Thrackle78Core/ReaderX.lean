import Thrackle78Core.Filter
import Thrackle78Core.Reader

/-!
# Reading filter files and certificates with filters (core Lean only)

Records as in `Thrackle78Core.Reader`, plus `L i` (listed system `i`) and `F φ` (pruned by filter `φ`). A filter file
starts with `H h g₀ … g_{h-1}`, then `S c` and `c` systems (rows separated by `|`), then the records of its tree. As for
`Reader`, the soundness of the checks holds for any data.
-/

namespace Thrackle78Core

/-- The tag of a record: `E` `0`, `K`/`B` `1` (at the letter), `L` `3`, `F` `4` (after the letter), else `2`. -/
def readTagX (b : ByteArray) (pos : Nat) : Nat × Nat :=
  let p := skipWs b 64 pos
  let c := byteAt b p
  if c == 69 then (0, p + 1) else if c == 75 || c == 66 then (1, p)
  else if c == 76 then (3, p + 1) else if c == 70 then (4, p + 1) else (2, p)

/-- The text-format reader with listed systems and filters. -/
def textReaderX (b : ByteArray) : ReaderX where
  tag := readTagX b
  cert := readCert b
  num := readNat b

/-- Skip spaces only (not line ends). -/
def skipSp (b : ByteArray) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos => if byteAt b pos == 32 then skipSp b fuel (pos + 1) else pos

/-- Read one row (numbers up to `|` or the line end); the position is after the `|` or at the line end. -/
def readRow (b : ByteArray) : Nat → Nat → List Nat → List Nat × Nat
  | 0, pos, acc => (acc.reverse, pos)
  | fuel + 1, pos, acc =>
    let p := skipSp b 64 pos
    let c := byteAt b p
    if c == 124 then (acc.reverse, p + 1)
    else if 48 ≤ c && c ≤ 57 then
      let x := readDigits b 20 0 p
      readRow b fuel x.2 (x.1 :: acc)
    else (acc.reverse, p)

/-- Read `h` rows of one system. -/
def readSystem (b : ByteArray) : Nat → Nat → List (List Nat) → List (List Nat) × Nat
  | 0, pos, acc => (acc.reverse, pos)
  | cnt + 1, pos, acc =>
    let r := readRow b 1000 pos []
    readSystem b cnt r.2 (r.1 :: acc)

/-- Read `c` systems of `h` rows each. -/
def readSystems (b : ByteArray) (h : Nat) : Nat → Nat → List (List (List Nat)) → List (List (List Nat)) × Nat
  | 0, pos, acc => (acc.reverse, pos)
  | cnt + 1, pos, acc =>
    let s := readSystem b h (skipWs b 64 pos) []
    readSystems b h cnt s.2 (s.1 :: acc)

/-- Read `cnt` numbers. -/
def readNats (b : ByteArray) : Nat → Nat → List Nat → List Nat × Nat
  | 0, pos, acc => (acc.reverse, pos)
  | cnt + 1, pos, acc =>
    let x := readNat b pos
    readNats b cnt x.2 (x.1 :: acc)

/-- Parse a filter file: the filter and the reader of its tree records. -/
def parseFilter (b : ByteArray) : Filt × ReaderX :=
  let p0 := skipWs b 64 0
  let h := readNat b (p0 + 1)
  let g := readNats b h.1 h.2 []
  let p1 := skipWs b 64 g.2
  let c := readNat b (p1 + 1)
  let sys := readSystems b h.1 c.1 c.2 []
  ({ g := g.1, sys := sys.1 }, textReaderX (b.extract sys.2 b.size))

end Thrackle78Core
