import Thrackle78Core
import T78Loader
import T78FX
import T78FXF
import T78BM3
import T78BM3Fam
import T78T337D

/-! Inputs of the native run `T337` for `lTH337` (core Lean, untrusted): shard-state lines and batches (states with
index `≡ r (mod 1200)`, parsed per batch), the indexed batch filters `c10aX` and `c10bX` (one data array), the oracle
family and the family hints. The top-tree inputs are in `T78T337T`, the filter-tree inputs in `T78T337H`.
* states: states10_sym3.txt (sha256 31e7a3d2145205ab…, 283026 states), 1 chunks
-/

load_cert_chunk T78Native.T337.ds0 "data/T337.s0" 4165992990176001164

namespace T78Native.T337

open Thrackle78Core

/-- The compact lines of the indexed filters (each chunk split separately). -/
def dlines : Array String :=
  #[dc0, dc1, dc2, dc3, dc4, dc5, dc6, dc7, dc8, dc9].foldl (fun acc c => acc ++ ((c.splitOn "\n").filter (· ≠ "")).toArray) #[]

/-- The systems of the indexed filters. -/
def dsysAt (j : Nat) : List (List Nat) := parseCompact (dlines.getD j "")

/-- The bucket boundaries of the indexed filters. -/
def dbl : Array Nat := (((dbltxt).replace "\n" " ").splitOn " ").filterMap String.toNat? |>.toArray

/-- Indexed filter `c10a` (H-edges [0, 1, 2, 6, 7, 8, 9, 10, 11, 12]). -/
def c10aX : FiltX := ⟨[0, 1, 2, 6, 7, 8, 9, 10, 11, 12], 10, dlines.size, dsysAt, dbl, mkBkeys [0, 1, 2, 6, 7, 8, 9, 10, 11, 12] 10 dsysAt dbl⟩

/-- Indexed filter `c10b` (H-edges [3, 4, 5, 6, 7, 8, 9, 10, 11, 12]; the same systems). -/
def c10bX : FiltX := ⟨[3, 4, 5, 6, 7, 8, 9, 10, 11, 12], 10, dlines.size, dsysAt, dbl, mkBkeys [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 10 dsysAt dbl⟩

/-- The indexed filters of the batches. -/
def fsX : List FiltX := [c10aX, c10bX]

/-- The state lines of a chunk (after its header). -/
def linesOf (s : String) : Array String := (((s.splitOn "\n").drop 11).filter (· ≠ "")).toArray

/-- All state lines. -/
def lines : Array String := linesOf ds0

/-- The entries `r, r + N, r + 2N, …` of an array. -/
def sliceStep (A : Array String) (N r : Nat) : List String :=
  (List.range ((A.size + N - 1 - r) / N)).map fun j => A.getD (r + j * N) ""

/-- Batch `r`. -/
def batch (r : Nat) : List (Nat × Array (List Nat)) := (sliceStep lines 1200 r).map fun ln => (10, stateRowsOf 13 ln)

/-- The oracle of a listing. -/
def orcF : Array (Nat × Nat) → Oracle := fun es => BM3.bmOrcKR 12 es

/-- The family oracle of a listing. -/
def famOrcF (es : Array (Nat × Nat)) := BM3.famOrc 12 es

/-- The adaptation of a family model to a child, for a listing. -/
def adaptF (es : Array (Nat × Nat)) := BM3.adapt 12 es

end T78Native.T337
