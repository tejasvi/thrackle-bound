import Thrackle78Core
import T78Loader
import T78FX
import T78BM3
import T78BM3Fam
import T78N681Dh12
import T78N681Dh54

/-! Inputs of the native run `N681` for `lDB681` (core Lean, untrusted): shard-state lines and batches (states with
index `≡ r (mod 1200)`, parsed per batch), the indexed batch filters (h12, h54), the
oracle family and the family hints. The top-tree inputs are in `T78N681T`.
* states: DB681r_states10_sym.txt (sha256 b85af604a8812b08…, 694211 states), 2 chunks
-/

load_cert_chunk T78Native.N681.ds0 "data/N681.s0" 7934510893877276264
load_cert_chunk T78Native.N681.ds1 "data/N681.s1" 17826545950475415033

namespace T78Native.N681

open Thrackle78Core

/-- The compact lines of indexed filter `h12` (each chunk split separately). -/
def h12lines : Array String :=
  #[h12c0, h12c1, h12c2, h12c3, h12c4, h12c5].foldl (fun acc c => acc ++ ((c.splitOn "\n").filter (· ≠ "")).toArray) #[]

/-- The systems of indexed filter `h12`. -/
def h12sysAt (j : Nat) : List (List Nat) := parseCompact (h12lines.getD j "")

/-- The bucket boundaries of indexed filter `h12`. -/
def h12bl : Array Nat := (((h12bltxt).replace "\n" " ").splitOn " ").filterMap String.toNat? |>.toArray

/-- Indexed filter `h12` (H-edges [0, 6, 7, 8, 9, 10, 11, 12, 1, 2]). -/
def h12X : FiltX :=
  ⟨[0, 6, 7, 8, 9, 10, 11, 12, 1, 2], 10, h12lines.size, h12sysAt, h12bl, mkBkeys [0, 6, 7, 8, 9, 10, 11, 12, 1, 2] 10 h12sysAt h12bl⟩

/-- The compact lines of indexed filter `h54` (each chunk split separately). -/
def h54lines : Array String :=
  #[h54c0, h54c1, h54c2, h54c3, h54c4, h54c5].foldl (fun acc c => acc ++ ((c.splitOn "\n").filter (· ≠ "")).toArray) #[]

/-- The systems of indexed filter `h54`. -/
def h54sysAt (j : Nat) : List (List Nat) := parseCompact (h54lines.getD j "")

/-- The bucket boundaries of indexed filter `h54`. -/
def h54bl : Array Nat := (((h54bltxt).replace "\n" " ").splitOn " ").filterMap String.toNat? |>.toArray

/-- Indexed filter `h54` (H-edges [0, 12, 11, 10, 9, 8, 7, 6, 5, 4]). -/
def h54X : FiltX :=
  ⟨[0, 12, 11, 10, 9, 8, 7, 6, 5, 4], 10, h54lines.size, h54sysAt, h54bl, mkBkeys [0, 12, 11, 10, 9, 8, 7, 6, 5, 4] 10 h54sysAt h54bl⟩

/-- The indexed filters of the batches. -/
def fsX : List FiltX := [h12X, h54X]

/-- The state lines of a chunk (after its header). -/
def linesOf (s : String) : Array String := (((s.splitOn "\n").drop 11).filter (· ≠ "")).toArray

/-- All state lines. -/
def lines : Array String := linesOf ds0 ++ linesOf ds1

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

end T78Native.N681
