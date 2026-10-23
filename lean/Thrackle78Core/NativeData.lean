import Std.Data.HashMap
import Thrackle78Core.ReaderX

/-!
# Helpers for the native runs (core Lean only, untrusted)

Parsing of shard-state files and index tables (hash maps) for the `look` functions. The soundness theorems hold for
every value of these functions; a wrong index is caught by the equality checks of `checkTop` / `walkHO`. The tables are
meant to be top-level constants (computed once): an index function `fun x => (tab S).get x` would rebuild the table at
every call.
-/

namespace Thrackle78Core

/-- The rows of one state line (`|`-separated rows of edges `0, …`), padded to `m` rows. -/
def stateRowsOf (m : Nat) (ln : String) : Array (List Nat) :=
  let rows := (ln.splitOn "|").map fun r => ((r.splitOn " ").filter (· ≠ "")).map String.toNat!
  (List.range m).toArray.map fun j => rows.getD j []

/-- The states of a state file (header `H k h`, then `h` edge lines, then one state per line), at stage `k`, with `m`
rows. -/
def statesOfFile (m : Nat) (s : String) : Array (Nat × Array (List Nat)) :=
  let lines := s.splitOn "\n"
  let hdr := ((lines.headD "").splitOn " ").filter (· ≠ "")
  let k := (hdr.getD 1 "0").toNat!
  let h := (hdr.getD 2 "0").toNat!
  ((lines.drop (h + 1)).filter (· ≠ "")).toArray.map fun ln => (k, stateRowsOf m ln)

/-- The states with index `≡ r (mod N)`, in order. -/
def sliceOf (A : Array (Nat × Array (List Nat))) (N r : Nat) : List (Nat × Array (List Nat)) :=
  ((List.range A.size).filter (· % N == r)).map fun i => A.getD i (0, #[])

/-- A hash table of indices; `get` returns `size` (not a valid index) for absent keys. -/
structure LookTab (α : Type) [BEq α] [Hashable α] where
  mp : Std.HashMap α Nat
  size : Nat

/-- The index of a key (or `size` if absent). -/
def LookTab.get {α : Type} [BEq α] [Hashable α] (t : LookTab α) (x : α) : Nat := t.mp.getD x t.size

/-- The index table of the entries of an array. -/
def stateTab (A : Array (Nat × Array (List Nat))) : LookTab (Nat × Array (List Nat)) :=
  ⟨(List.range A.size).foldl (fun mp i => mp.insert (A.getD i (0, #[])) i) {}, A.size⟩

/-- The index table of the systems of a filter. -/
def sysTab (S : List (List (List Nat))) : LookTab (List (List Nat)) :=
  let A := S.toArray
  ⟨(List.range A.size).foldl (fun mp i => mp.insert (A.getD i []) i) {}, A.size⟩

end Thrackle78Core
