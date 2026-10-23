import T78T337

/-! Top-only inputs of the native run `T337`: the top filters (the bucket keys of `c10aX` and `c10bX` on their first 7
H-edges) and the list of all batches with the index function of the shard states. -/

namespace T78Native.T337

open Thrackle78Core

/-- The filters of the top tree. -/
def fsT : List Filt := [c10aX.topFilt 7, c10bX.topFilt 7]

/-- All batches. -/
def Ls : List (List (Nat × Array (List Nat))) := (List.range 1200).map batch

/-- The index table of the shard states (a constant, computed once). -/
@[noinline] def lookTab : LookTab (Nat × Array (List Nat)) := stateTab Ls.flatten.toArray

/-- The index function of the shard states. -/
def look (s : Nat × Array (List Nat)) : Nat := lookTab.get s

end T78Native.T337
