import T78T337
import Std.Data.HashMap

/-! Filter-tree inputs of the native run `T337`: the index function of the systems of the indexed filters (filter-tree
leaves, cover check) and the shard states of the filter tree of `c10a` (stage 7; h7.txt,
sha256 ad2f6993a7000dee…). -/

load_cert_chunk T78Native.T337.dhs "data/T337.hs" 12479999084125234521

namespace T78Native.T337

open Thrackle78Core

/-- The index table of the compact lines (a constant, computed once). -/
@[noinline] def dtab : Std.HashMap String Nat :=
  (List.range dlines.size).foldl (fun mp j => mp.insert (dlines.getD j "") j) {}

/-- The index function of the systems (by their compact line). -/
def dlook (x : List (List Nat)) : Nat :=
  dtab.getD ("|".intercalate (x.map fun r => String.ofList (r.map fun d => Char.ofNat (d + 48)))) dlines.size

/-- The shard states of the filter tree of `c10a`. -/
def HA : Array (Nat × Array (List Nat)) := statesOfFile 13 dhs

/-- Filter-tree batch `i`. -/
def hbatch (i : Nat) : List (Nat × Array (List Nat)) := sliceOf HA 600 i

/-- All filter-tree batches. -/
def hLs : List (List (Nat × Array (List Nat))) := (List.range 600).map hbatch

/-- The index table of the filter-tree shard states (a constant, computed once). -/
@[noinline] def hlookTab : LookTab (Nat × Array (List Nat)) := stateTab hLs.flatten.toArray

/-- The index function of the filter-tree shard states. -/
def hlook (s : Nat × Array (List Nat)) : Nat := hlookTab.get s

end T78Native.T337
