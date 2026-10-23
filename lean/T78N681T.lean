import T78N681
import Std.Data.HashMap

/-! Top-only inputs of the native run `N681`: the list of all batches and the index function of the shard states (top
tree), the top-tree filters with their index functions (lDB681_f0.filt, lDB681_f1.filt, lDB681_f2.filt), the
index functions of the indexed filters (filter trees, cover checks) and the shard states of the filter tree of
`h12` (stage 9; h12_9.txt, sha256 7823d73392bfaba2…). -/

load_cert_chunk T78Native.N681.dhs "data/N681.hs" 6458437920328408844
load_cert_chunk T78Native.N681.df0 "data/N681.f0" 7052831588427506595
load_cert_chunk T78Native.N681.df1 "data/N681.f1" 8230367550982721696
load_cert_chunk T78Native.N681.df2 "data/N681.f2" 17868859426052611772

namespace T78Native.N681

open Thrackle78Core

/-- Top filter 0. -/
def φ0 : Filt := (parseFilter df0.toUTF8).1

/-- The index table of the systems of top filter 0 (a constant, computed once). -/
@[noinline] def tab0 : LookTab (List (List Nat)) := sysTab φ0.sys

/-- The index function of the systems of top filter 0. -/
def look0 (rl : List (List Nat)) : Nat := tab0.get rl

/-- Top filter 1. -/
def φ1 : Filt := (parseFilter df1.toUTF8).1

/-- The index table of the systems of top filter 1 (a constant, computed once). -/
@[noinline] def tab1 : LookTab (List (List Nat)) := sysTab φ1.sys

/-- The index function of the systems of top filter 1. -/
def look1 (rl : List (List Nat)) : Nat := tab1.get rl

/-- Top filter 2. -/
def φ2 : Filt := (parseFilter df2.toUTF8).1

/-- The index table of the systems of top filter 2 (a constant, computed once). -/
@[noinline] def tab2 : LookTab (List (List Nat)) := sysTab φ2.sys

/-- The index function of the systems of top filter 2. -/
def look2 (rl : List (List Nat)) : Nat := tab2.get rl

/-- The filters of the top tree. -/
def fsT : List (Filt × (List (List Nat) → Nat)) :=
  [(φ0, look0), (φ1, look1), (φ2, look2)]

/-- All batches. -/
def Ls : List (List (Nat × Array (List Nat))) := (List.range 1200).map batch

/-- The index table of the shard states (a constant, computed once). -/
@[noinline] def lookTab : LookTab (Nat × Array (List Nat)) := stateTab Ls.flatten.toArray

/-- The index function of the shard states. -/
def look (s : Nat × Array (List Nat)) : Nat := lookTab.get s

/-- The index table of the compact lines of `h12` (a constant, computed once). -/
@[noinline] def h12tab : Std.HashMap String Nat :=
  (List.range h12lines.size).foldl (fun mp j => mp.insert (h12lines.getD j "") j) {}

/-- The index function of the systems of `h12` (by their compact line). -/
def h12look (x : List (List Nat)) : Nat :=
  h12tab.getD ("|".intercalate (x.map fun r => String.ofList (r.map fun d => Char.ofNat (d + 48))))
    h12lines.size

/-- The index table of the compact lines of `h54` (a constant, computed once). -/
@[noinline] def h54tab : Std.HashMap String Nat :=
  (List.range h54lines.size).foldl (fun mp j => mp.insert (h54lines.getD j "") j) {}

/-- The index function of the systems of `h54` (by their compact line). -/
def h54look (x : List (List Nat)) : Nat :=
  h54tab.getD ("|".intercalate (x.map fun r => String.ofList (r.map fun d => Char.ofNat (d + 48))))
    h54lines.size

/-- The shard states of the filter tree of `h12`. -/
def HA : Array (Nat × Array (List Nat)) := statesOfFile 13 dhs

/-- Filter-tree batch `i`. -/
def hbatch (i : Nat) : List (Nat × Array (List Nat)) := sliceOf HA 300 i

/-- All filter-tree batches. -/
def hLs : List (List (Nat × Array (List Nat))) := (List.range 300).map hbatch

/-- The index table of the filter-tree shard states (a constant, computed once). -/
@[noinline] def hlookTab : LookTab (Nat × Array (List Nat)) := stateTab hLs.flatten.toArray

/-- The index function of the filter-tree shard states. -/
def hlook (s : Nat × Array (List Nat)) : Nat := hlookTab.get s

end T78Native.N681
