import Thrackle78Core
import T78Loader

/-! Inputs of the native run `N682` for `lDB682` (core Lean, untrusted): the data (shard states and filter systems,
FNV-1a pinned files under `data/`), the filters with their index functions, the shard states (stage and rows), the
batches (states with index `≡ r (mod 96)`), the index function of the states, and the oracle family.
* `ds`: DB682_states9.txt (sha256 61bd480bc4df4fd4…, 2761242 bytes)
* `df0`: lDB682_f0.filt (sha256 7fad309d075ae966…, 203549 bytes)
* `df1`: lDB682_f1.filt (sha256 a443acb8d57ad69a…, 6260416 bytes)
* `df2`: lDB682_f2.filt (sha256 0c78e137323de22a…, 6260416 bytes)
-/

load_cert_chunk T78Native.N682.ds "data/N682.s" 13630635552790755747
load_cert_chunk T78Native.N682.df0 "data/N682.f0" 13081586737104127599
load_cert_chunk T78Native.N682.df1 "data/N682.f1" 13691664943625634877
load_cert_chunk T78Native.N682.df2 "data/N682.f2" 14126420647093599626

namespace T78Native.N682

open Thrackle78Core

/-- Filter 0. -/
def φ0 : Filt := (parseFilter df0.toUTF8).1

/-- The index table of the systems of filter 0 (a constant, computed once). -/
@[noinline] def tab0 : LookTab (List (List Nat)) := sysTab φ0.sys

/-- The index function of the systems of filter 0. -/
def look0 (rl : List (List Nat)) : Nat := tab0.get rl

/-- Filter 1. -/
def φ1 : Filt := (parseFilter df1.toUTF8).1

/-- The index table of the systems of filter 1 (a constant, computed once). -/
@[noinline] def tab1 : LookTab (List (List Nat)) := sysTab φ1.sys

/-- The index function of the systems of filter 1. -/
def look1 (rl : List (List Nat)) : Nat := tab1.get rl

/-- Filter 2. -/
def φ2 : Filt := (parseFilter df2.toUTF8).1

/-- The index table of the systems of filter 2 (a constant, computed once). -/
@[noinline] def tab2 : LookTab (List (List Nat)) := sysTab φ2.sys

/-- The index function of the systems of filter 2. -/
def look2 (rl : List (List Nat)) : Nat := tab2.get rl

/-- The filters and their index functions. -/
def fs : List (Filt × (List (List Nat) → Nat)) :=
  [(φ0, look0), (φ1, look1), (φ2, look2)]

/-- The shard states. -/
def LA : Array (Nat × Array (List Nat)) := statesOfFile 12 ds

/-- Batch `r`. -/
def batch (r : Nat) : List (Nat × Array (List Nat)) := sliceOf LA 96 r

/-- All batches. -/
def Ls : List (List (Nat × Array (List Nat))) := (List.range 96).map batch

/-- The index table of the shard states (a constant, computed once). -/
@[noinline] def lookTab : LookTab (Nat × Array (List Nat)) := stateTab Ls.flatten.toArray

/-- The index function of the shard states. -/
def look (s : Nat × Array (List Nat)) : Nat := lookTab.get s

/-- The oracle of a listing. -/
def orcF : Array (Nat × Nat) → Oracle := fun es => BM.bmOrcKR 11 es

end T78Native.N682
