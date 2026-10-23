import Thrackle78Core
import T78Loader

/-! Inputs of the native run `N660` for `lDB660` (core Lean, untrusted): the data (shard states and filter systems,
FNV-1a pinned files under `data/`), the filters with their index functions, the shard states (stage and rows), the
batches (states with index `≡ r (mod 48)`), the index function of the states, and the oracle family.
* `ds`: DB660_states9.txt (sha256 457c4e849c7ce3fc…, 1582298 bytes)
* `df0`: lDB660_f0.filt (sha256 565fd92fac8f2fe4…, 310 bytes)
* `df1`: lDB660_f1.filt (sha256 87753f968237cb6d…, 3561 bytes)
* `df2`: lDB660_f2.filt (sha256 40dba12c8cbaacbe…, 3561 bytes)
* `df3`: lDB660_f3.filt (sha256 ae8cde0fab2b92e3…, 97157 bytes)
* `df4`: lDB660_f4.filt (sha256 ec8959de2b48b8d4…, 97157 bytes)
* `df5`: lDB660_f5.filt (sha256 00a1ff13c5d314c5…, 48716 bytes)
-/

load_cert_chunk T78Native.N660.ds "data/N660.s" 13554510060676743361
load_cert_chunk T78Native.N660.df0 "data/N660.f0" 10113894247900095187
load_cert_chunk T78Native.N660.df1 "data/N660.f1" 16842994707919591244
load_cert_chunk T78Native.N660.df2 "data/N660.f2" 6329728430003678887
load_cert_chunk T78Native.N660.df3 "data/N660.f3" 9684978408478269512
load_cert_chunk T78Native.N660.df4 "data/N660.f4" 1525553910817422704
load_cert_chunk T78Native.N660.df5 "data/N660.f5" 9298009586464679562

namespace T78Native.N660

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

/-- Filter 3. -/
def φ3 : Filt := (parseFilter df3.toUTF8).1

/-- The index table of the systems of filter 3 (a constant, computed once). -/
@[noinline] def tab3 : LookTab (List (List Nat)) := sysTab φ3.sys

/-- The index function of the systems of filter 3. -/
def look3 (rl : List (List Nat)) : Nat := tab3.get rl

/-- Filter 4. -/
def φ4 : Filt := (parseFilter df4.toUTF8).1

/-- The index table of the systems of filter 4 (a constant, computed once). -/
@[noinline] def tab4 : LookTab (List (List Nat)) := sysTab φ4.sys

/-- The index function of the systems of filter 4. -/
def look4 (rl : List (List Nat)) : Nat := tab4.get rl

/-- Filter 5. -/
def φ5 : Filt := (parseFilter df5.toUTF8).1

/-- The index table of the systems of filter 5 (a constant, computed once). -/
@[noinline] def tab5 : LookTab (List (List Nat)) := sysTab φ5.sys

/-- The index function of the systems of filter 5. -/
def look5 (rl : List (List Nat)) : Nat := tab5.get rl

/-- The filters and their index functions. -/
def fs : List (Filt × (List (List Nat) → Nat)) :=
  [(φ0, look0), (φ1, look1), (φ2, look2), (φ3, look3), (φ4, look4), (φ5, look5)]

/-- The shard states. -/
def LA : Array (Nat × Array (List Nat)) := statesOfFile 12 ds

/-- Batch `r`. -/
def batch (r : Nat) : List (Nat × Array (List Nat)) := sliceOf LA 48 r

/-- All batches. -/
def Ls : List (List (Nat × Array (List Nat))) := (List.range 48).map batch

/-- The index table of the shard states (a constant, computed once). -/
@[noinline] def lookTab : LookTab (Nat × Array (List Nat)) := stateTab Ls.flatten.toArray

/-- The index function of the shard states. -/
def look (s : Nat × Array (List Nat)) : Nat := lookTab.get s

/-- The oracle of a listing. -/
def orcF : Array (Nat × Nat) → Oracle := fun es => BM.bmOrcKR 11 es

end T78Native.N660
