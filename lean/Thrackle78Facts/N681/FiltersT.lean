import Thrackle78Facts.N681.FT0
import Thrackle78Facts.N681.FT1
import Thrackle78Facts.N681.FT2

open Thrackle78 Thrackle78Core

theorem T78Native.N681.filtersT_ok : T78Native.N681.fsT.all (fun φl => checkFilterO 12 lDB681.toArray φl.1 φl.2 T78Native.N681.orcF) = true := by
  simp only [T78Native.N681.fsT, List.all_cons, List.all_nil, T78Native.N681.filterT_ok_0, T78Native.N681.filterT_ok_1, T78Native.N681.filterT_ok_2, Bool.and_self]
