import Thrackle78.Checker.FilterB
import T78N660

open Thrackle78 Thrackle78Core

theorem T78Native.N660.filters_ok :
    T78Native.N660.fs.all (fun φl => checkFilterO 11 lDB660.toArray φl.1 φl.2 T78Native.N660.orcF) = true := by
  native_decide
