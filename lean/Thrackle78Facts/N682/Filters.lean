import Thrackle78.Checker.FilterB
import T78N682

open Thrackle78 Thrackle78Core

theorem T78Native.N682.filters_ok :
    T78Native.N682.fs.all (fun φl => checkFilterO 11 lDB682.toArray φl.1 φl.2 T78Native.N682.orcF) = true := by
  native_decide
