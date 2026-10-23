import Thrackle78.Checker.FilterB
import T78N660

open Thrackle78 Thrackle78Core

theorem T78Native.N660.top_ok :
    checkTop 11 lDB660.toArray (T78Native.N660.fs.map Prod.fst) (T78Native.N660.orcF lDB660.toArray) T78Native.N660.Ls.flatten.toArray T78Native.N660.look =
      true := by
  native_decide
