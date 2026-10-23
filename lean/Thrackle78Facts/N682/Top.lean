import Thrackle78.Checker.FilterB
import T78N682

open Thrackle78 Thrackle78Core

theorem T78Native.N682.top_ok :
    checkTop 11 lDB682.toArray (T78Native.N682.fs.map Prod.fst) (T78Native.N682.orcF lDB682.toArray) T78Native.N682.Ls.flatten.toArray T78Native.N682.look =
      true := by
  native_decide
