import Thrackle78.Checker.FilterB
import T78N660

open Thrackle78 Thrackle78Core

theorem T78Native.N660.batch_ok_34 :
    checkBFromList 11 lDB660.toArray (T78Native.N660.fs.map Prod.fst) (T78Native.N660.orcF lDB660.toArray) (T78Native.N660.batch 34) = true := by
  native_decide
