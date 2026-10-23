import Thrackle78.Checker.FilterB
import T78N682

open Thrackle78 Thrackle78Core

theorem T78Native.N682.batch_ok_53 :
    checkBFromList 11 lDB682.toArray (T78Native.N682.fs.map Prod.fst) (T78Native.N682.orcF lDB682.toArray) (T78Native.N682.batch 53) = true := by
  native_decide
