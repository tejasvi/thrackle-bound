import Thrackle78.Checker.FilterX
import T78N681

open Thrackle78 Thrackle78Core

theorem T78Native.N681.batch_ok_50 :
    checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch 50) = true := by
  native_decide
