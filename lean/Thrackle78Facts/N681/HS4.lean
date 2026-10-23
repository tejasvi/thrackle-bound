import Thrackle78.Checker.FilterX
import T78N681T

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hshard_ok_4 :
    checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch 4) = true := by
  native_decide
