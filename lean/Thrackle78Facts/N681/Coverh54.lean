import Thrackle78.Checker.FilterX
import Thrackle78.Checker.FilterAut
import T78N681T

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.N681.cover_h54 :
    (autFilt σ681 flip681 T78Native.N681.h12X.toFilt).sys.all (T78Native.N681.h54X.inS T78Native.N681.h54look) = true := by
  native_decide
