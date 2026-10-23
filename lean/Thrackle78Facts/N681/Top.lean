import Thrackle78.Checker.FilterX
import Thrackle78.Checker.Sym681Q
import T78N681T

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.N681.top_ok :
    checkTopQ 12 lDB681.toArray (T78Native.N681.fsT.map Prod.fst) (T78Native.N681.orcF lDB681.toArray) T78Native.N681.Ls.flatten.toArray T78Native.N681.look
      (symSkip 10 R681 σ681 flip681) = true := by
  native_decide
