import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.U11

/-! `CompFacts.u11`: the listing `lU11` (as run) is not combinatorially thrackleable (native check of a
certificate with 6 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u11 : ¬ CombThr (mkE 11 lU11) :=
  not_combThr_mkE_of_checkI 11 lU11 (by decide)
    [parseFilter (T78Data.u11f0c0.toUTF8),
      parseFilter (T78Data.u11f1c0.toUTF8),
      parseFilter (T78Data.u11f2c0.toUTF8),
      parseFilter (T78Data.u11f3c0.toUTF8),
      parseFilter (T78Data.u11f4c0.toUTF8),
      parseFilter (T78Data.u11f5c0.toUTF8
          ++ T78Data.u11f5c1.toUTF8
          ++ T78Data.u11f5c2.toUTF8
          ++ T78Data.u11f5c3.toUTF8
          ++ T78Data.u11f5c4.toUTF8
          ++ T78Data.u11f5c5.toUTF8
          ++ T78Data.u11f5c6.toUTF8
          ++ T78Data.u11f5c7.toUTF8
          ++ T78Data.u11f5c8.toUTF8
          ++ T78Data.u11f5c9.toUTF8
          ++ T78Data.u11f5c10.toUTF8
          ++ T78Data.u11f5c11.toUTF8
          ++ T78Data.u11f5c12.toUTF8)]
    (textReaderX (T78Data.u11mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
