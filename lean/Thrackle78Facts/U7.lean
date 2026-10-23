import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.U7

/-! `CompFacts.u7`: the listing `lU7` (as run) is not combinatorially thrackleable (native check of a
certificate with 5 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u7 : ¬ CombThr (mkE 11 lU7) :=
  not_combThr_mkE_of_checkI 11 lU7 (by decide)
    [parseFilter (T78Data.u7f0c0.toUTF8),
      parseFilter (T78Data.u7f1c0.toUTF8),
      parseFilter (T78Data.u7f2c0.toUTF8),
      parseFilter (T78Data.u7f3c0.toUTF8),
      parseFilter (T78Data.u7f4c0.toUTF8
          ++ T78Data.u7f4c1.toUTF8
          ++ T78Data.u7f4c2.toUTF8
          ++ T78Data.u7f4c3.toUTF8
          ++ T78Data.u7f4c4.toUTF8
          ++ T78Data.u7f4c5.toUTF8
          ++ T78Data.u7f4c6.toUTF8
          ++ T78Data.u7f4c7.toUTF8
          ++ T78Data.u7f4c8.toUTF8
          ++ T78Data.u7f4c9.toUTF8
          ++ T78Data.u7f4c10.toUTF8
          ++ T78Data.u7f4c11.toUTF8
          ++ T78Data.u7f4c12.toUTF8)]
    (textReaderX (T78Data.u7mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
