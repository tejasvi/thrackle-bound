import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.U9

/-! `CompFacts.u9`: the listing `lU9` (as run) is not combinatorially thrackleable (native check of a
certificate with 5 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u9 : ¬ CombThr (mkE 10 lU9) :=
  not_combThr_mkE_of_checkI 10 lU9 (by decide)
    [parseFilter (T78Data.u9f0c0.toUTF8),
      parseFilter (T78Data.u9f1c0.toUTF8),
      parseFilter (T78Data.u9f2c0.toUTF8),
      parseFilter (T78Data.u9f3c0.toUTF8),
      parseFilter (T78Data.u9f4c0.toUTF8
          ++ T78Data.u9f4c1.toUTF8
          ++ T78Data.u9f4c2.toUTF8
          ++ T78Data.u9f4c3.toUTF8
          ++ T78Data.u9f4c4.toUTF8
          ++ T78Data.u9f4c5.toUTF8
          ++ T78Data.u9f4c6.toUTF8
          ++ T78Data.u9f4c7.toUTF8
          ++ T78Data.u9f4c8.toUTF8
          ++ T78Data.u9f4c9.toUTF8
          ++ T78Data.u9f4c10.toUTF8
          ++ T78Data.u9f4c11.toUTF8
          ++ T78Data.u9f4c12.toUTF8)]
    (textReaderX (T78Data.u9mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
