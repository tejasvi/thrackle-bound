import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.U13

/-! `CompFacts.u13`: the listing `lU13` (as run) is not combinatorially thrackleable (native check of a
certificate with 6 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u13 : ¬ CombThr (mkE 10 lU13) :=
  not_combThr_mkE_of_checkI 10 lU13 (by decide)
    [parseFilter (T78Data.u13f0c0.toUTF8),
      parseFilter (T78Data.u13f1c0.toUTF8),
      parseFilter (T78Data.u13f2c0.toUTF8),
      parseFilter (T78Data.u13f3c0.toUTF8),
      parseFilter (T78Data.u13f4c0.toUTF8),
      parseFilter (T78Data.u13f5c0.toUTF8
          ++ T78Data.u13f5c1.toUTF8
          ++ T78Data.u13f5c2.toUTF8
          ++ T78Data.u13f5c3.toUTF8
          ++ T78Data.u13f5c4.toUTF8
          ++ T78Data.u13f5c5.toUTF8
          ++ T78Data.u13f5c6.toUTF8
          ++ T78Data.u13f5c7.toUTF8
          ++ T78Data.u13f5c8.toUTF8
          ++ T78Data.u13f5c9.toUTF8
          ++ T78Data.u13f5c10.toUTF8
          ++ T78Data.u13f5c11.toUTF8
          ++ T78Data.u13f5c12.toUTF8)]
    (textReaderX (T78Data.u13mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
