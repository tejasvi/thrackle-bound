import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.DB662

/-! `CompFacts.db662`: the listing `lDB662` (as run) is not combinatorially thrackleable (native check of a
certificate with 2 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db662 : ¬ CombThr (mkE 9 lDB662) :=
  not_combThr_mkE_of_checkI 9 lDB662 (by decide)
    [parseFilter (T78Data.db662f0c0.toUTF8),
      parseFilter (T78Data.db662f1c0.toUTF8
          ++ T78Data.db662f1c1.toUTF8
          ++ T78Data.db662f1c2.toUTF8
          ++ T78Data.db662f1c3.toUTF8
          ++ T78Data.db662f1c4.toUTF8
          ++ T78Data.db662f1c5.toUTF8
          ++ T78Data.db662f1c6.toUTF8
          ++ T78Data.db662f1c7.toUTF8
          ++ T78Data.db662f1c8.toUTF8)]
    (textReaderX (T78Data.db662mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
