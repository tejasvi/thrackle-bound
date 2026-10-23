import Thrackle78Core.ReaderX
import Thrackle78Core.Bytes
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.DB683_0
import T78Data.DB683_1
import T78Data.DB683_2
import T78Data.DB683_3
import T78Data.DB683_4
import T78Data.DB683_5

/-! `CompFacts.db683`: the listing `lDB683` (as run) is not combinatorially thrackleable (native check of a
certificate with 3 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db683 : ¬ CombThr (mkE 10 lDB683) :=
  not_combThr_mkE_of_checkI 10 lDB683 (by decide)
    [parseFilter (catBytes [T78Data.db683f0c0]),
      parseFilter (catBytes [T78Data.db683f1c0,
          T78Data.db683f1c1,
          T78Data.db683f1c2,
          T78Data.db683f1c3,
          T78Data.db683f1c4,
          T78Data.db683f1c5,
          T78Data.db683f1c6,
          T78Data.db683f1c7,
          T78Data.db683f1c8,
          T78Data.db683f1c9,
          T78Data.db683f1c10,
          T78Data.db683f1c11,
          T78Data.db683f1c12]),
      parseFilter (catBytes [T78Data.db683f2c0,
          T78Data.db683f2c1,
          T78Data.db683f2c2,
          T78Data.db683f2c3,
          T78Data.db683f2c4,
          T78Data.db683f2c5,
          T78Data.db683f2c6,
          T78Data.db683f2c7,
          T78Data.db683f2c8])]
    (textReaderX (catBytes [T78Data.db683mc0,
          T78Data.db683mc1,
          T78Data.db683mc2,
          T78Data.db683mc3,
          T78Data.db683mc4,
          T78Data.db683mc5,
          T78Data.db683mc6,
          T78Data.db683mc7,
          T78Data.db683mc8,
          T78Data.db683mc9,
          T78Data.db683mc10,
          T78Data.db683mc11,
          T78Data.db683mc12,
          T78Data.db683mc13,
          T78Data.db683mc14,
          T78Data.db683mc15,
          T78Data.db683mc16,
          T78Data.db683mc17,
          T78Data.db683mc18,
          T78Data.db683mc19,
          T78Data.db683mc20,
          T78Data.db683mc21,
          T78Data.db683mc22,
          T78Data.db683mc23])) (by native_decide)

end Thrackle78.Facts
