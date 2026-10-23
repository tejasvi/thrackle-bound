import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.U16

/-! `CompFacts.u16`: the listing `lU16` (as run) is not combinatorially thrackleable (native check of a
certificate with 6 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u16 : ¬ CombThr (mkE 10 lU16) :=
  not_combThr_mkE_of_checkI 10 lU16 (by decide)
    [parseFilter (T78Data.u16f0c0.toUTF8),
      parseFilter (T78Data.u16f1c0.toUTF8),
      parseFilter (T78Data.u16f2c0.toUTF8),
      parseFilter (T78Data.u16f3c0.toUTF8),
      parseFilter (T78Data.u16f4c0.toUTF8),
      parseFilter (T78Data.u16f5c0.toUTF8
          ++ T78Data.u16f5c1.toUTF8
          ++ T78Data.u16f5c2.toUTF8
          ++ T78Data.u16f5c3.toUTF8
          ++ T78Data.u16f5c4.toUTF8
          ++ T78Data.u16f5c5.toUTF8
          ++ T78Data.u16f5c6.toUTF8
          ++ T78Data.u16f5c7.toUTF8
          ++ T78Data.u16f5c8.toUTF8
          ++ T78Data.u16f5c9.toUTF8
          ++ T78Data.u16f5c10.toUTF8
          ++ T78Data.u16f5c11.toUTF8
          ++ T78Data.u16f5c12.toUTF8)]
    (textReaderX (T78Data.u16mc0.toUTF8)) (by native_decide)

end Thrackle78.Facts
