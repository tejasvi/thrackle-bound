import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.U14

/-! `CompFacts.u14`: the listing `lU14` (as run) is not combinatorially thrackleable (native check of a
1341036-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u14 : ¬ CombThr (mkE 10 lU14) :=
  not_combThr_mkE_of_check 10 lU14 (by decide)
    (textReader (T78Data.u14c0.toUTF8
        ++ T78Data.u14c1.toUTF8
        ++ T78Data.u14c2.toUTF8
        ++ T78Data.u14c3.toUTF8
        ++ T78Data.u14c4.toUTF8)) (by native_decide)

end Thrackle78.Facts
