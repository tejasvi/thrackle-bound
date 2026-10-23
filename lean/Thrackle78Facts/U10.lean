import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.U10

/-! `CompFacts.u10`: the listing `lU10` (as run) is not combinatorially thrackleable (native check of a
850934-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u10 : ¬ CombThr (mkE 10 lU10) :=
  not_combThr_mkE_of_check 10 lU10 (by decide)
    (textReader (T78Data.u10c0.toUTF8
        ++ T78Data.u10c1.toUTF8
        ++ T78Data.u10c2.toUTF8)) (by native_decide)

end Thrackle78.Facts
