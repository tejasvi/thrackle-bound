import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.V7

/-! `CompFacts.v7`: the listing `lV7` (as run) is not combinatorially thrackleable (native check of a
859809-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem v7 : ¬ CombThr (mkE 10 lV7) :=
  not_combThr_mkE_of_check 10 lV7 (by decide)
    (textReader (T78Data.v7c0.toUTF8
        ++ T78Data.v7c1.toUTF8
        ++ T78Data.v7c2.toUTF8
        ++ T78Data.v7c3.toUTF8)) (by native_decide)

end Thrackle78.Facts
