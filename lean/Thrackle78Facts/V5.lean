import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.V5

/-! `CompFacts.v5`: the listing `lV5` (as run) is not combinatorially thrackleable (native check of a
850934-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem v5 : ¬ CombThr (mkE 9 lV5) :=
  not_combThr_mkE_of_check 9 lV5 (by decide)
    (textReader (T78Data.v5c0.toUTF8
        ++ T78Data.v5c1.toUTF8
        ++ T78Data.v5c2.toUTF8
        ++ T78Data.v5c3.toUTF8)) (by native_decide)

end Thrackle78.Facts
