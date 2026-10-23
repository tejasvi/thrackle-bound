import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.DB663

/-! `CompFacts.db663`: `DB(6,6,-3)` (listing `lDB663` as run) is not combinatorially thrackleable (native check of a
532,018-node certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db663 : ¬ CombThr (mkE 8 lDB663) :=
  not_combThr_mkE_of_check 8 lDB663 (by decide)
    (textReader (T78Data.db663c0.toUTF8 ++ T78Data.db663c1.toUTF8)) (by native_decide)

end Thrackle78.Facts
