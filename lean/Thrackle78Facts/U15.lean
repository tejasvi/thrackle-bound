import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.U15

/-! `CompFacts.u15`: the listing `lU15` (as run) is not combinatorially thrackleable (native check of a
30965-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem u15 : ¬ CombThr (mkE 9 lU15) :=
  not_combThr_mkE_of_check 9 lU15 (by decide)
    (textReader (T78Data.u15c0.toUTF8)) (by native_decide)

end Thrackle78.Facts
