import Thrackle78Core.Reader
import Thrackle78.Checker.MkE
import T78Data.V4

/-! `CompFacts.v4`: the listing `lV4` (as run) is not combinatorially thrackleable (native check of a
30965-record certificate). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem v4 : ¬ CombThr (mkE 8 lV4) :=
  not_combThr_mkE_of_check 8 lV4 (by decide)
    (textReader (T78Data.v4c0.toUTF8)) (by native_decide)

end Thrackle78.Facts
